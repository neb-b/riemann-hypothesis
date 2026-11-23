module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0695
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0806
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0823
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraicWeightDominantIsoExists
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArtinPullbackIsGoodTwistOfAnticyclotomicTame
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0820
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0788
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0798
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0479
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0829
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0822
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0545
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0824
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0828
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0162
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0780

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraicFormsLevelGroupEqTwistLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MtRead
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.MtLev

theorem blockSizes_sub_eq_twoBlock {n : ℕ} (r : ℕ) : (Formalism.L2.DIV.blkOf (n := n) r (n - r)) = Formalism.L2.DIV.blk2 r := by
  funext a
  unfold Formalism.L2.DIV.blkOf Formalism.L2.DIV.blk2
  split_ifs with h
  · rfl
  · have : (a.val - r) / (n - r) = 0 := Nat.div_eq_of_lt (by omega)
    rw [this]

theorem mem_levJ_iff {D : D7} {S T : HSp D} {n : ℕ} (B : Base S T) (t : Twist D Circle) (P : principalLevelFrame.RowPsi S n) (g : GAf D.host.E n) :
    frameEquiv P g ∈ B.levJ t ↔ Lev.finE S (P.ψ g) ∈ Formalism.L2.DIV.lev D.sp.cm S.gram B.F.βS (B.levS t) := Iff.rfl

end GlobalTheory.MtLev

namespace GlobalTheory.MtLev

variable {D : D7} {V : HSp D} {n : ℕ} {hF : D.host.F = maximalRealSubfield D.host.E} {P : principalLevelFrame.RowPsi V n}

theorem loc_zero (hP : IdFrame hF P) (hn : V.rank = n) {κ : GAf D.host.E n} (hκ : κ ∈ ReciprocityTheory.Aut.Umax D.host.E n)
    (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (a c : Fin V.rank) :
    Valued.v (NX.locM s κ (Fin.cast hn a) (Fin.cast hn c)) < 1 ↔
      (Formalism.L2.DIV.redFn 1 s.w (Lev.finE V (P.ψ κ)) : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.DIV.kP s.w)) a c = 0 := by
  have h := ((_root_.GlobalTheory.MtRead.Red.red_eq_local D V n hF P hP hn κ).2 s hκ a c).2 0
  simp only [map_zero, zero_sub, Valuation.map_neg] at h
  exact h

theorem loc_one (hP : IdFrame hF P) (hn : V.rank = n) {κ : GAf D.host.E n} (hκ : κ ∈ ReciprocityTheory.Aut.Umax D.host.E n)
    (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (a : Fin V.rank) :
    Valued.v (NX.locM s κ (Fin.cast hn a) (Fin.cast hn a) - 1) < 1 ↔
      (Formalism.L2.DIV.redFn 1 s.w (Lev.finE V (P.ψ κ)) : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.DIV.kP s.w)) a a = 1 := by
  have h := ((_root_.GlobalTheory.MtRead.Red.red_eq_local D V n hF P hP hn κ).2 s hκ a a).2 1
  simp only [map_one] at h
  rw [Valuation.map_sub_swap] at h
  exact h

theorem cast_surj (hn : V.rank = n) (a : Fin n) : ∃ a' : Fin V.rank, Fin.cast hn a' = a :=
  ⟨Fin.cast hn.symm a, by simp⟩

theorem inParah_iff (hP : IdFrame hF P) (hn : V.rank = n) {κ : GAf D.host.E n} (hκ : κ ∈ ReciprocityTheory.Aut.Umax D.host.E n)
    (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (r : ℕ) :
    NX.InParah s.v r (NX.locM s κ) ↔ Formalism.L2.DIV.redFn 1 s.w (Lev.finE V (P.ψ κ)) ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) := by
  constructor
  · rintro ⟨-, h⟩ i j hij
    unfold Formalism.L2.DIV.blk2 at hij
    split_ifs at hij with h1 h2 <;> try omega
    exact (loc_zero hP hn hκ s i j).1 (h _ _ (by simpa using h2) (by simpa using h1))
  · intro h
    refine ⟨fun a b => ?_, fun a b ha hb => ?_⟩
    · obtain ⟨a', rfl⟩ := cast_surj hn a
      obtain ⟨b', rfl⟩ := cast_surj hn b
      exact ((_root_.GlobalTheory.MtRead.Red.red_eq_local D V n hF P hP hn κ).2 s hκ a' b').1
    · obtain ⟨a', rfl⟩ := cast_surj hn a
      obtain ⟨b', rfl⟩ := cast_surj hn b
      refine (loc_zero hP hn hκ s a' b').2 (Formalism.L2.DIV.mem_blockTri.1 h a' b' ?_)
      simp only [Fin.coe_cast] at ha hb
      unfold Formalism.L2.DIV.blk2
      rw [if_pos hb, if_neg (by omega)]
      exact Nat.zero_lt_one

end GlobalTheory.MtLev

namespace GlobalTheory.MtLev

variable {D : D7} {V : HSp D} {n : ℕ} {hF : D.host.F = maximalRealSubfield D.host.E} {P : principalLevelFrame.RowPsi V n}

def UT {m : ℕ} {k : Type} [CommRing k] (r : ℕ) (M : Matrix (Fin m) (Fin m) k) : Prop :=
  ∀ a c : Fin m, (a : ℕ) < r → (c : ℕ) < r → (c < a → M a c = 0) ∧ (a = c → M a c = 1)

theorem inLevG_iff (hP : IdFrame hF P) (hn : V.rank = n) {κ : GAf D.host.E n} (hκ : κ ∈ ReciprocityTheory.Aut.Umax D.host.E n)
    (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (r : ℕ) :
    NX.InLevG s.v r (NX.locM s κ) ↔ Formalism.L2.DIV.redFn 1 s.w (Lev.finE V (P.ψ κ)) ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) ∧
      UT r (Formalism.L2.DIV.redFn 1 s.w (Lev.finE V (P.ψ κ)) : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.DIV.kP s.w)) := by
  unfold NX.InLevG
  refine and_congr (inParah_iff hP hn hκ s r) ⟨fun h a c ha hc => ?_, fun h a b ha hb => ?_⟩
  · have h' := h (Fin.cast hn a) (Fin.cast hn c) (by simpa using ha) (by simpa using hc)
    refine ⟨fun hca => (loc_zero hP hn hκ s a c).1 (h'.1 hca), fun hac => ?_⟩
    subst hac
    exact (loc_one hP hn hκ s a).1 (h'.2 rfl)
  · obtain ⟨a', rfl⟩ := cast_surj hn a
    obtain ⟨b', rfl⟩ := cast_surj hn b
    have h' := h a' b' (by simpa using ha) (by simpa using hb)
    refine ⟨fun hba => (loc_zero hP hn hκ s a' b').2 (h'.1 hba), fun hab => ?_⟩
    have e : a' = b' := by simpa using hab
    subst e
    exact (loc_one hP hn hκ s a').2 (h'.2 rfl)

theorem UT_iff {m r : ℕ} {k : Type} [CommRing k] (hr : r ≤ m) (M : Matrix (Fin m) (Fin m) k) :
    UT r M ↔ ∀ a c : Fin r, (c < a → M (Fin.castLE hr a) (Fin.castLE hr c) = 0) ∧
      (a = c → M (Fin.castLE hr a) (Fin.castLE hr c) = 1) := by
  constructor
  · intro h a c
    have h' := h (Fin.castLE hr a) (Fin.castLE hr c) a.2 c.2
    exact ⟨fun hca => h'.1 hca, fun hac => h'.2 (by rw [hac])⟩
  · intro h a c ha hc
    have h' := h ⟨a, ha⟩ ⟨c, hc⟩
    have ea : Fin.castLE hr ⟨a, ha⟩ = a := Fin.ext rfl
    have ec : Fin.castLE hr ⟨c, hc⟩ = c := Fin.ext rfl
    rw [ea, ec] at h'
    refine ⟨fun hca => h'.1 hca, fun hac => h'.2 (by subst hac; rfl)⟩

end GlobalTheory.MtLev

namespace GlobalTheory.MtLev

theorem rTup_mem_iff (D : D7) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)) (t : Twist D Circle)
    (x : GL (Fin (Vc D j).rank) (Lev.EAf D)) (hPg : ∀ PP, PP ∈ B.G.Pg ↔ ∃ kv, PP = NX.pG D kv)
    (iso : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), ZMod (D.host.g kv.1) ≃+* kP (NX.pG D kv))
    (eG : G0g D.nd ≃* G0 B.G.Pg (Wc D j).rank)
    (hiso : ∀ (g : G0g D.nd) kv (h : NX.pG D kv ∈ B.G.Pg) (a c : Fin (Wc D j).rank), (eG g ⟨NX.pG D kv, h⟩).val a c =
      iso kv ((g kv).val (Fin.cast (FWT.rank_Wc j) a) (Fin.cast (FWT.rank_Wc j) c)))
    (hH : ∀ g, eG g ∈ B.G.P.H ↔ g ∈ D.nexp.U)
    (hU : D.nexp.U = NX.Uup (fun kv : (Σ kk : Fin 2, D.nd.PlG kk) => D.host.g kv.1) D.R.r)
    (hblk : ∀ kv, Formalism.L2.DIV.redFn 1 (NX.pG D kv) x ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 (Wc D j).rank)) :
    Formalism.L2.DIV.rTup 1 (B.levS t) x ∈ B.G.P.H ↔ ∀ kv, ∀ a c : Fin (Wc D j).rank,
      (c < a → (Formalism.L2.DIV.redFn 1 (NX.pG D kv) x : Matrix (Fin (Vc D j).rank) (Fin (Vc D j).rank) (kP (NX.pG D kv))) (Fin.castLE B.hr a) (Fin.castLE B.hr c) = 0) ∧
      (a = c → (Formalism.L2.DIV.redFn 1 (NX.pG D kv) x : Matrix (Fin (Vc D j).rank) (Fin (Vc D j).rank) (kP (NX.pG D kv))) (Fin.castLE B.hr a) (Fin.castLE B.hr c) = 1) := by
  set y : G0 B.G.Pg (Wc D j).rank := Formalism.L2.DIV.rTup 1 (B.levS t) x with hy
  have key : ∀ kv (h : NX.pG D kv ∈ B.G.Pg) (a c : Fin (Wc D j).rank),
      ((eG.symm y) kv).val (Fin.cast (FWT.rank_Wc j) a) (Fin.cast (FWT.rank_Wc j) c) =
        (iso kv).symm ((Formalism.L2.DIV.redFn 1 (NX.pG D kv) x : Matrix (Fin (Vc D j).rank) (Fin (Vc D j).rank) (kP (NX.pG D kv))) (Fin.castLE B.hr a) (Fin.castLE B.hr c)) := by
    intro kv h a c
    have e := hiso (eG.symm y) kv h a c
    rw [MulEquiv.apply_symm_apply] at e
    rw [RingEquiv.eq_symm_apply, ← e]
    have e2 : (y ⟨NX.pG D kv, h⟩ : Matrix (Fin (Wc D j).rank) (Fin (Wc D j).rank) (kP (NX.pG D kv))) =
        (Formalism.L2.DIV.upperLeftBlock B.hr (Formalism.L2.DIV.redFn 1 (NX.pG D kv) x) : Matrix (Fin (Wc D j).rank) (Fin (Wc D j).rank) (kP (NX.pG D kv))) := rfl
    rw [e2, Formalism.L2.DIV.upper_block_val_submatrix B.hr (hblk kv)]
    rfl
  have hmem := hH (eG.symm y)
  rw [MulEquiv.apply_symm_apply] at hmem
  refine hmem.trans ?_
  rw [hU, NX.mem_Uup]
  refine forall_congr' fun kv => ?_
  have h : NX.pG D kv ∈ B.G.Pg := (hPg _).2 ⟨kv, rfl⟩
  have hc : ∀ a' : Fin D.R.r, ∃ a : Fin (Wc D j).rank, Fin.cast (FWT.rank_Wc j) a = a' :=
    fun a' => ⟨Fin.cast (FWT.rank_Wc j).symm a', by simp⟩
  constructor
  · rintro ⟨h1, h2⟩ a c
    refine ⟨fun hca => ?_, fun hac => ?_⟩
    · have e : ((eG.symm y) kv).val (Fin.cast (FWT.rank_Wc j) a) (Fin.cast (FWT.rank_Wc j) c) = 0 := h1 hca
      rw [key kv h] at e
      exact (map_eq_zero_iff _ (iso kv).symm.injective).1 e
    · subst hac
      have e := h2 (Fin.cast (FWT.rank_Wc j) a)
      rw [key kv h] at e
      exact (iso kv).symm.injective (by rw [e, map_one])
  · intro H
    refine ⟨fun a' c' hca => ?_, fun a' => ?_⟩
    · obtain ⟨a, rfl⟩ := hc a'
      obtain ⟨c, rfl⟩ := hc c'
      rw [key kv h, (H a c).1 hca, map_zero]
    · obtain ⟨a, rfl⟩ := hc a'
      rw [key kv h, (H a a).2 rfl, map_one]

end GlobalTheory.MtLev

namespace GlobalTheory.MtLev

theorem levMem : ∀ (D : D7) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e : ℤ) (W₀ : Type) [AddCommGroup W₀] [Module (FractionRing (D.ntw.O i)) W₀] (ρ₀ : Representation (FractionRing (D.ntw.O i)) (ReciprocityTheory.Aut.GQ D.host.E D.R.nV) W₀) (τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ) (M : NX.MtVReal D i (j.1 + 1) b k Q ψ e W₀ ρ₀ τ) (B : GlobalTheory.ExportSeries.Base (Vc D j) (Wc D j)) (t : Twist D Circle) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi (Vc D j) D.R.nV), IdFrame hF P → B.F.βS = 1 → (∀ PP, PP ∈ B.G.Pg ↔ ∃ kv, PP = NX.pG D kv) → Function.Injective (NX.pG D) → t.Q = M.QP → B.de.Q = M.DP → ∀ (iso : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), ZMod (D.host.g kv.1) ≃+* kP (NX.pG D kv)) (eG : G0g D.nd ≃* G0 B.G.Pg (Wc D j).rank), (∀ (g : G0g D.nd) kv (h : NX.pG D kv ∈ B.G.Pg) (a c : Fin (Wc D j).rank), (eG g ⟨NX.pG D kv, h⟩).val a c = iso kv ((g kv).val (Fin.cast (FWT.rank_Wc j) a) (Fin.cast (FWT.rank_Wc j) c))) → (∀ g, eG g ∈ B.G.P.H ↔ g ∈ D.nexp.U) → D.nexp.U = NX.Uup (fun kv : (Σ kk : Fin 2, D.nd.PlG kk) => D.host.g kv.1) D.R.r → ∀ g, g ∈ M.J ↔ frameEquiv P g ∈ B.levJ t := by
  intro D i j b k Q ψ e W₀ _ _ ρ₀ τ M B t hF P hP hβ hPg hinj htQ hdQ iso eG hiso hH hU g
  classical
  obtain ⟨hn, -⟩ := id hP
  have hrW : (Wc D j).rank = D.R.r := FWT.rank_Wc j
  have hSt := (_root_.GlobalTheory.MtRead.Red.red_eq_local D (Vc D j) D.R.nV hF P hP hn g).1
  have hUA := GlobalTheory.LevSplit.finE_mem_UA (Vc D j) (P.ψ g)
  have levG_iff : ∀ (hU' : g ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV) kv,
      NX.InLevG (M.sp (NX.pG D kv)).v D.R.r (NX.locM (M.sp (NX.pG D kv)) g) ↔
        Formalism.L2.DIV.redFn 1 (NX.pG D kv) (Lev.finE (Vc D j) (P.ψ g)) ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 (Wc D j).rank) ∧
        UT (Wc D j).rank (Formalism.L2.DIV.redFn 1 (NX.pG D kv) (Lev.finE (Vc D j) (P.ψ g)) :
          Matrix (Fin (Vc D j).rank) (Fin (Vc D j).rank) (kP (NX.pG D kv))) := by
    intro hU' kv
    have h := inLevG_iff hP hn hU' (M.sp (NX.pG D kv)) D.R.r
    rw [M.sp_w _ (Or.inr (Or.inr ⟨kv, rfl⟩))] at h
    rw [h, hrW]
  have par_iff : ∀ (hU' : g ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV) PP, (PP ∈ M.QP ∨ PP ∈ M.DP) →
      (NX.InParah (M.sp PP).v D.R.r (NX.locM (M.sp PP) g) ↔
        Formalism.L2.DIV.redFn 1 PP (Lev.finE (Vc D j) (P.ψ g)) ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 (Wc D j).rank)) := by
    intro hU' PP hPP
    have h := inParah_iff hP hn hU' (M.sp PP) D.R.r
    rw [M.sp_w _ (hPP.elim Or.inl (fun h => Or.inr (Or.inl h)))] at h
    rw [h, hrW]
  have hblkOf : Formalism.L2.DIV.blkOf (n := (Vc D j).rank) (Wc D j).rank ((Vc D j).rank - (Wc D j).rank) =
      Formalism.L2.DIV.blk2 (Wc D j).rank := blockSizes_sub_eq_twoBlock _
  rw [M.J_mem, mem_levJ_iff, hβ, Formalism.L2.DIV.mem_lev, Formalism.L2.DIV.mem_parLev]
  constructor
  · rintro ⟨hU', hG, hQ, hD⟩
    have hGk := fun kv => (levG_iff hU' kv).1 (hG kv)
    have hblk : ∀ kv, Formalism.L2.DIV.redFn 1 (NX.pG D kv) (Lev.finE (Vc D j) (P.ψ g)) ∈
        Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 (Wc D j).rank) := fun kv => (hGk kv).1
    refine ⟨⟨hUA, hSt.1 hU', fun PP hPP => ?_, fun PP hPP => ?_⟩, ?_⟩
    · obtain ⟨kv, rfl⟩ := (hPg PP).1 hPP
      change _ ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf (Wc D j).rank ((Vc D j).rank - (Wc D j).rank))
      rw [hblkOf]
      exact hblk kv
    · change PP ∈ B.de.Q ∪ t.Q at hPP
      rw [hdQ, htQ] at hPP
      rcases Finset.mem_union.1 hPP with h | h
      · exact (par_iff hU' PP (Or.inr h)).1 (hD PP h)
      · exact (par_iff hU' PP (Or.inl h)).1 (hQ PP h)
    · exact (rTup_mem_iff D j B t _ hPg iso eG hiso hH hU hblk).2 fun kv => (UT_iff B.hr _).1 (hGk kv).2
  · rintro ⟨⟨-, hSt', hPg', hQ'⟩, hR⟩
    have hU' := hSt.2 hSt'
    have hblk : ∀ kv, Formalism.L2.DIV.redFn 1 (NX.pG D kv) (Lev.finE (Vc D j) (P.ψ g)) ∈
        Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 (Wc D j).rank) := fun kv => by
      have h := hPg' (NX.pG D kv) ((hPg _).2 ⟨kv, rfl⟩)
      change _ ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf (Wc D j).rank ((Vc D j).rank - (Wc D j).rank)) at h
      rwa [hblkOf] at h
    have hR' := (rTup_mem_iff D j B t _ hPg iso eG hiso hH hU hblk).1 hR
    have hQm : ∀ PP, PP ∈ M.QP ∨ PP ∈ M.DP → PP ∈ (B.levS t).Q := fun PP h => by
      change PP ∈ B.de.Q ∪ t.Q
      rw [hdQ, htQ]
      exact h.elim (Finset.mem_union_right _) (Finset.mem_union_left _)
    refine ⟨hU', fun kv => (levG_iff hU' kv).2 ⟨hblk kv, (UT_iff B.hr _).2 (hR' kv)⟩,
      fun PP hPP => (par_iff hU' PP (Or.inl hPP)).2 (hQ' PP (hQm PP (Or.inl hPP))),
      fun PP hPP => (par_iff hU' PP (Or.inr hPP)).2 (hQ' PP (hQm PP (Or.inr hPP)))⟩

end GlobalTheory.MtLev
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraicWeightDominantIsoExistsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraic_weight_dominant_iso_exists : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (emb : ι → L →+* ℂ), Function.Injective (emb) → (∀ t t', (emb) t ≠ ComplexEmbedding.conjugate ((emb) t')) → (∀ σ : L →+* ℂ, ∃ t, σ = (emb) t ∨ σ = ComplexEmbedding.conjugate ((emb) t)) → ∀ a : NG.AlgWt L n, ∃ (lam : ι → DomWeight n) (T : a.W ≃ₗ[ℂ] VV ℂ lam), ∀ (γ : ReciprocityTheory.Aut.GQ L n) (γ₀ : GL (Fin n) L), (((γ : GAf L n) : GL (Fin n) (ReciprocityTheory.Aut.AL L)) : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) = (γ₀ : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom → ∀ x, T (a.ρ γ x) = rhoVr emb lam γ₀ (T x) := by
  first | exact @GlobalTheory.WtClass.exists_equiv_VV | exact GlobalTheory.WtClass.exists_equiv_VV | (intros; apply GlobalTheory.WtClass.exists_equiv_VV <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArtinPullbackIsGoodTwistOfAnticyclotomicTameStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.artinPullback_isGoodTwist_of_anticyclotomic_tame : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (a : Recip D N.Om), a.Good → ∀ (A : Type) [CommGroup A] (φ : G D.host.E N.Om →* A) (l : ℕ), l.Prime → (∀ σ, ∃ n : ℕ, φ σ ^ (l ^ n) = 1) → IsOpen (φ.ker : Set (G D.host.E N.Om)) → AntiHom X.cc φ → ∀ Q : Finset (Pl D.host.E), SplitSet Q → (∀ P ∈ Q, ((l : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → (∀ v : Pl D.host.E, v ∉ Q → (∀ P ∈ Q, ¬ Formalism.BasicNotions.IsConjPl D.host P v) → ∀ B : ValuationSubring N.Om, IsPlaceOver B v → ∀ σ ∈ Ine (F := D.host.E) B, φ σ = 1) → (⟨Q, a.pull φ, resOf (a.pull φ)⟩ : Twist D A).Good := by
  first | exact @GlobalTheory.TwistPull.good_pull | exact GlobalTheory.TwistPull.good_pull | (intros; apply GlobalTheory.TwistPull.good_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralFlipSplitPlacesInvariantFormPhaseStatement
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralFlip_splitPlaces_invariantForm_phase : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χV χW om → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (eT : AE D) (m : ℕ) (z : GA D V) (x : (AE D)ˣ) (ℓ : (WO V W → ℂ) →ₗ[ℂ] ℂ), IsIdemSum eT T → m ≠ 0 → Formalism.L2.Theta.mt V z = flipElt eT m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) → IsFlipDet V eT m x → (∀ y : WO V W, IsHalf (cA D eT) y → ∀ φ : WO V W → ℂ, IsThetaFunO ψ V W φ → ℓ (heisO ψ V W y φ) = ℓ φ) → ∃ r : ℝ, 0 < r ∧ ∀ f : WO V W → ℂ, IsThetaFunO ψ V W f → ℓ (om (z⁻¹, 1) f) = (r : ℂ) * ((χW x : Circle) : ℂ)⁻¹ * ℓ f := by
  first | exact @GlobalTheory.LevelSeries.centralFlip_phase | exact GlobalTheory.LevelSeries.centralFlip_phase | (intros; apply GlobalTheory.LevelSeries.centralFlip_phase <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefLatLeTranslateSplitPlacesPrimeToL
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LatTranslate

theorem coefFn_natCast_smul {D : D7} {n : ℕ} {K : Type} [Field K] (σ : K →+* ℂ) (lam : D.what₂.Tau → Formalism.BasicNotions.DomWeight n)
    (N : ℕ) (F : Formalism.L2.DIV.Pol K D.what₂.Tau n) (x : GLR D n) :
    coefFn σ lam ((N : K) • F) x = (N : ℂ) * coefFn σ lam F x := by
  simp only [coefFn, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval₂Hom_C, map_natCast]
  ring

theorem coefLatFn_transfer {D : D7} {n : ℕ} {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ)
    (emb : D.what₂.Tau → D.host.E →+* K) (lam : D.what₂.Tau → Formalism.BasicNotions.DomWeight n) {O O' : Subring ℂ} (hOO : O ≤ O')
    {M M' : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (N : ℕ) (hN : N ≠ 0) (hinv : ((N : ℂ))⁻¹ ∈ O')
    (hF : ∀ F ∈ Formalism.L2.DIV.nabAtr emb lam M, (N : K) • F ∈ Formalism.L2.DIV.nabAtr emb lam M')
    {φ : GLR D n → ℂ} (hφ : φ ∈ coefLatFn σ emb O lam M) : φ ∈ coefLatFn σ emb O' lam M' := by
  induction hφ using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨F, hFm, rfl⟩ := h
    have h1 : coefFn σ lam (((N : K) • F : Formalism.L2.DIV.VV K lam) : Formalism.L2.DIV.Pol K D.what₂.Tau n) ∈ coefLatFn σ emb O' lam M' :=
      Submodule.subset_span ⟨_, hF F hFm, rfl⟩
    have h2 := Submodule.smul_mem _ (⟨_, hinv⟩ : O') h1
    convert h2 using 1
    funext x
    have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN
    change _ = (N : ℂ)⁻¹ * _
    rw [Submodule.coe_smul, coefFn_natCast_smul, inv_mul_cancel_left₀ hN']
  | zero => exact zero_mem _
  | add _ _ _ _ h1 h2 => exact add_mem h1 h2
  | smul c _ _ h1 => exact Submodule.smul_mem _ (⟨c, hOO c.2⟩ : O') h1

theorem normProd_ne_zero {D : D7} (Q : Finset (Pl D.host.E)) : normProd Q ≠ 0 := by
  unfold normProd
  refine Finset.prod_ne_zero_iff.2 fun v _ => ?_
  rw [Ne, Ideal.absNorm_eq_zero_iff]
  exact v.ne_bot


set_option maxHeartbeats 800000 in
theorem lat_translate : ∀ (D : D7) (ρ : Setup D.ntw), ρ.Good → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool), ∀ k (Q : Finset (Pl D.host.E)) (h hQ : GA D (Vc D j)) P, SplitSet Q → Disjoint Q (D.ntw.S0 i) → h ∈ GfC (Vc D j) → SuppAt (idem Q) (Vc D j) hQ → P ∈ ρ.lat i j b (ρ.eO i b).range h → P ∈ ρ.lat i j b (ρ.eOk i b k).range (h * hQ) := by
  intro D ρ hρ i j b k Q h hQ P hS hD hh hsupp hP
  unfold GlobalTheory.SeriesTie.Setup.lat GlobalTheory.ExportSeries.Base.coefLat at *
  rw [GlobalTheory.ExportSeries.mem_harmLat] at *
  refine ⟨hP.1, ?_⟩
  obtain ⟨c, h1, h2⟩ := _root_.GlobalTheory.LatCmpQ.latAt_translate_bounded D ρ hρ i j b Q h hQ hS hsupp
  have hN0 : normProd Q ^ c ≠ 0 := pow_ne_zero _ (normProd_ne_zero Q)
  obtain ⟨a, ha⟩ := GlobalTheory.T.dualWeylLattice_exists_natPow_smul_mem _ _ _ _ (labLL0 D) (ρ.B i j b).w.lam _ _ (normProd Q ^ c) hN0 (by first | exact GlobalTheory.LatFull.latAt_isFullLattice D ρ hρ i j b h | exact (GlobalTheory.LatFull.latAt_isFullLattice D ρ hρ i j b h).toIsLattice)
    (by first | exact GlobalTheory.LatFull.latAt_isFullLattice D ρ hρ i j b (h * hQ) | exact (GlobalTheory.LatFull.latAt_isFullLattice D ρ hρ i j b (h * hQ)).toIsLattice) h1 h2
  have hu : ((normProd Q : ℕ) : ℂ)⁻¹ ∈ (ρ.eOk i b k).range := hρ.range_le i b k (GlobalTheory.T.inv_place_norm_product_mem_coefficient_ring D ρ i b Q hD)
  have hinv : (((normProd Q ^ c) ^ a : ℕ) : ℂ)⁻¹ ∈ (ρ.eOk i b k).range := by
    rw [Nat.cast_pow, Nat.cast_pow, ← inv_pow, ← inv_pow]
    exact Subring.pow_mem _ (Subring.pow_mem _ hu _) _
  have hF : ∀ F ∈ Formalism.L2.DIV.nabAtr (labLL0 D) (ρ.B i j b).w.lam ((ρ.B i j b).latAt (finPt (Vc D j) h)),
      (((normProd Q ^ c) ^ a : ℕ) : ↥D.LL0) • F ∈
        Formalism.L2.DIV.nabAtr (labLL0 D) (ρ.B i j b).w.lam ((ρ.B i j b).latAt (finPt (Vc D j) (h * hQ))) := by
    intro F hF
    have := ha F hF
    rwa [Nat.cast_pow (α := ↥D.LL0) (normProd Q ^ c) a]
  exact coefLatFn_transfer (Formalism.L2.Host.embLL0 D) (labLL0 D) (ρ.B i j b).w.lam (hρ.range_le i b k)
    ((normProd Q ^ c) ^ a) (pow_ne_zero _ hN0) hinv hF hP.2

end GlobalTheory.LatTranslate

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsFundamentalDomainRationalUpperUnitriangu
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped ENNReal nonZeroDivisors

namespace GlobalTheory.CellDec

theorem exists_isFundamentalDomain_NE : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (μ : Measure (GA E a)),
    ∃ 𝓕₀ : Set (GA E a), IsFundamentalDomain (GlobalTheory.CellDec.NE E a) 𝓕₀ μ := by
  intro E _ _ a μ
  haveI : DiscreteTopology (GlobalTheory.CellDec.NE E a) :=
    GlobalTheory.MirTower.discrete_of_le_range (Subgroup.map_le_range _ _)
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI : SecondCountableTopology (Matrix (Fin a) (Fin a) (Ad E)) :=
    inferInstanceAs (SecondCountableTopology (Fin a → Fin a → Ad E))
  haveI : SecondCountableTopology (Matrix (Fin a) (Fin a) (Ad E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (GA E a) :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  exact GlobalTheory.FundDomDiscrete.exists_isFundamentalDomain _ μ

end GlobalTheory.CellDec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockVacOmFin
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift.FactorInf

theorem fockVac_om_fin {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om) {θ : InfFam D}
    (hθ : IsInfFam θ) {γ : GA D T} (hγ : γ ∈ GfC T) (τ : D.what₂.Tau)
    (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hv : IsFockVacAt (heisO ψ S T) θ τ J f) :
    IsFockVacAt (heisO ψ S T) θ τ J (om (1, γ) f) := by
  have e : ∀ z : Matrix (Fin T.rank) (Fin S.rank) ℂ, compAt θ τ (mt T γ) * z * compAt θ τ (mt S (1 : GA D S)⁻¹) = z := fun z => by
    rw [inv_one, GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ T hγ τ,
      GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ S (Subgroup.one_mem _) τ, Matrix.one_mul, Matrix.mul_one]
  intro z
  have h := congrArg (om (1, γ)) (hv z)
  unfold annih at h ⊢
  rw [map_add (f := _), map_smul, GlobalTheory.OrientedHeis.om_dRho hom hθ 1 γ τ z hf, GlobalTheory.OrientedHeis.om_dRho hom hθ 1 γ τ (J z) hf,
    e, e, map_zero] at h
  exact h

theorem factInf : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i t, FactInf R i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hF i t μ 𝓕 hμ u hu γ hγ P P'
  have hW := hL.thP.ωP i t
  have hθ : IsInfFam R.θ := hL.models.inf
  have hth : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have := hL.thP.pt_theta i t 1
    unfold RealDat.ptP at this
    rwa [GlobalTheory.FiniteFock.pureTensorO_one] at this
  have hvac : ∀ τ, IsFockVacAt (heisO R.ψ (Vc D i) (Wc D i)) R.θ τ (cplxO 1 (cart (R.MW i (sg0 D A)) τ)) (R.vP i t) :=
    GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ (fun _ => 1) _ _ _ _ _ _ _ _ _ _ (hL.thP.vP i t) hth
  set f₁ := R.ωP i t (1, γ) (R.vP i t) with hf₁
  have hth1 : IsThetaFunO R.ψ (Vc D i) (Wc D i) f₁ := hW.om_pres _ _ hth
  have hvac1 : ∀ τ, IsFockVacAt (heisO R.ψ (Vc D i) (Wc D i)) R.θ τ (cplxO 1 (cart (R.MW i (sg0 D A)) τ)) f₁ :=
    fun τ => fockVac_om_fin hW hθ hγ τ _ hth (hvac τ)
  have hmul : R.ωP i t (1, u * γ) (R.ptP i t P) = R.ωP i t (1, u) (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1)
      (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) f₁ P) := by
    have e : ((1 : GA D (Vc D i)), u * γ) = (1, u) * (1, γ) := by simp
    rw [e, map_mul, Module.End.mul_apply]
    congr 1
    unfold RealDat.ptP
    exact GlobalTheory.OrientedHeis.om_fin_pureTensorO _ _ _ _ _ _ hW R.θ hθ 1 (Subgroup.one_mem _) γ hγ _ _ _ _ _ P hth
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.VacPairSchur.pair_eq D R.ψ R.θ (Vc D i) (Wc D i) _ _ (R.ωP i t) hW hθ (fun _ => 1) (R.BV i)
    (cart (R.MW i (sg0 D A))) (onb (R.MW i (sg0 D A))) (fun _ => (Vc D i).rank)
    (fun τ => ((Wc D i).sig (tauE D τ)).1) (fun τ => isCartanInv_one_of_onb (hL.models.BV i τ))
    (GlobalTheory.AdTh.VecFock.isCartanInv_cart _) (hL.models.BV i)
    (fun τ => GlobalTheory.AdTh.VecFock.isONBasis_onb _ τ _ (hL.models.order i τ)) μ 𝓕 hμ u hu P P'
  have hne := (vecNe D G Pl0 T A Ks R F hL hF i t μ 𝓕 hμ).1
  rw [hmul]
  unfold RealDat.ptP
  rw [hc f₁ _ hth1 hth hvac1 hvac, hc _ _ hth hth hvac hvac]
  unfold coef
  rw [← hf₁]
  field_simp

end GlobalTheory.RawLift.FactorInf
end
end

