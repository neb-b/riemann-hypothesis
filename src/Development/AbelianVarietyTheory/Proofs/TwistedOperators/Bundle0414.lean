module

public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0211
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BunExists
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0398
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.NatCastKPZero
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0405
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0252
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0404
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0377
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianFormDualFlagEqReducedFrameCoordinates
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead
open GlobalTheory.SeeConjGroup Formalism.L2.SG.HidaSetting
open scoped Matrix

noncomputable section
namespace GlobalTheory.SeeConjGroup.CoefRead

open Classical

theorem flagVector_map_bilinear {M N P : Type} [Zero M] [Zero N] [Zero P] (φ : M → N → P) (hφ : φ 0 0 = 0) (ρ k n : ℕ)
    (e' f' : Fin ρ → M) (b' : Fin k → M) (z' : M) (e f : Fin ρ → N) (b : Fin k → N) (z : N) (q : Fin n) :
    φ (flagV ρ k n e' f' b' z' q) (flagV ρ k n e f b z q) =
      flagV ρ k n (fun a => φ (e' a) (e a)) (fun a => φ (f' a) (f a)) (fun i => φ (b' i) (b i)) (φ z' z) q := by
  unfold flagV
  split_ifs <;> simp [hφ]

theorem flagV_mem {M : Type} [Zero M] (S : Set M) (h0 : (0 : M) ∈ S) {ρ k n : ℕ} {e f : Fin ρ → M} {b : Fin k → M} {z : M}
    (he : ∀ a, e a ∈ S) (hf : ∀ a, f a ∈ S) (hb : ∀ i, b i ∈ S) (hz : z ∈ S) (q : Fin n) : flagV ρ k n e f b z q ∈ S := by
  unfold flagV
  split_ifs <;> simp_all

theorem sum_flagV {M : Type} [AddCommMonoid M] (ρ k n : ℕ) (hn : n = 2 * ρ + k + 1) (e f : Fin ρ → M) (b : Fin k → M) (z : M) :
    ∑ q : Fin n, flagV ρ k n e f b z q = (∑ a, e a) + (∑ i, b i) + z + ∑ a, f a := by
  subst hn
  rw [← Fin.sum_congr' _ (show ρ + (k + (1 + ρ)) = 2 * ρ + k + 1 by ring)]
  rw [Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_one]
  have h1 : ∀ a : Fin ρ, flagV ρ k (2 * ρ + k + 1) e f b z (Fin.cast (by ring) (Fin.castAdd (k + (1 + ρ)) a)) = e a := by
    intro a
    unfold flagV
    simp
  have h2 : ∀ i : Fin k, flagV ρ k (2 * ρ + k + 1) e f b z
      (Fin.cast (by ring) (Fin.natAdd ρ (Fin.castAdd (1 + ρ) i))) = b i := by
    intro i
    unfold flagV
    simp
  have h3 : flagV ρ k (2 * ρ + k + 1) e f b z
      (Fin.cast (by ring) (Fin.natAdd ρ (Fin.natAdd k (Fin.castAdd ρ (0 : Fin 1))))) = z := by
    unfold flagV
    simp
  have h4 : ∀ a : Fin ρ, flagV ρ k (2 * ρ + k + 1) e f b z
      (Fin.cast (by ring) (Fin.natAdd ρ (Fin.natAdd k (Fin.natAdd 1 a)))) = f (Fin.rev a) := by
    intro a
    unfold flagV
    have := a.2
    simp only [Fin.val_cast, Fin.val_natAdd]
    rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dif_pos (by omega)]
    congr 1
    ext
    simp [Fin.val_rev]
    omega
  simp only [h1, h2, h3, h4]
  rw [show (∑ a : Fin ρ, f (Fin.rev a)) = ∑ a, f a from Equiv.sum_comp Fin.revPerm f]
  abel

theorem memLf (D : D7) (v : Fin (Yc D 0).rank → EAf D) : v ∈ (II D).Lf ↔
    v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (E := D.host.E) ((II D).L : Submodule (𝓞 D.host.E) (Fin (Yc D 0).rank → D.host.E)) :=
  Set.ext_iff.1 (Formalism.IndefR.Eqv.lamAf_eq_hatL (V := Yc D 0) (II D).L) v

theorem rank_val (D : D7) : (Yc D 0).rank = 2 * D.R.rS + D.R.k + 1 := by
  rw [show (Yc D 0).rank = D.R.r from Formalism.L2.SG.InstExistsPf.rank_eq D]
  obtain ⟨j, hj⟩ := D.R.m_even; have := D.R.two_le_m; simp only [Formalism.BasicNotions.Ranks.r, Formalism.BasicNotions.Ranks.rS]; omega

open Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.Pf.BunEx.Unip in
theorem hA_neg_left' (I : AutInst) (a b : VA I) : hA I (-a) b = - hA I a b := by
  rw [show -a = (-1 : I.E ⊗[I.F] Af I.F) • a by simp, hA_smul_left]
  simp

open Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.Pf.BunEx.Unip in
theorem resS_zero_of {D : D7} (PP : Pl D.host.E) {x c : EAf D} (hx : x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (e : x = c * x) (h0 : resS D.host.F PP ⟨c, hc⟩ = 0) :
    resS D.host.F PP ⟨x, hx⟩ = 0 := by
  have : (⟨x, hx⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨c, hc⟩ * ⟨x, hx⟩ := Subtype.ext e
  rw [this, map_mul, h0, zero_mul]

open Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.Pf.BunEx.Unip in
theorem ew_int {D : D7} {g : ℕ} {e0 f0 : Fin D.R.rS → VA (II D)} {z0 : VA (II D)} {bw bwd : Fin D.R.k → VA (II D)}
    {ew : (II D).E ⊗[(II D).F] Af (II D).F} (hF : Formalism.L2.SG.Pf.BunEx.Unip.FH (II D) g e0 f0 z0 bw bwd ew) (i : Fin D.R.k) :
    ew ∈ IntAf (II D).F (II D).E := by
  obtain ⟨t, ht, e⟩ := hF.dual i i
  simp only [if_true] at e
  have h1 : hA (II D) (bwd i) (bw i) ∈ IntAf (II D).F (II D).E := hA_int (II D) (hF.mem.2.2 i).2 (hF.mem.2.2 i).1
  have h2 : ((g : ℕ) : (II D).E ⊗[(II D).F] Af (II D).F) * t ∈ IntAf (II D).F (II D).E :=
    Subring.mul_mem _ (natCast_mem _ g) ht
  have : ew = hA (II D) (bwd i) (bw i) - (g : (II D).E ⊗[(II D).F] Af (II D).F) * t := by rw [← e]; ring
  rw [this]
  exact Subring.sub_mem _ h1 h2

open Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.Pf.BunEx.Unip in
theorem second {D : D7} {g : ℕ} {e0 f0 : Fin D.R.rS → VA (II D)} {z0 : VA (II D)} {bw bwd : Fin D.R.k → VA (II D)}
    {ew : (II D).E ⊗[(II D).F] Af (II D).F} (hF : Formalism.L2.SG.Pf.BunEx.Unip.FH (II D) g e0 f0 z0 bw bwd ew) {β : GL (Fin (Yc D 0).rank) (EAf D)}
    {PP : Pl D.host.E} {w : Bool} (hL : LocAt g e0 f0 z0 bw bwd ew β PP w) (u : VA (II D)) (i : Fin D.R.k)
    (h1 : hA (II D) ((if w then bw else bwd) i) u ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    resS D.host.F PP ⟨_, h1⟩ = 0 := by
  have hew := ew_int hF i
  cases w
  · have e : hA (II D) (bwd i) u = ew * hA (II D) (bwd i) u := by
      conv_lhs => rw [hF.bwd_w i]
      rw [hA_smul_left, sigA_sigA]
    exact resS_zero_of PP h1 hew e (by simpa using hL.2.1 hew)
  · have hs := sigA_mem (II D) hew
    have e : hA (II D) (bw i) u = sigA (II D) ew * hA (II D) (bw i) u := by
      conv_lhs => rw [hF.bw_w i]
      rw [hA_smul_left]
    exact resS_zero_of PP h1 hs e (by simpa using hL.2.2.1 hs)

open Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.Pf.BunEx.Unip in
theorem Rc_flag {D : D7} (e0 f0 : Fin D.R.rS → VA (II D)) (z0 : VA (II D)) (bw bwd : Fin D.R.k → VA (II D)) (w : Bool)
    (u : VA (II D)) :
    Rc (II D) e0 f0 z0 bw bwd u =
      (∑ q : Fin (Yc D 0).rank, hA (II D) (flagV D.R.rS D.R.k (Yc D 0).rank f0 e0 (dualOrRevBasis w bw bwd) (-z0) q) u •
        flagV D.R.rS D.R.k (Yc D 0).rank e0 f0 (basisOrRevDual w bw bwd) z0 q) +
      ∑ i, hA (II D) ((if w then bw else bwd) i) u • (if w then bwd else bw) i := by
  have hq := fun q => flagVector_map_bilinear (fun x y : VA (II D) => hA (II D) x u • y) (by simp) D.R.rS D.R.k (Yc D 0).rank
    f0 e0 (dualOrRevBasis w bw bwd) (-z0) e0 f0 (basisOrRevDual w bw bwd) z0 q
  simp only [hq]
  rw [sum_flagV _ _ _ (rank_val D)]
  unfold Rc
  cases w
  · simp only [basisOrRevDual, dualOrRevBasis, Bool.false_eq_true, if_false, hA_neg_left', neg_smul]
    rw [show (∑ x : Fin D.R.k, hA (II D) (bw x.rev) u • bwd x.rev) = ∑ x, hA (II D) (bw x) u • bwd x from
      Equiv.sum_comp Fin.revPerm (fun i => hA (II D) (bw i) u • bwd i)]
    abel
  · simp only [basisOrRevDual, dualOrRevBasis, if_true, hA_neg_left', neg_smul]
    abel

theorem key_gen {A : Type} [CommRing A] (S : Subring A) {n ι κ : Type} [Fintype n] [DecidableEq n] [Fintype ι] [Fintype κ]
    (M : Matrix n n A) (u : n → A) (c : ι → A) (G : ι → n → A) (d : κ → A) (o : κ → n → A) (gg : A) (z : n → A)
    (hu : u = (∑ q, c q • G q) + (∑ i, d i • o i) + gg • z) (p : n) (hup : (M *ᵥ u) p ∈ S)
    (hc : ∀ q, c q ∈ S) (hG : ∀ q, (M *ᵥ G q) p ∈ S) (hd : ∀ i, d i ∈ S) (ho : ∀ i, (M *ᵥ o i) p ∈ S)
    (hg : gg ∈ S) (hz : (M *ᵥ z) p ∈ S) :
    (⟨_, hup⟩ : S) = (∑ q, ⟨_, hc q⟩ * ⟨_, hG q⟩) + (∑ i, ⟨_, hd i⟩ * ⟨_, ho i⟩) + ⟨_, hg⟩ * ⟨_, hz⟩ := by
  apply Subtype.ext
  subst hu
  simp [Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_smul, Finset.sum_apply]

theorem read_gen {A K : Type} [CommRing A] [CommRing K] (S : Subring A) (φ : S →+* K) {n κ : Type} [Fintype n]
    [DecidableEq n] [Fintype κ] (M : Matrix n n A) (u : n → A) (c : n → A) (G : n → n → A) (d : κ → A) (o : κ → n → A)
    (gg : A) (z : n → A) (hu : u = (∑ q, c q • G q) + (∑ i, d i • o i) + gg • z) (p : n) (hup : (M *ᵥ u) p ∈ S)
    (hc : ∀ q, c q ∈ S) (hG : ∀ q, (M *ᵥ G q) p ∈ S) (hd : ∀ i, d i ∈ S) (ho : ∀ i, (M *ᵥ o i) p ∈ S)
    (hg : gg ∈ S) (hz : (M *ᵥ z) p ∈ S) (hδ : ∀ q, φ ⟨_, hG q⟩ = if p = q then 1 else 0)
    (hd0 : ∀ i, φ ⟨_, hd i⟩ = 0) (hg0 : φ ⟨_, hg⟩ = 0) :
    φ ⟨_, hc p⟩ = φ ⟨_, hup⟩ := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [key_gen S M u c G d o gg z hu p hup hc hG hd ho hg hz, map_add (f := _), map_add (f := _), map_sum, map_sum, map_mul, hg0, zero_mul,
    add_zero]
  simp only [map_mul, hd0, zero_mul, Finset.sum_const_zero, add_zero, hδ, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

theorem resS_natCast {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (PP : Pl E) (g : ℕ)
    (hg : (g : 𝓞 E) ∈ PP.asIdeal) : resS F PP (g : Formalism.L2.Herm.intAf F E) = 0 := by
  rw [map_natCast, ← map_natCast (Ideal.Quotient.mk PP.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
  exact hg

theorem redV_of {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (PP : Pl E) (v : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) (j : Fin n)
    (h : ((β⁻¹).val *ᵥ v) j ∈ Formalism.L2.Herm.intAf F E) : redV β PP v j = resS F PP ⟨_, h⟩ := dif_pos h

set_option maxHeartbeats 1000000 in
open Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.Pf.BunEx.Unip in
theorem coef_read : ∀ {D : D7} (g : ℕ) (e0 f0 : Fin D.R.rS → VA (II D)) (z0 : VA (II D)) (bw bwd : Fin D.R.k → VA (II D)) (ew : EAf D), Formalism.L2.SG.Pf.BunEx.Unip.FH (II D) g e0 f0 z0 bw bwd ew → ∀ (β : GL (Fin (Yc D 0).rank) (EAf D)) (PP : Pl D.host.E) (w : Bool), IsFrame β (II D).L → LocAt g e0 f0 z0 bw bwd ew β PP w → ∀ u ∈ (II D).Lf, (∀ p (h1 : hA (II D) (flagV D.R.rS D.R.k (Yc D 0).rank f0 e0 (dualOrRevBasis w bw bwd) (-z0) p) u ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), resS D.host.F PP ⟨_, h1⟩ = redV β PP u p) ∧ (∀ i (h1 : hA (II D) ((if w then bw else bwd) i) u ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), resS D.host.F PP ⟨_, h1⟩ = 0) := by
  intro D g e0 f0 z0 bw bwd ew hF β PP w hβ hL u hu
  refine ⟨fun p h1 => ?_, fun i h1 => second hF hL u i h1⟩
  have hint : ∀ v ∈ (II D).Lf, ∀ j, ((β⁻¹).val *ᵥ v) j ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E :=
    fun v hv => (hβ v).1 ((memLf D v).1 hv)
  have hexp := Formalism.L2.SG.Pf.BunEx.Unip.exp hF u hu
  obtain ⟨z, hz, hzm⟩ := Formalism.L2.SG.Pf.BunEx.Unip.mL_dvd (dvd_refl g) _ hexp
  have hu' := sub_eq_iff_eq_add'.1 hzm
  rw [Rc_flag e0 f0 z0 bw bwd w u] at hu'
  have hred := hL.2.2.2
  have hsD : ∀ i, dualOrRevBasis w bw bwd i ∈ (II D).Lf := by
    intro i; cases w
    · exact (hF.mem.2.2 _).1
    · exact (hF.mem.2.2 _).2
  have hDv : ∀ q, flagV D.R.rS D.R.k (Yc D 0).rank f0 e0 (dualOrRevBasis w bw bwd) (-z0) q ∈ (II D).Lf :=
    fun q => flagV_mem ((II D).Lf : Set (VA (II D))) (zero_mem _) (fun a => (hF.mem.1 a).2) (fun a => (hF.mem.1 a).1)
      hsD (neg_mem hF.mem.2.1) q
  have ho : ∀ i, (if w then bwd else bw) i ∈ (II D).Lf := by
    intro i; cases w
    · exact (hF.mem.2.2 _).1
    · exact (hF.mem.2.2 _).2
  have hoD : ∀ i, (if w then bw else bwd) i ∈ (II D).Lf := by
    intro i; cases w
    · exact (hF.mem.2.2 _).2
    · exact (hF.mem.2.2 _).1
  have hC : ∀ q, hA (II D) (flagV D.R.rS D.R.k (Yc D 0).rank f0 e0 (dualOrRevBasis w bw bwd) (-z0) q) u ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E := fun q => hA_int (II D) (hDv q) hu
  have hCo : ∀ i, hA (II D) ((if w then bw else bwd) i) u ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    fun i => hA_int (II D) (hoD i) hu
  have hGi : ∀ q, ((β⁻¹).val *ᵥ
      flagV D.R.rS D.R.k (Yc D 0).rank e0 f0 (basisOrRevDual w bw bwd) z0 q) p ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    fun q => (hred p q).fst
  have hoi : ∀ i, ((β⁻¹).val *ᵥ (if w then bwd else bw) i) p ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E := fun i => hint _ (ho i) p
  have hzi := hint z hz p
  have hui := hint u hu p
  have hgI : ((g : ℕ) : (II D).E ⊗[(II D).F] Af (II D).F) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := natCast_mem _ g
  have key := key_gen (Formalism.L2.Herm.intAf D.host.F D.host.E) (β⁻¹).val u _ _ _ _ _ z hu' p hui hC hGi hCo hoi hgI hzi
  have hgc : (⟨_, hgI⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = (g : Formalism.L2.Herm.intAf D.host.F D.host.E) := Subtype.ext (by push_cast; rfl)
  rw [hgc] at key
  have hg0 : resS D.host.F PP ⟨_, hgI⟩ = 0 := by
    rw [hgc]; exact resS_natCast PP g hL.1
  have hδ : ∀ q, resS D.host.F PP ⟨_, hGi q⟩ = if p = q then 1 else 0 := fun q => (hred p q).snd
  have hfin := read_gen (Formalism.L2.Herm.intAf D.host.F D.host.E) (resS D.host.F PP) (β⁻¹).val u _ _ _ _ _ z hu' p hui hC hGi
    hCo hoi hgI hzi hδ (fun i => second hF hL u i (hCo i)) hg0
  have hR := redV_of β PP u p hui
  rw [hR]
  exact hfin

end GlobalTheory.SeeConjGroup.CoefRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAdelicGlueVectorOfSelfDualPrimitive
section
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdIsom.SelfDualGlue

variable {D : D7} {u : D.what₂.Word} {Y X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V} {z : Y.V}

theorem vA_flat (x : X.V) (a : D.host.E) : vA Y (ι x + a • z) = mA Y X ι *ᵥ vA X x + inc D a • vA Y z := by
  rw [vA_add, vA_smul, mA_mulVec_vA]

theorem inc_hD_flat (h : IsLine Y X ι z u) (x x' : X.V) (a a' : D.host.E) :
    inc D (Y.hD (ι x + a • z) (ι x' + a' • z)) =
      hA X (vA X x) (vA X x') - inc D a * cjA D (inc D a') * inc D (Tu D u) := by
  rw [← hA_vA, vA_flat, vA_flat]
  exact hA_flat h _ _ _ _

theorem mem_glueLat_iff {L₀ : Lat X} {x₀ : X.V} (y : Y.V) : y ∈ glueLat Y X ι z u L₀ x₀ ↔
    ∃ x : X.V, Formalism.L2.Herm.crd X x ∈ L₀ ∧ ∃ a : 𝓞 D.host.E,
      y = ι (x + (a : D.host.E) • x₀) + ((a : D.host.E) * (Tu D u)⁻¹) • z := by
  rw [mem_glueLat]
  refine exists_congr fun x => and_congr_right fun _ => exists_congr fun a => ?_
  rw [map_add (f := _), map_smul, smul_add, smul_smul]
  constructor <;> rintro rfl <;> abel

theorem coords_of_mem (h : IsLine Y X ι z u) {L₀ : Lat X} {x₀ x : X.V} {a : D.host.E}
    (hm : ι x + a • z ∈ glueLat Y X ι z u L₀ x₀) :
    ∃ x₁ ∈ hat L₀, ∃ b ∈ OA D, vA X x = x₁ + b • vA X x₀ ∧ inc D a = b * inc D (Tu D u)⁻¹ := by
  have hv := vA_mem_hat Y hm
  rw [vA_flat, mem_hat_glueLat] at hv
  obtain ⟨x₁, hx₁, b, hb, e⟩ := hv
  obtain ⟨e1, e2⟩ := flat_inj h e
  exact ⟨x₁, hx₁, b, hb, e1, e2⟩

theorem mem_flatSp (x : X.V) (a : D.host.E) : ι x + a • z ∈ flatSp Y X ι z := Submodule.add_mem_sup (LinearMap.mem_range_self ι x)
    (Submodule.smul_mem _ a (Submodule.mem_span_singleton_self z))


set_option maxHeartbeats 1600000 in
theorem isGlueVec_of_isSDIn : ∀ (D : D7) (u : D.what₂.Word) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V), IsLine Y X ι z u → ∀ (L₀ : Lat X) (x₀ : X.V), Submodule.IsFullLattice D.host.E L₀ → IsSDIn Y (flatSp Y X ι z) (glueLat Y X ι z u L₀ x₀) → IsPrim Y z (glueLat Y X ι z u L₀ x₀) → IsGlueVec X u L₀ (vA X x₀) := by
  intro D u Y X ι z h L₀ x₀ hlat hSD hP
  obtain ⟨-, -, hsd⟩ := hSD

  have key : ∀ (p : X.V) (α : D.host.E) (q : X.V) (β : D.host.E),
      ι p + α • z ∈ glueLat Y X ι z u L₀ x₀ → ι q + β • z ∈ glueLat Y X ι z u L₀ x₀ →
      hA X (vA X p) (vA X q) - inc D α * cjA D (inc D β) * inc D (Tu D u) ∈ OA D := by
    intro p α q β hp hq
    rw [← inc_hD_flat h, inc_mem_iff]
    exact (hsd _ (mem_flatSp (ι := ι) (z := z) q β)).1 hq _ hp

  have hX : ∀ p : X.V, Formalism.L2.Herm.crd X p ∈ L₀ → ι p + (0 : D.host.E) • z ∈ glueLat Y X ι z u L₀ x₀ := by
    intro p hp
    rw [mem_glueLat_iff]
    exact ⟨p, hp, 0, by simp⟩
  have hg : ι x₀ + (Tu D u)⁻¹ • z ∈ glueLat Y X ι z u L₀ x₀ := by
    rw [mem_glueLat_iff]
    exact ⟨0, by simp, 1, by simp⟩
  have hv : ∀ y : Fin X.rank → D.host.E,
      (fun i => inc D (y i)) = vA X ((Formalism.L2.Herm.crd X).symm y) := by
    intro y
    funext i
    simp [vA]
  have hrat : ∀ p q : X.V, Formalism.L2.Herm.crd X p ∈ L₀ → Formalism.L2.Herm.crd X q ∈ L₀ →
      hA X (vA X p) (vA X q) ∈ OA D := by
    intro p q hp hq
    simpa using key p 0 q 0 (hX p hp) (hX q hq)

  have hright : ∀ f, (∀ y ∈ L₀, hA X f (fun i => inc D (y i)) ∈ OA D) →
      ∀ y ∈ hat L₀, hA X f y ∈ OA D := by
    intro f hf y hy
    refine hat_induction (p := fun y => hA X f y ∈ OA D) hf ?_ ?_ ?_ hy
    · show hA X f 0 ∈ OA D
      rw [hA_zero_right]
      exact zero_mem _
    · intro a b ha hb
      show hA X f (a + b) ∈ OA D
      rw [hA_add_right]
      exact add_mem ha hb
    · intro a ha b hb
      show hA X f (a • b) ∈ OA D
      rw [hA_smul_right]
      exact mul_mem (cjA_mem ha) hb
  have hint : ∀ x ∈ hat L₀, ∀ y ∈ hat L₀, hA X x y ∈ OA D := by
    intro x hx
    refine hright x fun y hy => hA_mem_of_forall (fun x' hx' => ?_) x hx
    rw [hv x', hv y]
    exact hrat _ _ (by simpa using hx') (by simpa using hy)

  have hz : ι 0 + (1 : D.host.E) • z ∈ glueLat Y X ι z u L₀ x₀ := by
    rw [map_zero, zero_add]
    exact (hP 1).2 (one_mem _)
  obtain ⟨x₁, hx₁, b, -, e1, e2⟩ := coords_of_mem h hz
  have hb : b = inc D (Tu D u) := by
    rw [map_one] at e2
    calc b = b * (inc D (Tu D u)⁻¹ * inc D (Tu D u)) := by rw [inc_inv_mul, mul_one]
      _ = inc D (Tu D u) := by rw [← mul_assoc, ← e2, one_mul]
  have h0 : vA X (0 : X.V) = 0 := by simpa using vA_add X (0 : X.V) 0
  refine ⟨?_, hint, ?_, ?_, ?_⟩
  · rw [h0] at e1
    rw [← hb, eq_sub_of_add_eq' e1.symm]
    exact sub_mem_hat zero_mem_hat hx₁
  · refine hright (vA X x₀) fun y hy => ?_
    rw [hv y]
    simpa using key x₀ (Tu D u)⁻¹ _ 0 hg (hX _ (by simpa using hy))
  · have := key x₀ (Tu D u)⁻¹ x₀ (Tu D u)⁻¹ hg hg
    rwa [cjA_inc_inv, mul_assoc, inc_inv_mul, mul_one] at this
  ·

    intro y hy
    obtain ⟨y₀, hy₀⟩ := exists_sub_inc_mem_hat hlat.span_eq_top y
    obtain ⟨q, rfl⟩ := (Formalism.L2.Herm.crd X).surjective y₀
    change y - vA X q ∈ hat L₀ at hy₀
    have hq : ι q + X.hD q x₀ • z ∈ glueLat Y X ι z u L₀ x₀ := by
      refine (hsd _ (mem_flatSp (ι := ι) (z := z) q (X.hD q x₀))).2 fun v hv' => ?_
      obtain ⟨p, hp, a, rfl⟩ := (mem_glueLat_iff v).1 hv'
      have hp' : vA X p ∈ hat L₀ := inc_mem_hat hp
      have h1 : hA X (vA X p) (vA X q) ∈ OA D := by
        rw [show vA X q = y - (y - vA X q) from (sub_sub_cancel y (vA X q)).symm, hA_sub_right]
        exact sub_mem (hy _ hp') (hint _ hp' _ hy₀)
      rw [← inc_mem_iff, inc_hD_flat h, ← hA_vA X q x₀, cjA_hA, vA_add, vA_smul, hA_add_left,
        hA_smul_left, map_mul (inc D)]
      convert h1 using 1
      linear_combination (-(inc D (a : D.host.E) * hA X (vA X x₀) (vA X q))) * inc_inv_mul u
    obtain ⟨x₂, hx₂, c, hc, e3, -⟩ := coords_of_mem h hq
    refine ⟨c, hc, ?_⟩
    have e4 : y - c • vA X x₀ = (y - vA X q) + x₂ := by
      rw [e3]
      abel
    rw [e4]
    exact add_mem_hat hy₀ hx₂

end GlobalTheory.AdIsom.SelfDualGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiActionFunctionIsUnfoldingNoCompactCore
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
open GlobalTheory.Unf.FB

noncomputable section


open GlobalTheory.ThLaws in
theorem GlobalTheory.th_isTh_lev : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (y : WO J.W₀ B.L → ℂ), GlobalTheory.Unf.FB.Quasi ψ J.W₀ B.L y → ∀ x₀ : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E, (rat x₀ : Mx D B.V.rank (σ + 1)) = xLast B.d (vecB B.o B.ζ) → IsTh ψ J.d B.V x₀ (fun n => star (jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) n y 0) * star (psiFlag ψ J.d n)) := by
  intro D ψ hψ σ J B y hy x₀ hx₀
  obtain ⟨hcont, -, hleft, hcen, -, -⟩ := _root_.GlobalTheory.Unf.FB.ThLawsL.th_laws D ψ hψ σ J B y hy
  beta_reduce at hcen hleft
  obtain ⟨x₁, hx₁, -, -, hlast, hq⟩ := _root_.GlobalTheory.Asc.FBL.basePoint_spec D σ B
  have e : x₁ = x₀ := rat_injective (hx₁.trans hx₀.symm)
  refine ⟨hcont.comp continuous_subtype_val, fun γ hγQ hγN n hn => hleft γ hγN hγQ n hn, fun c n hn => ?_, ?_⟩
  · rw [hcen c n hn, hx₀, hq]
  intro j a ha1 ha0 hg
  have hl : a (Fin.last σ) = 0 := hlast a (by rw [e]; exact hg)
  have hj : j.1 < σ := by
    by_contra hc
    have : j = Fin.last σ := Fin.ext (by have := j.2; simp only [Fin.val_last]; omega)
    rw [this, hl] at ha1
    exact zero_ne_one ha1
  let j' : Fin (σ + 1) := ⟨j.1 + 1, by omega⟩
  have hjj : j < j' := by rw [Fin.lt_def]; simp [j']
  obtain ⟨t, ht⟩ := exists_psiE_ne_one hψ
  let A : Fin (σ + 1) → AE D := GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.ratVec a
  let Bv : Fin (σ + 1) → AE D := fun k => if k = j' then cA D t else 0
  have hB0 : ∀ k, k ≠ j' → Bv k = 0 := fun k hk => if_neg hk
  have hA0 : ∀ i, j < i → A i = 0 := fun i hi => by
    show incA D (a i) = 0
    rw [ha0 i hi, map_zero]
  have hN : ∀ i k, ¬(i ≤ j ∧ k = j') → A i * cA D (Bv k) = 0 := by
    intro i k hik
    by_cases hk : k = j'
    · rw [hA0 i (not_le.1 fun hi => hik ⟨hi, hk⟩), zero_mul]
    · rw [hB0 k hk, map_zero, mul_zero]
  have hAB : (fun k => cA D (Bv k)) ⬝ᵥ A = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [mul_comm]
    exact hN k k fun h => absurd (h.2 ▸ h.1) (not_le.2 hjj)
  have hupper : tvGL A Bv hAB ∈ upperUni (σ + 1) (AE D) := fun i k => by
    refine ⟨fun hki => ?_, ?_⟩
    · rw [tvGL_val, Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hki), tvN_apply,
        hN i k fun h => absurd (h.2 ▸ hki) (not_lt.2 (le_of_lt (lt_of_le_of_lt h.1 hjj))), zero_add]
    · rw [tvGL_val, Matrix.add_apply, Matrix.one_apply_eq, tvN_apply,
        hN i i fun h => absurd (h.2 ▸ h.1) (not_le.2 hjj), add_zero]
  have hUX : tvGL A Bv hAB ∈ UX D (σ + 1) := mem_UX.2 hupper
  have hu : J.d.levi (tvGL A Bv hAB) ∈ flagN J.d := J.d.levi_mem_NFlag hupper
  have hup : upSum (tvN A Bv) = t := by
    unfold upSum
    rw [Finset.sum_eq_single j, Finset.sum_eq_single j']
    · rw [if_pos (by simp [j']), tvN_apply, show Bv j' = cA D t from if_pos rfl, cA_cA']
      show incA D (a j) * t = t
      rw [ha1, map_one, one_mul]
    · intro k _ hk
      rw [tvN_apply, hB0 k hk, map_zero, mul_zero, ite_self]
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro i _ hi
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : k = j'
      · rw [if_neg]
        intro h
        apply hi
        rw [hk] at h
        exact Fin.ext (by simp [j'] at h; omega)
      · rw [tvN_apply, hB0 k hk, map_zero, mul_zero, ite_self]
    · intro h; exact absurd (Finset.mem_univ _) h
  refine ⟨J.d.jY *ᵥ Bv, J.d.levi (tvGL A Bv hAB), star (psiE ψ t), ?_, levi_isTransv J.d A Bv hAB,
    Subgroup.mem_inf.2 ⟨hu, Subgroup.mem_iInf.2 fun i => ?_⟩, ?_, ?_⟩
  · show GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.form J.W (J.d.jX *ᵥ A) (J.d.jY *ᵥ Bv) = 0
    rw [form_mulVec, ← J.d.pX_eq, Matrix.mulVec_mulVec, J.d.pX_jX, Matrix.one_mulVec, hAB]
  · rw [mem_fixer]
    have hcol : ∀ m, (tvGL A Bv hAB).1 m i.1 = (1 : Mx D (σ + 1) (σ + 1)) m i.1 := fun m => by
      rw [tvGL_val, Matrix.add_apply, tvN_apply,
        hN m i.1 fun h => absurd (h.2 ▸ i.2) (not_le.2 hjj), add_zero]
    ext k l
    have h1 := congrFun (congrFun (J.d.levi_jX (tvGL A Bv hAB)) k) i.1
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, id] at h1 ⊢
    rw [h1]
    simp only [hcol, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · intro h1
    apply ht
    rw [← star_star (psiE ψ t), h1, star_one]
  · intro n hn n' hn'
    have hx : ∀ u ∈ UX D (σ + 1), zEll B.L (σ + 1) B.ζ ⬝ u.1 = zEll B.L (σ + 1) B.ζ := fun u hu => zEll_mul B.L B.ζ hu
    have hJu : jacS ψ J.d B.L (zEll B.L (σ + 1) B.ζ) (J.d.levi (tvGL A Bv hAB)) = id := by
      have := jacS_levi_mul ψ J.d B.L (zEll B.L (σ + 1) B.ζ) (hx _ hUX) 1
      rwa [mul_one, jacS_one] at this
    have hpu : psiFlag ψ J.d (J.d.levi (tvGL A Bv hAB)) = psiE ψ t := by
      rw [psiFlag, blockX_levi, tvGL_val, upSum_add, upSum_one, zero_add, hup]
    beta_reduce
    rw [GlobalTheory.JacHom.jacS_mul J.d hx ψ (mul_mem hn hu) hn', GlobalTheory.JacHom.jacS_mul J.d hx ψ hn hu, hJu,
      GlobalTheory.JacHom.jacS_mul J.d hx ψ hn hn', psiFlag_mul J.d ψ (mul_mem hn hu) hn', psiFlag_mul J.d ψ hn hu,
      psiFlag_mul J.d ψ hn hn', hpu]
    simp only [id, star_mul']
    ring
end
end

