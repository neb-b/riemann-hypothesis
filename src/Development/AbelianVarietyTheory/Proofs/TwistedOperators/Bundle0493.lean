module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1503
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0477
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1281
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselVertexLatticeSplitsAlongWitt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.MonoBes

variable {D : D7}

theorem colMul_pX {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (i : Fin ρ) (y : Fin S.rank → AE D) :
    GlobalTheory.FinPl.colMul d.jX i ((d.pX *ᵥ y) i) = rat (fun k l => d.e k i * d.qX i l) *ᵥ y := by
  funext k
  simp only [GlobalTheory.FinPl.colMul, HypDec.jX, HypDec.pX, rat, mulVec, dotProduct, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  show (incA D) (d.qX i l) * y l * (incA D) (d.e k i) = (incA D) (d.e k i * d.qX i l) * y l
  rw [map_mul]
  ring

theorem colMul_pY {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (i : Fin ρ) (y : Fin S.rank → AE D) :
    GlobalTheory.FinPl.colMul d.jY i ((d.pY *ᵥ y) i) = rat (fun k l => d.e' k i * d.qY i l) *ᵥ y := by
  funext k
  simp only [GlobalTheory.FinPl.colMul, HypDec.jY, HypDec.pY, rat, mulVec, dotProduct, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  show (incA D) (d.qY i l) * y l * (incA D) (d.e' k i) = (incA D) (d.e' k i * d.qY i l) * y l
  rw [map_mul]
  ring

theorem mulVec_eq_sum_colMul {m n : ℕ} (x : Mx D m n) (w : Fin n → AE D) :
    x *ᵥ w = ∑ i, GlobalTheory.FinPl.colMul x i (w i) := by
  funext k
  simp only [mulVec, dotProduct, GlobalTheory.FinPl.colMul, Finset.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem mulVec_eq_sum_col {m n : ℕ} (x : Matrix (Fin m) (Fin n) D.host.E) (w : Fin n → D.host.E) :
    x *ᵥ w = ∑ i, fun k => x k i * w i := by
  funext k
  simp only [mulVec, dotProduct, Finset.sum_apply]

theorem rank_one_mulVec {m n k : ℕ} (a : Matrix (Fin m) (Fin k) D.host.E) (b : Matrix (Fin k) (Fin n) D.host.E)
    (i : Fin k) (x : Fin n → D.host.E) : (fun r l => a r i * b i l) *ᵥ x = fun r => a r i * (b *ᵥ x) i := by
  funext r
  simp only [mulVec, dotProduct, Finset.mul_sum, mul_assoc]

theorem monoAt_of_proj {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (L : Lat S)
    (hX : ∀ i, ∀ x ∈ L, (fun k => d.e k i * (d.qX *ᵥ x) i) ∈ L)
    (hY : ∀ i, ∀ x ∈ L, (fun k => d.e' k i * (d.qY *ᵥ x) i) ∈ L) (v : GlobalTheory.FinPl.Pl D) :
    MonoAt d L (L.comap ((Matrix.mulVecLin d.i₀).restrictScalars (𝓞 D.host.E))) v := by
  have h0 : ∀ x ∈ L, d.i₀ *ᵥ (d.q0 *ᵥ x) ∈ L := by
    intro x hx
    have e : d.i₀ *ᵥ (d.q0 *ᵥ x) = x - d.e *ᵥ (d.qX *ᵥ x) - d.e' *ᵥ (d.qY *ᵥ x) := by
      have := congrArg (· *ᵥ x) d.sum_eq_one_rat
      simp only [add_mulVec, one_mulVec, ← mulVec_mulVec] at this
      rw [sub_sub, eq_sub_iff_add_eq]
      calc _ = d.e *ᵥ (d.qX *ᵥ x) + d.i₀ *ᵥ (d.q0 *ᵥ x) + d.e' *ᵥ (d.qY *ᵥ x) := by abel
        _ = x := this
    rw [e, mulVec_eq_sum_col d.e, mulVec_eq_sum_col d.e']
    exact L.sub_mem (L.sub_mem hx (L.sum_mem fun i _ => hX i x hx)) (L.sum_mem fun i _ => hY i x hx)
  intro y
  constructor
  · intro hy
    refine ⟨fun i => ?_, fun i => ?_, ?_⟩
    · rw [colMul_pX]; exact GlobalTheory.OrthSumLat.rat_mulVec_mem_latV _ (fun x hx => by rw [rank_one_mulVec]; exact hX i x hx) hy
    · rw [colMul_pY]; exact GlobalTheory.OrthSumLat.rat_mulVec_mem_latV _ (fun x hx => by rw [rank_one_mulVec]; exact hY i x hx) hy
    · exact GlobalTheory.OrthSumLat.rat_mulVec_mem_latV d.q0 h0 hy
  · rintro ⟨h1, h2, h3⟩
    have e : y = d.jX *ᵥ (d.pX *ᵥ y) + d.j0 *ᵥ (d.p0 *ᵥ y) + d.jY *ᵥ (d.pY *ᵥ y) := by
      have h : d.jX * d.pX + d.j0 * d.p0 + d.jY * d.pY = 1 := by
        have h := congrArg rat d.sum_eq_one_rat
        rw [rat_add, rat_add, rat_one] at h
        simpa only [HypDec.jX, HypDec.j0, HypDec.jY,
          HypDec.pX, HypDec.p0, HypDec.pY, rat, Matrix.map_mul] using h
      have := congrArg (· *ᵥ y) h
      simp only [add_mulVec, one_mulVec, ← mulVec_mulVec] at this
      exact this.symm
    rw [e, mulVec_eq_sum_colMul d.jX, mulVec_eq_sum_colMul d.jY]
    refine add_mem (add_mem (AddSubgroup.sum_mem _ fun i _ => h1 i) ?_) (AddSubgroup.sum_mem _ fun i _ => h2 i)
    exact GlobalTheory.OrthSumLat.rat_mulVec_mem_latV d.i₀ (fun x hx => hx) h3

section SlopeTestRemainingChoices

variable {A B B₀ : HSp D} {c ρ : ℕ}

theorem antiDiagonalEpsilonGram_mulVec_of_rev_ne (ε : D.host.E) (u : Fin c → D.host.E) (j : Fin c) (hj : j.rev ≠ j) :
    (antiDiagonalSignGramMatrix c ε *ᵥ u) j = u j.rev := by
  simp only [mulVec, dotProduct, antiDiagonalSignGramMatrix]
  rw [Finset.sum_eq_single j.rev]
  · rw [if_pos (by simp only [Fin.val_rev]; omega), if_neg (Ne.symm hj), one_mul]
  · intro b _ hb
    rw [if_neg, zero_mul]
    intro h
    apply hb
    ext
    simp only [Fin.val_rev]
    omega
  · intro h; exact absurd (Finset.mem_univ _) h

theorem mulVec_single_apply {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (j : Fin n) (x : D.host.E) (k : Fin m) :
    (M *ᵥ Pi.single j x) k = M k j * x := by
  simp [mulVec, dotProduct, Pi.single_apply]

theorem auxiliaryVectors_pairing_eq_antiDiagonal_gram (a : HermitianOrthogonalExtensionData A B c (-1)) (y : Fin A.rank → D.host.E) (u : Fin c → D.host.E) :
    (a.aᴴ * B.gram) *ᵥ (frameMat B A a.ι *ᵥ y + a.a *ᵥ u) = antiDiagonalSignGramMatrix c (-1) *ᵥ u := by
  have hG : B.gramᴴ = B.gram := Matrix.ext fun i j => B.herm.eq _ _
  have h1 : a.aᴴ * B.gram * frameMat B A a.ι = 0 := by
    have h := congrArg Matrix.conjTranspose a.perp
    change ((frameMat B A a.ι)ᴴ * B.gram * a.a)ᴴ = 0ᴴ at h
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hG, Matrix.conjTranspose_zero,
      Matrix.mul_assoc] using h
  have h2 : a.aᴴ * B.gram * a.a = antiDiagonalSignGramMatrix c (-1) := a.gram
  rw [mulVec_add, mulVec_mulVec, mulVec_mulVec, h1, h2, zero_mulVec, zero_add]

theorem proj_mem (a : HermitianOrthogonalExtensionData A B c (-1)) (d : HypDec B B₀ ρ) (hd : IsAuxiliaryVectorWittDec a d) (Λ : Lat A)
    (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :
    (∀ i, ∀ x ∈ a.lat Λ 𝔟, (fun k => d.e k i * (d.qX *ᵥ x) i) ∈ a.lat Λ 𝔟) ∧
      (∀ i, ∀ x ∈ a.lat Λ 𝔟, (fun k => d.e' k i * (d.qY *ᵥ x) i) ∈ a.lat Λ 𝔟) := by
  obtain ⟨hc, he, s, he'⟩ := hd
  have hrev : ∀ i : Fin ρ, (Fin.castLE (by omega) i : Fin c).rev ≠ Fin.castLE (by omega) i := by
    intro i h
    have := congrArg Fin.val h
    simp only [Fin.val_rev, Fin.val_castLE] at this
    have := i.2
    omega
  have qX_eq : ∀ x (i : Fin ρ),
      (d.qX *ᵥ x) i = star (s i) * ((a.aᴴ * B.gram) *ᵥ x) (Fin.castLE (by omega) i : Fin c).rev := by
    intro x i
    rw [HypDec.qX, he', ← mulVec_mulVec, ← mulVec_mulVec]
    simp only [mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [conjTranspose_apply, colsOf, star_mul']
    ring_nf
  have qY_eq : ∀ x (i : Fin ρ),
      (d.qY *ᵥ x) i = star ((-D.host.xi0) ^ (i.1 + 1)) * ((a.aᴴ * B.gram) *ᵥ x) (Fin.castLE (by omega) i : Fin c) := by
    intro x i
    rw [HypDec.qY, he, ← mulVec_mulVec, ← mulVec_mulVec]
    simp only [mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [conjTranspose_apply, colsOf, star_mul']
    ring_nf
  have scal : ∀ i : Fin ρ, star (s i) * (-D.host.xi0) ^ (i.1 + 1) = 1 := by
    intro i
    have h1 : (fun k => d.e k i) =
        frameMat B A a.ι *ᵥ 0 + a.a *ᵥ Pi.single (Fin.castLE (by omega) i : Fin c) ((-D.host.xi0) ^ (i.1 + 1)) := by
      funext k
      show _ = (frameMat B A a.ι *ᵥ 0 + a.a *ᵥ _) k
      rw [he, mulVec_zero, zero_add, mulVec_single_apply]
      simp only [colsOf]
      ring
    have h2 : (d.e'ᴴ * B.gram * d.e) i i = (d.qX *ᵥ fun k => d.e k i) i := rfl
    have h3 := congrFun (congrFun d.e'e i) i
    rw [h2, h1, qX_eq, auxiliaryVectors_pairing_eq_antiDiagonal_gram, antiDiagonalEpsilonGram_mulVec_of_rev_ne _ _ _ (by rw [Fin.rev_rev]; exact (hrev i).symm), Fin.rev_rev, Pi.single_eq_same,
      Matrix.one_apply_eq] at h3
    exact h3
  refine ⟨fun i x hx => ?_, fun i x hx => ?_⟩
  · obtain ⟨y, hy, u, hu, rfl⟩ := hx
    refine ⟨0, Λ.zero_mem, Pi.single (Fin.castLE (by omega) i : Fin c) (u (Fin.castLE (by omega) i)), fun p => ?_, ?_⟩
    · by_cases hp : p = Fin.castLE (by omega) i
      · subst hp; rw [Pi.single_eq_same]; exact hu _
      · rw [Pi.single_eq_of_ne hp]; exact (𝔟 p).zero_mem
    · funext k
      show _ = (frameMat B A a.ι *ᵥ 0 + a.a *ᵥ _) k
      rw [qX_eq, auxiliaryVectors_pairing_eq_antiDiagonal_gram, antiDiagonalEpsilonGram_mulVec_of_rev_ne _ _ _ (by rw [Fin.rev_rev]; exact (hrev i).symm), Fin.rev_rev, mulVec_zero,
        zero_add, mulVec_single_apply, he]
      simp only [colsOf]
      linear_combination (a.a k (Fin.castLE (by omega) i) * u (Fin.castLE (by omega) i)) * scal i
  · obtain ⟨y, hy, u, hu, rfl⟩ := hx
    refine ⟨0, Λ.zero_mem, Pi.single (Fin.castLE (by omega) i : Fin c).rev (u (Fin.castLE (by omega) i : Fin c).rev),
      fun p => ?_, ?_⟩
    · by_cases hp : p = (Fin.castLE (by omega) i : Fin c).rev
      · subst hp; rw [Pi.single_eq_same]; exact hu _
      · rw [Pi.single_eq_of_ne hp]; exact (𝔟 p).zero_mem
    · have hs : s i * star ((-D.host.xi0) ^ (i.1 + 1)) = 1 := by
        have := congrArg star (scal i)
        rw [star_mul', star_star, star_one] at this
        exact this
      funext k
      show _ = (frameMat B A a.ι *ᵥ 0 + a.a *ᵥ _) k
      rw [qY_eq, auxiliaryVectors_pairing_eq_antiDiagonal_gram, antiDiagonalEpsilonGram_mulVec_of_rev_ne _ _ _ (hrev i), mulVec_zero, zero_add, mulVec_single_apply, he']
      simp only [colsOf]
      linear_combination (a.a k (Fin.castLE (by omega) i : Fin c).rev * u (Fin.castLE (by omega) i : Fin c).rev) * hs

end SlopeTestRemainingChoices

theorem monoAt_bes : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (F : Frames G), Std F → ∀ (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) (v : GlobalTheory.FinPl.Pl D), MonoAt (F.dB ρ h) (G.Λ (.grid (2 * ρ + 2) 0)) (lat0 F ρ h) v := by
  intro D T L sc G F hF ρ h v
  have hL : G.Λ (.grid (2 * ρ + 2) 0) = (G.colDec (2 * ρ + 2) (by omega) h).lat (G.Λ (.core (2 * ρ + 2)))
      (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1)) := G.sp.colLat _ _ h
  obtain ⟨hX, hY⟩ := proj_mem (G.colDec (2 * ρ + 2) (by omega) h) (F.dB ρ h) (hF.hB ρ h) (G.Λ (.core (2 * ρ + 2)))
    (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1))
  rw [← hL] at hX hY
  exact monoAt_of_proj (F.dB ρ h) _ hX hY v

end GlobalTheory.MonoBes

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColPtInvMemStdLatIff
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv GlobalTheory.LastVertexMove

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.LastColLat

variable {D : D7}

theorem actO_one_mem_latO (S T : HSp D) (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (h : GA D T)
    (hh : Lev.finE T h ∈ Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) LT))
    (u : WO S T) (hu : u ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True) :
    actO S T 1 h u ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True := by
  induction hu using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hu
    have e := GlobalTheory.AdelicLatMove.rankOne_pure S T a s t 1 α
    rw [mul_one] at e
    rw [← e, GlobalTheory.AdelicLatMove.actO_rankOne]
    refine GlobalTheory.AdelicLatMove.rankOne_mem_latO S T LS LT a ha _ ?_ _
      ((hh _).1 (GlobalTheory.AdelicLatMove.pure_mem_hatL LT α hα t ht))
    rw [GlobalTheory.AdelicLatMove.mt_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
    exact GlobalTheory.AdelicLatMove.pure_mem_hatL LS 1 (one_mem _) s hs
  | zero => simp only [actO, Matrix.mul_zero, Matrix.zero_mul]; exact zero_mem _
  | add y z _ _ hy hz => simp only [actO, Matrix.mul_add, Matrix.add_mul] at hy hz ⊢; exact add_mem hy hz
  | neg y _ hy => simp only [actO, Matrix.mul_neg, Matrix.neg_mul] at hy ⊢; exact neg_mem hy

theorem actO_inv_mem_latO_iff (S T : HSp D) (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (h : GA D T)
    (hh : Lev.finE T h ∈ Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) LT)) (u : WO S T) :
    actO S T (1 : GA D S)⁻¹ h⁻¹ u ∈ latO S T (LS : Set _) (LT : Set _) (fun _ => True) ↔
      u ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True := by
  have hh' : Lev.finE T h⁻¹ ∈ Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) LT) := by
    rw [map_inv]; exact inv_mem hh
  constructor
  · intro hu
    have := actO_one_mem_latO S T LS LT h hh _ hu
    rwa [GlobalTheory.AdelicLatMove.actO_actO_inv] at this
  · intro hu
    rw [inv_one]
    exact actO_one_mem_latO S T LS LT h⁻¹ hh' u hu

end GlobalTheory.LastColLat

namespace GlobalTheory.LastColLat

open Matrix

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem finEmb_stab {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (y : GfC A)
    (hy : Lev.finE A y.1 ∈ Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) Λ)) :
    Lev.finE B (finEmb d y).1 ∈ Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) (d.lat Λ fun _ => 1)) :=
  GlobalTheory.T.finiteEmbedding_mem_stabilizer_auxiliaryLattice d Λ y hy

theorem levRow_stab (S : GridChoice W U) (t : T) :
    ∀ n (hn : 1 ≤ n) (h : n ≤ D.R.m) (k : FinPt G (.grid n D.R.m)), finG (G.V (.grid n D.R.m)) k ∈ S.levRow t n h →
      Lev.finE (G.V (.grid n D.R.m)) k.1 ∈ Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.grid n D.R.m))) := by
  intro n hn h k hk
  obtain ⟨i, rfl⟩ : ∃ i, n = i + 1 := ⟨n - 1, by omega⟩
  have hmem : finG (G.V (.grid (i + 1) D.R.m)) k ∈
      S.levRow t (i + 1) h ⊓ UA D.sp.cm (G.V (.grid (i + 1) D.R.m)).gram :=
    Subgroup.mem_inf.2 ⟨hk, GlobalTheory.LevSplit.finE_mem_UA _ _⟩
  have hlevel : S.levRow t (i + 1) h ⊓ UA D.sp.cm (G.V (.grid (i + 1) D.R.m)).gram =
      G.levMax (.grid (i + 1) D.R.m) := by
    have hm : D.R.m ≠ 0 := by have := D.R.two_le_m; omega
    have hlocal (w : Pl D.host.E) (b : ℕ) (hb : b ≠ 0) :
        givenLevel G t w (i + 1, b) =
          GlobalTheory.SplitWeil.KO (Kw w) (Fin ((locGrid G t w).rank (i + 1, b))) := by
      cases b with
      | zero => exact (hb rfl).elim
      | succ _ => rfl
    rw [GridData.levMax]
    exact GlobalTheory.FunObj.LevRowSucc.prodLev_inf_UA
      (S.B.isFrame (i + 1) D.R.m (by omega) h le_rfl)
      (G.isV (X := .grid (i + 1) D.R.m) ⟨h, le_rfl⟩ fun j e => by cases e).sd (locPl G t) _ _
      (fun w => hlocal w.1 D.R.m hm)
  rw [hlevel, GridData.levMax, congLev_top] at hmem
  exact (Subgroup.mem_inf.1 hmem).2

theorem conj_stab (N : Std G U) {X : Node} (hX : DefNode D.R.m X) (g : FinPt G X)
    (hg : Lev.finE (G.V X) g.1 ∈ Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ X))) :
    Lev.finE (G.V X) ((N.u X)⁻¹ * g * N.u X).1 ∈
      Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) (colLat (N.fr X))) := by
  intro v
  have hu := N.u_lat X hX
  have e : ((Lev.finE (G.V X) ((N.u X)⁻¹ * g * N.u X).1 : GL _ _) : Matrix _ _ _) *ᵥ v =
      ((Lev.finE (G.V X) (N.u X).1)⁻¹ : GL _ _).1 *ᵥ ((Lev.finE (G.V X) g.1).1 *ᵥ ((Lev.finE (G.V X) (N.u X).1).1 *ᵥ v)) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [e, hu, hu, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  exact hg _

theorem topLast_stab (N : Std G U) (g : FinPt G (.top D.R.m))
    (hg : Lev.finE (G.V (.top D.R.m)) g.1 ∈
      Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) (colLat (N.fr (.top D.R.m))))) :
    Lev.finE (G.V (.top ((lastIx D : ℕ) + 1))) (topLast g).1 ∈
      Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) (colLat (N.fr (.top ((lastIx D : ℕ) + 1))))) := by
  have key : ∀ n (e : D.R.m = n) (g : FinPt G (.top D.R.m)),
      Lev.finE (G.V (.top D.R.m)) g.1 ∈ Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) (colLat (N.fr (.top D.R.m)))) →
      Lev.finE (G.V (.top n)) (e ▸ g : FinPt G (.top n)).1 ∈
        Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) (colLat (N.fr (.top n)))) := by
    intro n e g hg
    subst e
    exact hg
  exact key _ (lastIx_succ D) g hg

theorem colPt_inv_mem_stdLat_iff : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T}, t ∈ U → ∀ k : FinPt G (.grid D.R.m D.R.m),
    finG (G.V (.grid D.R.m D.R.m)) k ∈ S.levRow t D.R.m le_rfl →
    ∀ x : WO (G.pS (.top t (lastIx D))) (G.pT (.top t (lastIx D))),
    actO _ _ (colPt S t (finEmb G.sp.topDec k)).1⁻¹ (colPt S t (finEmb G.sp.topDec k)).2⁻¹ x ∈ stdLat S (.top t (lastIx D)) ↔
      x ∈ stdLat S (.top t (lastIx D)) := by
  intro D T L sc G W U S t _ k hk x
  have hm : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
  have h1 := levRow_stab S t D.R.m hm le_rfl k hk
  have e : G.Λ (.top D.R.m) = G.sp.topDec.lat (G.Λ (.grid D.R.m D.R.m)) (fun _ => 1) := G.sp.topLat
  have h2 : Lev.finE (G.V (.top D.R.m)) (finEmb G.sp.topDec k).1 ∈
      Formalism.UG.stabGL (Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.top D.R.m))) := by
    rw [e]; exact finEmb_stab G.sp.topDec _ k h1
  have h3 := conj_stab S.N (X := .top D.R.m) (by simp [DefNode]) _ h2
  have h4 := topLast_stab S.N _ h3
  exact actO_inv_mem_latO_iff _ _ _ _ _ h4 x

end GlobalTheory.LastColLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplementaryAdelicSchwartzArchimedeanReplace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.TwistRest

open scoped Classical in
theorem restTr : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (r : (κ → AF F) → ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r → f ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f₁ r := by
  intro F _ _ κ _ f f₁ r hr hf
  obtain ⟨hinv, hsch⟩ := hr

  set g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ := fun y => r (fun i => ((0 : InfiniteAdeleRing F), y i)) with hgdef
  have hrg : ∀ x : κ → AF F, r x = g (fun i => (x i).2) := by
    intro x
    let z : κ → AF F := fun i => ((x i).1, (0 : FiniteAdeleRing (𝓞 F) F))
    have hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) z := by
      intro u hu
      have hu1 : u.1 = 0 :=
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
      funext i
      change (u * z i : AF F) = 0
      refine Prod.ext ?_ ?_
      · change u.1 * (x i).1 = 0
        rw [hu1, zero_mul]
      · change u.2 * 0 = 0
        exact mul_zero _
    let x' : κ → AF F := fun i => ((0 : InfiniteAdeleRing F), (x i).2)
    have := hinv x' z hz
    have hx : x = x' + z := by
      funext i
      refine Prod.ext ?_ ?_
      · change (x i).1 = (0 : InfiniteAdeleRing F) + (x i).1
        rw [zero_add]
      · change (x i).2 = (x i).2 + (0 : FiniteAdeleRing (𝓞 F) F)
        rw [add_zero]
    exact (congrArg r hx).trans this
  have htens : ∀ f' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (⇑f') r = GlobalTheory.WeilM.pureA F (⇑f') g := by
    intro f'
    funext x
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, GlobalTheory.WeilM.pureA, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI]
    rw [hrg x]

  obtain ⟨x₀, hx₀⟩ : ∃ x₀, f x₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (SchwartzMap.ext h)
  let a : κ → InfiniteAdeleRing F := fun i => (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x₀ i)
  let Λ : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :=
    { toFun := fun Φ y => Φ (fun i => (a i, y i))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hΛ : ∀ (f' : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g' : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
      Λ (GlobalTheory.WeilM.pureA F f' g') = f' x₀ • g' := by
    intro f' g'
    funext y
    change f' (fun i => (InfiniteAdeleRing.ringEquiv_mixedSpace F) (a i)) * g' y = f' x₀ * g' y
    congr 1
    apply congrArg f'
    funext i
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (x₀ i)
  have hle : GlobalTheory.WeilM.schA F κ ≤ (GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)).comap Λ := by
    refine Submodule.span_le.2 ?_
    rintro Φ ⟨f', g', hg', rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, hΛ]
    exact Submodule.smul_mem _ _ hg'
  have hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) := by
    have h1 := hle (htens f ▸ hsch)
    rw [Submodule.mem_comap, hΛ] at h1
    have := Submodule.smul_mem _ (f x₀)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hx₀, one_smul] at this
  refine ⟨hinv, ?_⟩
  rw [htens f₁]
  exact Submodule.subset_span ⟨f₁, g, hg, rfl⟩

end GlobalTheory.TwistRest
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagonalFixingDoublingMatrix
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.SplitDblGen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev dC (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) :
    Matrix (Fin d ⊕ Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) := diagCols (Fin d)

def half : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) := algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (⅟(2 : AF F))

def diagonalFixingDoublingMatrix (c : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (d : ℕ) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  1 + (half * c) • (dC F E d * (GlobalTheory.InertDbl.antiCols d)ᵀ)

def splitDoublingNBlock {d : ℕ} (c : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (K K' : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  ((half : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) * half * half) • ((1 - c) • (K - 1) - (1 + c) • (K' - 1))

def nMat {d : ℕ} (c : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (K K' : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  let nBlock : Matrix (Fin d ⊕ Fin d) (Fin d) _ :=
    GlobalTheory.InertDbl.antiCols d * splitDoublingNBlock c K K'
  1 + nBlock * (dC F E d)ᵀ

def tMat {d : ℕ} (c : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (K : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin d) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  1 + (half * (1 + c)) • (K - 1)

end GlobalTheory.SplitDblGen
end
end

