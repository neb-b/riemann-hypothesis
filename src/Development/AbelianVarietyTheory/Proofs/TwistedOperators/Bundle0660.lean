module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0650
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0414
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0409
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0604
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0537
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0599
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0379
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1128
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1166
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0546
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0565
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0385

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridBasePointTrivialOffTensorPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RowVal

theorem placeIdem_eq_under_of_idemAt {D : D7} {P : HeightOneSpectrum (𝓞 D.host.E)} {e : Formalism.L2.Theta.AE D}
    (h : Formalism.L2.NTheta.IsIdemAt e P) {v' : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v' ε)
    (hs : e + cA D e = algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) ε) : v' = P.under (𝓞 D.host.F) := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨h1, h2, -⟩ := h.1
  have hm : e * (e + cA D e) = e := by rw [mul_add, h1, h2, add_zero]
  by_contra hne
  have h0 := (GlobalTheory.IdemSupport.place_comp hΦ hε).2.2 P (fun e => hne e.symm)
  have h3 := GlobalTheory.IdemSupport.ev_mul (Φ := Φ) e (e + cA D e) P
  rw [hm, hs, h0, mul_zero, (GlobalTheory.IdemSupport.delta_of_isIdemAt hΦ h).2.1] at h3
  exact one_ne_zero h3

theorem base_mt_mulVec_off : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (B : Frames G) (b : Pts G), IsBase t B b → ∀ v : GlobalTheory.FinPl.Pl D, (∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ v) → ∀ y : Fin (G.V (.grid D.R.m 0)).rank → AE D, (∀ i, y i ∈ idAt D (· = v)) → Formalism.L2.Theta.mt _ (b 0) *ᵥ y = y := by
  intro D T L sc G t B b hb v hv y hy
  obtain ⟨e, ⟨⟨es, hes, rfl⟩, -⟩, hsupp, -⟩ := hb.1
  have hkill : ∀ PP ∈ locPl G t, ∀ a ∈ idAt D (· = v), (es PP + cA D (es PP)) * a = 0 := by
    intro PP hPP a ha
    obtain ⟨-, -, v', ε, hε, hs⟩ := (hes PP hPP).1
    have hv' : v' = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) := placeIdem_eq_under_of_idemAt (hes PP hPP) hε hs
    rw [hs]
    apply (GlobalTheory.FinPl.placeIdem_acts D v' ε hε).2
    rw [GlobalTheory.FinPl.mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere] at ha ⊢
    refine ⟨ha.1, fun w hw => ha.2 w ?_⟩
    intro h
    apply hw
    intro hwv'
    exact hv PP hPP (hv'.symm.trans (hwv'.symm.trans h))
  have hz : ∀ i, ((Formalism.L2.Theta.mt _ (b 0) - 1) *ᵥ y) i ∈ idAt D (· = v) := fun i => by
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)
  have hE : ∀ i, ((Formalism.L2.Theta.mt _ (b 0) - 1) *ᵥ y) i =
      ((∑ PP ∈ locPl G t, es PP) + cA D (∑ PP ∈ locPl G t, es PP)) * ((Formalism.L2.Theta.mt _ (b 0) - 1) *ᵥ y) i := by
    intro i
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_assoc, hsupp i j]
  have h0 : (Formalism.L2.Theta.mt _ (b 0) - 1) *ᵥ y = 0 := by
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hE i, map_sum, ← Finset.sum_add_distrib, Finset.sum_mul]
    exact Finset.sum_eq_zero fun PP hPP => hkill PP hPP _ (hz i)
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
  exact h0

end GlobalTheory.RowVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridRowMovedLatticeSplitsJacobiLargeDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

open GlobalTheory.AscFin GlobalTheory.AscFin.MonoJac GlobalTheory.RowShape
open GlobalTheory.SeeSaw.SplitLat (colProj)
open scoped nonZeroDivisors

namespace GlobalTheory.RowShape.MonoRow

variable {D : D7}

def cfR (c : ℕ) {ρ : ℕ} (r : Fin ρ → D.host.E) : Matrix (Fin ρ) (Fin c) D.host.E :=
  fun p q => if p.1 = q.1 then (r p)⁻¹ else 0

theorem cols_mul_coeff_eq_reflected_sum {n c ρ : ℕ} (a : Matrix (Fin n) (Fin c) D.host.E) (hc : c = 2 * ρ) (h : ρ ≤ c) (r s : Fin ρ → D.host.E)
    (hr : ∀ p, r p ≠ 0) (hs : ∀ p, s p ≠ 0) :
    a = (colsOf a (Fin.castLE h) r : Matrix (Fin n) (Fin ρ) D.host.E) * (cfR c r : Matrix (Fin ρ) (Fin c) D.host.E) +
      (colsOf a (fun p : Fin ρ => (Fin.castLE h p : Fin c).rev) s : Matrix (Fin n) (Fin ρ) D.host.E) *
        (cfE' c s : Matrix (Fin ρ) (Fin c) D.host.E) := by
  refine Matrix.ext fun k q => ?_
  rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]
  simp only [colsOf, cfR, cfE']
  by_cases hq : q.1 < ρ
  · rw [Finset.sum_eq_single ⟨q.1, hq⟩, Finset.sum_eq_zero]
    · rw [if_pos rfl, add_zero, show (Fin.castLE h ⟨q.1, hq⟩ : Fin c) = q from Fin.ext rfl, mul_comm,
        ← mul_assoc, inv_mul_cancel₀ (hr _), one_mul]
    · intro p _
      rw [if_neg (by omega), mul_zero]
    · intro p _ hp
      rw [if_neg (fun e => hp (Fin.ext e)), mul_zero]
    · intro hn; exact absurd (Finset.mem_univ _) hn
  · have hp' : c - 1 - q.1 < ρ := by have := q.2; omega
    rw [Finset.sum_eq_zero, Finset.sum_eq_single ⟨c - 1 - q.1, hp'⟩]
    · rw [if_pos (by have := q.2; simp only [Fin.val_mk]; omega), zero_add,
        show ((Fin.castLE h ⟨c - 1 - q.1, hp'⟩ : Fin c).rev) = q from Fin.ext (by simp [Fin.val_rev]; omega),
        mul_comm, ← mul_assoc, inv_mul_cancel₀ (hs _), one_mul]
    · intro p _ hp
      rw [if_neg (fun e => hp (Fin.ext (show p.1 = c - 1 - q.1 by omega))), mul_zero]
    · intro hn; exact absurd (Finset.mem_univ _) hn
    · intro p _
      rw [if_neg (by have := p.2; omega), mul_zero]

theorem mono_at_lattice_of_column_frames {A B : HSp D} {c ρ : ℕ} {ε : D.host.E} (t : HermitianOrthogonalExtensionData A B c ε) (d : HypDec B A ρ) (hc : c = 2 * ρ)
    (hρ : ρ ≤ c) (r s : Fin ρ → D.host.E) (hr : ∀ p, r p ≠ 0) (hs : ∀ p, s p ≠ 0)
    (he : d.e = colsOf t.a (Fin.castLE hρ) r) (he' : d.e' = colsOf t.a (fun p : Fin ρ => (Fin.castLE hρ p : Fin c).rev) s)
    (hi : d.i₀ = frameMat B A t.ι) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E))
    (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (v : GlobalTheory.FinPl.Pl D) : GlobalTheory.FinPl.MonoAt d (t.lat Λ 𝔟) Λ v := by
  have ha := cols_mul_coeff_eq_reflected_sum t.a hc hρ r s hr hs
  rw [← he, ← he'] at ha
  have hX : d.qX * t.a = cfR c r := by
    rw [ha, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, GlobalTheory.SeeSaw.SplitLat.qX_e, GlobalTheory.SeeSaw.SplitLat.qX_e',
      Matrix.one_mul, Matrix.zero_mul, add_zero]
  have hY : d.qY * t.a = cfE' c s := by
    rw [ha, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, GlobalTheory.SeeSaw.SplitLat.qY_e, GlobalTheory.SeeSaw.SplitLat.qY_e',
      Matrix.one_mul, Matrix.zero_mul, zero_add]
  have h0 : d.q0 * t.a = 0 := by
    rw [ha, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, GlobalTheory.SeeSaw.SplitLat.wittDecomposition_coreProj_mul_e_eq_zero, GlobalTheory.SeeSaw.SplitLat.wittZeroProjection_mul_dualBasis_eq_zero,
      Matrix.zero_mul, Matrix.zero_mul, add_zero]
  refine monoAt_of_proj d _ _ (fun i => ?_) (fun i => ?_) ?_ ?_ v
  · refine sumLat_map _ (Pi.single (Fin.castLE hρ i) 1) ?_ ?_ ?_
    · rw [colProj_mul, ← hi, GlobalTheory.SeeSaw.SplitLat.qX_i₀, colProj_zero]
    · rw [colProj_mul, hX]
      refine Matrix.ext fun k q => ?_
      rw [Matrix.mul_diagonal, he]
      simp only [colProj, Matrix.of_apply, colsOf, cfR]
      by_cases hq : i.1 = q.1
      · have e : (Fin.castLE hρ i : Fin c) = q := Fin.ext hq
        subst e
        rw [if_pos hq, Pi.single_eq_same, mul_one, mul_comm (r i), mul_assoc, mul_inv_cancel₀ (hr _), mul_one]
      · have e : q ≠ (Fin.castLE hρ i : Fin c) := fun e => hq (by rw [e]; rfl)
        rw [if_neg hq, mul_zero, Pi.single_apply, if_neg e, mul_zero]
    · intro p
      rw [Pi.single_apply]
      split_ifs
      · exact Or.inr rfl
      · exact Or.inl rfl
  · refine sumLat_map _ (Pi.single (Fin.castLE hρ i : Fin c).rev 1) ?_ ?_ ?_
    · rw [colProj_mul, ← hi, GlobalTheory.SeeSaw.SplitLat.qY_i₀, colProj_zero]
    · rw [colProj_mul, hY]
      refine Matrix.ext fun k q => ?_
      rw [Matrix.mul_diagonal, he']
      simp only [colProj, Matrix.of_apply, colsOf, cfE']
      by_cases hq : q.1 + i.1 + 1 = c
      · have e : (Fin.castLE hρ i : Fin c).rev = q := Fin.ext (by simp [Fin.val_rev]; omega)
        subst e
        rw [if_pos hq, Pi.single_eq_same, mul_one, mul_comm (s i), mul_assoc, mul_inv_cancel₀ (hs _), mul_one]
      · have e : q ≠ (Fin.castLE hρ i : Fin c).rev := fun e => hq (by rw [e]; simp [Fin.val_rev]; omega)
        rw [if_neg hq, mul_zero, Pi.single_apply, if_neg e, mul_zero]
    · intro p
      rw [Pi.single_apply]
      split_ifs
      · exact Or.inr rfl
      · exact Or.inl rfl
  · exact sumLat_proj d.q0 (by rw [← hi]; exact GlobalTheory.SeeSaw.SplitLat.wittDecomposition_coreProj_mul_core_eq_one d) h0
  · intro x hx
    rw [hi]
    exact mem_sumLat_of hx

theorem monoAt_jacDec {A B : HSp D} {c σ : ℕ} {ε : D.host.E} (t : HermitianOrthogonalExtensionData A B c ε) (h : c = 2 * σ)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
    (v : GlobalTheory.FinPl.Pl D) : GlobalTheory.FinPl.MonoAt (GlobalTheory.RowUnf.jacDec t h) (t.lat Λ 𝔟) Λ v := by
  have hρ : σ ≤ c := by omega
  refine mono_at_lattice_of_column_frames t _ h hρ 1 1 (fun _ => one_ne_zero) (fun _ => one_ne_zero) ?_ ?_ rfl Λ 𝔟 v
  · refine Matrix.ext fun k p => ?_
    simp only [colsOf, Pi.one_apply, one_mul]
    rfl
  · refine Matrix.ext fun k p => ?_
    simp only [colsOf, Pi.one_apply, one_mul]
    rfl

end GlobalTheory.RowShape.MonoRow

theorem GlobalTheory.RowShape.rowN_monoAt : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ n (hn : n < D.R.m) σ
    (h : D.R.m - 1 - n = 2 * σ) v, GlobalTheory.FinPl.MonoAt (rowJac ch.G n hn σ h) (GlobalTheory.RowShape.rowN ch.G n) (ch.G.Λ (.top n)) v := by
  refine ⟨0, fun _ _ _ => ⟨0, fun D _ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F _ ch _ _ => ?_⟩⟩
  intro n hn σ h v
  rw [GlobalTheory.RowShape.rowN, dite_eq_left hn]
  exact GlobalTheory.RowShape.MonoRow.monoAt_jacDec _ h _ _ v

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIdemSumEqSumSinglePlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.IdemSingleSum

theorem sum_mul_sum_orth {R ι : Type} [Ring R] [DecidableEq ι] (f : ι → R) (hid : ∀ i, f i * f i = f i)
    (horth : ∀ i j, i ≠ j → f i * f j = 0) (S S' : Finset ι) :
    (∑ i ∈ S, f i) * (∑ j ∈ S', f j) = ∑ i ∈ S ∩ S', f i := by
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  calc ∑ i ∈ S, ∑ j ∈ S', f i * f j = ∑ i ∈ S, if i ∈ S' then f i else 0 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases hi : i ∈ S'
        · rw [if_pos hi, Finset.sum_eq_single_of_mem i hi fun j _ hji => horth i j (Ne.symm hji), hid]
        · rw [if_neg hi]
          exact Finset.sum_eq_zero fun j hj => horth i j fun hij => hi (by rw [hij]; exact hj)
    _ = ∑ i ∈ S ∩ S', f i := Finset.sum_ite_mem S S' f

theorem isIdemAt_of_single {D : D7} {a : AE D} {w : Pl D.host.E} (h : IsIdemSum a {w}) :
    Formalism.L2.NTheta.IsIdemAt a w := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := h
  simpa using hes w (Finset.mem_singleton_self w)

private theorem mul_self_eq_of_isIdemAt {D : D7} {x : AE D} {w : Formalism.L2.DIV.Pl D.host.E}
    (hx : Formalism.L2.NTheta.IsIdemAt x w) : x * x = x := by
  have h := GlobalTheory.PartialIdemSum.mul_sum_of_isIdemAt hx {w} (fun _ => x) (by simpa using hx)
  simpa only [Finset.sum_singleton, Finset.mem_singleton_self, if_true] using h

private theorem mul_eq_zero_of_isIdemAt_of_ne {D : D7} {x y : AE D} {w w' : Formalism.L2.DIV.Pl D.host.E}
    (hx : Formalism.L2.NTheta.IsIdemAt x w) (hy : Formalism.L2.NTheta.IsIdemAt y w') (hne : w ≠ w') : x * y = 0 := by
  have h := GlobalTheory.PartialIdemSum.mul_sum_of_isIdemAt hx {w'} (fun _ => y) (by simpa using hy)
  rwa [Finset.sum_singleton, if_neg (by simpa using hne)] at h

private theorem eq_of_isIdemAt_of_isIdemAt {D : D7} {x y : AE D} {w : Formalism.L2.DIV.Pl D.host.E}
    (hx : Formalism.L2.NTheta.IsIdemAt x w) (hy : Formalism.L2.NTheta.IsIdemAt y w) : x = y := by
  have h1 := GlobalTheory.PartialIdemSum.mul_sum_of_isIdemAt hx {w} (fun _ => y) (by simpa using hy)
  have h2 := GlobalTheory.PartialIdemSum.mul_sum_of_isIdemAt hy {w} (fun _ => x) (by simpa using hx)
  simp only [Finset.sum_singleton, Finset.mem_singleton_self, if_true] at h1 h2
  calc x = x * y := h1.symm
    _ = y * x := mul_comm x y
    _ = y := h2

theorem sum_single : ∀ (D : D7) (e : AE D) (P : Finset (Pl D.host.E)), IsIdemSum e P → ∀ (eL : P → AE D), (∀ w, IsIdemSum (eL w) {w.1}) → e = ∑ w, eL w ∧ (∀ S : Finset P, IsIdemSum (∑ w ∈ S, eL w) (S.map (Function.Embedding.subtype _))) ∧ ∀ S S' : Finset P, (∑ w ∈ S, eL w) * (∑ w ∈ S', eL w) = ∑ w ∈ S ∩ S', eL w := by
  intro D e P he eL hL
  obtain ⟨⟨es, hes, hsum⟩, he0⟩ := he
  have hat : ∀ w : P, Formalism.L2.NTheta.IsIdemAt (eL w) w.1 := fun w => isIdemAt_of_single (hL w)
  have hprod : ∀ S S' : Finset P, (∑ w ∈ S, eL w) * (∑ w ∈ S', eL w) = ∑ w ∈ S ∩ S', eL w := fun S S' =>
    sum_mul_sum_orth eL (fun w => mul_self_eq_of_isIdemAt (hat w))
      (fun w w' hne => mul_eq_zero_of_isIdemAt_of_ne (hat w) (hat w') fun h => hne (Subtype.ext h)) S S'
  have htot : e = ∑ w, eL w := by
    rw [hsum, ← Finset.sum_coe_sort P es]
    exact Finset.sum_congr rfl fun w _ => (eq_of_isIdemAt_of_isIdemAt (hat w) (hes w.1 w.2)).symm
  refine ⟨htot, fun S => ⟨⟨es, ?_, ?_⟩, ?_⟩, hprod⟩
  · intro PP hPP
    obtain ⟨w, -, rfl⟩ := Finset.mem_map.1 hPP
    exact hes w.1 w.2
  · rw [Finset.sum_map]
    exact Finset.sum_congr rfl fun w _ => eq_of_isIdemAt_of_isIdemAt (hat w) (hes w.1 w.2)
  · have hse : (∑ w ∈ S, eL w) * e = ∑ w ∈ S, eL w := by
      rw [htot, hprod, Finset.inter_univ]
    set s := ∑ w ∈ S, eL w
    calc s * cA D s = (s * e) * cA D (e * s) := by rw [hse, mul_comm e s, hse]
      _ = s * (e * cA D e) * cA D s := by rw [map_mul]; ring
      _ = 0 := by rw [he0, mul_zero, zero_mul]

end GlobalTheory.IdemSingleSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualGridRowMovedLatticeLargeDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped nonZeroDivisors

namespace GlobalTheory.RowShape

variable {D : D7}

theorem mem_spanSingleton_mul_iff {s x : D.host.E} (hs : s ≠ 0) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :
    x ∈ FractionalIdeal.spanSingleton _ s * I ↔ x * s⁻¹ ∈ I := by
  rw [FractionalIdeal.mem_singleton_mul]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rwa [mul_comm, ← mul_assoc, inv_mul_cancel₀ hs, one_mul]
  · intro h
    exact ⟨x * s⁻¹, h, by rw [mul_comm, mul_assoc, inv_mul_cancel₀ hs, mul_one]⟩

theorem tiltSc_ne_zero (j : ℕ) (p : Fin (D.R.m - 1 - j)) : tiltSc D j p ≠ 0 := by
  unfold tiltSc
  split_ifs
  · exact inv_ne_zero (pow_ne_zero _ cmHost_imaginaryGenerator_ne_zero)
  · exact star_ne_zero.2 (pow_ne_zero _ cmHost_imaginaryGenerator_ne_zero)
  · exact one_ne_zero

theorem tiltSc_mul_star_rev (j : ℕ) (p : Fin (D.R.m - 1 - j)) : tiltSc D j p * star (tiltSc D j p.rev) = 1 := by
  have hx : D.host.xi0 ≠ 0 := cmHost_imaginaryGenerator_ne_zero
  obtain ⟨a, ha⟩ := D.R.m_even
  have hp := p.2
  unfold tiltSc
  by_cases hj : Odd j
  · obtain ⟨b, hb⟩ := hj
    have hj' : Odd j := ⟨b, hb⟩
    rw [if_pos hj', if_pos hj', Fin.val_rev]
    by_cases h1 : 2 * p.1 < D.R.m - 1 - j
    · rw [if_pos h1, if_neg (by omega)]
      have e : D.R.m - 1 - j - 1 - (D.R.m - 1 - j - (p.1 + 1)) = p.1 := by omega
      rw [e, star_star, inv_mul_cancel₀ (pow_ne_zero _ hx)]
    · rw [if_neg h1, if_pos (by omega)]
      have e : D.R.m - 1 - j - (p.1 + 1) = D.R.m - 1 - j - 1 - p.1 := by omega
      rw [e, star_inv₀, mul_inv_cancel₀ (star_ne_zero.2 (pow_ne_zero _ hx))]
  · rw [if_neg hj, if_neg hj, star_one, one_mul]

theorem rowId_ne_zero_and_dual (j : ℕ) (p : Fin (D.R.m - 1 - j)) :
    rowId D j p ≠ 0 ∧ ∀ x, x ∈ rowId D j p.rev ↔ star x ∈ (rowId D j p)⁻¹ := by
  obtain ⟨hA, hconj⟩ := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).1
  obtain ⟨h0, hd⟩ := GlobalTheory.ChiGrid.stairId_ne_zero_and_mem_rev_iff D _ _ hA hconj (D.R.m - 1 - j) p
  have hs := tiltSc_ne_zero (D := D) j p
  have hs' := tiltSc_ne_zero (D := D) j p.rev
  refine ⟨mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.2 hs) h0, fun x => ?_⟩
  unfold rowId
  rw [mul_inv, FractionalIdeal.spanSingleton_inv, mem_spanSingleton_mul_iff hs', mem_spanSingleton_mul_iff (inv_ne_zero hs),
    inv_inv, hd, star_mul', star_inv₀]
  have e : (star (tiltSc D j p.rev))⁻¹ = tiltSc D j p := by
    exact inv_eq_of_mul_eq_one_left (tiltSc_mul_star_rev j p)
  rw [e]

variable {T : Type} {L : LevCh D T} {sc : Consts}

theorem isSelfDualC_rowN (G : GridData L sc) (j : ℕ) (hj : j ≤ D.R.m) : IsSelfDualC _ (rowN G j) := by
  unfold rowN
  split_ifs with h
  · refine GlobalTheory.ChiGrid.SumDual.isSelfDualC_lat D _ _ _ _ (G.rowDec j h) _ _ (Or.inr rfl)
      (G.isV (X := .top j) hj (fun _ h' => by cases h')).sd (fun p => (rowId_ne_zero_and_dual j p).1)
      (fun p x => (rowId_ne_zero_and_dual j p).2 x)
  · exact (G.isV (X := .grid D.R.m j) ⟨le_rfl, hj⟩ (fun _ h' => by
      have := D.R.two_le_m
      injection h' with h1; omega)).sd

end GlobalTheory.RowShape

theorem GlobalTheory.RowShape.big_isSelfDualC_rowN :
    Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ j, j ≤ D.R.m → IsSelfDualC _ (GlobalTheory.RowShape.rowN ch.G j) :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ j hj => GlobalTheory.RowShape.isSelfDualC_rowN ch.G j hj⟩⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiFlagCharPrimitiveMovedLatticeLargeDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped nonZeroDivisors

namespace GlobalTheory.RowShape

namespace PrimJac

theorem rowJac_line {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (n : ℕ) (hn : n < D.R.m) (σ : ℕ)
    (h : D.R.m - 1 - n = 2 * σ) (v : Pl D) (p : Fin σ) (a : AE D) :
    colMul (rowJac G n hn σ h).jX p a ∈ latV _ (rowN G n) (· = v) ↔
      a ∈ idV (rowId D n (Fin.castLE (by omega) p)) v := by
  have e1 : colMul (rowJac G n hn σ h).jX p a =
      fun k => a * incA D (1 * (G.rowDec n hn).a k (Fin.castLE (by omega) p)) := by
    funext k
    simp [colMul, HypDec.jX, rat, Matrix.map_apply, rowJac, jacDec, HermitianOrthogonalExtensionData.iso]
  have e2 : rowN G n = (G.rowDec n hn).lat (G.Λ (.top n)) (rowId D n) := by
    unfold rowN; rw [dite_eq_left hn]
  rw [e1, e2, GlobalTheory.StairLine.line_mem_iff _ _ _ _ (by simp only [Fin.coe_castLE]; omega) one_ne_zero v a, inv_one,
    FractionalIdeal.spanSingleton_one, one_mul]

theorem stairId_ne_zero (D : D7) (c : ℕ) (p : Fin c) : stairId D.host.AA D.host.AAbar c p ≠ 0 := by
  unfold stairId
  exact mul_ne_zero (pow_ne_zero _ (GlobalTheory.CuspCharLattice.host_AA_ne_zero _))
    (inv_ne_zero (pow_ne_zero _ (GlobalTheory.Member.LatSelfDual.AAbar_ne_zero D)))

theorem tiltSc_first {D : D7} {n : ℕ} (hodd : Odd n) (p : Fin (D.R.m - 1 - n)) (hp : 2 * p.1 < D.R.m - 1 - n) :
    tiltSc D n p = (D.host.xi0 ^ p.1)⁻¹ := by
  unfold tiltSc; rw [if_pos hodd, if_pos hp]

theorem rowId_ratio {D : D7} {n : ℕ} (hodd : Odd n) (p q : Fin (D.R.m - 1 - n)) (hpq : q.1 = p.1 + 1)
    (hq : 2 * q.1 < D.R.m - 1 - n) : rowId D n p * (rowId D n q)⁻¹ = dI D := by
  have hx : D.host.xi0 ≠ 0 := cmHost_imaginaryGenerator_ne_zero
  unfold rowId
  rw [tiltSc_first hodd p (by omega), tiltSc_first hodd q hq,
    stairId_succ (GlobalTheory.Member.LatSelfDual.AAbar_ne_zero D) p q hpq]
  have hS := stairId_ne_zero D (D.R.m - 1 - n) q
  revert hS
  generalize stairId D.host.AA D.host.AAbar (D.R.m - 1 - n) q = S
  intro hS
  rw [mul_inv, FractionalIdeal.spanSingleton_inv, inv_inv]
  unfold dI
  calc _ = FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (D.host.xi0 ^ p.1)⁻¹ *
        FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (D.host.xi0 ^ q.1) * D.host.AA * D.host.AAbar * (S * S⁻¹) := by ring
    _ = _ := by
      rw [mul_inv_cancel₀ hS, mul_one, FractionalIdeal.spanSingleton_mul_spanSingleton, hpq, pow_succ,
        ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hx), one_mul]

end PrimJac

open PrimJac

theorem primAt_rowJac {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (ψ : AddChar (AF D.host.F) ℂ)
    (hψ : IsStdChar D ψ (-1)) (n : ℕ) (hn : n < D.R.m) (σ : ℕ) (h : D.R.m - 1 - n = 2 * σ) (v : Pl D) :
    PrimAt ψ (rowJac G n hn σ h) (rowN G n) v := by
  have hodd : Odd n := by
    obtain ⟨k, hk⟩ := D.R.m_even
    exact ⟨k - σ - 1, by omega⟩
  intro i j hij s hs
  have key : (∀ a : AE D, colMul (rowJac G n hn σ h).jX j a ∈ latV _ (rowN G n) (· = v) →
      colMul (rowJac G n hn σ h).jX i (s * a) ∈ latV _ (rowN G n) (· = v)) ↔
      ∀ a ∈ idV (rowId D n (Fin.castLE (by omega) j)) v, s * a ∈ idV (rowId D n (Fin.castLE (by omega) i)) v :=
    ⟨fun H a ha => (rowJac_line G n hn σ h v i _).1 (H a ((rowJac_line G n hn σ h v j a).2 ha)),
      fun H a hc => (rowJac_line G n hn σ h v i _).2 (H a ((rowJac_line G n hn σ h v j a).1 hc))⟩
  have hne : ∀ p : Fin (D.R.m - 1 - n), rowId D n p ≠ 0 := fun p => mul_ne_zero
    (by
      rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
      unfold tiltSc
      split_ifs <;> simp [cmHost_imaginaryGenerator_ne_zero])
    (stairId_ne_zero D _ p)
  rw [key, GlobalTheory.IdealQuot.mul_subset_iff D v _ _ (hne _) (hne _) s hs,
    rowId_ratio hodd _ _ (by simp only [Fin.coe_castLE]; exact hij) (by simp only [Fin.coe_castLE]; have := j.2; omega)]
  exact DiffDual.idV_dI_iff D ψ hψ v s hs

theorem big_primAt_rowJac : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ n (hn : n < D.R.m) σ
    (h : D.R.m - 1 - n = 2 * σ) v, GlobalTheory.FinPl.PrimAt ch.W.ψ (rowJac ch.G n hn σ h) (GlobalTheory.RowShape.rowN ch.G n) v :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ n hn σ h v =>
    primAt_rowJac ch.G ch.W.ψ ch.W.ψ_std n hn σ h v⟩⟩

end GlobalTheory.RowShape
end

