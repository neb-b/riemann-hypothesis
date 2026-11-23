module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0678
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0658
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0356
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0573
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0683
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0633
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0676
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0649
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0521
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0644
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0344
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0566
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiLevelOneCosetAtGoodPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0674
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0685
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0522
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0339
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0348

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.Unf.FB (selFirst lastE mul_mul_mul_of_gram)

namespace GlobalTheory.AscFin.GoodStd

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem xLast_rat {V V₀ A L : HSp D} {σ : ℕ} (d : HypDec V V₀ σ) (o : OrthDec V₀ A L) (ζ : Fin L.rank → D.host.E)
    (hζ : IsLineVec L ζ) : ∃ x₀ : Matrix (Fin V.rank) (Fin (σ + 1)) D.host.E,
      LinearIndependent D.host.E x₀.transpose ∧ xLast d (vecB o ζ) = rat x₀ := by
  set x₀ : Matrix (Fin V.rank) (Fin (σ + 1)) D.host.E := d.e * selFirst D σ + d.i₀ * vecMulVec (vecB o ζ) (lastE D σ) with hx₀
  have hne : ∀ x : Fin σ, (Fin.last σ = x.castSucc) ↔ False := fun x => iff_false_intro (Fin.castSucc_lt_last x).ne'
  have hrat : xLast d (vecB o ζ) = rat x₀ := by
    funext k j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [hx₀, xLast, rat, selFirst, lastE, Matrix.mul_apply, vecMulVec, HypDec.j0, mulVec, dotProduct, ratV, vecB, hne]
    · simp [hx₀, xLast, rat, selFirst, lastE, Matrix.mul_apply, vecMulVec, HypDec.jX, mulVec, dotProduct, ratV, vecB]
  have hgram : x₀ᴴ * V.gram * x₀ = (vecMulVec ζ (lastE D σ))ᴴ * L.gram * vecMulVec ζ (lastE D σ) := by
    have hXX := mul_mul_mul_of_gram (n := Fin (σ + 1)) d.ee
    have h0X := mul_mul_mul_of_gram (n := Fin (σ + 1)) d.i₀e
    have hX0 : d.eᴴ * V.gram * d.i₀ = 0 := by
      have := congrArg conjTranspose d.i₀e
      rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, conjTranspose_zero,
        ← Matrix.mul_assoc] at this
    have hX0' := mul_mul_mul_of_gram (n := Fin (σ + 1)) hX0
    have h00 := mul_mul_mul_of_gram (n := Fin (σ + 1)) d.iso
    have hBB := mul_mul_mul_of_gram (n := Fin (σ + 1)) o.isoB
    have hz : vecMulVec (vecB o ζ) (lastE D σ) = o.iB * vecMulVec ζ (lastE D σ) := by
      rw [vecB, mul_vecMulVec]
    rw [hx₀, hz]
    simp only [conjTranspose_add, conjTranspose_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hXX, h0X, hX0',
      h00, hBB, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  refine ⟨x₀, ?_, hrat⟩
  refine Fintype.linearIndependent_iff.2 ?_
  intro g hg
  have hv : x₀ *ᵥ g = 0 := by
    funext k
    have := congrFun hg k
    simpa [Finset.sum_apply, mulVec, dotProduct, mul_comm] using this
  have h0 : d.e'ᴴ * V.gram * d.i₀ = 0 := by
    have := congrArg conjTranspose d.i₀e'
    rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, conjTranspose_zero,
      ← Matrix.mul_assoc] at this
  have hq : (d.e'ᴴ * V.gram) * x₀ = selFirst D σ := by
    rw [hx₀, Matrix.mul_add, ← Matrix.mul_assoc, d.e'e, Matrix.one_mul, ← Matrix.mul_assoc, h0, Matrix.zero_mul, add_zero]
  have h1 : selFirst D σ *ᵥ g = 0 := by rw [← hq, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  have h2 : ((vecMulVec ζ (lastE D σ))ᴴ * L.gram * vecMulVec ζ (lastE D σ)) *ᵥ g = 0 := by
    rw [← hgram, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  intro i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · have h3 := congrFun h2 (Fin.last σ)
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, vecMulVec_mulVec, conjTranspose_vecMulVec, vecMulVec_mulVec] at h3
    simp [lastE, mulVec_smul] at h3
    rcases h3 with h3 | h3
    · exact h3
    · exact absurd h3 hζ.2
  · have := congrFun h1 i
    simpa [selFirst, mulVec, dotProduct] using this

theorem loc_cls {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (s : Step ψ V V₀ W W₀ ρ σ)
    (x : Mx D W.rank ρ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (hx : x = rat x₀) (y : Mx D V₀.rank σ)
    (p : Pieces V₀ W W₀ ρ σ) (Γ : AddSubgroup (WO V W)) (K : Subgroup (GA D W)) (hψ : IsStdChar D ψ (-1))
    (hli : LinearIndependent D.host.E x₀.transpose) (hp : p.Is dV dW x ψ) (hs : Splits dV dW p x y ψ Γ)
    (hfin : K ≤ GfC W) (hcpt : IsCompact (K : Set (GA D W)))
    (hopn : IsOpen ((K.subgroupOf (GfC W) : Subgroup (GfC W)) : Set (GfC W)))
    (hfix : ∀ f, VacG ψ V W Γ f → ∀ k ∈ K, s.om (1, k) f = f)
    (hsupp : ∀ h, Cond dW p x y ψ (fun _ => True) h → (∀ κ ∈ K, Cond dW p x y ψ (fun _ => True) (h * κ)) →
      ∃ r ∈ Rgrp W x, ∃ a ∈ GinfC W, ∃ k ∈ K, h = r * a * k) :
    Loc dV dW s x y (cls dV dW p x y ψ) p.Γ₀ K ∧ ∀ Φ ∈ cls dV dW p x y ψ, VacG ψ V W Γ Φ := by
  subst hx
  have hvac : ∀ Φ ∈ cls dV dW p (rat x₀) y ψ, VacG ψ V W Γ Φ := fun Φ hΦ =>
    _root_.GlobalTheory.AscFin.SplitVac.cls_vac D ψ hψ V V₀ W W₀ ρ σ dV dW p (rat x₀) y Γ hp hs Φ hΦ
  have hst := fun Φ hΦ => _root_.GlobalTheory.AscFinStab.cls_stable D ψ V V₀ W W₀ ρ σ dV dW s x₀ y hli p hp Φ hΦ
  refine ⟨⟨fun Φ hΦ => hΦ.1, fun Φ hΦ => (hst Φ hΦ).1, fun Φ hΦ => (hst Φ hΦ).2.1, fun Φ hΦ => (hst Φ hΦ).2.2, hfin,
    hcpt, hopn, fun Φ hΦ k hk => hfix Φ (hvac Φ hΦ) k hk, ?_, _root_.GlobalTheory.AscFinNe.flat_ne_zero D ψ hψ V V₀ W W₀ ρ σ dV dW s x₀ y hli p hp⟩, hvac⟩
  intro Φ hΦ h hne
  refine hsupp h (GlobalTheory.T.unfoldingConditions_of_flatMap_weilAction_ne_zero D ψ V V₀ W W₀ ρ σ dV dW s x₀ y hli p hp Φ hΦ h hne) fun κ hκ =>
    GlobalTheory.T.unfoldingConditions_of_flatMap_weilAction_ne_zero D ψ V V₀ W W₀ ρ σ dV dW s x₀ y hli p hp Φ hΦ (h * κ) ?_
  have e : s.om (1, h * κ) Φ = s.om (1, h) Φ := by
    have : ((1 : GA D V), h * κ) = (1, h) * (1, κ) := by simp
    rw [this, map_mul, Module.End.mul_apply, hfix Φ (hvac Φ hΦ) κ hκ]
  rwa [e]

end GlobalTheory.AscFin.GoodStd

namespace GlobalTheory.AscFin.GoodStd

theorem std_good : GlobalTheory.SepRows.DepFixed → All fun {_} _ _ _ {G} W _ =>
    ∀ (v : CoreVol G) (F : GlobalTheory.Asc.Frames G), Std F → F.Good v W (lineLat F) := by
  intro hDF D hQ T L μ0 hL sc G W M hM v F hF
  have hψ : IsStdChar D W.ψ (-1) := W.ψ_std
  have cj := _root_.GlobalTheory.ConjDict.conj_dict hDF D hQ T L μ0 hL sc G W M hM
  have gl := _root_.GlobalTheory.PlaceLevelCosets.levCoset_of_places D hQ T L μ0 hL sc G W M hM
  have kv := _root_.GlobalTheory.LevelOffS.inK_mem_lev D hQ T L μ0 hL sc G W M hM
  have lt := _root_.GlobalTheory.LastSeeSaw.lastLat_std D hQ T L μ0 hL sc G W M hM F hF
  refine ⟨?_, ?_, lt.1, fun h => lt.2 v h⟩
  · intro ρ h s hs
    obtain ⟨hbase, -, hx, -⟩ := GlobalTheory.Unf.base_point D _ _ ρ (F.dJ ρ h)
    obtain ⟨hpIs, hspl⟩ := _root_.GlobalTheory.PcBF.pieces_bf D hQ T L μ0 hL sc G W M hM F hF ρ h
    have gd := _root_.GlobalTheory.GoodPosBF.goodPosition_offBadPlaces_from_besselLevel D hQ T L μ0 hL sc G W M hM F hF ρ h
    have g0 := gl (2 * ρ + 1) (by omega)
    have hsupp : ∀ g, Cond (F.dJ ρ h) (pcBF W F ρ h) (xZero (F.dJ ρ h)) (yBF F ρ h) W.ψ (fun _ => True) g →
        (∀ κ ∈ lev G (.grid (2 * ρ + 1) 0),
          Cond (F.dJ ρ h) (pcBF W F ρ h) (xZero (F.dJ ρ h)) (yBF F ρ h) W.ψ (fun _ => True) (g * κ)) →
        ∃ r ∈ Rgrp _ (xZero (F.dJ ρ h)), ∃ a ∈ GinfC _, ∃ k ∈ lev G (.grid (2 * ρ + 1) 0), g = r * a * k := by
      intro g hc hcK
      refine g0.2 (Rgrp _ (xZero (F.dJ ρ h))) g ?_ ?_
      · intro w hw h₁ hh₁ h₂ hh₂ e
        obtain ⟨g1, g2, g3⟩ := gd w hw
        refine _root_.GlobalTheory.OneCosetGood.oneCoset_good D W.ψ hψ _ _ _ _ ρ (F.dB ρ h) (F.dJ ρ h) (pcBF W F ρ h) (vecB (F.oB ρ h) (F.ζ (ρ + 1)))
          _ _ _ _ w g1 g2 g3 h₁ hh₁ ?_
        intro κ hκ
        have hκl : κ ∈ lev G (.grid (2 * ρ + 1) 0) := kv (2 * ρ + 1) (by omega) w hw κ hκ
        have hcomm : κ * h₂ = h₂ * κ := ((GlobalTheory.FinPl.localComponents D (· = w)).2 _).2.1 κ hκ.1 h₂ hh₂
        have e' : g * κ = (h₁ * κ) * h₂ := by rw [e, mul_assoc, ← hcomm, mul_assoc]
        have hc' := hcK κ hκl
        rw [e'] at hc'
        exact _root_.GlobalTheory.AscFin.cond_loc D W.ψ hψ _ _ _ _ ρ ρ (F.dB ρ h) (F.dJ ρ h) (pcBF W F ρ h) _ _ (· = w) (h₁ * κ) h₂
          (mul_mem hh₁ hκ.1) hh₂ hc'
      · intro h₁ hh₁ h₂ hh₂ e
        exact _root_.GlobalTheory.OneCosetBF.one_coset_bf D hQ T L μ0 hL sc G W M hM F hF ρ h h₁ hh₁
          (_root_.GlobalTheory.AscFin.cond_loc D W.ψ hψ _ _ _ _ ρ ρ (F.dB ρ h) (F.dJ ρ h) (pcBF W F ρ h) _ _ (fun v => v ∈ G.pl.S0) h₁ h₂ hh₁ hh₂
            (e ▸ hc))
    obtain ⟨hloc, hvac⟩ := loc_cls (F.dB ρ h) (F.dJ ρ h) s (xZero (F.dJ ρ h)) (F.dJ ρ h).e hx (yBF F ρ h) (pcBF W F ρ h)
      (latRow G (2 * ρ + 1)) (lev G (.grid (2 * ρ + 1) 0)) hψ hbase.1 hpIs hspl g0.1.1 g0.1.2.1 g0.1.2.2
      (fun f hf k hk => by rw [hs]; exact (cj (2 * ρ + 1) (by omega)).2.2.2.2.2.2 f hf k hk) hsupp
    exact ⟨_, _, hloc, hvac, _root_.GlobalTheory.AscFin.BoxBF.main D hQ T L μ0 hL sc G W M hM F hF ρ h⟩
  · intro σ h h' s hs
    obtain ⟨x₀, hli, hx⟩ := xLast_rat (F.dB σ h') (F.oB σ h') (F.ζ (σ + 1)) (F.line (σ + 1))
    obtain ⟨hpIs, hspl⟩ := _root_.GlobalTheory.AscFin.piecesFB_is_and_splits D hQ T L μ0 hL sc G W M hM F hF σ h h'
    have gd := _root_.GlobalTheory.AscFin.GoodFB.goodAt_stdAt_fb D hQ T L μ0 hL sc G W M hM F hF σ h h'
    have lat := (_root_.GlobalTheory.AscFin.GridLat.lattices_grid D hQ T L μ0 hL sc G W M hM F hF).2.1 σ h'
    have g0 := gl (2 * σ + 2) (by omega)
    have hsupp : ∀ g, Cond (F.dB σ h') (pcFB W F σ h h') (xFB F σ h') 0 W.ψ (fun _ => True) g →
        (∀ κ ∈ lev G (.grid (2 * σ + 2) 0), Cond (F.dB σ h') (pcFB W F σ h h') (xFB F σ h') 0 W.ψ (fun _ => True) (g * κ)) →
        ∃ r ∈ Rgrp _ (xFB F σ h'), ∃ a ∈ GinfC _, ∃ k ∈ lev G (.grid (2 * σ + 2) 0), g = r * a * k := by
      intro g hc _
      refine g0.2 (Rgrp _ (xFB F σ h')) g ?_ ?_
      · intro w hw h₁ hh₁ h₂ hh₂ e
        obtain ⟨g1, g2⟩ := gd w hw
        exact _root_.GlobalTheory.AscFin.OneCosetFJ.oneCoset_good D W.ψ hψ _ _ _ _ _ _ σ (F.dJ (σ + 1) h) (F.dB σ h') (F.oB σ h') (F.ζ (σ + 1)) (F.line (σ + 1))
          (pcFB W F σ h h') _ _ _ _ (G.Λ (.core (2 * σ + 2))) _ w g1 g2 (G.sp.P_is (2 * σ + 2) (by omega)).sd lat.2.2.1
          (lat.2.2.2 w) h₁ hh₁
          (_root_.GlobalTheory.AscFin.cond_loc D W.ψ hψ _ _ _ _ (σ + 1) σ (F.dJ (σ + 1) h) (F.dB σ h') (pcFB W F σ h h') _ _ (· = w) h₁ h₂ hh₁ hh₂
            (e ▸ hc))
      · intro h₁ hh₁ h₂ hh₂ e
        exact _root_.GlobalTheory.CosetFJ.one_coset_decomposition_base D hQ T L μ0 hL sc G W M hM F hF σ h h' h₁ hh₁
          (_root_.GlobalTheory.AscFin.cond_loc D W.ψ hψ _ _ _ _ (σ + 1) σ (F.dJ (σ + 1) h) (F.dB σ h') (pcFB W F σ h h') _ _ (fun v => v ∈ G.pl.S0)
            h₁ h₂ hh₁ hh₂ (e ▸ hc))
    obtain ⟨hloc, hvac⟩ := loc_cls (F.dJ (σ + 1) h) (F.dB σ h') s (xFB F σ h') x₀ hx 0 (pcFB W F σ h h')
      (latRow G (2 * σ + 2)) (lev G (.grid (2 * σ + 2) 0)) hψ hli hpIs hspl g0.1.1 g0.1.2.1 g0.1.2.2
      (fun f hf k hk => by rw [hs]; exact (cj (2 * σ + 2) (by omega)).2.2.2.2.2.2 f hf k hk) hsupp
    exact ⟨_, _, hloc, hvac, _root_.GlobalTheory.BoxFB.vacG_boxT_fb D hQ T L μ0 hL sc G W M hM F hF σ h h'⟩

end GlobalTheory.AscFin.GoodStd
