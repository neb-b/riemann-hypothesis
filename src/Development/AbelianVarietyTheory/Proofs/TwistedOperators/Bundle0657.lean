module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0648
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatTensorPureTensorEqProdContr
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitFrameOddLatticeRight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0276

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatDictionaryDoubleStepAtPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

namespace GlobalTheory.FlatPlace

theorem dblP_big : Big fun ch => ChrP ch → ArrP ch → LocP ch → BesP ch → JacP ch → DblP ch := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro hChr hArr hLoc hBes hJac
  intro t w hw p hp β r r₀ h hpts M hM φ v f hvf j hje hj
  have hstd : IsStdChar D ch.W.ψ (-1) := by rw [hch.weil.ψ]; exact s.std
  obtain ⟨hψ, hcond, -⟩ := hChr t w hw p hp
  have hm := D.R.m_even
  have hj' : j + 2 * ((D.R.m - 4 - j) / 2 + 1) + 2 = D.R.m := by
    obtain ⟨a, ha⟩ := hm; obtain ⟨b, hb⟩ := hje; omega
  have hj2 : j + 1 + 1 + 2 * ((D.R.m - 4 - j) / 2) + 2 = D.R.m := by omega
  have h0 : ¬ j + 2 * 0 + 2 = D.R.m := by omega
  have hL := hLoc t w hw p hp β r r₀ h hpts
  have t0 : topRank (locGrid ch.G t w) j + D.R.m = (locGrid ch.G t w).rank (D.R.m, j) + j + 1 :=
    topRank_add (G := locGrid ch.G t w) one_le_sLen j
  have t1 : topRank (locGrid ch.G t w) (j + 1) + D.R.m = (locGrid ch.G t w).rank (D.R.m, j + 1) + (j + 1) + 1 :=
    topRank_add (G := locGrid ch.G t w) one_le_sLen (j + 1)
  have t2 : topRank (locGrid ch.G t w) (j + 1 + 1) + D.R.m = (locGrid ch.G t w).rank (D.R.m, j + 1 + 1) + (j + 1 + 1) + 1 :=
    topRank_add (G := locGrid ch.G t w) one_le_sLen (j + 1 + 1)
  have hc0 : topRank (locGrid ch.G t w) j + (2 * ((D.R.m - 4 - j) / 2) + 1 + 1 + 1) = (locGrid ch.G t w).rank (D.R.m, j) := by
    omega
  have hc1 : topRank (locGrid ch.G t w) (j + 1) + (2 * ((D.R.m - 4 - j) / 2) + 1 + 1) =
      (locGrid ch.G t w).rank (D.R.m, j + 1) := by
    omega
  have hc2 : topRank (locGrid ch.G t w) (j + 1 + 1) + (2 * ((D.R.m - 4 - j) / 2) + 1) =
      (locGrid ch.G t w).rank (D.R.m, j + 1 + 1) := by
    omega
  have hodd : Odd (j + 1) := hje.add_one
  have hev2 : Even (j + 1 + 1) := hodd.add_one

  obtain ⟨T₁, hT₁, hO₁, Φ₁, hΦ₁, hTΦ₁⟩ := hArr t w hw p hp φ j (by omega) (v ⟨j, by omega⟩) (f ⟨j, by omega⟩)
    (hvf ⟨j, by omega⟩) (epsV ch.G t w) ((repsAt ch.G t w).elt β) (fun X => epsV_mem (G := ch.G) t w X)
    (h j * r₀ j) ((r₀ j)⁻¹ * r j) (h (j + 1) * r₀ (j + 1)) ((r₀ (j + 1))⁻¹ * r (j + 1))
    (hL j (by omega)).1 (hL (j + 1) (by omega)).1
    (Fin (topRank (locGrid ch.G t w) j) ⊕ Fin (2 * ((D.R.m - 4 - j) / 2) + 1 + 1 + 1))
    (Fin (topRank (locGrid ch.G t w) (j + 1)) ⊕ Fin (2 * ((D.R.m - 4 - j) / 2) + 1 + 1)) (frame hc0) (frame hc1)
  obtain ⟨T₂, hT₂, hO₂, Φ₂, hΦ₂, hTΦ₂⟩ := hArr t w hw p hp φ (j + 1) (by omega) (v ⟨j + 1, by omega⟩) (f ⟨j + 1, by omega⟩)
    (hvf ⟨j + 1, by omega⟩) (epsV ch.G t w) ((repsAt ch.G t w).elt β) (fun X => epsV_mem (G := ch.G) t w X)
    (h (j + 1) * r₀ (j + 1)) ((r₀ (j + 1))⁻¹ * r (j + 1)) (h (j + 1 + 1) * r₀ (j + 1 + 1))
    ((r₀ (j + 1 + 1))⁻¹ * r (j + 1 + 1))
    (hL (j + 1) (by omega)).1 (hL (j + 1 + 1) (by omega)).1
    (Fin (topRank (locGrid ch.G t w) (j + 1)) ⊕ Fin (2 * ((D.R.m - 4 - j) / 2) + 1 + 1))
    (Fin (topRank (locGrid ch.G t w) (j + 1 + 1)) ⊕ Fin (2 * ((D.R.m - 4 - j) / 2) + 1)) (frame hc1) (frame hc2)

  have hB0 := hBes t w hw p hp M hM j ((D.R.m - 4 - j) / 2 + 1) hj' (GlobalTheory.Unf.Inhab.nonempty_volN _).some
    (h j * r₀ j) ((hL j (by omega)).2.1 hje) _ hc0
  have hJ1 := hJac t w hw p hp M hM j ((D.R.m - 4 - j) / 2 + 1) hj' (GlobalTheory.Unf.Inhab.nonempty_volN _).some
    (h (j + 1) * r₀ (j + 1)) (Or.inr ((hL (j + 1) (by omega)).2.2 hodd)) _ hc1
  have hB2 := hBes t w hw p hp M hM (j + 1 + 1) ((D.R.m - 4 - j) / 2) hj2 (GlobalTheory.Unf.Inhab.nonempty_volN _).some
    (h (j + 1 + 1) * r₀ (j + 1 + 1)) ((hL (j + 1 + 1) (by omega)).2.1 hev2) _ hc2
  intro I S x Ξ₁ Ξ₂ c₁ c₂ hc
  have hxi := Witness.xi_ne p
  have es : (p.xi ^ ((D.R.m - 4 - j) / 2 + 1))⁻¹ * p.xi = (p.xi ^ ((D.R.m - 4 - j) / 2))⁻¹ := by
    rw [pow_succ, mul_inv, mul_assoc, inv_mul_cancel₀ hxi, mul_one]
  let Fd : GlobalTheory.LocMod.Dbl p (besAt ch.G hM j ((D.R.m - 4 - j) / 2 + 1) hj' (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
      (jacAt ch.G hM (j + 1) ((D.R.m - 4 - j) / 2 + 1) (by omega))
      (besAt ch.G hM (j + 1 + 1) ((D.R.m - 4 - j) / 2) hj2 (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
      (Fin (topRank (locGrid ch.G t w) j)) (Fin (topRank (locGrid ch.G t w) (j + 1)))
      (Fin (topRank (locGrid ch.G t w) (j + 1 + 1))) (2 * ((D.R.m - 4 - j) / 2)) :=
    ⟨_, inv_ne_zero (pow_ne_zero _ hxi), _, _, _, _, _, _, hB0, hJ1, es ▸ hB2⟩

  obtain ⟨O₁, hOne₁, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := Kw w)
    (Y := Fin (topRank (locGrid ch.G t w) (j + 1)) ⊕ Fin (2 * ((D.R.m - 4 - j) / 2) + 1 + 1))
    (Y' := Fin (topRank (locGrid ch.G t w) j) ⊕ Fin (2 * ((D.R.m - 4 - j) / 2) + 1 + 1 + 1))
  obtain ⟨O₂, hOne₂, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := Kw w)
    (Y := Fin (topRank (locGrid ch.G t w) (j + 1 + 1)) ⊕ Fin (2 * ((D.R.m - 4 - j) / 2) + 1))
    (Y' := Fin (topRank (locGrid ch.G t w) (j + 1)) ⊕ Fin (2 * ((D.R.m - 4 - j) / 2) + 1 + 1))
  have hv1 : ch.W.om (.mu t D.R.m j) ((h * r₀) j, (h * r₀) (j + 1)) (v ⟨j, by omega⟩) = T₁ O₁ := (hO₁ O₁ hOne₁).symm
  have hv2 : ch.W.om (.mu t D.R.m (j + 1)) ((h * r₀) (j + 1), (h * r₀) (j + 1 + 1)) (v ⟨j + 1, by omega⟩) = T₂ O₂ :=
    (hO₂ O₂ hOne₂).symm
  have hf1 : ch.W.om (.mu t D.R.m j) ((h * r) j, (h * r) (j + 1)) (f ⟨j, by omega⟩) = T₁ Φ₁ := by
    rw [hTΦ₁]; simp only [Pi.mul_apply, mul_assoc, mul_inv_cancel_left]
  have hf2 : ch.W.om (.mu t D.R.m (j + 1)) ((h * r) (j + 1), (h * r) (j + 1 + 1)) (f ⟨j + 1, by omega⟩) = T₂ Φ₂ := by
    rw [hTΦ₂]; simp only [Pi.mul_apply, mul_assoc, mul_inv_cancel_left]
  have E : ∀ (Φ : SchDown ch.G t) (g : Pts ch.G), conAt ch.W hM Φ g j =
      GlobalTheory.Unf.contr (linkAt hM j _ hj' (GlobalTheory.Unf.Inhab.nonempty_volN _).some (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
        (ch.G.V (.top (j + 1))) ((GlobalTheory.Unf.Inhab.nonempty_volM D _ _).some)
        (GlobalTheory.Unf.flatBF (B := besAt ch.G hM j _ hj' (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
          (J := jacAt ch.G hM (j + 1) ((D.R.m - 4 - j) / 2 + 1) (by omega))
          (stepAt ch.G ch.W t hM j (by omega) (besDecAt ch.G j _ hj')
            (rowJac ch.G (j + 1) (by omega) ((D.R.m - 4 - j) / 2 + 1) (by omega)))
          (ch.W.om (.mu t D.R.m j) (g j, g (j + 1)) (Φ ⟨j, by omega⟩)))
        (GlobalTheory.Unf.flatFB (J := jacAt ch.G hM (j + 1) ((D.R.m - 4 - j) / 2 + 1) (by omega))
          (B := besAt ch.G hM (j + 1 + 1) ((D.R.m - 4 - j) / 2) (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
          (stepAt ch.G ch.W t hM (j + 1) (by omega) (rowJac ch.G (j + 1) (by omega) ((D.R.m - 4 - j) / 2 + 1) (by omega))
            (besDecAt ch.G (j + 1 + 1) ((D.R.m - 4 - j) / 2) (by omega)))
          (ch.W.om (.mu t D.R.m (j + 1)) (g (j + 1), g (j + 1 + 1)) (Φ ⟨j + 1, by omega⟩))) := by
    intro Φ g
    unfold conAt
    rw [dite_eq_right h0]
    exact dif_pos hj'
  rw [E v (h * r₀), E f (h * r)]
  rw [hv1, hv2, hf1, hf2]
  have hz : ∀ (S' : Finset I), (∀ q₁ q₂, ∑ i ∈ S', x i * ((Ξ₁ i).1 q₁ * (Ξ₂ i).1 q₂) = 0) → ∀ q,
      GlobalTheory.LocFlat.contr (psiAt ch.W w) (unitVol w) (GlobalTheory.LocFlat.flCol (psiAt ch.W w) (unitVol w) ((D.R.m - 4 - j) / 2 + 1 + 1)
        (0 : SB (Matrix (Fin (topRank (locGrid ch.G t w) (j + 1)) ⊕ Fin (2 * ((D.R.m - 4 - j) / 2) + 1 + 1))
          (Fin (topRank (locGrid ch.G t w) j) ⊕ Fin (2 * ((D.R.m - 4 - j) / 2) + 1 + 1 + 1)) (Kw w))).1)
        (GlobalTheory.LocFlat.flRow (psiAt ch.W w) (unitVol w) ((D.R.m - 4 - j) / 2 + 1) Φ₂.1) q =
        ∑ i ∈ S', x i * ((Ξ₁ i).1 q.1 * (Ξ₂ i).1 q.2) := by
    intro S' hS' q
    rw [hS' q.1 q.2]
    simp [GlobalTheory.LocFlat.contr, GlobalTheory.LocFlat.flCol, GlobalTheory.RootEx.opE, GlobalTheory.StepData.hat]
  refine ⟨fun hvan => ?_, fun hq => ?_⟩
  · refine Eq.trans (_root_.GlobalTheory.DblStepLoc.contr_flat_expand D (Kw w) (unitVol w) (isUnitVol_unitVol w) p ch.W.ψ hstd (psiAt ch.W w) hψ hcond
      ((D.R.m - 4 - j) / 2) _ _ _ _ _ _ _ Fd _ _ _ _ T₁ T₂ hT₁ hT₂ 0 Φ₂ O₁ O₂ hOne₁ hOne₂ I S x Ξ₁ Ξ₂ c₁ c₂ hc (hz S hvan)).symm ?_
    exact (_root_.GlobalTheory.DblStepLoc.contr_flat_expand D (Kw w) (unitVol w) (isUnitVol_unitVol w) p ch.W.ψ hstd (psiAt ch.W w) hψ hcond ((D.R.m - 4 - j) / 2)
      _ _ _ _ _ _ _ Fd _ _ _ _ T₁ T₂ hT₁ hT₂ 0 Φ₂ O₁ O₂ hOne₁ hOne₂ I ∅ x Ξ₁ Ξ₂ c₁ c₂ (by simp)
      (hz ∅ fun _ _ => Finset.sum_empty)).trans Finset.sum_empty
  · have hloc : ∀ q, GlobalTheory.LocFlat.contr (psiAt ch.W w) (unitVol w)
        (GlobalTheory.LocFlat.flCol (psiAt ch.W w) (unitVol w) ((D.R.m - 4 - j) / 2 + 1 + 1) Φ₁.1)
        (GlobalTheory.LocFlat.flRow (psiAt ch.W w) (unitVol w) ((D.R.m - 4 - j) / 2 + 1) Φ₂.1) q =
        ∑ i ∈ S, x i * ((Ξ₁ i).1 q.1 * (Ξ₂ i).1 q.2) := by
      intro q
      rw [← hq q, show Φ₁.1 = _ from funext hΦ₁, show Φ₂.1 = _ from funext hΦ₂]
      unfold facAt locA
      rw [dite_eq_right (show ¬ j + 2 * 0 + 2 = (locGrid ch.G t w).m from h0),
        dif_pos (show j + 2 * (((locGrid ch.G t w).m - 4 - j) / 2 + 1) + 2 = (locGrid ch.G t w).m from hj')]
      rfl
    exact _root_.GlobalTheory.DblStepLoc.contr_flat_expand D (Kw w) (unitVol w) (isUnitVol_unitVol w) p ch.W.ψ hstd (psiAt ch.W w) hψ hcond ((D.R.m - 4 - j) / 2)
      _ _ _ _ _ _ _ Fd _ _ _ _ T₁ T₂ hT₁ hT₂ Φ₁ Φ₂ O₁ O₂ hOne₁ hOne₂ I S x Ξ₁ Ξ₂ c₁ c₂ hc hloc

end GlobalTheory.FlatPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatDictionaryScalarLargeDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

namespace GlobalTheory.FlatScal

noncomputable section

open GlobalTheory.LocMod (Place Frame IsOne)
open GlobalTheory.SplitWeil (SB)
open GlobalTheory.SplitFlip (Grid Edge oppositePath gdet)
open GlobalTheory.FlatPlace

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def xiEdge (ξ : kˣ →* ℂˣ) : Edge → kˣ →* ℂˣ
  | .theta _ _ => ξ
  | .ex _ _ => 1

theorem kappa_split (Γ : Grid k) (μ₀ : ℕ → kˣ →* ℂˣ) (ξ : kˣ →* ℂˣ) (h : ∀ j, Γ.mu j = μ₀ j * ξ) (b : Edge) (X : ℕ × ℕ) :
    Γ.kappa b X = ({Γ with mu := μ₀} : Grid k).kappa b X * xiEdge ξ b := by
  cases b with
  | theta i j =>
    show Γ.mu (j + 1) / Γ.eta ^ ((Γ.rank X + 1) % 2) = μ₀ (j + 1) / Γ.eta ^ ((Γ.rank X + 1) % 2) * ξ
    rw [h, mul_div_right_comm]
  | ex i j =>
    show Γ.chi (Γ.m - i) / Γ.eta ^ ((Γ.rank X + 1) % 2) = Γ.chi (Γ.m - i) / Γ.eta ^ ((Γ.rank X + 1) % 2) * 1
    rw [mul_one]

def xiPart (Γ : Grid k) (ξ : kˣ →* ℂˣ) (g : Γ.VertexGroup) : ℂˣ :=
  ((oppositePath Γ.m).map fun b => xiEdge ξ b (gdet (g b.src)) * (xiEdge ξ b (gdet (g b.tgt)))⁻¹).prod

theorem charFactor_split (Γ : Grid k) (μ₀ : ℕ → kˣ →* ℂˣ) (ξ : kˣ →* ℂˣ) (h : ∀ j, Γ.mu j = μ₀ j * ξ)
    (g : Γ.VertexGroup) :
    charFactor Γ g = charFactor ({Γ with mu := μ₀} : Grid k) g * xiPart Γ ξ g := by
  simp only [charFactor, xiPart, kappa_split Γ μ₀ ξ h, ← List.prod_map_mul]
  refine congrArg List.prod (List.map_congr_left fun b _ => ?_)
  simp only [MonoidHom.mul_apply, mul_inv]
  exact mul_mul_mul_comm _ _ _ _

theorem xiPart_mem (Γ : Grid k) (ξ : kˣ →* ℂˣ) (g : Γ.VertexGroup) (H : Subgroup ℂˣ) (hH : ∀ x, ξ x ∈ H) :
    xiPart Γ ξ g ∈ H := by
  refine H.list_prod_mem fun x hx => ?_
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 hx
  have e : ∀ u, xiEdge ξ b u ∈ H := fun u => by
    cases b with
    | theta _ _ => exact hH u
    | ex _ _ => exact H.one_mem
  exact H.mul_mem (e _) (H.inv_mem (e _))

theorem prod_edgeFactor (Γ : Grid k) (ε : Γ.VertexGroup) (hε : ∀ X, ε X ∈ GlobalTheory.SplitWeil.KO k _) :
    ((oppositePath Γ.m).map (Γ.edgeFactor .one ε)).prod = ((charFactor Γ ε : ℂˣ) : ℂ) := by
  rw [charFactor, ← Units.coeHom_apply, map_list_prod, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun b _ => ?_)
  have ha : ∀ X (z : ℂ), GlobalTheory.SplitFlip.apow (gdet (GlobalTheory.SplitFlip.Assignment.one.read (ε X))) z = 1 := fun X z => by
    refine GlobalTheory.SplitFlip.apow_of_valuation_eq_one ?_ z
    rw [show GlobalTheory.SplitFlip.Assignment.one.read (ε X) = GlobalTheory.SplitFlip.invT (ε X) from rfl, GlobalTheory.SplitFlip.gdet_invT,
      Units.val_inv_eq_inv_val, map_inv₀, GlobalTheory.SplitFlip.valuation_gdet_of_mem_KO (hε X), inv_one]
  simp only [Grid.edgeFactor, ha, mul_one, Function.comp, Units.coeHom_apply, Units.val_mul]

theorem charFactor_eq_one (Γ : Grid k) (ε : Γ.VertexGroup) (hε : ∀ X, ε X ∈ GlobalTheory.SplitWeil.KO k _)
    (hrow : ∀ i < Γ.m, ε (i, Γ.m) = 1 ∧ ε (i + 1, Γ.m) = 1)
    (hμ : ∀ j < Γ.m, IsUnram (Γ.mu (j + 1))) (hη : IsUnram Γ.eta) : charFactor Γ ε = 1 := by
  refine List.prod_eq_one fun x hx => ?_
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hx
  simp only [oppositePath, List.mem_append, List.mem_map, List.mem_range, List.mem_reverse] at hb
  rcases hb with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
  · show Γ.kappa _ (i, Γ.m) (gdet (ε (i, Γ.m))) * (Γ.kappa _ (i + 1, Γ.m) (gdet (ε (i + 1, Γ.m))))⁻¹ = 1
    have g1 : ∀ n, gdet (1 : GL (Fin n) k) = 1 := fun _ => map_one _
    rw [(hrow i hi).1, (hrow i hi).2, g1, g1, map_one, map_one, inv_one, mul_one]
  · have hu : ∀ X, Γ.kappa (.theta Γ.m j) X (gdet (ε X)) = 1 := fun X => by
      have hv := GlobalTheory.SplitFlip.valuation_gdet_of_mem_KO (hε X)
      show (Γ.mu (j + 1) / Γ.eta ^ ((Γ.rank X + 1) % 2)) (gdet (ε X)) = 1
      rw [MonoidHom.div_apply, MonoidHom.pow_apply, hμ j hj _ hv, hη _ hv, one_pow, div_one]
    show Γ.kappa _ _ (gdet (ε _)) * (Γ.kappa _ _ (gdet (ε _)))⁻¹ = 1
    rw [hu, hu, inv_one, mul_one]

end Local

section Grid0

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}


variable (G : GridData L sc) in
def grid0 (w : Pl D.host.E) : Grid (Kw w) where
  m := D.R.m
  r := D.R.r
  t := D.R.t
  s := sLen D
  mu j := (muBase L j).loc w
  chi i := (G.ch.chiH i).loc w
  eta := L.C.eta.loc w


open Classical in
def eps0 (G : GridData L sc) (w : Pl D.host.E) : (grid0 G w).VertexGroup :=
  onColumn (G := grid0 G w) fun j => if j ∈ idx D then GlobalTheory.SplitFlip.diagGL fun a =>
    if Odd j ∧ topRank (grid0 G w) j + (D.R.m - 1 - j) / 2 ≤ a.1 then Units.map (Int.castRingHom (Kw w)).toMonoidHom (-1) else 1
    else 1


variable (G : GridData L sc) in
def stair0 (w : Pl D.host.E) : (grid0 G w).VertexGroup :=
  onColumn (G := grid0 G w) fun j => if j + 2 ≤ D.R.m then stair (grid0 G w) (unifAt w) (cosExp G w) j else 1

theorem elt_stair (G : GridData L sc) (t : T) (w : Pl D.host.E)
    (β : Cosets (G := locGrid G t w) one_le_sLen (givenLevel G t w))
    (hβ : ∀ i, β i = DoubleCoset.mk _ _ (stair (locGrid G t w) (unifAt w) (cosExp G w) (i + 1))) :
    (repsAt G t w).elt β = (stair0 G w : (locGrid G t w).VertexGroup) := by
  have hb : β = fun i : Fin _ => DoubleCoset.mk _ _ (stair (locGrid G t w) (unifAt w) (cosExp G w) (i.1 + 1)) := funext hβ
  subst hb
  funext X
  obtain ⟨i, j⟩ := X
  by_cases hi : i = D.R.m
  · subst hi
    have e1 : (stair0 G w : (locGrid G t w).VertexGroup) (D.R.m, j) =
        if j + 2 ≤ D.R.m then stair (locGrid G t w) (unifAt w) (cosExp G w) j else 1 := onColumn_apply (G := grid0 G w) _ j
    rw [e1]
    split_ifs with hj
    · exact through_elt _ hj
    · exact elt_eq_one t w _ (by omega)
  · show onColumn (G := locGrid G t w) _ (i, j) = onColumn (G := grid0 G w) _ (i, j)
    rw [onColumn, onColumn, dite_eq_right (show ¬ (i, j).1 = (locGrid G t w).m from hi),
      dite_eq_right (show ¬ (i, j).1 = (grid0 G w).m from hi)]
    rfl

end Grid0


open Classical in
theorem scal : Big fun ch => ScalP ch := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  refine ⟨fun w => if w ∈ ch.G.pl.W0 then
      ((charFactor (grid0 ch.G w) (eps0 ch.G w) * charFactor (grid0 ch.G w) (stair0 ch.G w) : ℂˣ) : ℂ) else 1,
    fun t w => (xiPart (locGrid ch.G t w) ((R.toLevCh.xiH t).loc w) (epsV ch.G t w) *
      if w ∈ ch.G.pl.W0 then xiPart (locGrid ch.G t w) ((R.toLevCh.xiH t).loc w) (stair0 ch.G w) else 1)⁻¹,
    fun t w => ?_, fun w hw => if_neg hw, fun t w hw β hβ => ?_⟩
  · have hH : ∀ x, (R.toLevCh.xiH t).loc w x ∈ xiVals R.toLevCh t := fun x => Subgroup.subset_closure ⟨w, x, rfl⟩
    refine inv_mem (mul_mem (xiPart_mem _ _ _ _ hH) ?_)
    split_ifs
    · exact xiPart_mem _ _ _ _ hH
    · exact one_mem _
  · have hmu : ∀ j, (locGrid ch.G t w).mu j = (fun j => (muBase R.toLevCh j).loc w) j * (R.toLevCh.xiH t).loc w :=
      fun j => MonoidHom.ext fun _ => rfl
    have hsplit := charFactor_split (locGrid ch.G t w) _ _ hmu
    dsimp only
    unfold zetaLoc
    rw [prod_edgeFactor _ _ (epsV_mem t w)]
    by_cases h0 : w ∈ ch.G.pl.W0
    · have hk : keepAt ch.G w = false := by simp [keepAt, h0]
      rw [hk, if_pos h0, if_pos h0, elt_stair ch.G t w β (hβ h0)]
      have key : charFactor (locGrid ch.G t w) (epsV ch.G t w) * charFactor (locGrid ch.G t w) (stair0 ch.G w) =
          (charFactor (grid0 ch.G w) (eps0 ch.G w) * charFactor (grid0 ch.G w) (stair0 ch.G w)) *
          ((xiPart (locGrid ch.G t w) ((R.toLevCh.xiH t).loc w) (epsV ch.G t w) *
            xiPart (locGrid ch.G t w) ((R.toLevCh.xiH t).loc w) (stair0 ch.G w))⁻¹)⁻¹ := by
        rw [inv_inv, hsplit (epsV ch.G t w), hsplit (stair0 ch.G w)]
        exact mul_mul_mul_comm _ _ _ _
      simp only [Bool.false_eq_true, if_false]
      rw [← Units.val_inv_eq_inv_val, ← Units.val_mul, ← Units.val_mul]
      exact congrArg Units.val key
    · have hk : keepAt ch.G w = true := by simp [keepAt, h0]
      rw [hk, if_neg h0, if_neg h0, if_pos rfl]
      have ha : w.under (𝓞 D.host.F) ∉ ch.G.pl.S0 := by
        rcases GlobalTheory.FunObj.Good.locPl_cases hw with ⟨a, b⟩ | ⟨a, -, -⟩
        · exact absurd (by rw [b]; exact Finset.mem_image_of_mem ch.G.pl.w a) h0
        · exact a
      have hoff : ∀ i j, i ≠ D.R.m → epsV ch.G t w (i, j) = 1 := fun i j hi => by
        show onColumn (G := locGrid ch.G t w) _ (i, j) = 1
        rw [onColumn, dite_eq_right (show ¬ (i, j).1 = (locGrid ch.G t w).m from hi)]
      have h1 : charFactor ({locGrid ch.G t w with mu := fun j => (muBase R.toLevCh j).loc w} : Grid (Kw w))
          (epsV ch.G t w) = 1 := by
        refine charFactor_eq_one _ _ (epsV_mem t w) (fun i hi => ⟨hoff i _ (Nat.ne_of_lt hi), ?_⟩) (fun j hj => ?_) ?_
        · by_cases e : i + 1 = D.R.m
          · show epsV ch.G t w (i + 1, D.R.m) = 1
            rw [show (i + 1, D.R.m) = (D.R.m, D.R.m) by rw [e]]
            exact epsV_eq_one t w (by omega)
          · exact hoff _ _ e
        · replace hj : j < D.R.m := hj
          show IsUnram ((muBase R.toLevCh (j + 1)).loc w)
          rw [muBase, dite_eq_left hj]
          refine GlobalTheory.FunObj.Good.isUnram_loc.2 ((R.toLevCh.C.isMu0 ⟨j, hj⟩).unr w fun k hk => ?_)
          refine ha (ch.G.pl.mem_S0_of_sum_eq.2 (Or.inr ((GlobalTheory.ChiGrid.S1_mem_OmF D).2 ?_)))
          have : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (w.under (𝓞 D.host.F)).asIdeal := by
            show algebraMap _ (𝓞 D.host.E) _ ∈ w.asIdeal
            rw [map_natCast]; exact hk
          fin_cases k
          · exact Or.inl this
          · exact Or.inr (Or.inl this)
        · exact GlobalTheory.FunObj.Good.isUnram_loc.2 (R.toLevCh.C.isEta.unr w)
      simp only [hsplit (epsV ch.G t w), h1, one_mul, mul_one, Units.val_inv_eq_inv_val, inv_inv]

end

end GlobalTheory.FlatScal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatTensorPureTensorEqProdLocalFactors
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

namespace GlobalTheory.FlatPlace

open GlobalTheory.SplitFlip (Grid Edge)

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]

theorem flCol_datC_congr (ψ : AddChar k Circle) (ν : Measure k) {a b N N' : ℕ} (Φ : Matrix (Fin N) (Fin N') k → ℂ)
    {c₁ c₂ p₁ p₂ : ℕ} (hc : c₁ = c₂) (hp : p₁ = p₂) (h₁ : a + c₁ = N') (h₁' : b + (c₁ + 1) = N) (h₂ : a + c₂ = N')
    (h₂' : b + (c₂ + 1) = N) :
    GlobalTheory.LocFlat.flCol ψ ν p₁ (datC h₁ h₁' Φ) = GlobalTheory.LocFlat.flCol ψ ν p₂ (datC h₂ h₂' Φ) := by
  subst hc hp; rfl

theorem flRow_datC_congr (ψ : AddChar k Circle) (ν : Measure k) {a b N N' : ℕ} (Φ : Matrix (Fin N) (Fin N') k → ℂ)
    {c₁ c₂ p₁ p₂ : ℕ} (hc : c₁ = c₂) (hp : p₁ = p₂) (h₁ : a + c₁ = N') (h₁' : b + (c₁ + 1) = N) (h₂ : a + c₂ = N')
    (h₂' : b + (c₂ + 1) = N) :
    GlobalTheory.LocFlat.flRow ψ ν p₁ (datC h₁ h₁' Φ) = GlobalTheory.LocFlat.flRow ψ ν p₂ (datC h₂ h₂' Φ) := by
  subst hc hp; rfl

theorem stepDatum_eq_datC (G : Grid k) (hs : 1 ≤ G.s) (φ : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ)
    (j : Fin (G.m - 1)) :
    stepDatum hs φ j = datC (c := G.m - 2 - j) (c' := G.m - 2 - j + 1)
      (by have := topRank_add hs (j + 1); have := j.2; show _ = G.rank (G.m, j + 1); omega)
      (by have := topRank_add hs j; have := j.2; show _ = G.rank (G.m, j); omega) (φ (.theta G.m j)) := rfl

theorem theta_sub_congr (G : Grid k) (φ : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ) (x : ColArgs G)
    {i i' : ℕ} (h : i = i') (p₁ : G.rank (G.m, i + 1) ≤ topRank G (i + 1)) (p₂ : G.rank (G.m, i) = topRank G i)
    (p₃ : G.rank (G.m, i' + 1) ≤ topRank G (i' + 1)) (p₄ : G.rank (G.m, i') = topRank G i') :
    φ (.theta G.m i) ((x i).submatrix (Fin.castLE p₁) (Fin.cast p₂))ᵀ =
      φ (.theta G.m i') ((x i').submatrix (Fin.castLE p₃) (Fin.cast p₄))ᵀ := by
  subst h; rfl

theorem prod_fin_even (n : ℕ) (g : ℕ → ℂ) :
    (∏ j ∈ Finset.range (2 * n), if Even j then g j else 1) = ∏ i ∈ Finset.range n, g (2 * i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.prod_range_succ, Finset.prod_range_succ, ih,
      Finset.prod_range_succ, if_pos (even_two_mul n), if_neg (by rw [Nat.not_even_iff_odd]; exact odd_two_mul_add_one n), mul_one]

theorem locA_last (G : Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k)
    (φ : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ) (x : ColArgs G) (j : ℕ) (hj : j + 2 = G.m) :
    locA G hs ψ ν φ j (x j, x (j + 1)) =
      φ (.theta G.m (G.m - 1)) (lastMap hs (by omega) x)ᵀ * GlobalTheory.StepData.hat ψ ν (-1) (fun u =>
        GlobalTheory.LocFlat.flCol ψ ν 1 (stepDatum hs φ ⟨G.m - 2, by omega⟩) (fromCols (x (G.m - 2)) (Matrix.of fun r _ => u r)))
        (x (G.m - 2 + 1) (topLast G (G.m - 2 + 1 + 1))) := by
  obtain rfl : j = G.m - 2 := by omega
  rw [locA, dite_eq_left (by omega), stepDatum_eq_datC]
  refine congrArg₂ (· * ·) ?_ ?_
  · exact theta_sub_congr G φ x (by omega) _ _ _ _
  · congr 1
    funext u
    exact congrFun (flCol_datC_congr ψ ν _ (by simp) rfl _ _ _ _) _

theorem locA_double (G : Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k)
    (φ : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ) (hm : Even G.m) (j : ℕ) (he : Even j)
    (hj : j < G.m - 2) (q) :
    locA G hs ψ ν φ j q =
      GlobalTheory.LocFlat.contr ψ ν (GlobalTheory.LocFlat.flCol ψ ν ((G.m - 2 - j) / 2 + 1) (stepDatum hs φ ⟨j, by omega⟩))
        (GlobalTheory.LocFlat.flRow ψ ν ((G.m - 2 - (j + 1)) / 2 + 1) (stepDatum hs φ ⟨j + 1, by omega⟩)) q := by
  obtain ⟨a, ha⟩ := he
  obtain ⟨b, hb⟩ := hm
  rw [locA, dite_eq_right (by omega), dite_eq_left (by omega), stepDatum_eq_datC, stepDatum_eq_datC]
  exact congrArg₂ (fun A B => GlobalTheory.LocFlat.contr ψ ν A B q)
    (flCol_datC_congr ψ ν _ (by simp only; omega) (by omega) _ _ _ _)
    (flRow_datC_congr ψ ν _ (by simp only; omega) (by omega) _ _ _ _)

end

theorem flatTensor_pureTensor_eq_prod_locA : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (G : GlobalTheory.SplitFlip.Grid k) (hs : 1 ≤ G.s), 2 ≤ G.m → Even G.m → ∀ (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (φ : ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ), (∀ j < G.m - 1, φ (.theta G.m j) ∈ SB _) → ∀ (x : ColArgs G) (y : RowArgs G), flatTensor hs ψ ν (G.lines₂ (GlobalTheory.SplitFlip.oppositePath G.m) φ) x y = (∏ i ∈ Finset.range G.m, φ (.ex i G.m) (y i)ᵀ) * ∏ n ∈ Finset.range (G.m / 2), locA G hs ψ ν φ (2 * n) (x (2 * n), x (2 * n + 1)) := by
  intro k _ _ _ _ _ _ G hs hm hme ψ ν hψ hψ1 hν φ hφ x y
  rw [GlobalTheory.FunObj.flatTensor_pureTensor_eq_prod_contr k G hs hm hme ψ ν hψ hψ1 hν φ hφ x y, mul_assoc]
  congr 1
  obtain ⟨n, hn⟩ : ∃ n, G.m = 2 * n + 2 := by obtain ⟨b, hb⟩ := hme; exact ⟨b - 1, by omega⟩
  have hr : G.m / 2 = n + 1 := by omega
  rw [hr, Finset.prod_range_succ, mul_comm, locA_last G hs ψ ν φ x (2 * n) (by omega)]
  congr 1
  have h2 : G.m - 2 = 2 * n := by omega
  rw [← prod_fin_even n (fun j => locA G hs ψ ν φ j (x j, x (j + 1)))]
  rw [← Fin.prod_univ_eq_prod_range (fun j => if Even j then locA G hs ψ ν φ j (x j, x (j + 1)) else 1) (2 * n)]
  rw [← h2]
  refine Finset.prod_congr rfl fun j _ => if_ctx_congr Iff.rfl (fun hj => ?_) fun _ => rfl
  exact (locA_double G hs ψ ν φ ⟨n + 1, by omega⟩ j hj j.2 _).symm

end GlobalTheory.FlatPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitFrameOddLatticeRightStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_frame_odd_lattice_right : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0, ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : GlobalTheory.FinPl.SplitPt D k) (β : GlobalTheory.FinPl.Frame p (G.V (.grid (2 * (σ + 1) + 1) 0)) (Fin (G.V (.grid (2 * (σ + 1) + 1) 0)).rank)) (ϖ : 𝒪[k])
    (κ : Fin (2 * (σ + 1) + 1 - 1) → Fin (G.V (.grid (2 * (σ + 1) + 1) 0)).rank),
  p.v = v →
  Formalism.L2.NTheta.IsIdemAt p.e (G.pl.w v) →
  β.IsLat (G.Λ (.grid (2 * (σ + 1) + 1) 0)) (Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k)) →
  Irreducible ϖ →
  Function.Injective κ →
  (∀ r i, β.b i (κ r) = (ϖ : k) ^ (G.pl.depth sc v * (r.1 + 1)) * p.pr (incA D ((G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a i r))) →
  (∀ j, j ∉ Set.range κ → ∀ r, ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a * (G.V (.grid (2 * (σ + 1) + 1) 0)).gram).map
      (fun c => p.pr (incA D c)) * β.b) r j = 0) →
  ∀ t : Fin (σ + 1) → k, (∀ q, t q • ((fun i => p.pr (cA D (xZero (F.dJ (σ + 1) h) i q))) ᵥ*
    ((G.V (.grid (2 * (σ + 1) + 1) 0)).gram.map (fun c => p.pr (incA D c)) * β.b)) = Pi.single (κ ⟨2 * (σ + 1) - 1 - q.1, by omega⟩) 1) →
  ∀ a ∈ (pcBF W F (σ + 1) h).A₁, ∀ q i, ∃ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ G.pl.depth sc v,
    (z : k) = t q * ((fun j => p.pr (cA D (a j q))) ᵥ*
      ((G.V (.grid (2 * (σ + 1) + 1) 0)).gram.map (fun c => p.pr (incA D c)) * β.b)) i := by
  first | exact @GlobalTheory.AscFin.FrameBarBF.bessel_step_conj_place_column_functional_bound | exact GlobalTheory.AscFin.FrameBarBF.bessel_step_conj_place_column_functional_bound | (intros; apply GlobalTheory.AscFin.FrameBarBF.bessel_step_conj_place_column_functional_bound <;> assumption)
end

