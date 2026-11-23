module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0013
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle0007

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsDecK
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped Topology
open UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Lit.Geo.Cs.decK :
    UpperTheory.V.Lit.Geo.Cs.DecK := by
  intro E _ _ _ a ho U Ξ f Y C c f₀ hS W hW lam hl q k A B hA hB
  obtain ⟨hfl, hflow⟩ := fieldFlow E a ho U Ξ Y C hS.fld W hW
  obtain ⟨z, hz⟩ := zwSz E a U Y C hS.fld W hW (k + 1)
  obtain ⟨C₁, hC₁, hhom⟩ := homSz (HV E a) (Fin Ξ.d → ℂ) q k z
  obtain ⟨D₁, hD₁, hmv⟩ := move E a ho U Ξ (q + 1) k C
  obtain ⟨L, hL⟩ := hl.bdd C
  refine ⟨C₁ * D₁ * Real.exp (B * L + A * C), by positivity, fun M hM w hw g x hg => ?_⟩
  obtain ⟨hfield, hfz, hq⟩ := twOps E a ho U Ξ W hfl g x
  have hsm := ((hq (q + 1)).1 w).1
  have heq := (hq q).2 w
  have key : ∀ t ∈ Set.Icc (0 : ℝ) 1, Sz k (Tw U Ξ w.1 g x) (flow (Zw U W g x) t (hOne E a))
      (D₁ * (M * (Real.exp (B * L + A * C) * Real.exp (B * |lam (pt g x)| - A * f (pt g x))))) := by
    intro t ht
    have ht' : |t| ≤ 1 := abs_le.2 ⟨by linarith [ht.1], ht.2⟩
    obtain ⟨h, hh, h1, h2⟩ := hS.root (pt g x) t ht'
    have hn := abs_le.1 (hS.near (pt g x) t h ht' hh)
    have e : flow (Zw U W g x) t (hOne E a) = sand h (hOne E a) := by
      rw [hfz, hflow g h x t hh, ← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel_left]
    rw [e]
    refine hmv w g x h _ ⟨h1, h2⟩ ((hw (g * h) x (by rw [pt_mul]; linarith [hn.1])).mono ?_)
    refine mul_le_mul_of_nonneg_left ?_ hM
    rw [← Real.exp_add, pt_mul, hl.add]
    refine Real.exp_le_exp.2 ?_
    have b1 : |lam (pt g x) + lam (infGL E a h)| ≤ L + |lam (pt g x)| := by
      linarith [abs_add_le (lam (pt g x)) (lam (infGL E a h)), hL h ⟨h1, h2⟩]
    have b2 := mul_le_mul_of_nonneg_left b1 hB
    have b3 := mul_le_mul_of_nonneg_left hn.1 hA
    linarith
  have main := hhom (cone E a) (Zw U W g x) (Tw U Ξ w.1 g x) _ ho hfield hsm (hOne E a) hOne_mem_cone (hz g x) key
  refine (main.congr ?_).mono (le_of_eq (by ring))
  filter_upwards [ho.mem_nhds hOne_mem_cone] with p hp
  exact (heq p hp).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsDecP
section
open UpperTheory.V.Lit.Geo

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor in
open scoped ContDiff Topology in
theorem UpperTheory.V.Lit.Geo.Cs.decP :
    UpperTheory.V.Lit.Geo.Cs.DecP := by
  intro E _ _ _ a ho U Ξ f Y C c f₀ hS W hW lam hl q k B hB
  obtain ⟨hfl, hflow⟩ := fieldFlow E a ho U Ξ Y C hS.fld W hW
  obtain ⟨c₁, hc₁⟩ := Cs.zwSz E a U Y C hS.fld W hW (k + 1)
  obtain ⟨C₁, hC₁, hpb⟩ := Cs.pbSz (HV E a) (Fin Ξ.d → ℂ) q k c₁
  obtain ⟨D₁, hD₁, hmv⟩ := Cs.move E a ho U Ξ q k C
  obtain ⟨B₁, hB₁⟩ := hl.bdd C
  refine ⟨C₁ * D₁ * Real.exp (B * B₁), by positivity, fun A M hA hM w hw g x hg => ?_⟩
  obtain ⟨hF, hfe, hops⟩ := Cs.twOps E a ho U Ξ W hfl g x
  obtain ⟨hsm, hpe⟩ := (hops q).1 w
  obtain ⟨h, hh, hb⟩ := hS.root (Cs.pt g x) 1 (by simp)
  have hone : hOne E a ∈ cone E a := hOne_mem_cone
  have hpt : flow (Cs.Zw U W g x) 1 (hOne E a) = sand h (hOne E a) := by
    rw [hfe, hflow g h x 1 hh, ← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel_left]
  have hup : f (Cs.pt g x) + c ≤ f (Cs.pt (g * h) x) := by
    rw [Cs.pt_mul]
    exact hS.up _ h hg (by rw [hh, one_smul])
  have hlam : |lam (Cs.pt (g * h) x)| ≤ |lam (Cs.pt g x)| + B₁ := by
    rw [Cs.pt_mul, hl.add]
    exact (abs_add_le _ _).trans (add_le_add le_rfl (hB₁ h hb))
  have h1 := hmv w g x h _ hb (hw (g * h) x (by linarith [hS.c_pos]))
  rw [← hpt] at h1
  have hmem : flow (Cs.Zw U W g x) 1 (hOne E a) ∈ cone E a := hF.2 _ hone 1 ⟨zero_le_one, le_rfl⟩
  have h2 := hpb (Cs.Zw U W g x) 1 (Cs.Tw U Ξ w.1 g x) (hOne E a) _ (by simp)
    (hF.1.contDiffAt (ho.mem_nhds hone)) (hc₁ g x) (hsm.contDiffAt (ho.mem_nhds hmem)) h1
  refine (h2.congr (Filter.eventuallyEq_of_mem (ho.mem_nhds hone) fun p hp => (hpe p hp).symm)).mono ?_
  have he : Real.exp (B * |lam (Cs.pt (g * h) x)| - A * f (Cs.pt (g * h) x)) ≤
      Real.exp (B * B₁) * Real.exp (-(A * c)) * Real.exp (B * |lam (Cs.pt g x)| - A * f (Cs.pt g x)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    nlinarith [mul_le_mul_of_nonneg_left hlam hB, mul_le_mul_of_nonneg_left hup hA]
  calc _ = C₁ * D₁ * M * Real.exp (B * |lam (Cs.pt (g * h) x)| - A * f (Cs.pt (g * h) x)) := by ring
    _ ≤ C₁ * D₁ * M * (Real.exp (B * B₁) * Real.exp (-(A * c)) *
        Real.exp (B * |lam (Cs.pt g x)| - A * f (Cs.pt g x))) := mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Imports
section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Geo.Cs
open scoped Topology

theorem UpperTheory.V.Lit.Geo.Cs.loc :
    UpperTheory.V.Lit.Geo.Cs.Loc := by
  intro E _ _ _ a ho U Ξ f lam hf hl Φ hD hΦ q k A B R hA hB s p hp hR
  obtain ⟨c, hc⟩ := UpperTheory.V.Lit.Geo.Cs.locBd E a p hp
  obtain ⟨D, hD0, hmv⟩ := UpperTheory.V.Lit.Geo.Cs.move E a ho U Ξ q k c
  obtain ⟨B₀, hB₀⟩ := hl.bdd c
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective s
  have hcont : ContinuousAt (Φ (y : GL (Fin a) (Af E) ⧸ U)) p :=
    ((hΦ.1 _).continuousOn.continuousAt (ho.mem_nhds hp))
  have hev : ∀ᶠ x in 𝓝 p, R < Φ (y : GL (Fin a) (Af E) ⧸ U) x := hcont.eventually (lt_mem_nhds hR)
  refine ⟨_, hc.and hev, D * Real.exp (B * (B₀ + |lam (finGL E a y)|)), fun M hM w hw x hx => ?_⟩
  obtain ⟨⟨h, hh, rfl⟩, hx⟩ := hx
  rw [hD h y] at hx
  have h1 := hw h y hx.le
  have h2 := hmv w 1 y h _ hh (by rw [one_mul]; exact h1)
  rw [Tw_one] at h2
  refine h2.mono ?_
  rw [mul_assoc, mul_comm _ M]
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hM) hD0
  have h3 : |lam (pt h y)| ≤ B₀ + |lam (finGL E a y)| := by
    rw [pt, hl.add]
    exact (abs_add_le _ _).trans (add_le_add (hB₀ h hh) le_rfl)
  have h4 := mul_nonneg hA (hf (pt h y))
  have h5 := mul_le_mul_of_nonneg_left h3 hB
  linarith
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullLevD
section
open UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Dr Matrix

theorem UpperTheory.V.Lit.Geo.levD :
    LevD := by
  intro E _ _ _ a U Ξ q α hα
  have ho : IsOpen (cone E a) := isOpen_iff_mem_nhds.2 fun p hp => by
    obtain ⟨τ, -, h⟩ := locSec E a p hp
    exact h.mono fun x hx => ⟨τ x, hx⟩
  obtain ⟨w, hc, hg⟩ := (levGood E a ho U Ξ q).1 α hα
  have hom := omGood _ _ _ _ (geo ho U Ξ) 0 (isFlow_zero _) q
  refine ⟨?_, fun β hβ => ?_⟩
  · obtain ⟨α', hc', hl⟩ := (levGood E a ho U Ξ (q + 1)).2 _ (hom.1 w hg).2
    rw [(corrUniq E a ho U Ξ (q + 1)).1 _ _ _ (corrD E a ho U Ξ q α w hc) hc']
    exact hl
  · obtain ⟨w', hc', hg'⟩ := (levGood E a ho U Ξ q).1 β hβ
    obtain ⟨γ, hc'', hl⟩ := (levGood E a ho U Ξ q).2 _ (hom.2.1 w w' hg hg')
    have hs : Corr U Ξ (α - β) (w - w').1 := fun g x X => by
      rw [AlternatingMap.sub_apply, map_sub, Pi.sub_apply, Matrix.mulVec_sub, ← hc g x X, ← hc' g x X]
      rfl
    rw [(corrUniq E a ho U Ξ q).1 _ _ _ hs hc'']
    exact hl
end

