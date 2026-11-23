module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0028
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0026
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.ScaledTorsionPointNonsingular
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.ExistsFinitePartOneIdeleSplitCongruenceQuotient

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgAnLat
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1

theorem good_lattice (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (g2 g3 : ℂ_[l])
    (hg : IsGoodModel l L ι g2 g3) :
    ∃ L' : PeriodPair, LatModel l L' ι g2 g3 ∧ ∀ d, HasCMBy d L → HasCMBy d L' := by
  obtain ⟨-, -, h2, h3, -, lam, hlam, e2, e3⟩ := hg
  have hm : ι.symm lam ≠ 0 := by
    intro h
    apply hlam
    have := congrArg ι h
    simpa using this
  have hc : (ι.symm lam)⁻¹ ≠ 0 := inv_ne_zero hm
  obtain ⟨-, -, -, -, -, -, -, -, -, hg2, hg3⟩ := F.homogeneity L (ι.symm lam)⁻¹ hc
  refine ⟨F.scalePair L (ι.symm lam)⁻¹ hc, ⟨?_, ?_, h2, h3⟩,
    fun d hd => F.hasCMByScale d L _ hc hd⟩
  · rw [hg2, e2]
    simp
  · rw [hg3, e3]
    simp

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgAnWp
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1

theorem shortW_map (l : ℕ) [Fact l.Prime] (g2 g3 : ℂ) (ι : ℂ ≃+* ℂ_[l]) :
    A.shortW (ι g2) (ι g3) = (A.shortW g2 g3).map (ι : ℂ →+* ℂ_[l]) := by
  ext <;> simp [A.shortW, WeierstrassCurve.map, map_ofNat]

theorem wp_bridge (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) :
    A.wpReg (A.shortW (ι L.g₂) (ι L.g₃)) = PowerSeries.map (ι : ℂ →+* ℂ_[l]) (F.pSeries L) := by
  have h1 := F.curveBridge (A.shortW L.g₂ L.g₃) L (A.shortInv ℂ _ _).2.1 (A.shortInv ℂ _ _).2.2.1
  have h2 := (A.zMap ℂ ℂ_[l] (ι : ℂ →+* ℂ_[l]) (A.shortW L.g₂ L.g₃)).2.2.1
  rw [← h1, h2, shortW_map]

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorStatus
section
noncomputable section
open scoped Classical

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM Formalism.ELL WeierstrassCurve
open Formalism.L2.Th1.E (px py IntCurve)
open Formalism.L2.Th1.A (shortW)

theorem cmTorsion_of_point (hpt : TorPt) : CM4 := by
  intro d L _ _ _ l _ hl _ ι lam hlam m2 m3 n2 n3 hΔ z N hN0 hN hz hz0
  have hg : GoodPair l (lam ^ 4 * ι L.g₂) (lam ^ 6 * ι L.g₃) := ⟨hl, m2, m3, n2, n3, hΔ⟩
  obtain ⟨h, hNP⟩ := hpt l L ι lam hlam z N hz hz0
  have hP0 : (Affine.Point.some _ _ h) ≠ 0 := Affine.Point.some_ne_zero h
  obtain ⟨hx, hy⟩ := tor_kur hg _ N hN0 hN hNP hP0
  obtain ⟨-, ix, iy⟩ := integral_of_not_mem_formalGroup hg _ (torsion_not_mem_formalGroup hg _ N hN hNP hP0)
  have hx' : lam ^ 2 * ι (L.weierstrassP z) ∈ MaximalUnramifiedExtension l := hx
  have hy' : lam ^ 3 * ι (L.derivWeierstrassP z) / 2 ∈ MaximalUnramifiedExtension l := hy
  have ix' : ‖lam ^ 2 * ι (L.weierstrassP z)‖ ≤ 1 := ix
  have iy' : ‖lam ^ 3 * ι (L.derivWeierstrassP z) / 2‖ ≤ 1 := iy
  have e : lam ^ 3 * ι (L.derivWeierstrassP z) = 2 * (lam ^ 3 * ι (L.derivWeierstrassP z) / 2) := by
    ring
  have h2 : ‖(2 : ℂ_[l])‖ ≤ 1 := by
    simpa using IsUltrametricDist.norm_natCast_le_one ℂ_[l] 2
  refine ⟨hx', ?_, ix', ?_⟩
  · rw [e]
    exact mul_mem (by simp) hy'
  · rw [e, norm_mul]
    exact mul_le_one₀ h2 (norm_nonneg _) iy'

theorem torPt : TorPt := Formalism.L2.Th1.E.scaled_torsion_point_of_add Formalism.L2.Th1.E.PtOfAdd_of

theorem cm4 : CM4 := cmTorsion_of_point torPt

end ReciprocityTheory.ChartRestriction.L1
end
end

