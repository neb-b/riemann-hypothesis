module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LGenKH
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0216
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0253
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0264
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolarPartIdentity
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0130

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LCfRelC
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LCfRel

open Set GlobalTheory.Eis GlobalTheory.StdUnn.HeightExists GlobalTheory.StdUnn.PolesModel

variable {D : D7} {n : ℕ}

theorem law_fam {H : G D n → ℝ≥0} (hH : IsHt H) {χ : (AE D)ˣ →* Circle} {s₁ : ℂ} {φ : G D n → ℂ} (h : IsLaw χ s₁ φ)
    (z : ℂ) : IsLaw χ z (fam H φ s₁ z) := by
  intro q hq a ha g
  simp only [fam]
  rw [hH.2.2 q hq a ha g, h q hq a ha g, npow_mul]
  have e : npow (absA D (Matrix.GeneralLinearGroup.det a)) (z + (n : ℂ) / 2) =
      npow (absA D (Matrix.GeneralLinearGroup.det a)) (z - s₁) *
        npow (absA D (Matrix.GeneralLinearGroup.det a)) (s₁ + (n : ℂ) / 2) := by
    rw [← npow_add (hom_pos _ _)]; congr 1; ring
  rw [e]; ring

theorem cont_fam {H : G D n → ℝ≥0} (hH : IsHt H) {φ : G D n → ℂ} (hφ : Continuous φ) (s₁ : ℂ) :
    Continuous fun u : ℂ × G D n => fam H φ s₁ u.1 u.2 := by
  simp only [fam, npow_eq_exp (hH.2.1 _)]
  have h1 : Continuous fun u : ℂ × G D n => Real.log (H u.2 : ℝ) :=
    (NNReal.continuous_coe.comp (hH.1.comp continuous_snd)).log fun u => (NNReal.coe_pos.2 (hH.2.1 _)).ne'
  exact (((Complex.continuous_ofReal.comp h1).mul (continuous_fst.sub continuous_const)).cexp).mul
    (hφ.comp continuous_snd)

def cset (nb : hermA D n → G D n) {v : Pl D} (C : Cut D n v) (g : G D n) : Set (G D n) :=
  ⋃ x ∈ C.s, (fun k => g * k * nb x) '' (K D n : Set (G D n))

theorem isCompact_cset (nb : hermA D n → G D n) {v : Pl D} (C : Cut D n v) (g : G D n) : IsCompact (cset nb C g) :=
  C.s.isCompact_biUnion fun _ _ => isCompact_K.image ((continuous_const.mul continuous_id).mul continuous_const)

theorem mem_cset (nb : hermA D n → G D n) {v : Pl D} (C : Cut D n v) (g : G D n) (u : KAt D n v) {x : hermA D n}
    (hx : x ∈ C.s) : g * (u : G D n) * nb x ∈ cset nb C g :=
  mem_biUnion hx ⟨u, (Subgroup.mem_inf.1 u.2).1, rfl⟩

theorem farRight {χ : (AE D)ˣ →* Circle} {H : G D n → ℝ≥0} (hH : IsHt H) {s₀ : ℂ} {φ : G D n → ℂ}
    (hφc : Continuous φ) (hφl : IsLaw χ s₀ φ) (nb : hermA D n → G D n) {v : Pl D} (C : Cut D n v) (c : ℂ → ℂ)
    (νv : Measure (KAt D n v)) [IsFiniteMeasure νv]
    (hrel : ∀ z g, ∫ k, cutR nb C (fam H φ s₀ z) (g * k) ∂νv = c z * fam H φ s₀ z g)
    {z : ℂ} (hz : (n : ℝ) / 2 < z.re) (g : G D n) :
    ∫ u, cutR nb C (eisS (fam H φ s₀ z)) (g * u) ∂νv = c z * eisS (fam H φ s₀ z) g := by
  have := t2Space_adeleRing' (F := D.host.F)
  have hcont := cont_fam hH hφc s₀
  have hz' : Continuous (fam H φ s₀ z) := hcont.comp (continuous_const.prodMk continuous_id)
  obtain ⟨w, hw, hwb⟩ := exists_majorant (P := P D n) (Γ := GF D n) (χ := χ.comp detP) (ρ := (n : ℝ) / 2)
    (σ := (n : ℝ) / 2) (Φ := fam H φ s₀) isIwasawa isCompact_K hcont.continuousOn
    (fun s _ q g => by
      have := law_fam hH hφl s q q.2 (leviBlock (D := D) (n := n) q) rfl g
      push_cast
      exact this)
    (fun τ hτ => summable_spherical τ hτ) isCompact_singleton (singleton_subset_iff.2 hz) (isCompact_cset nb C g)
  have hb : ∀ q (u : KAt D n v) x, x ∈ C.s →
      ‖fam H φ s₀ z (((q.out : GF D n) : G D n) * g * u * nb x)‖ ≤ w q := fun q u x hx => by
    have := hwb q z rfl _ (mem_cset nb C g u hx)
    simpa only [term, mul_assoc] using this
  have hterm : ∀ u : KAt D n v, cutR nb C (eisS (fam H φ s₀ z)) (g * u) =
      ∑' q : Cosets (P D n) (GF D n), cutR nb C (fam H φ s₀ z) (((q.out : GF D n) : G D n) * g * u) := by
    intro u
    simp only [cutR, eisS, cosetSum]
    rw [Summable.tsum_finsetSum fun x hx => (Summable.of_norm_bounded hw fun q => by
      simpa only [term, mul_assoc] using hwb q z rfl _ (mem_cset nb C g u hx)).mul_left (C.co x)]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← tsum_mul_left]
    simp only [term, mul_assoc]
  calc ∫ u, cutR nb C (eisS (fam H φ s₀ z)) (g * u) ∂νv
      = ∫ u, ∑' q : Cosets (P D n) (GF D n), cutR nb C (fam H φ s₀ z) (((q.out : GF D n) : G D n) * g * u) ∂νv := by
        congr 1; funext u; exact hterm u
    _ = ∑' q : Cosets (P D n) (GF D n), ∫ u, cutR nb C (fam H φ s₀ z) (((q.out : GF D n) : G D n) * g * u) ∂νv := by
        refine integral_tsum_dom νv _ (fun q => (∑ x ∈ C.s, ‖C.co x‖) * w q) (hw.mul_left _) (fun q u => ?_)
          fun q => ?_
        · simp only [cutR]
          refine (norm_sum_le _ _).trans ?_
          rw [Finset.sum_mul]
          refine Finset.sum_le_sum fun x hx => ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hb q u x hx) (norm_nonneg _)
        · refine Continuous.aestronglyMeasurable ?_
          simp only [cutR]
          exact continuous_finsetSum _ fun x _ => continuous_const.mul
            (hz'.comp ((continuous_const.mul continuous_subtype_val).mul continuous_const))
    _ = ∑' q : Cosets (P D n) (GF D n), c z * fam H φ s₀ z (((q.out : GF D n) : G D n) * g) := by
        congr 1; funext q; exact hrel z _
    _ = c z * eisS (fam H φ s₀ z) g := by
        rw [tsum_mul_left]; rfl

end PositivityTheory.Rg.Rsw.L.LCfRel

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LGenKI
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace PositivityTheory.Rg.Rsw.L.LGenK

open Matrix

variable {D : D7} {n : ℕ}

theorem factor {S : Finset (Pl D)} (hS2 : ∀ v ∉ S, (2 : 𝓞 D.host.F) ∉ v.asIdeal) {k : G D n} (hk : k ∈ KOff D n S) :
    ∃ g1 g2 g3 g4 : G D n, k = g1 * (g2 * (g3 * g4)) ∧ g1 ∈ KOff D n S ∧ IsN g1 ∧ g2 ∈ KOff D n S ∧ IsM g2 ∧
      g3 ∈ KOff D n S ∧ (∃ w u, IsW w ∧ IsN u ∧ u ∈ KOff D n S ∧ g3 = w * u * w⁻¹) ∧ g4 ∈ KOff D n S ∧ IsN g4 := by
  obtain ⟨hinf, hSv, hint⟩ := KOff_props hk
  obtain ⟨X, hXh, hXinf, hXS, hXint, hz, hu⟩ := exists_X hS2 hk
  obtain ⟨a, ha⟩ : ∃ a, a = bA (mat k) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = bB (mat k) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = bC (mat k) := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = bD (mat k) := ⟨_, rfl⟩
  have hMb : mat k = blk4 a b c d := by rw [ha, hb, hc, hd, block_matrix_of_blocks]
  obtain ⟨ia, ib, ic, id⟩ := blocks_at (infPart D) hinf
  simp only [← ha, ← hb, ← hc, ← hd] at ia ib ic id hz hu
  obtain ⟨u, hudef⟩ : ∃ u, u = d + c * X := ⟨_, rfl⟩
  simp only [← hudef] at hz hu
  obtain ⟨ui, hui⟩ : ∃ ui, ui = u⁻¹ := ⟨_, rfl⟩
  have hu1 : u * ui = 1 := by rw [hui]; exact Matrix.mul_nonsing_inv _ hu
  have hu2 : ui * u = 1 := by rw [hui]; exact Matrix.nonsing_inv_mul _ hu
  obtain ⟨β, hβ⟩ : ∃ β, β = a * X + b := ⟨_, rfl⟩
  have hh : mat (k * nOf X hXh) = blk4 a β c u := by rw [mat_mul, mat_nOf, hMb, block_matrix_mul_upper_unipotent, hβ, hudef]
  have hunit := unit_fromBlocks (cA D) a β c u (by rw [← hh]; exact mat_unit _)
  obtain ⟨-, R2, -⟩ := unit_rel _ a β c u hunit
  obtain ⟨-, -, C3⟩ := unit_col _ a β c u hunit
  obtain ⟨hXnh, hZnh, hid⟩ := fact_alg (cA D) a β c u ui hu1 hu2 R2 C3
  have hZn' : cj (cA D) (-(ui * c)) = -(ui * c) := by rw [cj_neg, hZnh]
  have hXh' : cj (cA D) (-X) = -X := by rw [cj_neg, hXh]

  have hIa : ∀ v ∉ S, IntM v a ∧ IntM v b ∧ IntM v c ∧ IntM v d := fun v hv =>
    integral_block_matrix_iff.1 (by rw [← hMb]; exact hint v hv)
  have hIX : ∀ v ∉ S, IntM v X := fun v hv => hXint v hv
  have hIu : ∀ v ∉ S, IntM v ui := by
    intro v hv
    rw [hui]
    refine IntM.inv ?_ hu (hz v)
    rw [hudef]; exact (hIa v hv).2.2.2.add ((hIa v hv).2.2.1.mul (hIX v hv))
  have hIXn : ∀ v ∉ S, IntM v (β * ui) := fun v hv => by
    rw [hβ]; exact (((hIa v hv).1.mul (hIX v hv)).add (hIa v hv).2.1).mul (hIu v hv)
  have hIZn : ∀ v ∉ S, IntM v (-(ui * c)) := fun v hv => ((hIu v hv).mul (hIa v hv).2.2.1).neg

  have hXn0 : ∀ (T : Type) [CommRing T] (f : AE D →+* T), a.map f = 1 → b.map f = 0 → X.map f = 0 →
      (β * ui).map f = 0 := by
    intro T _ f h1 h2 h3
    rw [Matrix.map_mul, hβ, map_add', Matrix.map_mul, h2, h3]; simp
  have hZn0 : ∀ (T : Type) [CommRing T] (f : AE D →+* T), c.map f = 0 → (-(ui * c)).map f = 0 := by
    intro T _ f h1
    rw [map_neg', Matrix.map_mul, h1]; simp
  have hS' : ∀ v ∈ S, a.map (cv D v) = 1 ∧ b.map (cv D v) = 0 ∧ c.map (cv D v) = 0 ∧ d.map (cv D v) = 1 := by
    intro v hv
    have := blocks_at (cv D v) (hSv v hv)
    simp only [← ha, ← hb, ← hc, ← hd] at this
    exact this

  have m4 : nOf (-X) hXh' ∈ KOff D n S :=
    nOf_mem _ _ (by rw [map_neg', hXinf, neg_zero]) (fun v hv => by rw [map_neg', hXS v hv, neg_zero])
      (fun v hv => (hIX v hv).neg)
  have mX : nOf X hXh ∈ KOff D n S := nOf_mem _ _ hXinf hXS hIX
  have m1 : nOf (β * ui) hXnh ∈ KOff D n S :=
    nOf_mem _ _ (hXn0 _ _ ia ib hXinf) (fun v hv => hXn0 _ _ (hS' v hv).1 (hS' v hv).2.1 (hXS v hv)) hIXn
  have mu3 : nOf (-(ui * c)) hZn' ∈ KOff D n S :=
    nOf_mem _ _ (hZn0 _ _ ic) (fun v hv => hZn0 _ _ (hS' v hv).2.2.1) hIZn
  have m3 : wE D n * nOf (-(ui * c)) hZn' * (wE D n)⁻¹ ∈ KOff D n S :=
    conj_mem _ _ (hZn0 _ _ ic) (fun v hv => hZn0 _ _ (hS' v hv).2.2.1) hIZn
  have hmg3 : mat (wE D n * nOf (-(ui * c)) hZn' * (wE D n)⁻¹) = blk4 1 0 (ui * c) 1 := by
    rw [mat_conj, neg_neg]
  have hmg1i : mat (nOf (β * ui) hXnh)⁻¹ = blk4 1 (-(β * ui)) 0 1 := mat_inv_eq (by rw [mat_nOf, upper_unipotent_block_inverse])
  have hmg3i : mat (wE D n * nOf (-(ui * c)) hZn' * (wE D n)⁻¹)⁻¹ = blk4 1 0 (-(ui * c)) 1 :=
    mat_inv_eq (by rw [hmg3, lower_unipotent_block_inverse])
  have hX4 : nOf X hXh * nOf (-X) hXh' = 1 := by
    apply mat_inj
    rw [mat_mul, mat_nOf, mat_nOf, upper_unipotent_block_inverse, mat_one]
  set g1 := nOf (β * ui) hXnh with hg1
  set g3 := wE D n * nOf (-(ui * c)) hZn' * (wE D n)⁻¹ with hg3
  have hmg2 : mat (g1⁻¹ * k * nOf X hXh * g3⁻¹) = blk4 (a - β * ui * c) 0 0 u := by
    rw [mat_mul, mat_mul, mat_mul, hmg1i, hmg3i, Matrix.mul_assoc (blk4 1 (-(β * ui)) 0 1), ← mat_mul, hh, ← hid]
    calc blk4 1 (-(β * ui)) 0 1 * (blk4 1 (β * ui) 0 1 * blk4 (a - β * ui * c) 0 0 u * blk4 1 0 (ui * c) 1) *
          blk4 1 0 (-(ui * c)) 1
        = (blk4 1 (-(β * ui)) 0 1 * blk4 1 (β * ui) 0 1) * blk4 (a - β * ui * c) 0 0 u *
            (blk4 1 0 (ui * c) 1 * blk4 1 0 (-(ui * c)) 1) := by simp only [Matrix.mul_assoc]
      _ = blk4 (a - β * ui * c) 0 0 u := by
          rw [lower_unipotent_block_inverse, Matrix.mul_one]
          have := upper_unipotent_block_inverse (-(β * ui)); rw [neg_neg] at this; rw [this, Matrix.one_mul]
  refine ⟨g1, g1⁻¹ * k * nOf X hXh * g3⁻¹, g3, nOf (-X) hXh', ?_, m1, isN_nOf _ _, ?_, isM_of _ _ _ hmg2, m3,
    ⟨wE D n, _, isW_wE, isN_nOf _ _, mu3, rfl⟩, m4, isN_nOf _ _⟩
  · simp only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left, hX4, mul_one]
  · exact mul_mem (mul_mem (mul_mem (inv_mem m1) hk) mX) (inv_mem m3)

end PositivityTheory.Rg.Rsw.L.LGenK
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LIkSch
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LIkSch

theorem isCompact_K {D : D7} {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) {l : Lvl T} (hl : l.Good) :
    IsCompact (l.K : Set (GA D T)) := by
  exact (_root_.GlobalTheory.RegSch.good_level_conj_stab D T T₀ r d l.c hl.2.2
    (GlobalTheory.T.adelic_iwasawa_decomposition_wittIsotropicStabilizer D T T₀ r d l.c (fun v hv => GlobalTheory.Core.Rk.IP.Model.isSplit_two v hv) hl.2.2) l hl).2.1

end PositivityTheory.Rg.Rsw.L.LIkSch

namespace PositivityTheory.Rg.Rsw.L

theorem ikSch : IkSch := by
  intro D n t B W d I θ hθ Φ hΦ
  have hK : IsCompact (I.l.K : Set (GA D B)) := LIkSch.isCompact_K d I.good
  have h1 := _root_.GlobalTheory.CompactAvgSchwartz.projS_mem D θ hθ B n I.l.K hK I.νK I.probK Φ hΦ
  refine ⟨h1, ?_⟩
  obtain ⟨𝓕, h𝓕⟩ := I.cov₁
  exact _root_.GlobalTheory.RegSch.IkSchwartz.ikS_mem_schwartzA D θ hθ B W t n d I.μ₁ 𝓕 h𝓕 _ h1

end PositivityTheory.Rg.Rsw.L
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LResCoreA
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LResCore

open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

variable {D : D7} {n : ℕ}

theorem kAt_le_kOff {v : Pl D} {S : Finset (Pl D)} (hv : v ∉ S) : KAt D n v ≤ KOff D n S := by
  intro k hk
  obtain ⟨hK, hA⟩ := Subgroup.mem_inf.1 hk
  rw [mem_atPts] at hA
  rw [KOff, mem_levelOff]
  refine ⟨hA.1, fun w hw => hA.2 w ?_, fun w _ => ?_⟩
  · rw [Finset.mem_singleton]
    rintro rfl
    exact hv hw
  · by_cases hwv : w = v
    · subst hwv
      have h1 : k ∈ levelOpen D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) := hK.1
      exact Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 h1 w)
    · rw [hA.2 w (by rwa [Finset.mem_singleton])]
      exact one_mem _

theorem isCompact_kAt (v : Pl D) : IsCompact (KAt D n v : Set (G D n)) := by
  have : Submodule.IsFullLattice D.host.E (stdLattice D.host.E (n + n)) := isLattice_stdLattice
  have hK : IsCompact (K D n : Set (G D n)) := isCompact_levelAll (isCMExt_host D) _ _ _
  have e : (atPts D.sp.cm.sig (Jst D n) {v} : Set (G D n)) = (finPts D.sp.cm.sig (Jst D n) : Set (G D n)) ∩
      ⋂ w, ⋂ (_ : w ∉ ({v} : Finset (Pl D))), (proj D.sp.cm.sig (Jst D n) w) ⁻¹' {1} := by
    ext k
    simp only [SetLike.mem_coe, mem_atPts, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
  have hA : IsClosed (atPts D.sp.cm.sig (Jst D n) {v} : Set (G D n)) := by
    rw [e]
    exact (isClosed_finPts _ _).inter (isClosed_iInter fun w => isClosed_iInter fun _ =>
      isClosed_singleton.preimage (continuous_proj _ _ w))
  have e2 : (KAt D n v : Set (G D n)) = (K D n : Set (G D n)) ∩ (atPts D.sp.cm.sig (Jst D n) {v} : Set (G D n)) :=
    Subgroup.coe_inf _ _
  rw [e2]
  exact hK.inter_right hA

theorem exists_haar_prob {X : Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [MeasurableSpace X]
    [BorelSpace X] (K₀ : Subgroup X) (h : IsCompact (K₀ : Set X)) :
    ∃ ν : Measure K₀, ν.IsHaarMeasure ∧ IsProbabilityMeasure ν := by
  have : CompactSpace K₀ := isCompact_iff_compactSpace.mp h
  refine ⟨Measure.haarMeasure ⊤, inferInstance, ⟨?_⟩⟩
  simpa using Measure.haarMeasure_self (G := K₀) (K₀ := ⊤)

theorem isLaw_sw {t : ℕ} {B : HSp D} (hB : B.rank = n + t) {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle}
    {θ : InfFam D} {μB : Measure (Mx D B.rank n)} {ωB : G D n →* Module.End ℂ (schwartzA θ B.rank n)}
    (hω : IsWeilSch ψ χ θ B μB ωB) (Φ : schwartzA θ B.rank n) :
    IsLaw χ ((t : ℂ) / 2) (fun g => (ωB g Φ).1 0) := by
  intro q hq a ha g
  obtain ⟨m, u, b, rfl, hm, hu⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_levi_unip hq a ha
  have e' : ωB (m * u * g) Φ = ωB m (ωB u (ωB g Φ)) := by
    rw [map_mul, map_mul]; rfl
  have z1 : ((0 : Mx D B.rank n) ⬝ a.1 : Mx D B.rank n) = 0 := Matrix.zero_mul _
  have z2 : GlobalTheory.StdUnn.inner B (0 : Mx D B.rank n) 0 = 0 := by
    rw [GlobalTheory.StdUnn.inner, adj_zero, Matrix.zero_mul]
  have e3 : ((B.rank : ℂ) / 2) = (t : ℂ) / 2 + (n : ℂ) / 2 := by
    rw [hB]; push_cast; ring
  show (ωB (m * u * g) Φ).1 0 = _ * _ * (ωB g Φ).1 0
  rw [e', hω.levi m a hm, hω.unip u b hu, z1, z2, e3]
  simp [halfTr]

theorem theta_mul {θ : InfFam D} {V : HSp D} (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n))
    (Ψ : schwartzA θ V.rank n) (g u : G D n) (h : GA D V) : theta ω Ψ (g * u) h = theta ω (ω u Ψ) g h := by
  simp only [theta, map_mul]
  rfl

end PositivityTheory.Rg.Rsw.L.LResCore

end
end

