module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2696
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2583
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2555
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2548
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1796
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1840
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1613
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1711
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2695
public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0039
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2390
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2534
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2611
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2522
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2700
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1885
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1890
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFramePointStalk
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsHorizontalGeneratorOfCharts
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactification
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1895
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1535
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModelRuleSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatWeightRuleReadsNonvanishingDetSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantLengthOfReadingHorizontalSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1916
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1920
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1842
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorSmallCosetHalfIsSchwartzBruhat
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory ValuativeRel
open scoped TensorProduct nonZeroDivisors Pointwise

namespace GlobalTheory.FunObj.CosSB

open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV GlobalTheory.LatVac
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7}

section Small

variable {a b : ℕ}

theorem frAt_add (w : Pl D.host.E) (β' : GL (Fin b) (Lev.EAf D)) (β : GL (Fin a) (Lev.EAf D)) (x y : Mx D b a) :
    frAt w β' β (x + y) = frAt w β' β x + frAt w β' β y := by
  unfold frAt
  have h : (x + y).map (toEAf D) = x.map (toEAf D) + y.map (toEAf D) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.add_apply, map_add]
  rw [h, Comparison₂.fr_add]
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, map_add]

theorem frAt_sub (w : Pl D.host.E) (β' : GL (Fin b) (Lev.EAf D)) (β : GL (Fin a) (Lev.EAf D)) (x y : Mx D b a) :
    frAt w β' β (x - y) = frAt w β' β x - frAt w β' β y := by
  unfold frAt
  rw [Matrix.map_sub _ (toEAf D).map_sub, Comparison₂.fr_sub, Matrix.map_sub _ (cpt (D := D) w).map_sub]

theorem isSmall_add {P : Finset (Pl D.host.E)} {β' : GL (Fin b) (Lev.EAf D)} {β : GL (Fin a) (Lev.EAf D)} {n : ℤ}
    {x y : Mx D b a} (hx : IsSmall P β' β n x) (hy : IsSmall P β' β n y) : IsSmall P β' β n (x + y) :=
  fun w hw i j => by
    rw [frAt_add, Matrix.add_apply]
    exact Valuation.map_add_le _ (hx w hw i j) (hy w hw i j)

theorem isSmall_sub {P : Finset (Pl D.host.E)} {β' : GL (Fin b) (Lev.EAf D)} {β : GL (Fin a) (Lev.EAf D)} {n : ℤ}
    {x y : Mx D b a} (hx : IsSmall P β' β n x) (hy : IsSmall P β' β n y) : IsSmall P β' β n (x - y) :=
  fun w hw i j => by
    rw [frAt_sub, Matrix.sub_apply]
    exact Valuation.map_sub_le _ (hx w hw i j) (hy w hw i j)

theorem isHalf_add_nsmul {e : AE D} {t u : Mx D b a} (k : ℕ) (hu : IsHalf e u) : IsHalf e (t + k • u) ↔ IsHalf e t := by
  have h : ∀ i j, e * (t + k • u) i j = e * t i j + k • u i j := fun i j => by
    rw [Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul, mul_add, mul_left_comm, hu i j]
  unfold IsHalf
  refine forall₂_congr fun i j => ?_
  rw [h, Matrix.add_apply, Matrix.smul_apply, add_left_inj]

theorem v_unif_pow (w : Pl D.host.E) (n : ℕ) :
    Valued.v (((unifAt w ^ (n : ℤ) : (Kw w)ˣ)) : Kw w) = WithZero.exp (-(n : ℤ)) := by
  have h : Valued.v (unifAt w : Kw w) = WithZero.exp (-1 : ℤ) := unif_spec w
  rw [zpow_natCast, Units.val_pow_eq_pow_val, map_pow, h, ← WithZero.exp_nsmul]
  simp

theorem val_le_unif_iff (w : Pl D.host.E) (n : ℕ) (x : Kw w) :
    valuation (Kw w) x ≤ valuation (Kw w) (((unifAt w ^ (n : ℤ) : (Kw w)ˣ)) : Kw w) ↔
      Valued.v x ≤ WithZero.exp (-(n : ℤ)) :=
  (Comparison₂.vEq w _ _).trans (by rw [v_unif_pow])

end Small

section Lat

variable {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem nsmul_mem_hatMx {b : ℕ} (h2 : ∀ x ∈ latRat S T ΛS ΛT, b • x ∈ homLat ΛS ΛT) (𝔪 : Ideal (𝓞 D.host.E))
    {u : WO S T} (hu : u ∈ latO S T ΛS ΛT fun _ => True) :
    (b * Ideal.absNorm 𝔪) • u ∈ hatMx (𝔪 • homLat ΛS ΛT) := by
  refine latO_induction (p := fun u => (b * Ideal.absNorm 𝔪) • u ∈ hatMx (𝔪 • homLat ΛS ΛT)) ?_ ?_ ?_ ?_ hu
  · intro α hα X hX
    rw [← WeilOver.finTens_nsmul]
    refine AddSubgroup.subset_closure ⟨α, hα, _, ?_, rfl⟩
    rw [mul_nsmul, ← Nat.cast_smul_eq_nsmul (𝓞 D.host.E)]
    exact Submodule.smul_mem_smul (Ideal.absNorm_mem _) (h2 X hX)
  · rw [nsmul_zero]; exact zero_mem _
  · intro x y hx hy; rw [nsmul_add]; exact add_mem hx hy
  · intro x hx; rw [neg_nsmul]; exact neg_mem hx

theorem nsmul_mem_latO {a : ℕ} (h1 : ∀ x ∈ homLat ΛS ΛT, a • x ∈ latRat S T ΛS ΛT) (𝔪 : Ideal (𝓞 D.host.E))
    {u : WO S T} (hu : u ∈ hatMx (𝔪 • homLat ΛS ΛT)) : a • u ∈ latO S T ΛS ΛT fun _ => True := by
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hw
    exact WeilOver.finTens_nsmul α a x ▸ finTens_mem_latO hα (h1 x (Submodule.smul_le_right hx))
  | zero => rw [nsmul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [nsmul_add]; exact add_mem hx hy
  | neg x _ hx => rw [neg_nsmul]; exact neg_mem hx

theorem isSmall_of_mem_hatMx {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)}
    (hS : IsFrame βS ΛS) (hT : IsFrame βT ΛT) (P : Finset (Pl D.host.E)) (n : ℕ) {u : WO S T}
    (hu : u ∈ hatMx ((∏ w ∈ P, w.asIdeal ^ n) • homLat ΛS ΛT)) : IsSmall P βT βS n u := by
  intro w hw i j
  obtain ⟨s, hs, h⟩ := ((Comparison₂.mem_hatMx_iff hS hT _ u).1 hu).2 i j
  have h3 := Comparison₂.v_le_of_mem_idS (Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun w : Pl D.host.E => w.asIdeal ^ n) hw)) hs
  rw [val_le_unif_iff]
  change Valued.v (cpt w (Comparison₂.fr βT βS (u.map (toEAf D)) i j)) ≤ _
  rwa [← h]

end Lat

end GlobalTheory.FunObj.CosSB

namespace GlobalTheory.FunObj.CosSB

open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV GlobalTheory.LatVac
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem prod_pow_ne_bot {D : D7} (P : Finset (Pl D.host.E)) (n : ℕ) : (∏ w ∈ P, w.asIdeal ^ n) ≠ ⊥ := by
  rw [← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
  exact fun w _ => pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact w.ne_bot)


set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in
theorem isSBHalf_cosLoc : ∀ {D : D7} (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D))
    (βT : GL (Fin T.rank) (Lev.EAf D)) (P : Finset (Pl D.host.E)) (e : AE D) (n : ℕ) (r : WO S T),
    Submodule.IsFullLattice D.host.E ΛS → Submodule.IsFullLattice D.host.E ΛT → IsFrame βS ΛS → IsFrame βT ΛT →
    IsIdemSum e P → IsHalf e r → IsSBHalf e (latO S T ΛS ΛT fun _ => True) (cosLoc P e βT βS n r) := by
  intro D S T ΛS ΛT βS βT P e n r hS hT hFS hFT he _
  classical
  obtain ⟨a, ha, h1⟩ := WeilOver.exists_hom_le hS hT
  obtain ⟨b, hb, h2⟩ := WeilOver.exists_le_hom hS.toIsLattice hT.toIsLattice
  obtain ⟨e0, e1, e2⟩ := Comparison₂.cpt_idemSum he
  have hM : 0 < Ideal.absNorm (∏ w ∈ P, w.asIdeal ^ n) :=
    Nat.pos_of_ne_zero fun h => prod_pow_ne_bot P n (Ideal.absNorm_eq_zero_iff.1 h)

  set N : ℕ := Ideal.absNorm (∏ w ∈ P, w.asIdeal ^ 1) with hNdef
  have hN : 0 < N := Nat.pos_of_ne_zero fun h => prod_pow_ne_bot P 1 (Ideal.absNorm_eq_zero_iff.1 h)
  have hNmem : ∀ w ∈ P, (N : 𝓞 D.host.E) ∈ w.asIdeal := fun w hw => by
    have := Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun w : Pl D.host.E => w.asIdeal ^ 1) hw)
      (Ideal.absNorm_mem (∏ w ∈ P, w.asIdeal ^ 1))
    rw [pow_one] at this
    exact this

  have hc1 : ∀ p : Fin T.rank × Fin S.rank, ∃ k : ℕ, ∀ l, k ≤ l →
      ((N ^ l : ℕ) : Lev.EAf D) * (toEAf D e * Comparison₂.fr βT βS (r.map (toEAf D)) p.1 p.2) ∈ OA D :=
    fun p => exists_pow_mul_mem _ fun Q hQ => by
      have hQP : Q ∉ P := fun h => hQ (hNmem Q h)
      rw [map_mul, e2 Q hQP, zero_mul]
      exact zero_mem _
  choose kk hkk using hc1
  set c : ℕ := N ^ (Finset.univ.sup kk) with hcdef
  have hc0 : 0 < c := pow_pos hN _
  have hc : ∀ i j, (c : Lev.EAf D) * (toEAf D e * Comparison₂.fr βT βS (r.map (toEAf D)) i j) ∈ OA D :=
    fun i j => hkk (i, j) _ (Finset.le_sup (f := kk) (Finset.mem_univ (i, j)))
  refine ⟨fun t ht => ?_, (a * c) * (b * Ideal.absNorm (∏ w ∈ P, w.asIdeal ^ n)), by positivity,
    fun u hu hh t => ?_, fun t ht => ?_⟩
  · by_contra h
    exact ht (by unfold cosLoc; rw [if_neg fun H => h H.1])
  · have hk : IsSmall P βT βS n (((a * c) * (b * Ideal.absNorm (∏ w ∈ P, w.asIdeal ^ n))) • u) := by
      refine isSmall_of_mem_hatMx hFS hFT P n ?_
      rw [mul_nsmul']
      exact nsmul_mem (nsmul_mem_hatMx h2 _ hu) _
    unfold cosLoc
    refine if_congr (and_congr (isHalf_add_nsmul _ hh) ?_) rfl rfl
    rw [add_sub_right_comm]
    exact ⟨fun h => by simpa using isSmall_sub h hk, fun h => isSmall_add h hk⟩
  · obtain ⟨hth, hts⟩ : IsHalf e t ∧ IsSmall P βT βS n (t - r) := by
      by_contra h
      exact ht (by unfold cosLoc; rw [if_neg h])
    set X := Comparison₂.fr βT βS (t.map (toEAf D))
    set R := Comparison₂.fr βT βS (r.map (toEAf D))
    have hX : Comparison₂.fr βT βS ((c • t).map (toEAf D)) = (c : Lev.EAf D) • (toEAf D e • X) := by
      have : (c • t).map (toEAf D) = (c : Lev.EAf D) • (toEAf D e • t.map (toEAf D)) := by
        ext i j
        rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.map_apply, nsmul_eq_mul,
          map_mul, map_natCast, smul_eq_mul, smul_eq_mul]
        conv_lhs => rw [← hth i j]
        rw [map_mul]
      rw [this, Comparison₂.fr_smul, Comparison₂.fr_smul]
    have hsm : ∀ i j, toEAf D e * (X - R) i j ∈ OA D := fun i j => by
      refine (mem_OA_iff _).2 fun Q => ?_
      rw [map_mul]
      by_cases hQ : Q ∈ P
      · rw [e1 Q hQ, one_mul]
        have h3 := (val_le_unif_iff Q n _).1 (hts Q hQ i j)
        rw [frAt_sub, Matrix.sub_apply] at h3
        rw [HeightOneSpectrum.mem_adicCompletionIntegers, Matrix.sub_apply, map_sub]
        refine h3.trans ?_
        rw [← WithZero.exp_zero, WithZero.exp_le_exp]
        omega
      · rw [e2 Q hQ, zero_mul]
        exact zero_mem _
    have hint : ∀ i j, Comparison₂.fr βT βS ((c • t).map (toEAf D)) i j ∈ OA D := fun i j => by
      have : Comparison₂.fr βT βS ((c • t).map (toEAf D)) i j =
          (c : Lev.EAf D) * (toEAf D e * (X - R) i j) + (c : Lev.EAf D) * (toEAf D e * R i j) := by
        rw [hX, Matrix.smul_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, smul_eq_mul, ← mul_add, ← mul_add,
          sub_add_cancel]
      rw [this]
      exact add_mem (mul_mem (natCast_mem _ _) (hsm i j)) (hc i j)
    have hmem : c • t ∈ hatMx ((⊤ : Ideal (𝓞 D.host.E)) • homLat ΛS ΛT) := by
      refine (Comparison₂.mem_hatMx_iff hFS hFT ⊤ _).2 ⟨fun i j => ?_, fun i j => ⟨⟨_, hint i j⟩, ?_, rfl⟩⟩
      · rw [Matrix.smul_apply, map_nsmul, ← hth i j, map_mul, e0, zero_mul, smul_zero]
      · rw [idS, Ideal.map_top]
        exact Submodule.mem_top
    have := nsmul_mem (nsmul_mem_latO h1 ⊤ hmem) (b * Ideal.absNorm (∏ w ∈ P, w.asIdeal ^ n))
    convert this using 1
    rw [mul_comm (a * c), ← smul_smul, ← smul_smul a c t]

end GlobalTheory.FunObj.CosSB

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductiveMixedHeightReciprocityTwoSections
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

set_option autoImplicit false

theorem mixRecVal_cons_eq_resCyc_sub_resArch {k : Type} [CommRing k] {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] {q : Y ⟶ Sp k} (hA : IsAmb q) {e : ℕ} (hdim : topologicalKrullDim Y = (e + 1 + 1 : ℕ))
    {T : ∀ d : ℕ, (Fin d → HermLB q) → Y → ℝ} (hT : IsMix q (e + 1) T) (N : HermLB q) (L : Fin e → HermLB q)
    (t : N.B.Sec) {z : Y} (hz : Order.coheight z = 1) (hzt : z ∈ nonzeroLocus t) :
    T (e + 1) (Fin.cons N L) z = resCyc N.isLB t (T e L) z - resArch L N t z := by
  have hg : genericPoint (clo z) ∈ nonzeroLocus (secPull t (cloι z)) := by
    rw [GlobalTheory.nonzeroLocus_secPull]
    show cloι z (genericPoint (clo z)) ∈ nonzeroLocus t
    rw [cloι_genericPoint]
    exact hzt
  have hd : topologicalKrullDim (clo z) = ((e + 1 : ℕ) : WithBot ℕ∞) :=
    ((_root_.GlobalTheory.MixHt.dimOne k Y q hA (e + 1) hdim).2 z (genericPoint (clo z)) hz).1
  have h := hT.recur (clo z) (cloι z ≫ q) (cloι z) rfl e le_rfl hd N L (N.restr (cloι z))
    (fun a => (L a).restr (cloι z)) (HermLB.Isometric.refl _) (fun _ => HermLB.Isometric.refl _) _
    (isRatSec_ratOfSec _ hg)
  rw [cloι_genericPoint] at h
  rw [h, resCyc, resArch, dite_eq_left hg, dite_eq_left hg]
  rfl

end GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem finite_support_mult_mul {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [CompactSpace Y]
    (D : CartierDiv Y) (g : Y → ℝ) : (Function.support fun z => (D.mult z : ℝ) * g z).Finite :=
  D.finite_support_mult.subset fun z hz => by
    simp only [Function.mem_support] at hz ⊢
    intro h
    simp [h] at hz

theorem recVal_cons_recip : ArchRecip → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 + 1 : ℕ) → ∀ T, IsMix q (e + 1) T → ∀ (M N : HermLB q) (L : Fin e → HermLB q) (s : M.B.Sec) (t : N.B.Sec) (hs : genericPoint Y ∈ nonzeroLocus s) (ht : genericPoint Y ∈ nonzeroLocus t), (∀ z : Y, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → recVal (T (e + 1) (Fin.cons N L)) (Fin.cons N L : Fin (e + 1) → HermLB q) M (isRatSec_ratOfSec s hs) = recVal (T (e + 1) (Fin.cons M L)) (Fin.cons M L : Fin (e + 1) → HermLB q) N (isRatSec_ratOfSec t ht) := by
  intro hAR k _ Y _ _ q hA e hdim T hT M N L s t hs ht hcov
  have : IsNoetherian Y := hA.isNoetherian
  have key (A B : HermLB q) (a : A.B.Sec) (b : B.B.Sec) (ha : genericPoint Y ∈ nonzeroLocus a)
      (hab : ∀ z : Y, Order.coheight z = 1 → z ∈ nonzeroLocus a ∨ z ∈ nonzeroLocus b) (z : Y) :
      ((divOfSec A.isLB a ha).mult z : ℝ) * T (e + 1) (Fin.cons B L) z =
        ((divOfSec A.isLB a ha).mult z : ℝ) * resCyc B.isLB b (T e L) z -
          ((divOfSec A.isLB a ha).mult z : ℝ) * resArch L B b z := by
    by_cases h0 : (divOfSec A.isLB a ha).mult z = 0
    · simp [h0]
    · have hz := CartierDiv.coheight_eq_one_of_mult_ne_zero h0
      have hza : z ∉ nonzeroLocus a := fun h =>
        (notMem_supp_divOfSec.2 h) (CartierDiv.mem_supp_of_mult_ne_zero h0)
      rw [mixRecVal_cons_eq_resCyc_sub_resArch hA hdim hT B L b hz ((hab z hz).resolve_left hza), mul_sub]
  have hL : recVal (T (e + 1) (Fin.cons N L)) (Fin.cons N L : Fin (e + 1) → HermLB q) M (isRatSec_ratOfSec s hs) =
      (∑ᶠ z, ((divOfSec M.isLB s hs).mult z : ℝ) * resCyc N.isLB t (T e L) z -
        ∑ᶠ z, ((divOfSec M.isLB s hs).mult z : ℝ) * resArch L N t z) -
        mixArch (Fin.cons N L : Fin (e + 1) → HermLB q) M (isRatSec_ratOfSec s hs) := by
    rw [recVal, finsum_congr (key M N s t hs hcov), finsum_sub_distrib (finite_support_mult_mul _ _)
      (finite_support_mult_mul _ _)]
  have hR : recVal (T (e + 1) (Fin.cons M L)) (Fin.cons M L : Fin (e + 1) → HermLB q) N (isRatSec_ratOfSec t ht) =
      (∑ᶠ z, ((divOfSec N.isLB t ht).mult z : ℝ) * resCyc M.isLB s (T e L) z -
        ∑ᶠ z, ((divOfSec N.isLB t ht).mult z : ℝ) * resArch L M s z) -
        mixArch (Fin.cons M L : Fin (e + 1) → HermLB q) N (isRatSec_ratOfSec t ht) := by
    rw [recVal, finsum_congr (key N M t s ht fun z hz => (hcov z hz).symm),
      finsum_sub_distrib (finite_support_mult_mul _ _) (finite_support_mult_mul _ _)]
  have hC := _root_.GlobalTheory.MixHt.iterDiv_symm k Y q hA M.B N.B M.isLB N.isLB s t hs ht hcov (T e L)
  rw [hL, hR, hC]
  rcases _root_.GlobalTheory.MixHt.amb_vertical_or_arithVar k Y q hA (e + 1 + 1) hdim with ⟨l, _, _, hno⟩ | ⟨e', he', hav⟩
  · have z₀ := _root_.GlobalTheory.MixHt.mixArch_resArch_eq_zero_of_noCxPts k Y q hno
    rw [(z₀ (e + 1) (Fin.cons N L) M).1, (z₀ (e + 1) (Fin.cons M L) N).1]
    simp only [(z₀ e L N).2, (z₀ e L M).2, mul_zero, finsum_zero]
  · obtain rfl : e' = e + 1 := by omega
    have hA' := hAR k Y q e hav M N L s t hs ht hcov
    linarith

end GlobalTheory.MixHt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLatticeStabiliserFixesVacuum
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.InertSph

theorem vac_fixed : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, Acts (evFin F v) (om (1, k)) (G.M.vac v) (G.M.vac v) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hin hvT k hk
  obtain ⟨hSB, hne, θ, hθ, hfix⟩ := hT.geo.hM.vac v
  obtain ⟨φ₁, hφ₁, hact⟩ := GlobalTheory.T.weilRepresentationLocality_unitaryGroupW_pairVW F E σ B a a' G X om om' hT v k hk.1 _ hSB
  have hfix₁ := GlobalTheory.T.weilOperator_latticeStabiliser_right_preserves_vacuumType F E σ B a a' G X om om' hT v k hk θ hθ _ hSB φ₁ hφ₁ hfix hact
  obtain ⟨c, rfl⟩ := GlobalTheory.T.heisenbergSelfDualLattice_fixedFunctions_line F E σ B a a' G X om om' hT v (hT.base.inert v w hin).2.2
    (GlobalTheory.T.tensorLattice_inertPlace_selfDual F E σ B a a' G X om om' hT v w hin) θ hθ _ hSB hne hfix φ₁ hφ₁ hfix₁
  have hc := GlobalTheory.T.latticeStabilizer_vacuum_eigenvalue_eq_one_inertPlace F E σ B a a' G X om om' hT v w hin hvT k hk c hact
  rw [hc, one_smul] at hact
  exact hact

end GlobalTheory.InertSph
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableLogNormSectionArithmeticVariety
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem intg_logSec_of_arithVar : GlobalTheory.Published.Principalisation → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (σ : k →+* ℂ) (L : Fin D → MLine p σ) (M : MLine p σ) (s : M.B.Sec), genericPoint X ∈ nonzeroLocus s → Intg L (M.logSec s) := by
  intro hP k _ X _ _ p D hX σ L M s hs
  have := hX.isDomain
  have := hX.finite
  have hσ : Function.Injective σ := by
    have hk : RingHom.ker σ = ⊥ := Ideal.eq_bot_of_comap_eq_bot (R := ℤ) (by
      ext n
      simp [Ideal.mem_comap, RingHom.mem_ker])
    exact (RingHom.injective_iff_ker_eq_bot σ).2 hk
  let K := FractionRing k
  obtain ⟨τ, rfl⟩ : ∃ τ : K →+* ℂ, σ = τ.comp (algebraMap k K) :=
    ⟨IsFractionRing.lift hσ, by ext a; simp⟩
  let G := Limits.pullback p (spMap (algebraMap k K))
  let j : G ⟶ X := Limits.pullback.fst _ _
  let q : G ⟶ Sp K := Limits.pullback.snd _ _
  have hp : IsPullback j q p (spMap (algebraMap k K)) := IsPullback.of_hasPullback _ _
  obtain ⟨hGi, hGn, hproj, hdim, hgen, -, hstalk, -, -⟩ := _root_.GlobalTheory.Mix.genericFibre_facts k K X G p q j hp D hX
  obtain ⟨s', hs', -, -, hlog⟩ := _root_.GlobalTheory.Mix.exists_sec_bc k K X G p q j hp τ hstalk M s hs hgen
  have h1 := _root_.GlobalTheory.Mix.logSec_intg_proj hP K G q τ D hproj hdim (fun i => (L i).bc hp.w τ) (M.bc hp.w τ) s' hs'
  have h2 := ((_root_.GlobalTheory.MixGen.part_int_generic k K X G p q j hp τ D hX L).2 (M.logSec s)).1
  refine h2.1 ?_
  have e : (M.bc hp.w τ).logSec s' = fun y => M.logSec s (bcPt hp.w τ y) := funext hlog
  rwa [e] at h1

end GlobalTheory.Mix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFramePointStalkCompat
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatValZero

section Gen

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions
  GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.FlatCore GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}

theorem nonempty_keySec (hL : Laws U x) : Nonempty (KeySec Xo c) := by
  obtain ⟨κ, k₁, k₂, -, k₄, -, k₆, -, -⟩ := GlobalTheory.KeyFamClosing.keyFam_one
  let e : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ) :=
    (Fintype.equivFin _).symm
  obtain ⟨K, hKmem, hKval⟩ := _root_.GlobalTheory.KeyFourth.exists_unit_secZ_keyRule κ k₁ k₂ k₆ E H Dw l Xo c _ e hL.pos
  have hσ0 := goodEmb_goodOf c c.F.val.toRingHom
  obtain ⟨ρ, -⟩ := GlobalTheory.T.exists_keySection_fourthRoot_perComponent κ k₁ k₂ k₆ k₄ E H Dw l Xo c _ e _ r (U _) K hσ0 (hL.unf _ hσ0) hL.geo hL.pos
    hKmem hKval
  exact ⟨ρ⟩

def unitsV (T : CDVR) : Submonoid T.Fr where
  carrier := {z | z ≠ 0 ∧ vV T.V z = 0}
  one_mem' := ⟨one_ne_zero, by simp [vV]⟩
  mul_mem' := fun {a b} ha hb => ⟨mul_ne_zero ha.1 hb.1, by rw [vV_mul ha.1 hb.1, ha.2, hb.2, add_zero]⟩

end Gen

end GlobalTheory.FlatValZero

open GlobalTheory.FlatValZero


end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantDifferentialsConnectedPDivGroupCoordinaStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantDifferentials_connectedPDivGroup_coordinates : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d), (∀ w : Fin d → k, (fun n => ∑ i, w i • dUnit (R := k) (c.x n i)) ∈ G.omegaSub) ∧ ∀ u : G.omega, ∃! w : Fin d → k, ∀ n, u.1 n = ∑ i, w i • dUnit (R := k) (c.x n i) := by
  first | exact @GlobalTheory.OmegaCoord.omega_coord | exact GlobalTheory.OmegaCoord.omega_coord | (intros; apply GlobalTheory.OmegaCoord.omega_coord <;> assumption)
end

