module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2752
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2206
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1193
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2362
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1173
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2607
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2338
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1148
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1163
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1011
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2569
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2753
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2729
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2700
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0476
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2550
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2755
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2565
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2564
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2642
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2757
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2597
public import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0919

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankLeGeometricDegreeOfIsNef
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

namespace GlobalTheory.HSNef.RankNef

theorem rank_le_gdeg_of_isNef : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), P.L.IsNef D → ∀ (J : Type) [Fintype J] (e : J → X.functionField) (x : Fin D → X.functionField), LinearIndependent ℤ e → AlgebraicIndependent ℤ x → (∀ c, boxFam e x c ∈ P.H 1 0) → (D.factorial : ℝ) * Fintype.card J ≤ gdeg P.L D := by
  intro hAr hHS k _ X _ p D hX P hL J _ e x he hx hbox
  have hcz : CharZero X.functionField := by
    have := hX.charZero
    exact ((X.germToFunctionField ⊤).hom.charZero_iff (X.germToFunctionField_injective ⊤)).1 this
  have htb : IsTranscendenceBasis ℤ x := (_root_.GlobalTheory.ArithTrdeg.isTranscendenceBasis_functionField k X p D hX).2 x hx
  obtain ⟨A, hAamp, hAnef, s, hs, hs0⟩ := GlobalTheory.AmpleNefSmall.exists_ample_nef_smallSec hAr k X p D hX
  obtain ⟨r', hr'⟩ := exists_isRatSec A.isLB
  let Q : Pair p := ⟨P.L, A, P.r, r', P.hr, hr'⟩
  have hQbox : ∀ c, boxFam e x c ∈ Q.H 1 0 := by
    intro c z i j hi _
    obtain ⟨j', hj'⟩ : ∃ j', z ∈ P.A.B.U j' := by
      have h1 : z ∈ (⨆ j, P.A.B.U j) := by rw [P.A.isLB.cover]; trivial
      exact TopologicalSpace.Opens.mem_iSup.1 h1
    have h2 := hbox c z i j' hi hj'
    simpa [Pair.loc, Q] using h2
  have hbd : ∀ c, ∃ u : ℝ, 0 ≤ u ∧ boxFam e x c ∈ Q.Bl 1 0 (Real.exp u) :=
    fun c => _root_.GlobalTheory.HSNef.bounded_norm k X p D hX Q 1 0 _ (hQbox c)
  choose u hu0 hu using hbd
  set t₀ : ℝ := ∑ c, u c with ht₀
  have ht₀0 : 0 ≤ t₀ := Finset.sum_nonneg fun c _ => hu0 c
  have hBl : ∀ c, boxFam e x c ∈ Q.Bl 1 0 (Real.exp t₀) := fun c =>
    ⟨(hu c).1, fun σ y => ((hu c).2 σ y).trans
      (Real.exp_le_exp.2 (Finset.single_le_sum (fun c _ => hu0 c) (Finset.mem_univ c)))⟩
  obtain ⟨ε, hεinj, hεrange, hεnu, -⟩ := RepDict.rep_dict k X p Q 0 1 Q.A (Pair.rep_base k X p Q).2.1
  have hsm : ∀ w ∈ A.smallSec, ε w ∈ Q.Bl 0 1 1 := by
    intro w hw
    refine ⟨?_, fun σ y => ?_⟩
    · rw [← SetLike.mem_coe, ← hεrange]; exact ⟨w, rfl⟩
    · have hnn : 0 ≤ Q.nu 0 1 σ y (ε w) := by
        unfold Pair.nu; exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
      have h2 : Q.nu 0 1 σ y (ε w) ^ 2 ≤ 1 := by rw [hεnu]; exact hw σ y
      exact (pow_le_one_iff_of_nonneg hnn two_ne_zero).1 h2
  obtain ⟨g, hg, hg0⟩ : ∃ g ∈ Q.Bl 0 1 1, g ≠ 0 := by
    by_cases h : ε s = 0
    · refine ⟨ε 0, hsm 0 (HermLB.zero_mem_smallSec _), fun h0 => hs0 ?_⟩
      exact (hεinj (h0.trans h.symm)).symm
    · exact ⟨ε s, hsm s hs, h⟩
  have key : ∀ n : ℕ, 0 < n →
      (D.factorial : ℝ) * ((Fintype.card J * n ^ D : ℕ) : ℝ) ≤ gdeg ((P.L.pow n).tens A) D := by
    intro n hn
    have hrep : Q.Rep (n : ℤ) 1 ((Q.L.pow n).tens Q.A) := by
      have h1 := Pair.rep_pow k X p Q 1 0 Q.L n (Pair.rep_base k X p Q).1
      have h2 := Pair.rep_tens k X p Q _ _ 0 1 _ _ h1 (Pair.rep_base k X p Q).2.1
      simpa using h2
    have hamp : IsAmpleLB ((P.L.pow n).tens A).B :=
      _root_.GlobalTheory.AmpleNefFibZ.isAmpleLB_tens_of_nefFib k X p D hX (P.L.pow n) A
        (nefFib_of_isNef (GlobalTheory.NefPow.isNef_pow hAr k X p D hX P.L n hL)) hAamp
    have hsp : ((P.L.pow n).tens A).SemiPos D := (hL.semiPos.pow n).tens hAnef.semiPos
    have hvec : ∀ m : ℕ, 0 < m → ∃ v : Fin ((Fintype.card J * n ^ D) * m ^ D) → X.functionField,
        LinearIndependent ℤ v ∧ ∀ i, v i ∈ Q.Bl (m * (n : ℤ)) (m * 1) (Real.exp ((t₀ * n) * m)) := by
      intro m hm
      obtain ⟨v0, hv0, hv0s⟩ := _root_.GlobalTheory.many_independent_products_in_function_field X.functionField D x htb J e he (n * m) (Nat.mul_pos hn hm)
      have hcard : Fintype.card J * (n * m) ^ D = (Fintype.card J * n ^ D) * m ^ D := by rw [mul_pow]; ring
      have hgm : g ^ m ∈ Q.H ((m : ℤ) * 0) ((m : ℤ) * 1) :=
        (NuPow.pow_mem_H_and_nu_pow k X p Q 0 1 g hg.1 m).1
      have hgm0 : g ^ m ≠ 0 := pow_ne_zero _ hg0
      refine ⟨fun i => v0 (Fin.cast hcard.symm i) * g ^ m, ?_, fun i => ?_⟩
      · have hli := hv0.map' (LinearMap.mulRight ℤ (g ^ m))
          (LinearMap.ker_eq_bot.2 (mul_left_injective₀ hgm0))
        exact hli.comp _ (Fin.cast_injective _)
      · obtain ⟨w, a, ha, hw⟩ := hv0s (Fin.cast hcard.symm i)
        have hprod := _root_.GlobalTheory.HSNef.BoxProd.prod_mem_Bl k X p Q D J e x 1 0 (Real.exp t₀) (Real.exp_pos _).le hBl (n * m) w a ha
        rw [← hw] at hprod
        obtain ⟨hmem, hnu⟩ := NuMul.mul_mem_H_and_nu_mul k X p Q _ _ _ _ _ _ hprod.1 hgm
        have e1 : (((n * m : ℕ) : ℤ) * 1 + (m : ℤ) * 0) = (m : ℤ) * n := by push_cast; ring
        have e2 : (((n * m : ℕ) : ℤ) * 0 + (m : ℤ) * 1) = (m : ℤ) * 1 := by push_cast; ring
        rw [e1, e2] at hmem hnu
        refine ⟨hmem, fun σ y => ?_⟩
        rw [hnu, (NuPow.pow_mem_H_and_nu_pow k X p Q 0 1 g hg.1 m).2 σ y]
        have hA1 := hprod.2 σ y
        have hB1 : Q.nu 0 1 σ y g ^ m ≤ 1 := by
          have hnn : 0 ≤ Q.nu 0 1 σ y g := by
            unfold Pair.nu; exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
          exact pow_le_one₀ hnn (hg.2 σ y)
        have hnn' : 0 ≤ Q.nu ((n * m : ℕ) * 1) ((n * m : ℕ) * 0) σ y (v0 (Fin.cast hcard.symm i)) := by
          unfold Pair.nu; exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
        have hexp : Real.exp t₀ ^ (n * m) = Real.exp ((t₀ * n) * m) := by
          rw [← Real.exp_nat_mul]; push_cast; ring_nf
        calc _ ≤ Real.exp t₀ ^ (n * m) * 1 := mul_le_mul hA1 hB1 (pow_nonneg (by unfold Pair.nu; exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le) _) (pow_nonneg (Real.exp_pos _).le _)
          _ = _ := by rw [mul_one, hexp]
    have := _root_.GlobalTheory.HSNef.factorial_mul_le_gdeg_of_indep hAr hHS k X p D hX Q n 1 _ hrep hamp hsp (Fintype.card J * n ^ D) (t₀ * n) hvec
    exact this
  have hlim := _root_.GlobalTheory.DegGrowth.main hAr k X p D hX P.L A
  refine ge_of_tendsto hlim ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnD : (0 : ℝ) < (n : ℝ) ^ D := by positivity
  rw [le_div_iff₀ hnD]
  have := key n hn
  push_cast at this
  nlinarith [this]

end GlobalTheory.HSNef.RankNef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReciprocityDefectAddBundleSection
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DefectAdd

theorem compactSpace_of_projOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsProjOver f) : CompactSpace X := by
  obtain ⟨m, i, hi, rfl⟩ := h
  have := isProper_str R m
  have : IsProper (i ≫ PSpace.str R m) := inferInstance
  exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str R m)

theorem int_eq_add_of_ae {k : Type} [CommRing k] {Y : Scheme.{0}} {q : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    (L : Fin D → MLine q σ) {f g h : CxPts q σ → ℝ} (hf : Intg L f) (hg : Intg L g)
    (hh : ∀ ε : ℤˣ, ∀ᵐ y ∂part L ε, h y = f y + g y) :
    Mix.int L h = Mix.int L f + Mix.int L g := by
  simp only [Mix.int]
  rw [integral_congr_ae (hh 1), integral_congr_ae (hh (-1)), integral_add hf.1 hg.1, integral_add hf.2 hg.2]
  ring

theorem defect_add : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (L : Fin e → MLine p σ) (M A N : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (a : A.B.Sec) (ha : genericPoint X ∈ nonzeroLocus a) (t : N.B.Sec) (ht : genericPoint X ∈ nonzeroLocus t), (∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ⊓ nonzeroLocus a ∨ z ∈ nonzeroLocus t) → ∃ (s₁ : (M.tens A).B.Sec) (h₁ : genericPoint X ∈ nonzeroLocus s₁), nonzeroLocus s₁ = nonzeroLocus s ⊓ nonzeroLocus a ∧ side N L ((M.tens A).logSec s₁) (N.logSec t) (divOfSec (M.tens A).φ.isLB s₁ h₁) - side (M.tens A) L (N.logSec t) ((M.tens A).logSec s₁) (divOfSec N.φ.isLB t ht) = (side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) - side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht)) + (side N L (A.logSec a) (N.logSec t) (divOfSec A.φ.isLB a ha) - side A L (N.logSec t) (A.logSec a) (divOfSec N.φ.isLB t ht)) := by
  intro hP F _ X _ _ p σ e hproj hdim L M A N s hs a ha t ht hcod
  obtain ⟨s₁, h₁, hloc, hmult, hlog⟩ := _root_.GlobalTheory.Mix.exists_sec_tens F X p σ M A s hs a ha
  refine ⟨s₁, h₁, hloc, ?_⟩
  have hσ : Function.Injective σ := σ.injective
  haveI : CompactSpace X := compactSpace_of_projOver hproj
  have iM := _root_.GlobalTheory.Mix.logSec_intg_proj hP F X p σ (e + 1) hproj hdim (Fin.cons N L) M s hs
  have iA := _root_.GlobalTheory.Mix.logSec_intg_proj hP F X p σ (e + 1) hproj hdim (Fin.cons N L) A a ha
  have iMh := _root_.GlobalTheory.Mix.logSec_intg_proj hP F X p σ (e + 1) hproj hdim (Fin.cons M L) N t ht
  have iAh := _root_.GlobalTheory.Mix.logSec_intg_proj hP F X p σ (e + 1) hproj hdim (Fin.cons A L) N t ht
  have e1 : Mix.int (Fin.cons N L : Fin (e + 1) → MLine p σ) ((M.tens A).logSec s₁) =
      Mix.int (Fin.cons N L : Fin (e + 1) → MLine p σ) (M.logSec s) +
        Mix.int (Fin.cons N L : Fin (e + 1) → MLine p σ) (A.logSec a) := by
    refine int_eq_add_of_ae _ iM iA fun ε => ?_
    have h0 := _root_.GlobalTheory.MixNull.part_compl_null F X p σ hσ hproj (e + 1) (Fin.cons N L) ε (nonzeroLocus s₁) h₁
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with y hy
    exact hlog y (by simpa using hy)
  have e2 : Mix.int (Fin.cons (M.tens A) L : Fin (e + 1) → MLine p σ) (N.logSec t) =
      Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) (N.logSec t) +
        Mix.int (Fin.cons A L : Fin (e + 1) → MLine p σ) (N.logSec t) := by
    have key := _root_.GlobalTheory.Mix.int_update_tens F X p σ hproj (e + 1) (Fin.cons M L) 0 M A (N.logSec t)
      (by simpa only [Fin.update_cons_zero] using iMh) (by simpa only [Fin.update_cons_zero] using iAh)
    simpa only [Fin.update_cons_zero] using key.2
  have e3 : ∑ᶠ z, ((divOfSec (M.tens A).φ.isLB s₁ h₁).mult z : ℝ) * cycInt L (N.logSec t) z =
      ∑ᶠ z, ((divOfSec M.φ.isLB s hs).mult z : ℝ) * cycInt L (N.logSec t) z +
        ∑ᶠ z, ((divOfSec A.φ.isLB a ha).mult z : ℝ) * cycInt L (N.logSec t) z := by
    rw [← finsum_add_distrib]
    · refine finsum_congr fun z => ?_
      rw [hmult z]
      push_cast
      ring
    · exact (divOfSec M.φ.isLB s hs).finite_support_mult.subset fun z hz h0 => hz (by simp [h0])
    · exact (divOfSec A.φ.isLB a ha).finite_support_mult.subset fun z hz h0 => hz (by simp [h0])
  have e4 : ∑ᶠ z, ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L ((M.tens A).logSec s₁) z =
      ∑ᶠ z, ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L (M.logSec s) z +
        ∑ᶠ z, ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L (A.logSec a) z := by
    rw [← finsum_add_distrib]
    · refine finsum_congr fun z => ?_
      by_cases hz : (divOfSec N.φ.isLB t ht).mult z = 0
      · simp [hz]
      · rw [← mul_add]
        congr 1
        have hco := CartierDiv.coheight_eq_one_of_mult_ne_zero hz
        have hzt : z ∉ nonzeroLocus t := fun h =>
          (notMem_supp_divOfSec.2 h) (CartierDiv.mem_supp_of_mult_ne_zero hz)
        have hz1 : z ∈ nonzeroLocus s ⊓ nonzeroLocus a := (hcod z hco).resolve_right hzt
        have hz1' := TopologicalSpace.Opens.mem_inf.1 hz1
        have hzs₁ : z ∈ nonzeroLocus s₁ := hloc ▸ hz1
        have hdimz := (_root_.GlobalTheory.FieldDimCoheight.coheight_eq_one_iff F X p e hproj hdim z).1 hco
        obtain ⟨-, -, hnull, hint⟩ := _root_.GlobalTheory.CycFin.cycle_facts hP F X p σ hproj e L z hdimz
        refine int_eq_add_of_ae _ (hint M s hz1'.1) (hint A a hz1'.2) fun ε => ?_
        filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hnull _ hzs₁ ε)] with y hy
        exact hlog _ (by simpa using hy)
    · exact (divOfSec N.φ.isLB t ht).finite_support_mult.subset fun z hz h0 => hz (by simp [h0])
    · exact (divOfSec N.φ.isLB t ht).finite_support_mult.subset fun z hz h0 => hz (by simp [h0])
  simp only [side]
  rw [e1, e2, e3, e4]
  ring

end GlobalTheory.DefectAdd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReciprocityDefectIndependentFirstMetric
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MetricIndep

theorem compactSpace_of_projOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsProjOver f) : CompactSpace X := by
  obtain ⟨m, i, hi, rfl⟩ := h
  have := isProper_str R m
  have : IsProper (i ≫ PSpace.str R m) := inferInstance
  exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str R m)

theorem int_sub_half {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    (L : Fin D → MLine p σ) {f v : CxPts p σ → ℝ} (hf : Intg L f) (hv : Intg L v) :
    Mix.int L (fun y => f y - v y / 2) = Mix.int L f - Mix.int L v / 2 := by
  unfold Mix.int
  rw [integral_sub hf.1 (hv.1.div_const 2), integral_sub hf.2 (hv.2.div_const 2),
    integral_div, integral_div]
  ring

theorem upd_cons {α : Type*} {n : ℕ} (a b : α) (L : Fin n → α) :
    Function.update (Fin.cons a L : Fin (n + 1) → α) 0 b = Fin.cons b L :=
  Fin.update_cons_zero (α := fun _ => α) a L b

theorem side_sub_side_addFn : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (L : Fin e → MLine p σ) (M N : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (t : N.B.Sec) (ht : genericPoint X ∈ nonzeroLocus t), (∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → ∀ (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y), side N L ((M.addFn u hu).logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) - side (M.addFn u hu) L (N.logSec t) ((M.addFn u hu).logSec s) (divOfSec N.φ.isLB t ht) = side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) - side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht) := by
  intro hP F _ X _ _ p σ e hproj hdim L M N s hs t ht hcod u hu
  have hσ : Function.Injective σ := σ.injective
  have hcont : Continuous u := continuous_iff_continuousAt.2 fun y => (hu y).continuousAt
  have hcomp : CompactSpace X := compactSpace_of_projOver hproj
  obtain ⟨-, -, -, hlog⟩ := GlobalTheory.Mix.SecNorm.logSec_basic F X p σ M s

  have hA : Mix.int (Fin.cons N L : Fin (e + 1) → MLine p σ) ((M.addFn u hu).logSec s) =
      Mix.int (Fin.cons N L : Fin (e + 1) → MLine p σ) (M.logSec s) -
        Mix.int (Fin.cons N L : Fin (e + 1) → MLine p σ) u / 2 := by
    have hae : ∀ ε : ℤˣ, (M.addFn u hu).logSec s =ᵐ[part (Fin.cons N L : Fin (e + 1) → MLine p σ) ε]
        fun y => M.logSec s y - u y / 2 := by
      intro ε
      refine ae_iff.2 (measure_mono_null (fun y hy => ?_)
        (GlobalTheory.MixNull.part_compl_null F X p σ hσ hproj (e + 1) (Fin.cons N L) ε (nonzeroLocus s) hs))
      exact fun hy' => hy (hlog u hu y hy')
    have hf := _root_.GlobalTheory.Mix.logSec_intg_proj hP F X p σ (e + 1) hproj hdim (Fin.cons N L) M s hs
    have hv := (_root_.GlobalTheory.MixFin.finite_and_intg hP F X p σ (e + 1) hproj hdim (Fin.cons N L)).2 u hcont
    rw [← int_sub_half _ hf hv]
    unfold Mix.int
    rw [integral_congr_ae (hae 1), integral_congr_ae (hae (-1))]

  have hB : Mix.int (Fin.cons (M.addFn u hu) L : Fin (e + 1) → MLine p σ) (N.logSec t) =
      Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) (N.logSec t) +
        Mix.int (Fin.cons (MLine.ofFun u hu) L : Fin (e + 1) → MLine p σ) (N.logSec t) := by
    obtain ⟨hrefl, -, -, -, haddFn, -⟩ := GlobalTheory.Mix.isom_calculus F X X p p σ (𝟙 X) (Category.id_comp p)
    have hpart : ∀ ε : ℤˣ, part (Fin.cons (M.addFn u hu) L : Fin (e + 1) → MLine p σ) ε =
        part (Fin.cons (M.tens (MLine.ofFun u hu)) L : Fin (e + 1) → MLine p σ) ε :=
      GlobalTheory.Mix.part_eq_of_isom F X p σ hproj (e + 1) _ _ fun i => Fin.cases (haddFn M u hu) (fun j => hrefl (L j)) i
    have h1 := _root_.GlobalTheory.Mix.logSec_intg_proj hP F X p σ (e + 1) hproj hdim (Fin.cons M L) N t ht
    have h2 := _root_.GlobalTheory.Mix.logSec_intg_proj hP F X p σ (e + 1) hproj hdim (Fin.cons (MLine.ofFun u hu) L) N t ht
    have hadd := _root_.GlobalTheory.Mix.int_update_tens F X p σ hproj (e + 1) (Fin.cons M L : Fin (e + 1) → MLine p σ) 0 M
      (MLine.ofFun u hu) (N.logSec t)
    rw [upd_cons, upd_cons, upd_cons] at hadd
    replace hadd := hadd h1 h2
    rw [← hadd.2]
    unfold Mix.int
    rw [hpart, hpart]

  have hC : ∀ z, ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L ((M.addFn u hu).logSec s) z =
      ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L (M.logSec s) z -
        ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L u z / 2 := by
    intro z
    by_cases h : (divOfSec N.φ.isLB t ht).mult z = 0
    · simp [h]
    have hz1 := CartierDiv.coheight_eq_one_of_mult_ne_zero h
    have hzs : z ∈ nonzeroLocus s := (hcod z hz1).resolve_right fun hzt =>
      (notMem_supp_divOfSec.2 hzt) (CartierDiv.mem_supp_of_mult_ne_zero h)
    have hdz := (GlobalTheory.FieldDimCoheight.coheight_eq_one_iff F X p e hproj hdim z).1 hz1
    obtain ⟨-, hcc, hnull, hlc⟩ := _root_.GlobalTheory.CycFin.cycle_facts hP F X p σ hproj e L z hdz
    have hae : ∀ ε : ℤˣ, (fun y => (M.addFn u hu).logSec s (ptMap (closι z) rfl σ y)) =ᵐ[part (fun i => (L i).pull (closι z) rfl) ε]
        fun y => M.logSec s (ptMap (closι z) rfl σ y) - u (ptMap (closι z) rfl σ y) / 2 := by
      intro ε
      refine ae_iff.2 (measure_mono_null (fun y hy => ?_) (hnull (nonzeroLocus s) hzs ε))
      exact fun hy' => hy (hlog u hu _ hy')
    have hcyc : cycInt L ((M.addFn u hu).logSec s) z = cycInt L (M.logSec s) z - cycInt L u z / 2 := by
      have e2 := int_sub_half (fun i => (L i).pull (closι z) rfl) (hlc M s hzs) (hcc u hcont)
      unfold cycInt
      rw [← e2]
      unfold Mix.int
      rw [integral_congr_ae (hae 1), integral_congr_ae (hae (-1))]
    rw [hcyc]
    ring
  have hfs := CartierDiv.finite_support_mult (divOfSec N.φ.isLB t ht)
  have hsub : ∀ g : X → ℝ, (Function.support fun z => ((divOfSec N.φ.isLB t ht).mult z : ℝ) * g z).Finite :=
    fun g => hfs.subset fun z hz h0 => hz (by simp [h0])
  have hsum : ∑ᶠ z, ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L ((M.addFn u hu).logSec s) z =
      ∑ᶠ z, ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L (M.logSec s) z -
        (∑ᶠ z, ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L u z) / 2 := by
    simp only [hC]
    rw [div_eq_mul_inv, finsum_mul]
    exact finsum_sub_distrib (hsub _) ((hsub (fun z => cycInt L u z)).subset fun z hz h0 => hz (by
      have h1 : ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L u z = 0 := h0
      simp only [h1, zero_div]))
  have hPL := _root_.GlobalTheory.poincareLelong_sec hP F X p σ e hproj hdim L N t ht u hu
  simp only [side]
  rw [hA, hB, hsum]
  linarith

end GlobalTheory.MetricIndep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDescendsOfDescendsNearClosedFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem descend_of_near : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) →
    ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G']
    [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', N.Law → ∃ (G : Over (Sp R)) (_ : GrpObj G)
    (_ : IsCommMonObj G) (β : G'.left ⟶ G.left) (i : N.U ⟶ G), IsSemiAbelian G ∧ IsGrpPullback G' G π β ∧
    IsOpenImmersion i.left ∧ N.u ≫ β = pullback.fst _ _ ≫ i.left := by
  intro R _ _ _ hA S π hP hS hI G' _ _ hG' N hL
  have hNoeth : IsNoetherianRing R := hA.1
  have hIC : IsIntegrallyClosed R := hA.2.2.1
  obtain ⟨φ, hφ⟩ := _root_.GlobalTheory.Mum.Desc.exists_datum R hA S π hP hS hI G' hG' N hL
  obtain ⟨G, β, i, hsm, hpb, hop, hu, hc⟩ := _root_.GlobalTheory.Mum.descends_near_closed_fibre R hA S π hP hS hI G' hG' N hL φ hφ
  obtain ⟨g, c, hsa, hgp⟩ := _root_.GlobalTheory.DescGrp.exists_semiAbelian_descent R S π hP hS hI G' hG' G β hsm hpb φ hφ.1 hc
  exact ⟨G, g, c, β, i, hsa, hgp, hop, hu⟩

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetAtOfSizeAt
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim

namespace GlobalTheory.BigTop.Fun.SetFromSize

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem finite_tup (p : PtAt ex Csz) : Finite p.P.T := by
  classical
  have h1 := p.charW.tup.mu_off
  have h2 := p.charW.tup.mu_used
  have : (Set.univ : Set p.P.T) ⊆ insert p.P.A3.A.μ0 (p.R.mu '' (p.R.twPl : Set _)) := fun t _ => by
    rcases h2 t with h | ⟨w, rfl⟩
    · exact Or.inl h
    · by_cases hw : w ∈ p.R.twPl
      · exact Or.inr ⟨w, hw, rfl⟩
      · exact Or.inl (h1 w hw)
  exact Set.finite_univ_iff.1 ((((p.R.twPl).finite_toSet.image _).insert _).subset this)


end GlobalTheory.BigTop.Fun.SetFromSize

namespace GlobalTheory.BigTop.Fun

end GlobalTheory.BigTop.Fun

end
end

