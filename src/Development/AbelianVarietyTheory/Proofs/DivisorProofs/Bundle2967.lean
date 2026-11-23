module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1148
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2713
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2940
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2643
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHilbertSamuelLowerBoundCountRankAmple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2780
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2786
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2789
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2583
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2945
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2664
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2663
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2539
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2824
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2944
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0590
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2620
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2942
public import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2482
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2949
public import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AdmissibleBaseChartRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOfMemClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGoodSectionGroupFamilyAmpleMultiples
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp.GoodH

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem mem_H_of_eq (P : Pair p) {a a' b b' : ℤ} {f : X.functionField} (ha : a = a') (hb : b = b')
    (h : f ∈ P.H a b) : f ∈ P.H a' b' := by
  subst ha hb; exact h

theorem nu_nonneg (P : Pair p) (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) : 0 ≤ P.nu a b σ y f := by
  rw [Pair.nu]; positivity

theorem mono_mem {D : ℕ} (P : Pair p) (e : ℕ) (x : Fin (D + 1) → X.functionField) (hx : ∀ l, x l ∈ P.H e 0)
    (a b : ℤ) (g : X.functionField) (hg : g ∈ P.H a b) (α : Fin (D + 1) → ℕ) (S : Finset (Fin (D + 1))) :
    (∏ l ∈ S, x l ^ α l) * g ∈ P.H ((e : ℤ) * ((∑ l ∈ S, α l : ℕ) : ℤ) + a) b ∧
      ∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu ((e : ℤ) * ((∑ l ∈ S, α l : ℕ) : ℤ) + a) b σ y ((∏ l ∈ S, x l ^ α l) * g) =
        (∏ l ∈ S, P.nu e 0 σ y (x l) ^ α l) * P.nu a b σ y g := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty, one_mul, Nat.cast_zero, mul_zero, zero_add]
    exact ⟨hg, fun _ _ => trivial⟩
  | @insert j S hj ih =>
    obtain ⟨hp1, hp2⟩ := GlobalTheory.VolBr.NuPow.pow_mem_H_and_nu_pow k X p P (e : ℤ) 0 (x j) (hx j) (α j)
    obtain ⟨hm1, hm2⟩ := GlobalTheory.VolBr.NuMul.mul_mem_H_and_nu_mul k X p P _ _ _ _ _ _ hp1 ih.1
    have ea : ((α j : ℕ) : ℤ) * (e : ℤ) + ((e : ℤ) * ((∑ l ∈ S, α l : ℕ) : ℤ) + a) =
        (e : ℤ) * ((∑ l ∈ insert j S, α l : ℕ) : ℤ) + a := by
      rw [Finset.sum_insert hj]; push_cast; ring
    have eb : ((α j : ℕ) : ℤ) * 0 + b = b := by ring
    rw [ea, eb] at hm1 hm2
    have ep : (∏ l ∈ insert j S, x l ^ α l) * g = x j ^ α j * ((∏ l ∈ S, x l ^ α l) * g) := by
      rw [Finset.prod_insert hj, mul_assoc]
    rw [ep]
    refine ⟨hm1, fun σ y => ?_⟩
    rw [hm2, hp2, ih.2, Finset.prod_insert hj, mul_assoc]

end GlobalTheory.HSAmp.GoodH

namespace GlobalTheory.HSAmp.GoodH

theorem goodFam_H : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → GoodFam P D (gdeg P.L D / D.factorial) fun m => P.H m 1 := by
  intro hAr k _ X _ p D hX P hL
  obtain ⟨e, x, hx⟩ := GlobalTheory.T.exists_basepointFreeSectionTuple_ample_arith k X p D hX P hL
  have he : 0 < e := hx.pos

  have hup : ∀ s : ℕ, ∃ c : ℕ, ∀ q : ℕ, (P.H ((e * q + s : ℕ) : ℤ) 1).FG ∧
      Module.finrank ℤ (P.H ((e * q + s : ℕ) : ℤ) 1) ≤
        Module.finrank (ratF x) X.functionField * (q + c + D).choose D := by
    intro s
    obtain ⟨c, C, -, h⟩ := _root_.GlobalTheory.HSAmp.HSUpper.upper_bound k X p D hX P hL e x hx (s : ℤ) 1
    refine ⟨c, fun q => ?_⟩
    have e1 : ((e * q + s : ℕ) : ℤ) = (e : ℤ) * (q : ℤ) + (s : ℤ) := by push_cast; ring
    rw [e1]
    exact ⟨(h q).1, (h q).2.1⟩

  have hlow : ∀ s : ℕ, ∃ c : ℕ, ∀ q : ℕ, Module.finrank (ratF x) X.functionField * (q + D).choose D ≤
      Module.finrank ℤ (P.H ((e * (q + c) + s : ℕ) : ℤ) 1) := by
    intro s
    obtain ⟨c, C, -, h⟩ := _root_.GlobalTheory.HSAmp.FLower.count_rank_lower k X p D hX P hL e x hx (s : ℤ) 1
    obtain ⟨c', hc'⟩ := hup s
    refine ⟨c, fun q => ?_⟩
    obtain ⟨v, hv, hli⟩ := (h q).1
    have e1 : ((e * (q + c) + s : ℕ) : ℤ) = (e : ℤ) * ((q + c : ℕ) : ℤ) + (s : ℤ) := by push_cast; ring
    have hfg := (hc' (q + c)).1
    rw [e1] at hfg ⊢
    haveI : Module.Finite ℤ (P.H ((e : ℤ) * ((q + c : ℕ) : ℤ) + (s : ℤ)) 1) :=
      Module.Finite.iff_addGroup_fg.2 ((AddGroup.fg_iff_addSubgroup_fg _).2 hfg)
    let w : Fin (Module.finrank (ratF x) X.functionField * (q + D).choose D) →
        P.H ((e : ℤ) * ((q + c : ℕ) : ℤ) + (s : ℤ)) 1 := fun i => ⟨v i, hv i⟩
    have hw : LinearIndependent ℤ w :=
      LinearIndependent.of_comp (P.H ((e : ℤ) * ((q + c : ℕ) : ℤ) + (s : ℤ)) 1).subtype.toIntLinearMap hli
    simpa using hw.fintype_card_le_finrank
  have hrank := GlobalTheory.T.tendsto_div_pow_of_choose_bounds D e (Module.finrank (ratF x) X.functionField)
    (fun m => Module.finrank ℤ (P.H (m : ℤ) 1)) he (fun s _ => by
      obtain ⟨c, hc⟩ := hlow s
      obtain ⟨c', hc'⟩ := hup s
      exact ⟨c, c', fun q => ⟨hc q, (hc' q).2⟩⟩)
  have hdeg := _root_.GlobalTheory.HSAmp.finrank_ratF_eq_gdeg hAr k X p D hX P hL e x hx
  have hg : (Module.finrank (ratF x) X.functionField : ℝ) / ((e : ℝ) ^ D * D.factorial) = gdeg P.L D / D.factorial := by
    have : (e : ℝ) ^ D ≠ 0 := pow_ne_zero _ (by exact_mod_cast he.ne')
    rw [hdeg]
    exact mul_div_mul_left _ _ this

  have hkey : ∀ s : ℕ, ∃ C : ℝ, 1 ≤ C ∧ ∀ q : ℕ, 1 ≤ e * q + s →
      P.H ((e * q + s : ℕ) : ℤ) 1 ≤
        AddSubgroup.closure (ballIn P (P.H ((e * q + s : ℕ) : ℤ) 1) ((e * q + s : ℕ) : ℤ) 1 (C ^ (e * q + s))) := by
    intro s
    classical
    obtain ⟨c, w, Cr, -, hrep⟩ := _root_.GlobalTheory.HSRep.sections_eq_sum_aeval_bounded k X p D hX P hL e x hx (s : ℤ) 1
    let Λ : ℕ → AddSubgroup X.functionField := fun q => P.H ((e : ℤ) * (q : ℤ) + (s : ℤ)) 1
    have hmul : ∀ q l, ∀ f ∈ Λ q, x l * f ∈ Λ (q + 1) := by
      intro q l f hf
      have h := (GlobalTheory.VolBr.NuMul.mul_mem_H_and_nu_mul k X p P _ _ _ _ _ _ (hx.mem l) hf).1
      show x l * f ∈ P.H _ 1
      exact mem_H_of_eq P (by push_cast; ring) (by ring) h
    have hrepr : ∀ q, ∀ f ∈ Λ q, ∃ T : Fin (Module.finrank (ratF x) X.functionField) → MvPolynomial (Fin (D + 1)) ℤ,
        (∀ i, (T i).IsHomogeneous (q + c)) ∧ f = ∑ i, MvPolynomial.aeval x (T i) * w i := by
      intro q f hf
      obtain ⟨T, h1, h2, -⟩ := hrep q f hf
      exact ⟨T, h1, h2⟩
    obtain ⟨G, hG, hcl⟩ := _root_.GlobalTheory.HSAmpGen.exists_finite_homogeneous_generators X.functionField D c x _ w Λ hmul hrepr
    have hb : ∀ (a b : ℤ) (f : X.functionField), f ∈ P.H a b → ∃ C : ℝ, 0 ≤ C ∧ ∀ σ y, P.nu a b σ y f ≤ C := by
      intro a b f hf
      obtain ⟨C, hC⟩ := ((_root_.GlobalTheory.HSAmp.continuous_val_and_bounded k X p D hX P a b).2 f hf).2
      exact ⟨|C|, abs_nonneg _, fun σ y => (hC σ y).trans (le_abs_self _)⟩
    choose Cx hCx0 hCx using fun l => hb _ _ _ (hx.mem l)
    have hbG : ∀ g : ℕ × X.functionField, ∃ C : ℝ, 0 ≤ C ∧
        (g ∈ G → ∀ σ y, P.nu ((e : ℤ) * (g.1 : ℤ) + s) 1 σ y g.2 ≤ C) := by
      intro g
      by_cases hg : g ∈ G
      · obtain ⟨C, hC0, hC⟩ := hb _ _ _ (hG g hg)
        exact ⟨C, hC0, fun _ => hC⟩
      · exact ⟨0, le_rfl, fun h => absurd h hg⟩
    choose Cg hCg0 hCg using hbG
    have hC1 : 1 ≤ 1 + ∑ l, Cx l := le_add_of_nonneg_right (Finset.sum_nonneg fun l _ => hCx0 l)
    have hC2 : 1 ≤ 1 + ∑ g ∈ G, Cg g := le_add_of_nonneg_right (Finset.sum_nonneg fun g _ => hCg0 g)
    have hxl : ∀ l σ y, P.nu e 0 σ y (x l) ≤ 1 + ∑ l, Cx l := fun l σ y => (hCx l σ y).trans (by
      have := Finset.single_le_sum (fun j _ => hCx0 j) (Finset.mem_univ l); linarith)
    have hgl : ∀ g ∈ G, ∀ σ y, P.nu ((e : ℤ) * (g.1 : ℤ) + s) 1 σ y g.2 ≤ 1 + ∑ g ∈ G, Cg g :=
      fun g hg σ y => (hCg g hg σ y).trans (by
        have := Finset.single_le_sum (fun j _ => hCg0 j) hg; linarith)
    refine ⟨(1 + ∑ l, Cx l) * (1 + ∑ g ∈ G, Cg g), one_le_mul_of_one_le_of_one_le hC1 hC2, fun q hq => ?_⟩
    have e1 : ((e * q + s : ℕ) : ℤ) = (e : ℤ) * (q : ℤ) + (s : ℤ) := by push_cast; ring
    rw [e1]
    refine (hcl q).trans (AddSubgroup.closure_mono ?_)
    rintro f ⟨g, hg, α, hα, rfl⟩
    obtain ⟨h1, h2⟩ := mono_mem P e x hx.mem ((e : ℤ) * (g.1 : ℤ) + s) 1 g.2 (hG g hg) α Finset.univ
    have ea : (e : ℤ) * ((∑ l, α l : ℕ) : ℤ) + ((e : ℤ) * (g.1 : ℤ) + s) = (e : ℤ) * (q : ℤ) + (s : ℤ) := by
      rw [← hα]; push_cast; ring
    rw [ea] at h1 h2
    refine ⟨h1, fun σ y => ?_⟩
    rw [h2]
    have hnu0 : ∀ l, 0 ≤ P.nu e 0 σ y (x l) := fun l => nu_nonneg P _ _ σ y _
    have hqe : q ≤ e * q := Nat.le_mul_of_pos_left q he
    have hsum : ∑ l, α l ≤ e * q + s := by omega
    calc (∏ l, P.nu e 0 σ y (x l) ^ α l) * P.nu ((e : ℤ) * (g.1 : ℤ) + s) 1 σ y g.2
        ≤ (∏ l, (1 + ∑ l, Cx l) ^ α l) * (1 + ∑ g ∈ G, Cg g) :=
          mul_le_mul (Finset.prod_le_prod₀ (fun l _ => pow_nonneg (hnu0 l) _)
            fun l _ => pow_le_pow_left₀ (hnu0 l) (hxl l σ y) _) (hgl g hg σ y) (nu_nonneg P _ _ σ y _)
            (Finset.prod_nonneg fun _ _ => pow_nonneg (by linarith) _)
      _ = (1 + ∑ l, Cx l) ^ (∑ l, α l) * (1 + ∑ g ∈ G, Cg g) := by rw [Finset.prod_pow_eq_pow_sum]
      _ ≤ (1 + ∑ l, Cx l) ^ (e * q + s) * (1 + ∑ g ∈ G, Cg g) ^ (e * q + s) :=
          mul_le_mul (pow_le_pow_right₀ hC1 hsum) (le_self_pow₀ hC2 (by omega)) (by linarith)
            (pow_nonneg (by linarith) _)
      _ = ((1 + ∑ l, Cx l) * (1 + ∑ g ∈ G, Cg g)) ^ (e * q + s) := (mul_pow _ _ _).symm
  choose Cs hCs1 hCs using hkey
  refine ⟨fun m => le_rfl, fun m => ?_, ⟨∑ s ∈ Finset.range e, Cs s, ?_, fun m hm => ?_⟩, ?_⟩
  · obtain ⟨c, hc⟩ := hup (m % e)
    have h := (hc (m / e)).1
    rw [Nat.div_add_mod] at h
    exact h
  · exact (hCs1 0).trans (Finset.single_le_sum (fun j _ => zero_le_one.trans (hCs1 j)) (Finset.mem_range.2 he))
  · have hs := Nat.mod_lt m he
    have h := hCs (m % e) (m / e) (by rw [Nat.div_add_mod]; exact hm)
    rw [Nat.div_add_mod] at h
    have hle : Cs (m % e) ≤ ∑ s ∈ Finset.range e, Cs s :=
      Finset.single_le_sum (fun j _ => zero_le_one.trans (hCs1 j)) (Finset.mem_range.2 hs)
    refine h.trans (AddSubgroup.closure_mono ?_)
    rintro f ⟨hf, hf'⟩
    exact ⟨hf, fun σ y => (hf' σ y).trans (pow_le_pow_left₀ (zero_le_one.trans (hCs1 _)) hle _)⟩
  · rw [← hg]
    exact hrank

end GlobalTheory.HSAmp.GoodH
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMixedHeightByInductionSucc
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt.Step

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}

def extend (m : ℕ) (T : ∀ d : ℕ, (Fin d → HermLB p) → X → ℝ) (V : (Fin (m + 1) → HermLB p) → X → ℝ) :
    ∀ d : ℕ, (Fin d → HermLB p) → X → ℝ :=
  fun d L x => if h : d = m + 1 then V (fun a => L (Fin.cast h.symm a)) x else T d L x

theorem extend_of_ne {m : ℕ} {T : ∀ d : ℕ, (Fin d → HermLB p) → X → ℝ} {V : (Fin (m + 1) → HermLB p) → X → ℝ}
    {d : ℕ} (h : d ≠ m + 1) (L : Fin d → HermLB p) (x : X) : extend m T V d L x = T d L x := dif_neg h

theorem extend_self {m : ℕ} {T : ∀ d : ℕ, (Fin d → HermLB p) → X → ℝ} {V : (Fin (m + 1) → HermLB p) → X → ℝ}
    (L : Fin (m + 1) → HermLB p) (x : X) : extend m T V (m + 1) L x = V L x := by
  simp [extend]

theorem recVal_congr {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] {q : Y ⟶ Sp k} {e : ℕ} {h h' : Y → ℝ}
    (H : ∀ z, Order.coheight z = 1 → h z = h' z) (L : Fin e → HermLB q) (M : HermLB q)
    {r : M.B.ι → Y.functionFieldˣ} (hr : IsRatSec M.B r) : recVal h L M hr = recVal h' L M hr := by
  unfold recVal
  congr 1
  refine finsum_congr fun z => ?_
  by_cases hz : (M.div hr).mult z = 0
  · simp [hz]
  · rw [H z (CartierDiv.coheight_eq_one_of_mult_ne_zero hz)]

theorem isRatSec_tens_mul {Z : Scheme.{0}} [IsIntegral Z] {A B : LB Z} {r : A.ι → Z.functionFieldˣ}
    {s : B.ι → Z.functionFieldˣ} (hr : IsRatSec A r) (hs : IsRatSec B s) :
    IsRatSec (CechPic.tens A B) fun c : A.ι × B.ι => r c.1 * s c.2 := fun (c c' : A.ι × B.ι) h => by
  have h₁ : genericPoint Z ∈ A.U c.1 ⊓ A.U c'.1 := ⟨h.1.1, h.2.1⟩
  have h₂ : genericPoint Z ∈ B.U c.2 ⊓ B.U c'.2 := ⟨h.1.2, h.2.2⟩
  have e : fnOf _ h ((CechPic.tens A B).g c c' : Γ(Z, _)) =
      fnOf _ h₁ (A.g c.1 c'.1 : Γ(Z, _)) * fnOf _ h₂ (B.g c.2 c'.2 : Γ(Z, _)) := by
    change fnOf _ h ((res _ (A.g c.1 c'.1)).val * (res _ (B.g c.2 c'.2)).val) = _
    exact (map_mul (fnOf _ h) _ _).trans (congrArg₂ (· * ·) (fnOf_resG _ h _) (fnOf_resG _ h _))
  rw [Units.val_mul, Units.val_mul, hr c.1 c'.1 h₁, hs c.2 c'.2 h₂, e]
  ring

theorem isMix_succ : ArchInteg → ArchRecip → ∀ m : ℕ, (∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∃ T, IsMix q m T) → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsAmb p → ∃ T, IsMix p (m + 1) T := by
  intro hI hR m hm k _ X p hp
  classical
  haveI : IsNoetherian X := hp.isNoetherian
  obtain ⟨T, hT⟩ := hm k X p hp
  choose v hv using _root_.GlobalTheory.MixHt.StepVal.step_val hI hR m hm k X p hp T hT
  have hD := _root_.GlobalTheory.MixHt.hasDim_basic k X p hp
  have hdimi : ∀ (Y : Scheme.{0}) [IsIntegral Y] (i : Y ⟶ X) [IsClosedImmersion i] (d : ℕ),
      topologicalKrullDim Y = (d : ℕ) → HasDim (i (genericPoint Y)) d := fun Y _ i _ d h =>
    (hD.2.2.2.2.1 Y i (genericPoint Y) d).2 ((hD.2.2.2.2.2 Y d).2 h)
  have hcd : ∀ x : X, HasDim x (m + 1) → topologicalKrullDim (clo x) = ((m + 1 : ℕ) : WithBot ℕ∞) := fun x hx =>
    (hD.2.2.2.2.2 (clo x) (m + 1)).1
      ((hD.2.2.2.2.1 (clo x) (cloι x) (genericPoint (clo x)) (m + 1)).1 (by rw [cloι_genericPoint]; exact hx))
  have E : ∀ (x : X) (hx : HasDim x (m + 1)) (M : HermLB p) (L : Fin m → HermLB p)
      (M' : HermLB (cloι x ≫ p)) (L' : Fin m → HermLB (cloι x ≫ p)),
      (M.pull (cloι x) rfl).Isometric M' → (∀ a, ((L a).pull (cloι x) rfl).Isometric (L' a)) →
      ∀ (r : M'.B.ι → (clo x).functionFieldˣ) (hr : IsRatSec M'.B r)
        (TY : ∀ d : ℕ, (Fin d → HermLB (cloι x ≫ p)) → clo x → ℝ), IsMix (cloι x ≫ p) m TY →
      v x hx M L = recVal (TY m L') L' M' hr := by
    intro x hx M L M' L' hM hL r hr TY hTY
    rw [hv x hx M L (clo x) (cloι x ≫ p) (cloι x) rfl (cloι_genericPoint x) M' L' hM hL r hr]
    refine recVal_congr (fun z hz => ?_) L' M' hr
    have hz' : HasDim z m := ((_root_.GlobalTheory.MixHt.dimOne k (clo x) (cloι x ≫ p) (hp.sub _) m (hcd x hx)).1 z).1 hz
    exact _root_.GlobalTheory.MixHt.eq_of_isMix k X (clo x) p (cloι x ≫ p) hp (cloι x) rfl m m T TY hT hTY m le_rfl le_rfl L L' hL z hz'
  let V : (Fin (m + 1) → HermLB p) → X → ℝ := fun L x =>
    if hx : HasDim x (m + 1) then v x hx (L 0) (Fin.tail L) else 0
  have hV : ∀ (L : Fin (m + 1) → HermLB p) (x : X) (hx : HasDim x (m + 1)),
      extend m T V (m + 1) L x = v x hx (L 0) (Fin.tail L) := fun L x hx => by
    rw [extend_self]
    exact dif_pos hx
  have hsym : ∀ (x : X) (hx : HasDim x (m + 1)) (L : Fin (m + 1) → HermLB p) (e : Equiv.Perm (Fin (m + 1))),
      v x hx (L (e 0)) (Fin.tail fun a => L (e a)) = v x hx (L 0) (Fin.tail L) := by
    intro x hx L e
    obtain ⟨TY, hTY⟩ := hm k (clo x) (cloι x ≫ p) (hp.sub (cloι x))
    have hq : IsAmb (cloι x ≫ p) := hp.sub (cloι x)
    have hdx := hcd x hx
    let F : (Fin (m + 1) → HermLB p) → ℝ := fun L => v x hx (L 0) (Fin.tail L)
    change F (fun a => L (e a)) = F L
    rcases m with _ | n
    · have : (fun a => L (e a)) = L := funext fun a => congrArg L (@Subsingleton.elim (Fin 1) _ _ _)
      rw [this]
    · refine _root_.GlobalTheory.perm_invariant_of_cons_swap (HermLB p) n F (fun a L τ => ?_) (fun a b L => ?_) L e
      · simp only [F, Fin.cons_zero, Fin.tail_cons]
        obtain ⟨ra, hra⟩ := Cartier.exists_isRatSec (a.pull (cloι x) rfl).isLB
        rw [E x hx a (fun i => L (τ i)) (a.pull (cloι x) rfl) (fun i => (L (τ i)).pull (cloι x) rfl)
            (HermLB.Isometric.refl _) (fun _ => HermLB.Isometric.refl _) ra hra TY hTY,
          E x hx a L (a.pull (cloι x) rfl) (fun i => (L i).pull (cloι x) rfl)
            (HermLB.Isometric.refl _) (fun _ => HermLB.Isometric.refl _) ra hra TY hTY]
        exact (_root_.GlobalTheory.MixHt.recVal_iso_symm hI k (clo x) (cloι x ≫ p) hq (n + 1) hdx TY hTY _ ra hra).2.1
          (fun i => (L i).pull (cloι x) rfl) τ
      · simp only [F, Fin.cons_zero, Fin.tail_cons]
        obtain ⟨ra, hra⟩ := Cartier.exists_isRatSec (a.pull (cloι x) rfl).isLB
        obtain ⟨rb, hrb⟩ := Cartier.exists_isRatSec (b.pull (cloι x) rfl).isLB
        have iso : ∀ (c : HermLB p) (j : Fin (n + 1)), ((Fin.cons c L : Fin (n + 1) → HermLB p) j).pull (cloι x) rfl |>.Isometric
            ((Fin.cons (c.pull (cloι x) rfl) (fun i => (L i).pull (cloι x) rfl) : Fin (n + 1) → HermLB (cloι x ≫ p)) j) := by
          intro c j
          refine Fin.cases ?_ (fun i => ?_) j <;> simp only [Fin.cons_zero, Fin.cons_succ] <;> exact HermLB.Isometric.refl _
        rw [E x hx a _ (a.pull (cloι x) rfl) _ (HermLB.Isometric.refl _) (iso b) ra hra TY hTY,
          E x hx b _ (b.pull (cloι x) rfl) _ (HermLB.Isometric.refl _) (iso a) rb hrb TY hTY]
        exact _root_.GlobalTheory.MixHt.VSwap.main hI hR k (clo x) (cloι x ≫ p) hq n hdx TY hTY _ _ _ ra hra rb hrb
  refine ⟨extend m T V, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro d L M x hd hx hLM
    by_cases h : d = m + 1
    · subst h
      rw [hV _ _ hx, hV _ _ hx]
      obtain ⟨TY, hTY⟩ := hm k (clo x) (cloι x ≫ p) (hp.sub (cloι x))
      obtain ⟨r, hr⟩ := Cartier.exists_isRatSec ((L 0).pull (cloι x) rfl).isLB
      rw [E x hx (L 0) (Fin.tail L) ((L 0).pull (cloι x) rfl) (fun a => (Fin.tail L a).pull (cloι x) rfl)
          (HermLB.Isometric.refl _) (fun _ => HermLB.Isometric.refl _) r hr TY hTY,
        E x hx (M 0) (Fin.tail M) ((L 0).pull (cloι x) rfl) (fun a => (Fin.tail L a).pull (cloι x) rfl)
          ((hLM 0).symm.pull _ _) (fun a => (hLM a.succ).symm.pull _ _) r hr TY hTY]
    · rw [extend_of_ne h, extend_of_ne h]
      exact hT.iso d L M x (by omega) hx hLM
  · intro d L e x hd hx
    by_cases h : d = m + 1
    · subst h
      rw [hV _ _ hx, hV _ _ hx]
      exact hsym x hx L e
    · rw [extend_of_ne h, extend_of_ne h]
      exact hT.symm d L e x (by omega) hx
  · intro d A B L x hd hx
    by_cases h : d + 1 = m + 1
    · obtain rfl : d = m := by omega
      rw [hV _ _ hx, hV _ _ hx, hV _ _ hx]
      simp only [Fin.cons_zero, Fin.tail_cons]
      obtain ⟨TY, hTY⟩ := hm k (clo x) (cloι x ≫ p) (hp.sub (cloι x))
      obtain ⟨ra, hra⟩ := Cartier.exists_isRatSec (A.pull (cloι x) rfl).isLB
      obtain ⟨rb, hrb⟩ := Cartier.exists_isRatSec (B.pull (cloι x) rfl).isLB
      have ht := isRatSec_tens_mul hra hrb
      rw [E x hx (A.tens B) L ((A.pull (cloι x) rfl).tens (B.pull (cloι x) rfl)) (fun a => (L a).pull (cloι x) rfl)
          (HermLB.isometric_pull_tens A B _ _) (fun _ => HermLB.Isometric.refl _) _ ht TY hTY,
        E x hx A L (A.pull (cloι x) rfl) (fun a => (L a).pull (cloι x) rfl)
          (HermLB.Isometric.refl _) (fun _ => HermLB.Isometric.refl _) ra hra TY hTY,
        E x hx B L (B.pull (cloι x) rfl) (fun a => (L a).pull (cloι x) rfl)
          (HermLB.Isometric.refl _) (fun _ => HermLB.Isometric.refl _) rb hrb TY hTY]
      exact _root_.GlobalTheory.MixHt.recVal_tens hI k (clo x) (cloι x ≫ p) (hp.sub _) d (hcd x hx) _ _ _ _ ra hra rb hrb _ ht
        fun _ _ _ _ => rfl
    · rw [extend_of_ne h, extend_of_ne h, extend_of_ne h]
      exact hT.add d A B L x (by omega) hx
  · intro L x hx
    rw [extend_of_ne (by omega)]
    exact hT.zero L x hx
  · intro Y _ _ q i _ hi e he hdim M L M' L' hM hL r hr
    have hfun : (fun z => extend m T V e L (i z)) = fun z => T e L (i z) :=
      funext fun z => extend_of_ne (by omega) L (i z)
    rw [hfun]
    by_cases h : e + 1 = m + 1
    · obtain rfl : e = m := by omega
      have hx := hdimi Y i (e + 1) hdim
      rw [hV _ _ hx]
      simp only [Fin.cons_zero, Fin.tail_cons]
      exact hv _ hx M L Y q i hi rfl M' L' hM hL r hr
    · rw [extend_of_ne h]
      exact hT.recur Y q i hi e (by omega) hdim M L M' L' hM hL r hr

end GlobalTheory.MixHt.Step
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelSectionsExactKernelLocusOpenStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_sections_exact_kernel_locus_open : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (M : ℕ) (t : S ⟶ Sp (cycAway M)) (G : Over S) [GrpObj G] [IsCommMonObj G] (h : ℕ) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ G)), IsAbelianScheme G → 3 ≤ M → (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ M = 1) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x₀ : Sp k ⟶ S), (∀ a, (toUnit (Over.mk x₀) ≫ lev a = 1 ↔ ∃ b, a = M • b)) → ∃ W : S.Opens, Set.range x₀.base ⊆ W ∧ ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (x : Sp k' ⟶ S), Set.range x.base ⊆ W → ∀ a, (toUnit (Over.mk x) ≫ lev a = 1 ↔ ∃ b, a = M • b) := by
  first | (exact @GlobalTheory.levTriv_locus_open) | (exact GlobalTheory.levTriv_locus_open) | (intros; apply GlobalTheory.levTriv_locus_open  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelSectionsFormulasOfIdempotentImagePullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_sections_formulas_of_idempotent_image_pullback : ∀ (h h' M : ℕ) (O : Type) [Ring O] (e : O) (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin h' ⊕ Fin h' → ℤ)) (n : ℕ) (o : Fin n → O) (κ : Fin n → (Fin h' ⊕ Fin h' → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (S' T : Scheme.{0}) (t : S' ⟶ Sp (cycAway M)) (z : SiegPre h' M (zetaAway M) t) (act : O → (z.A ⟶ z.A)) (g : T ⟶ S') (c' : SiegPre h M (zetaAway M) (g ≫ t)) (w' : SiegPre h' M (zetaAway M) (g ≫ t)) (actw' : O → (w'.A ⟶ w'.A)), ActPB w' actw' z act g → ZRel e jl o κ c' w' actw' → (∀ a, g ≫ (z.lev (jl a) ≫ act e).left = g ≫ (z.lev (jl a)).left) ∧ ∀ a, g ≫ (z.lev a).left = g ≫ ((List.ofFn fun k => z.lev (jl (κ k a)) ≫ act (o k)).prod).left := by
  first | (exact @GlobalTheory.ZRelLevs.zrel_levs) | (exact GlobalTheory.ZRelLevs.zrel_levs) | (intros; apply GlobalTheory.ZRelLevs.zrel_levs  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NTorsionRationalCanonicalFamilyDividedData
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem torsRat_of_canon : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (iw : W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ), IsCN R → 1 ≤ n → IsUnit (n : R) → ∀ ζ : R, IsPrimitiveRoot ζ n → ∀ (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)), DataFrom T iw s ε n Q e → TorsRat Q.B n → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), Canon Q G P → TorsRat G n := by
  intro o W _ _ _ T R _ _ _ iw I _ s ε n hCN hn hu ζ hζ Q e hD hQB G _ _ P hC
  haveI : CharZero R := hCN.2.2.2
  have hfix := _root_.GlobalTheory.Mum.CanonTors.galois_fixed T R iw s ε n hCN hn hu ζ hζ Q e hD hQB G P hC
  obtain ⟨_, D', F, A', G', _, _, U', oA, oG, inc, pr, _, _, hinc, hpr, hip, _, _⟩ := hC
  exact _root_.GlobalTheory.TorsDescent.torsRat_of_retract_galoisFixed G G' A' U'.gen inc pr n U'.gen_hom hinc hpr hip hn hfix

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCastUnitLocusOpenStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.natCast_unit_locus_open : ∀ (S' : Scheme.{0}) (d : ℕ), ∃ U : S'.Opens, (∀ V : S'.Opens, V ≤ U → IsUnit ((d : ℕ) : Γ(V.toScheme, ⊤))) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S'), IsUnit ((d : ℕ) : Γ(T, ⊤)) → Set.range g.base ⊆ (U : Set S') := by
  first | (exact @GlobalTheory.UnitLocus.natCast_unit_locus) | (exact GlobalTheory.UnitLocus.natCast_unit_locus) | (intros; apply GlobalTheory.UnitLocus.natCast_unit_locus  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiFiniteOfRigidAtB
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartQF
theorem base_chartRing {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {k : Type} [Field k] {m e : ℕ}
    (C : Fam Xo c (ChartRing k m e)) : GlobalTheory.Mum.Base (ChartRing k m e) :=
  ⟨GlobalTheory.MumfordChart.admissibleBase_chartRing k m e, (C.b.charZero_iff C.b.injective).1 inferInstance⟩

end GlobalTheory.ChartQF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinPolarisationKernelLeUnitKernelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhin_polarisation_kernel_le_unit_kernel : ∀ (h M d : ℕ), 0 < d → ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (z : SiegPre (8 * h) M (zetaAway M) t) (act : GlobalTheory.ZarhinFam.ord d → (z.A ⟶ z.A)) (inc : c.A ⟶ z.A) (pr : z.A ⟶ c.A), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → z.Principal → IsRAct z.A act → Adj z.A z.P (GlobalTheory.ZarhinFam.bar d) act → IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 c.A → pr ≫ inc = act (GlobalTheory.ZarhinFam.idem d) → LBIso c.P (z.P.pull (inc ⊗ₘ inc).left) → ∀ (T : Over S) (x : T ⟶ c.A), (∃ u : (c.P.pull (lift (snd c.A T ≫ x) (fst c.A T)).left).Gen, u.IsGen) → x ≫ inc ≫ act (GlobalTheory.ZarhinFam.polUnit d) = 1 := by
  first | (exact @GlobalTheory.ZarhinFam.ker_pol_le_ker_polUnit) | (exact GlobalTheory.ZarhinFam.ker_pol_le_ker_polUnit) | (intros; apply GlobalTheory.ZarhinFam.ker_pol_le_ker_polUnit  <;> assumption)
end

