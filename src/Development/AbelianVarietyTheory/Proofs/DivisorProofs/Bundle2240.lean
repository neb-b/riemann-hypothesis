module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsTauZeroNonzeroAll
public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1804
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1512
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1851
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProbabilityMeasureAutQuotientNormalized
public import Development.AbelianVarietyTheory.Counterexamples.UpperHalfSurvey.ExistsFundSetOrth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0038
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2188
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0467
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationCompleteDVR
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModuliModelUltrametricPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1905
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0769
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0118

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormLowerBoundBergmanFunctionOnComponent
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

namespace GlobalTheory.BergLower

open MeasureTheory ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

theorem le_div_of_mean {β a I v S m J N : ℝ≥0∞} (ha0 : a ≠ 0) (hat : a ≠ ⊤) (hS0 : S ≠ 0) (hv : v ≠ ⊤)
    (hI : v = 0 → I = 0) (hβ : β * I ≤ a * v) (hJ : J * S = I) (hm : v ≤ m * S) (hN : N ≤ m⁻¹ * J) :
    β ≤ a / N := by
  rw [ENNReal.le_div_iff_mul_le (Or.inr ha0) (Or.inr hat)]
  by_cases h0 : v = 0
  · have hJ0 : J = 0 := by
      rw [hI h0] at hJ
      exact (mul_eq_zero.1 hJ).resolve_right hS0
    rw [hJ0, mul_zero, nonpos_iff_eq_zero] at hN
    simp [hN]
  · have h1 : N * v ≤ I := by
      calc N * v ≤ (m⁻¹ * J) * (m * S) := by gcongr
        _ = (m⁻¹ * m) * (J * S) := by ring
        _ ≤ 1 * I := by
          rw [hJ]
          gcongr
          exact ENNReal.inv_mul_le_one m
        _ = I := one_mul _
    have h2 : β * N * v ≤ a * v := by
      rw [mul_assoc]
      exact le_trans (by gcongr) hβ
    exact (ENNReal.mul_le_mul_iff_left h0 hv).1 h2

theorem pnorm_pos {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (la : Wt X.Ψ r)
    {P : Frame X.Ψ r → ℂ} {x : Frame X.Ψ r} (hx : x ∈ X.dom) (hP : P x ≠ 0) : 0 < X.pnorm la P x := by
  have hd : ∀ τ i, dmin X.Gm x τ i ≠ 0 := fun τ i h => by
    have := (hx τ).2 i
    rw [h] at this
    simp at this
  unfold Data.pnorm
  exact mul_pos (norm_pos_iff.2 hP) (Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ =>
    Real.rpow_pos_of_pos (norm_pos_iff.2 (div_ne_zero (hd _ _) (hd _ _))) _)

theorem le_bergOn : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), GlobalTheory.LevGeo.Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∀ (G : WTZ D.host.E) (Z : Comp Xo c) (y : FPt (U σ).X), (⟨y.1, y.2.1⟩ : Σ k, Frame ((U σ).X k).Ψ D.R.r) ∈ framesOn (U σ) Z → ∀ β : ENNReal, (∀ (x0 : Frame ((U σ).X y.1).Ψ D.R.r) (FF : Set (ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd ((U σ).X y.1)))), ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth ((U σ).X y.1) x0 → ReciprocityTheory.ChartRestriction.G.AR.Up.IsFundSet ((U σ).X y.1) x0 FF → ∃ P ∈ ((U σ).X y.1).SS (modelWt (U σ) G y.1), P y.2.1 ≠ 0 ∧ β * ∫⁻ z in FF, ENNReal.ofReal (((U σ).X y.1).pnorm (modelWt (U σ) G y.1) P (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt ((U σ).X y.1) x0 z) ^ 2) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF ((U σ).X y.1) x0) ≤ ENNReal.ofReal (((U σ).X y.1).pnorm (modelWt (U σ) G y.1) P y.2.1 ^ 2) * ReciprocityTheory.ChartRestriction.G.AR.Up.muF ((U σ).X y.1) x0 FF) → β ≤ bergOn (U σ) (D.sp.W j) (dict σ) Z G y := by
  intro D j H Dw l Xo c U dict hL σ hσ G Z y hy β hβ
  classical
  have hU : IsUnf (U σ) := hL.unf σ hσ
  obtain ⟨Kf, th, hr, -, -, hDU, -⟩ := hL.dictU σ hσ
  have hdom : ∀ g, (dict σ g).2 ∈ ((U σ).X (dict σ g).1).dom := Formalism.L2.Pj.dict_dom_of hDU
  have hex : ∀ (X : Data D.host.E D.R.r), ∃ x0, IsOrth X x0 ∧ ∃ FF, IsFundSet X x0 FF := fun X => by
    choose P _ hG using X.signature
    exact ⟨fun τ => P τ, fun τ => hG τ, GlobalTheory.MetricWeightTest.exists_fundSet_orth X (fun τ => hG τ)⟩
  choose x0 hx0 FF hFF using fun k => hex ((U σ).X k)
  obtain ⟨P, hP, hPy, hle⟩ := hβ (x0 y.1) (FF y.1) (hx0 _) (hFF _)
  set la := modelWt (U σ) G with hla
  obtain ⟨hS0, hST, hI⟩ := GlobalTheory.LevGeo.adelicProb_mul_volFund D j H Dw l Xo c U dict hL σ hσ x0 FF
    (fun k => ⟨hx0 k, hFF k⟩)
  set Q : Frame ((U σ).X y.1).Ψ D.R.r → ℂ := ((U σ).X y.1).dom.indicator P with hQ
  have hQP : ∀ x ∈ ((U σ).X y.1).dom, ((U σ).X y.1).pnorm (la y.1) Q x = ((U σ).X y.1).pnorm (la y.1) P x :=
    fun x hx => by unfold Data.pnorm; rw [hQ, Set.indicator_of_mem hx]
  have hQS : Q ∈ ((U σ).X y.1).SS (la y.1) :=
    (GlobalTheory.DomCongr.bddSec_cusp_congr D.host.E D.R.r _ _ P Q (fun x hx => (Set.indicator_of_mem hx _).symm)).2 hP
  set P' : Formalism.L2.Pj.FDSec (U σ).X := Function.update (fun _ => 0) y.1 Q with hP'
  have hP'y : P' y.1 = Q := Function.update_self _ _ _
  have hP'n : ∀ k, k ≠ y.1 → P' k = 0 := fun k hk => Function.update_of_ne hk _ _
  have hP'S : ∀ k, P' k ∈ ((U σ).X k).SS (la k) := fun k => by
    by_cases hk : k = y.1
    · subst hk; rw [hP'y]; exact hQS
    · rw [hP'n k hk]
      exact (ReciprocityTheory.ChartRestriction.G.FD.siegelSpaceAlgebra_holds (E := D.host.E) D.R.r ((U σ).X k) (la k) (la k) 0).1.1
  have hP'0 : ∀ k, ∀ x ∉ ((U σ).X k).dom, P' k x = 0 := fun k x hx => by
    by_cases hk : k = y.1
    · subst hk; rw [hP'y]; exact Set.indicator_of_notMem hx _
    · rw [hP'n k hk]; rfl
  have hP'm : P' ∈ Formalism.L2.Pj.holSub (U σ).X la := Formalism.L2.Pj.holCusp_mem_holSub _ _ hP'S
  have hsf : ∀ k, ((U σ).X k).IsSec (la k) (P' k) := fun k => (hP'S k).1.1
  have hJ := hI (fun k x => ENNReal.ofReal (((U σ).X k).pnorm (la k) (P' k) x ^ 2))
    (fun k => ENNReal.measurable_ofReal.comp ((GlobalTheory.PeterssonCompare.measurable_pnorm _ _
      (hsf k).1.continuousOn (hP'0 k)).pow_const 2))
    (fun k γ hγ x hx => by simp only [GlobalTheory.PeterssonCompare.pnorm_lact _ (hsf k) hγ hx])
    (fun k b hb x hx => by simp only [FrameDegreeData.pnorm_rmul _ _ _ (hsf k).2.1 x hx b hb])
  rw [Finset.sum_eq_single y.1 (f := fun k => ∫⁻ z in FF k, ENNReal.ofReal (((U σ).X k).pnorm (la k) (P' k)
      (cpt ((U σ).X k) (x0 k) z) ^ 2) ∂(muF ((U σ).X k) (x0 k)))
      (fun k _ hk => by simp [hP'n k hk, Formalism.L2.Pj.pnorm_zero])
    (fun h => absurd (Finset.mem_univ _) h), hP'y,
    setLIntegral_congr_fun (hFF y.1).1 (g := fun z => ENNReal.ofReal (((U σ).X y.1).pnorm (la y.1) P
      (cpt ((U σ).X y.1) (x0 y.1) z) ^ 2)) (fun z hz => by simp only [hQP _ ((hFF y.1).2.1 hz)])] at hJ
  have hM := hI (fun k _ => if k = y.1 then 1 else 0) (fun _ => measurable_const) (fun _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ => rfl)
  rw [Finset.sum_eq_single y.1 (f := fun k => ∫⁻ z in FF k, (if k = y.1 then (1 : ℝ≥0∞) else 0)
      ∂(muF ((U σ).X k) (x0 k))) (fun k _ hk => by simp [hk]) (fun h => absurd (Finset.mem_univ _) h),
    if_pos rfl, setLIntegral_one] at hM
  set Cl := classesOver (D.sp.W j) (dict σ) (framesOn (U σ) Z) with hCl
  have hm : ∫⁻ q : AutQ (D.sp.W j), (if (dict σ q.out).1 = y.1 then (1 : ℝ≥0∞) else 0) ∂(muQ1 (D.sp.W j)) ≤
      muQ1 (D.sp.W j) Cl := by
    refine le_trans (lintegral_mono fun q => ?_) (lintegral_indicator_one_le Cl)
    split_ifs with hq
    · have : q ∈ Cl := by
        have h1 := hdom q.out
        show dict σ q.out ∈ framesOn (U σ) Z
        generalize dict σ q.out = z at hq h1
        obtain ⟨k, x⟩ := z
        obtain rfl : k = y.1 := hq
        exact GlobalTheory.FramesUnion.framesOn_of_mem D.host.E H Dw l Xo c D.R.r U σ hU Z _ _ x h1 hy
      simp [this]
    · exact zero_le
  have hN : petE (D.sp.W j) (dict σ) (muOn (U σ) (D.sp.W j) (dict σ) Z) la P' ^ 2 ≤ (muQ1 (D.sp.W j) Cl)⁻¹ *
      ∫⁻ q : AutQ (D.sp.W j), ENNReal.ofReal (((U σ).X (dict σ q.out).1).pnorm (la (dict σ q.out).1)
        (P' (dict σ q.out).1) (dict σ q.out).2 ^ 2) ∂(muQ1 (D.sp.W j)) := by
    have e : petE (D.sp.W j) (dict σ) (muOn (U σ) (D.sp.W j) (dict σ) Z) la P' ^ 2 =
        ∫⁻ q : AutQ (D.sp.W j), ‖ptN la P' (dict σ q.out)‖ₑ ^ 2 ∂(muOn (U σ) (D.sp.W j) (dict σ) Z) := by
      have := lintegral_rpow_eNorm_eq_rpow_eLpNorm' (μ := muOn (U σ) (D.sp.W j) (dict σ) Z)
        (f := fun q : AutQ (D.sp.W j) => ptN la P' (dict σ q.out)) (q := 2) (by norm_num)
      simpa [petE, ENNReal.rpow_natCast] using this.symm
    rw [e]
    show ∫⁻ q, _ ∂((muQ1 (D.sp.W j) Cl)⁻¹ • (muQ1 (D.sp.W j)).restrict Cl) ≤ _
    rw [lintegral_smul_measure, smul_eq_mul]
    refine mul_le_mul_right
      (le_trans (lintegral_mono' Measure.restrict_le_self le_rfl) (le_of_eq (lintegral_congr fun q => ?_))) _
    rw [Real.enorm_eq_ofReal (ptN_nonneg _ _ _), ← ENNReal.ofReal_pow (ptN_nonneg _ _ _)]
    rfl
  have hpos := pnorm_pos ((U σ).X y.1) (la y.1) y.2.2 hPy
  have hpt : ENNReal.ofReal (ptN la P' ⟨y.1, y.2.1⟩) ^ 2 =
      ENNReal.ofReal (((U σ).X y.1).pnorm (la y.1) P y.2.1 ^ 2) := by
    rw [ENNReal.ofReal_pow hpos.le]
    show ENNReal.ofReal (((U σ).X y.1).pnorm (la y.1) (P' y.1) y.2.1) ^ 2 = _
    rw [hP'y, hQP _ y.2.2]
  refine le_trans ?_ (le_iSup₂_of_le (f := fun P (_ : P ∈ Formalism.L2.Pj.holSub (U σ).X la) =>
    ENNReal.ofReal (ptN la P ⟨y.1, y.2.1⟩) ^ 2 /
      petE (D.sp.W j) (dict σ) (muOn (U σ) (D.sp.W j) (dict σ) Z) la P ^ 2) P' hP'm le_rfl)
  rw [hpt]
  refine le_div_of_mean (ENNReal.ofReal_pos.2 (pow_pos hpos 2)).ne' ENNReal.ofReal_ne_top hS0
    (ne_top_of_le_ne_top hST (Finset.single_le_sum (f := fun k => muF ((U σ).X k) (x0 k) (FF k))
      (fun _ _ => zero_le) (Finset.mem_univ y.1)))
    (fun h => setLIntegral_measure_zero _ _ h) hle hJ ?_ hN
  rw [← hM]
  gcongr

end GlobalTheory.BergLower
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeformationChartPointReductionEqSpecialFibre
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open GlobalTheory.CechKS

set_option autoImplicit false
noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechKS

theorem mk_algebraMap_eq_mk_baseMap (K B : Type) [Field K] [CommRing B] [Algebra (DualNumber K) B]
    (d : DualNumber K) :
    Ideal.Quotient.mk (Ideal.span {algebraMap (DualNumber K) B DualNumber.eps}) (algebraMap (DualNumber K) B d) =
      Ideal.Quotient.mk (Ideal.span {algebraMap (DualNumber K) B DualNumber.eps})
        (baseMap K B (TrivSqZeroExt.fst d)) := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
  refine ⟨algebraMap (DualNumber K) B (TrivSqZeroExt.inl d.snd), ?_⟩
  rw [← map_mul, RingHom.comp_apply, ← map_sub]
  congr 1
  ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem chartPt_red : ∀ {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {A' : Over (Sp (DualNumber K))} [GrpObj A'] {i : A.left ⟶ A'.left} (hi : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) {X Z : Scheme.{0}} {h : Z ⟶ X} {y1 : Sp (DualNumber K) ⟶ X} {m : A.left ⟶ Z} {m' : A'.left ⟶ Z} (hm' : IsPullback m' A'.hom h y1) (him : i ≫ m' = m) {Ω : Z.affineOpens} {δ : Γ(Z, Ω.1) → Γ(Z, Ω.1)} {n : ℕ} {u : Fin n → (epsR K ⟶ A)} {θ : Matrix (Fin n) (Fin n) K} {Wo : A.left.Opens} {g : Γ(A.left, Wo)ˣ} {B : Type} [CommRing B] [Algebra (DualNumber K) B] {x : Sp B ⟶ A.left} {l : Sp B ⟶ A'.left} (hx : x ≫ A.hom = spMap (baseMap K B)) (hxΩ : ⊤ ≤ x ⁻¹ᵁ (m ⁻¹ᵁ Ω.1)) (hl : IsChartPt A' m m' Ω.1 δ u θ Wo g x l), spMap (Ideal.Quotient.mk (Ideal.span {algebraMap (DualNumber K) B DualNumber.eps})) ≫ l = spMap (Ideal.Quotient.mk (Ideal.span {algebraMap (DualNumber K) B DualNumber.eps})) ≫ x ≫ i := by
  intro K _ A _ A' _ i hi X Z h y1 m m' hm' him Ω δ n u θ Wo g B _ _ x l hx hxΩ hl
  set I : Ideal B := Ideal.span {algebraMap (DualNumber K) B DualNumber.eps} with hI
  set q : B →+* B ⧸ I := Ideal.Quotient.mk I with hq
  obtain ⟨h1, h2, h3⟩ := hl
  have hxm : ⊤ ≤ (x ≫ m) ⁻¹ᵁ Ω.1 := fun p hp => hxΩ hp
  have hA : (spMap q ≫ l) ≫ A'.hom = (spMap q ≫ x ≫ i) ≫ A'.hom := by
    have e : q.comp (algebraMap (DualNumber K) B) =
        ((q.comp (baseMap K B)).comp (TrivSqZeroExt.fstHom K K K).toRingHom) :=
      RingHom.ext fun d => mk_algebraMap_eq_mk_baseMap K B d
    rw [Category.assoc, h1, Category.assoc, Category.assoc, hi.1.w, ← Category.assoc x, hx, GlobalTheory.DeRham.epsRed]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [e]
  have hZ : (spMap q ≫ l) ≫ m' = (spMap q ≫ x ≫ i) ≫ m' := by
    have ha : ⊤ ≤ (spMap q ≫ l ≫ m') ⁻¹ᵁ Ω.1 := GlobalTheory.FlagMod.le_preimage_comp _ h2
    have hb : ⊤ ≤ (spMap q ≫ x ≫ m) ⁻¹ᵁ Ω.1 := GlobalTheory.FlagMod.le_preimage_comp _ hxm
    have e : ev (spMap q ≫ l ≫ m') Ω.1 ha = ev (spMap q ≫ x ≫ m) Ω.1 hb := by
      rw [GlobalTheory.FlagMod.ev_spMap q _ _ h2, GlobalTheory.FlagMod.ev_spMap q _ _ hxm]
      ext f
      simp only [RingHom.comp_apply]
      rw [← valR_eq_ev _ _ h2, ← valR_eq_ev _ _ hxm, h3 f, chartVal, map_add (f := _), map_mul,
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl : _ ∈ I), zero_mul, add_zero]
    rw [Category.assoc, Category.assoc, Category.assoc, him,
      ← GlobalTheory.FlagMod.spMap_ev (spMap q ≫ l ≫ m') Ω.2 ha, ← GlobalTheory.FlagMod.spMap_ev (spMap q ≫ x ≫ m) Ω.2 hb, e]
  exact hm'.hom_ext hZ hA

end GlobalTheory.CechKS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeformedLatticeValueEqHilbertEisensteinValue
section
set_option autoImplicit false

noncomputable section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.CMVal (OF Af lattice IsCMType)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum IsEisValue polydisc)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord defTerm)
open GlobalTheory.CMVal (modUnits unitRel)

namespace GlobalTheory.HilbFam.BrVal

theorem card_realEmb (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    Fintype.card (Emb F) = Module.finrank ℚ F := by
  rw [← NumberField.Embeddings.card F ℂ]
  refine Fintype.card_of_bijective (f := fun τ : F →+* ℝ ↦ (Complex.ofRealHom.comp τ : F →+* ℂ)) ⟨?_, ?_⟩
  · intro τ τ' hτ
    ext y
    have := DFunLike.congr_fun hτ y
    simpa using this
  · intro φ
    have hr : NumberField.ComplexEmbedding.IsReal φ := IsTotallyReal.complexEmbedding_isReal φ
    exact ⟨hr.embedding, by ext y; simp⟩

theorem prod_cpow_ofReal {J : Type} (s : Finset J) (f : J → ℝ) (hf : ∀ i, 0 ≤ f i) (r : ℂ) :
    ∏ i ∈ s, ((f i : ℝ) : ℂ) ^ r = (((∏ i ∈ s, f i : ℝ)) : ℂ) ^ r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ih, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hf a) (Finset.prod_nonneg fun i _ => hf i)]

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

theorem defTerm_eq (φ : I → E →+* ℂ) (k : ℕ) (z : I → ℂ) (σ : ℂ) (x : E) :
    defTerm φ k z σ x =
      (∏ i, defCoord φ z x i)⁻¹ ^ k * ((‖∏ i, defCoord φ z x i‖ : ℝ) : ℂ) ^ (-2 * σ) := by
  unfold defTerm
  rw [Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_inv_distrib, norm_prod,
    prod_cpow_ofReal _ _ (fun _ => norm_nonneg _)]

theorem defCoord_mul (φ : I → E →+* ℂ) (z : I → ℂ) (a x : E) (i : I) (ha : starRingEnd ℂ (φ i a) = φ i a) :
    defCoord φ z (a * x) i = φ i a * defCoord φ z x i := by
  simp only [defCoord, map_mul, ha]; ring

end GlobalTheory.HilbFam.BrVal

namespace GlobalTheory.HilbFam.BrVal

theorem isGVal_of_isEisValue : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] [DecidableEq I] (φ : I → E →+* ℂ) (e : I ≃ Emb (FR E)) (θ : E) (τ : ℍ) (Λ : Set E) (L : Lat (FR E)) (n : ℕ) (k : ℕ) (z : I → ℂ) (G : ℂ), Nonempty I → Even k → (∀ i (x : FR E), φ i (x : E) = ((e i x : ℝ) : ℂ)) → (∀ i, φ i θ = (τ : ℂ)) → 0 < n → (∀ x : Fin 2 → FR E, x ∈ L ↔ ∃ y ∈ Λ, (n : E) * y = (x 0 : E) * θ + (x 1 : E)) → IsEisValue φ k Λ z G → IsGVal k L (fun j ↦ τ + z (e.symm j) * (1 * τ + (starRingEnd ℂ (τ : ℂ) - τ))) (fun j ↦ 1 + z (e.symm j) * 1) ((((n : ℂ) ^ Module.finrank ℚ (FR E))⁻¹) ^ k * G) := by
  intro E _ _ _ I _ _ φ e θ τ Λ L n k z G hI hk hφ hθ hn hL hG
  obtain ⟨i0⟩ := hI
  set T : (Fin 2 → FR E) → E := fun x ↦ (x 0 : E) * θ + (x 1 : E) with hT
  have hTb : Function.Bijective T := GlobalTheory.HilbFam.EBasis.bijective_pair E (φ i0) θ (by
    rw [hθ i0, UpperHalfPlane.coe_im]; exact (UpperHalfPlane.im_pos τ).ne')
  have hnE : (n : E) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  set B : (Fin 2 → FR E) → E := fun x ↦ (n : E)⁻¹ * T x with hB
  have hBinj : Function.Injective B := fun x y h ↦ hTb.1 (mul_left_cancel₀ (inv_ne_zero hnE) h)
  have hB0 : B 0 = 0 := by simp [hB, hT]
  have hLB : ∀ x, x ∈ L ↔ B x ∈ Λ := by
    intro x
    rw [hL x]
    constructor
    · rintro ⟨y, hy, hny⟩
      have : B x = y := by
        show (n : E)⁻¹ * ((x 0 : E) * θ + (x 1 : E)) = y
        rw [← hny, ← mul_assoc, inv_mul_cancel₀ hnE, one_mul]
      rw [this]; exact hy
    · intro h
      exact ⟨B x, h, by
        show (n : E) * ((n : E)⁻¹ * ((x 0 : E) * θ + (x 1 : E))) = _
        rw [← mul_assoc, mul_inv_cancel₀ hnE, one_mul]⟩
  have hBu : ∀ (u : (OF E)ˣ) (x : Fin 2 → FR E), B (u • x) = algebraMap (OF E) E (u : OF E) * B x := by
    intro u x
    have h0 : ∀ j, (((u • x) j : FR E) : E) = (((u : OF E) : FR E) : E) * ((x j : FR E) : E) := by
      intro j
      rw [Pi.smul_apply, Units.smul_def, Algebra.smul_def]
      rfl
    simp only [hB, hT, h0]
    show _ = (((u : OF E) : FR E) : E) * _
    ring
  have hcoord : ∀ (x : Fin 2 → FR E) (i : I),
      coord (fun j ↦ τ + z (e.symm j) * (1 * τ + (starRingEnd ℂ (τ : ℂ) - τ))) (fun j ↦ 1 + z (e.symm j) * 1) x (e i)
        = (n : ℂ) * defCoord φ z (B x) i := by
    intro x i
    have h1 : T x = (n : E) * B x := by simp only [hB]; rw [← mul_assoc, mul_inv_cancel₀ hnE, one_mul]
    have h2 : defCoord φ z (T x) i = (n : ℂ) * defCoord φ z (B x) i := by
      rw [h1, defCoord_mul φ z _ _ i (by simp)]; simp
    rw [← h2]
    simp only [coord, defCoord, hT, map_add (f := _), map_mul, hφ, hθ, Equiv.symm_apply_apply, Complex.conj_ofReal]
    ring
  set b : Emb (FR E) → ℂ := fun j ↦ τ + z (e.symm j) * (1 * τ + (starRingEnd ℂ (τ : ℂ) - τ)) with hb
  set a : Emb (FR E) → ℂ := fun j ↦ 1 + z (e.symm j) * 1 with ha
  set d := Module.finrank ℚ (FR E) with hd
  have hcard : Fintype.card I = d := by
    rw [Fintype.card_congr e, hd, ← card_realEmb (FR E)]
  have hprod : ∀ x, ∏ j, coord b a x j = ((n : ℂ) ^ d) * ∏ i, defCoord φ z (B x) i := by
    intro x
    rw [← Equiv.prod_comp e]
    simp only [hcoord, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hcard]
  set c : ℂ → ℂ := fun σ ↦ (((n : ℂ) ^ d)⁻¹) ^ k * ((((n : ℝ) ^ d : ℝ)) : ℂ) ^ (-2 * σ) with hc
  have hterm : ∀ σ x, gTerm k σ b a x = c σ * defTerm φ k z σ (B x) := by
    intro σ x
    rw [defTerm_eq, gTerm, hprod, hc]
    simp only
    rw [_root_.mul_inv, _root_.mul_pow, norm_mul, norm_pow, Complex.norm_natCast, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (by positivity) (norm_nonneg _)]
    ring
  have hBne : ∀ x, x ≠ 0 → B x ≠ 0 := fun x hx h ↦ hx (hBinj (h.trans hB0.symm))
  let ι : cls L → modUnits Λ := fun q ↦ ⟨Quotient.mk _ (B q.1.out), B q.1.out, (hLB _).1 q.2.1, hBne _ q.2.2, rfl⟩
  have hinj : Function.Injective ι := by
    intro q1 q2 h
    have h' : Quotient.mk (unitRel (E := E)) (B q1.1.out) = Quotient.mk _ (B q2.1.out) := congrArg Subtype.val h
    obtain ⟨u, hu⟩ := Quotient.exact h'
    rw [← hBu] at hu
    have hx := hBinj hu
    apply Subtype.ext
    rw [← Quotient.out_eq q1.1, ← Quotient.out_eq q2.1]
    exact (Quotient.sound (MulAction.mem_orbit_iff.2 ⟨u, hx.symm⟩)).symm
  have hsurj : Function.Surjective ι := by
    rintro ⟨p, y, hy, hy0, hp⟩
    obtain ⟨x, hx⟩ := hTb.2 ((n : E) * y)
    have hBx : B x = y := by
      show (n : E)⁻¹ * T x = y
      rw [hx, ← mul_assoc, inv_mul_cancel₀ hnE, one_mul]
    have hxL : x ∈ L := (hLB x).2 (hBx ▸ hy)
    have hx0 : x ≠ 0 := by rintro rfl; exact hy0 (hBx ▸ hB0)
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1
      (Quotient.exact (Quotient.out_eq (Quotient.mk (MulAction.orbitRel (𝓞 (FR E))ˣ (Fin 2 → FR E)) x)))
    set q0 := Quotient.mk (MulAction.orbitRel (𝓞 (FR E))ˣ (Fin 2 → FR E)) x with hq0
    have hmem : q0 ∈ cls L := by
      refine ⟨?_, ?_⟩
      · rw [← hg, Units.smul_def]; exact L.smul_mem _ hxL
      · rw [← hg]; intro h0; exact hx0 ((smul_eq_zero_iff_eq g).1 h0)
    refine ⟨⟨q0, hmem⟩, ?_⟩
    apply Subtype.ext
    show Quotient.mk _ (B q0.out) = p
    rw [← hp, ← hg, hBu g x, hBx]
    exact (Quotient.sound (show (unitRel (E := E)).r y (algebraMap (OF E) E (g : OF E) * y) from ⟨g, rfl⟩)).symm
  have hval : ∀ σ (q : cls L), gTerm k σ b a q.1.out = c σ * defTerm φ k z σ (ι q).1.out := by
    intro σ q
    obtain ⟨u, hu⟩ : (unitRel (E := E)).r (B q.1.out) (ι q).1.out :=
      Quotient.exact (Quotient.out_eq (ι q).1).symm
    rw [hu, ← hBu, ← hterm, GlobalTheory.HilbFam.gTerm_unit_smul (FR E) k σ b a u q.1.out hk]
  have hsum : ∀ σ S, HasSum (fun p : modUnits Λ ↦ defTerm φ k z σ p.1.out) S →
      HasSum (fun q : cls L ↦ gTerm k σ b a q.1.out) (c σ * S) := by
    intro σ S h
    simp only [hval]
    exact ((Equiv.hasSum_iff (Equiv.ofBijective ι ⟨hinj, hsurj⟩)).2 h).mul_left (c σ)
  have hc0 : c 0 = (((n : ℂ) ^ d)⁻¹) ^ k := by simp [hc]
  refine ⟨fun hk2 ↦ ?_, fun hk2 ↦ ?_⟩
  · have hd0 : ∀ x : E, defTerm φ k z 0 x = ∏ i, (defCoord φ z x i)⁻¹ ^ k := by
      intro x; simp [defTerm]
    rw [← hc0]
    refine hsum 0 G ?_
    simp only [hd0]
    exact hG.1 hk2
  · obtain ⟨H, hHd, hHs, hH0⟩ := hG.2 hk2
    subst hk2
    have hn' : ((((n : ℝ) ^ d : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by positivity)
    have hcd : Differentiable ℂ c := fun σ ↦
      (differentiableAt_const _).mul (((differentiableAt_const (-2 : ℂ)).mul differentiableAt_id).const_cpow (Or.inl hn'))
    refine ⟨fun σ ↦ c σ * H σ, hcd.differentiableOn.mul hHd, fun σ hσ ↦ hsum σ _ (hHs σ hσ), ?_⟩
    rw [hH0, ← hc0]

end GlobalTheory.HilbFam.BrVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationExtensionLocalDomain
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.SplitPowEight

def isPowGrpOfUnique {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G] {j : ℕ} (pr : Fin j → (G' ⟶ G))
    (hpr : ∀ u, IsMonHom (pr u))
    (hu : ∀ (T : Over S) (y : Fin j → (T ⟶ G)), ∃! x : T ⟶ G', ∀ u, x ≫ pr u = y u) : IsPowGrp G' G j :=
  ⟨pr, hpr, Fan.IsLimit.mk _ (fun s => (hu s.pt s.proj).choose) (fun s u => (hu s.pt s.proj).choose_spec.1 u)
    fun s m hm => (hu s.pt s.proj).choose_spec.2 m hm⟩

def powPullback {S S' : Scheme.{0}} (f : S' ⟶ S) {G' G : Over S} [GrpObj G'] [GrpObj G] {j : ℕ}
    (p : IsPowGrp G' G j) : IsPowGrp ((Over.pullback f).obj G') ((Over.pullback f).obj G) j :=
  ⟨fun u => (Over.pullback f).map (p.pr u), fun u => by have := p.hom u; infer_instance,
    isLimitFanMkObjOfIsLimit (Over.pullback f) _ _ p.lim⟩

theorem exists_unif_pow8 : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ ψ : A.A.left ⟶ G.left, IsGrpPullback A.A G (jK V) ψ → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (io : V →+* W) (em : W →+* AlgebraicClosure (FractionRing V)) (D : DegData W (maximalIdeal W)) (Q : PolAV (Sp (FractionRing W))) (H : Over (Sp W)) (_ : GrpObj H) (_ : IsCommMonObj H) (U : Unif (maximalIdeal W) D Q H) (i : (Over.pullback (spMap io)).obj G ⟶ H) (r : Fin 8 → (H ⟶ (Over.pullback (spMap io)).obj G)), GlobalTheory.LN.CDvr W ∧ io.Finite ∧ Function.Injective io ∧ Function.Injective em ∧ (∀ v, em (io v) = algebraMap (FractionRing V) _ (algebraMap V _ v)) ∧ IsSemiAbelian H ∧ GlobalTheory.LN.ToATotal U.toUnifPre ∧ (∀ k, IsMonHom (r k)) ∧ i ≫ r 0 = 𝟙 _ ∧ ∀ (T : Over (Sp W)) (x y : T ⟶ H), (∀ k, x ≫ r k = y ≫ r k) → x = y := by
  intro V _ _ _ hV A G _ _ hG ψ hψ
  obtain ⟨hd, hc, hch⟩ := hV
  obtain ⟨gen, hgen, -⟩ := grpPullback_iso (isGrpPullback_pullback G (jK V)) hψ
  obtain ⟨G8, _, prG, hG8, hprG, huG⟩ := GlobalTheory.MBLow.exists_eighthPower_semiAbelianScheme V G hG
  have : IsCommMonObj G8 := hG8.comm
  let p8 : IsPowGrp G8 G 8 := isPowGrpOfUnique prG hprG huG
  let F := AlgebraicClosure (FractionRing V)
  have : FaithfulSMul V F := (faithfulSMul_iff_algebraMap_injective V F).2 (by
    rw [IsScalarTower.algebraMap_eq V (FractionRing V) F]
    exact (algebraMap (FractionRing V) F).injective.comp (IsFractionRing.injective V _))
  have : Algebra.IsAlgebraic V F :=
    (IsFractionRing.comap_isAlgebraic_iff (A := V) (K := FractionRing V) (C := F)).2 inferInstance
  obtain ⟨W, hWd, hWc, hWf, hsplit⟩ := GlobalTheory.Ex.UnifModel.exists_split V F G8 hG8
  have : CharZero F := charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective V F)
  have : CharZero W := RingHom.charZero (algebraMap W F)
  have hio : Function.Injective (algebraMap V W) := fun a b h =>
    FaithfulSMul.algebraMap_injective V F (congrArg Subtype.val h)
  let io : V →+* W := algebraMap V W
  let H := (Over.pullback (spMap io)).obj G8
  let pH : IsPowGrp H ((Over.pullback (spMap io)).obj G) 8 := powPullback (spMap io) p8
  have hH : IsSemiAbelian H := IsSemiAbelian.pullback _ G8 hG8
  obtain ⟨A', ψ', hψ'⟩ := GlobalTheory.UnifProperOpen.exists_polGeneric_pullback V A G gen hgen W io hio
  obtain ⟨d, -, hQ⟩ := GlobalTheory.MBLow.PowEightField.exists_eighthPower_evenUnimodular_charZero
  obtain ⟨Q, pr, inc, -, hS, hP⟩ := hQ (FractionRing W) A'
  let pQ : IsPowGrp Q.A A'.A 8 := isPowGrpOfUnique pr hP.1 hP.2.2.1
  obtain ⟨φ₀, hφ₀, -⟩ := GlobalTheory.PowFibre.exists_pow_pullback pH pQ hψ'
  obtain ⟨genH, hgenH, -⟩ := grpPullback_iso (isGrpPullback_pullback H (jK W)) hφ₀
  obtain ⟨L₁, -⟩ := GlobalTheory.abelianSchemeLaws_all
  have hE : ∃ E : SplitExt (Sp (ResidueField W)), E.IsGt ((Over.pullback (spMap (residue W))).obj H) := hsplit
  obtain ⟨s, -⟩ := GlobalTheory.ZH.exists_setting_of_hypS L₁ GlobalTheory.homExtension_semiAbelian_dvr_unconditional W hWc Q H hH hE
    hS genH hgenH
  obtain ⟨D, U, -, -, hU⟩ := GlobalTheory.uniformisation_dvr_unconditional W Q H s
  obtain ⟨i₀, hi₀, -⟩ := huG G (fun _ => 𝟙 G)
  refine ⟨W, inferInstance, inferInstance, inferInstance, io, algebraMap W F, D, Q, H, inferInstance, inferInstance, U,
    (Over.pullback (spMap io)).map i₀, pH.pr, ⟨hWd, hWc, inferInstance⟩, RingHom.finite_algebraMap.2 hWf, hio,
    Subtype.val_injective, fun v => ?_, hH, hU, pH.hom, ?_, fun T x y h => Fan.IsLimit.hom_ext pH.lim _ _ h⟩
  · exact IsScalarTower.algebraMap_apply V (FractionRing V) F v
  · show (Over.pullback (spMap io)).map i₀ ≫ (Over.pullback (spMap io)).map (prG 0) = _
    rw [← CategoryTheory.Functor.map_comp, hi₀ 0, CategoryTheory.Functor.map_id]

end GlobalTheory.SplitPowEight
end
end

