module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.OneTmulMemCenter
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.Approx
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.approx :
    UpperTheory.V.Cj.H.Approx := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ F hF
  by_contra hF0
  have hpos : 0 < ‖F‖ := norm_pos_iff.mpr hF0
  have hcont := GlobalTheory.AutomorphicL2Unitary.continuous_R (Γ := Γ) (μ := μ) F
  obtain ⟨f, hfc, hfs, hfr, hf1, hfW, hfF⟩ :=
    hF {g | ‖GlobalTheory.AutomorphicL2Unitary.R Γ μ g F - F‖ < ‖F‖ / 2} (by
      apply (isOpen_lt (continuous_norm.comp (hcont.sub continuous_const))
        continuous_const).mem_nhds
      show ‖GlobalTheory.AutomorphicL2Unitary.R Γ μ 1 F - F‖ < ‖F‖ / 2
      rw [map_one, ContinuousLinearMap.one_apply, sub_self, norm_zero]
      positivity)
  have hfre : ∀ y, f y = ((f y).re : ℂ) := by
    intro y
    obtain ⟨t, _, ht⟩ := hfr y
    rw [ht, Complex.ofReal_re]
  have hfnn : ∀ y, 0 ≤ (f y).re := by
    intro y
    obtain ⟨t, ht0, ht⟩ := hfr y
    rw [ht, Complex.ofReal_re]
    exact ht0
  have hint : MeasureTheory.Integrable f μ := hfc.integrable_of_hasCompactSupport hfs
  have hrep := (GlobalTheory.AutomorphicL2Unitary.isRepOp_Rop (Γ := Γ) (μ := μ) hint) F
  have hφ := hrep.1
  have hzero : ∫ g, f g • GlobalTheory.AutomorphicL2Unitary.R Γ μ g F ∂μ = 0 := hrep.2.symm.trans hfF
  have hI : ∫ g, RCLike.re (inner ℂ F (f g • GlobalTheory.AutomorphicL2Unitary.R Γ μ g F)) ∂μ = 0 := by
    rw [integral_re (hφ.const_inner F), integral_inner hφ F, hzero, inner_zero_right]
    simp
  have hbound : ∀ g, ‖F‖ ^ 2 / 2 * (f g).re
      ≤ RCLike.re (inner ℂ F (f g • GlobalTheory.AutomorphicL2Unitary.R Γ μ g F)) := by
    intro g
    have hre : RCLike.re (inner ℂ F (f g • GlobalTheory.AutomorphicL2Unitary.R Γ μ g F))
        = (f g).re * (inner ℂ F (GlobalTheory.AutomorphicL2Unitary.R Γ μ g F)).re := by
      rw [inner_smul_right]
      conv_lhs => rw [hfre g]
      simp
    rw [hre]
    by_cases hg : ‖GlobalTheory.AutomorphicL2Unitary.R Γ μ g F - F‖ < ‖F‖ / 2
    · have e1 : inner ℂ F (GlobalTheory.AutomorphicL2Unitary.R Γ μ g F)
          = inner ℂ F F - inner ℂ F (F - GlobalTheory.AutomorphicL2Unitary.R Γ μ g F) := by
        rw [inner_sub_right]
        ring
      have e2 : (inner ℂ F F).re = ‖F‖ ^ 2 := by
        simpa using inner_self_eq_norm_sq (𝕜 := ℂ) F
      have e3 := re_inner_le_norm (𝕜 := ℂ) F (F - GlobalTheory.AutomorphicL2Unitary.R Γ μ g F)
      rw [norm_sub_rev] at e3
      have e4 : ‖F‖ ^ 2 / 2 ≤ (inner ℂ F (GlobalTheory.AutomorphicL2Unitary.R Γ μ g F)).re := by
        rw [e1, Complex.sub_re, e2]
        have e3' : (inner ℂ F (F - GlobalTheory.AutomorphicL2Unitary.R Γ μ g F)).re ≤ ‖F‖ * (‖F‖ / 2) := by
          simp only [RCLike.re_to_complex] at e3
          exact e3.trans (mul_le_mul_of_nonneg_left hg.le (norm_nonneg F))
        nlinarith
      have h5 := mul_le_mul_of_nonneg_left e4 (hfnn g)
      linarith
    · have h0 : f g = 0 := hfW g hg
      rw [h0]
      simp
  have hpos2 : 0 < ∫ g, (f g).re ∂μ :=
    Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1)
      (Complex.continuous_re.comp hfc) (hfs.comp_left Complex.zero_re) (fun y => hfnn y)
      (by
        intro h
        apply hf1
        rw [hfre 1, h, Complex.ofReal_zero])
  have hmono : ∫ g, ‖F‖ ^ 2 / 2 * (f g).re ∂μ
      ≤ ∫ g, RCLike.re (inner ℂ F (f g • GlobalTheory.AutomorphicL2Unitary.R Γ μ g F)) ∂μ :=
    MeasureTheory.integral_mono (hint.re.const_mul _) ((hφ.const_inner F).re) hbound
  rw [hI, MeasureTheory.integral_const_mul] at hmono
  have h6 : 0 < ‖F‖ ^ 2 / 2 * ∫ g, (f g).re ∂μ := mul_pos (by positivity) hpos2
  linarith
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ChiGrow
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.chiGrow :
    UpperTheory.V.Cj.H.ChiGrow := by
  intro E _ _ _ a χ s _ φ hφ g
  obtain ⟨A, p, hA⟩ := hφ g
  obtain ⟨B, q, hB⟩ := chiDet_growth (a := a) χ⁻¹
  have hback : mulChi a χ⁻¹ (mulChi a χ φ) = φ := by
    rw [← mulChi_mul, mul_inv_cancel, mulChi_one]
  refine ⟨‖((chiDet a χ⁻¹ g : ℂˣ) : ℂ)‖ * (A * B), p + q, fun y => ?_⟩
  have e : φ.1 (g * infGL E a y) = ((chiDet a χ⁻¹ g : ℂˣ) : ℂ) *
      ((mulChi a χ φ).1 (g * infGL E a y) * ((chiDet a χ⁻¹ (infGL E a y) : ℂˣ) : ℂ)) := by
    conv_lhs => rw [← hback, mulChi_apply, map_mul, Units.val_mul]
    ring
  have hprod := mul_le_mul (hA y) (hB y) (norm_nonneg _) ((norm_nonneg _).trans (hA y))
  calc ‖φ.1 (g * infGL E a y)‖
      = ‖((chiDet a χ⁻¹ g : ℂˣ) : ℂ)‖ * (‖(mulChi a χ φ).1 (g * infGL E a y)‖ *
          ‖((chiDet a χ⁻¹ (infGL E a y) : ℂˣ) : ℂ)‖) := by rw [e, norm_mul, norm_mul]
    _ ≤ ‖((chiDet a χ⁻¹ g : ℂˣ) : ℂ)‖ * (A * GlobalTheory.CuspRep.height y ^ p * (B * GlobalTheory.CuspRep.height y ^ q)) :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = _ := by rw [pow_add]; ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CommOfZalg
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

namespace UpperTheory.V.Cj.H.CasimirOperatorShift

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem comm_of_zalg {z o : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) (ho : ∀ τ u, Commute (cap τ u) o) :
    Commute z o := by
  refine Algebra.adjoin_induction (p := fun x _ => Commute x o) ?_ (fun r => Algebra.commutes r _)
    (fun _ _ _ _ hx hy => hx.add_left hy) (fun _ _ _ _ hx hy => hx.mul_left hy) hz
  rintro _ ⟨τ, u, rfl⟩
  exact ho τ u

private theorem uC_sh (r : ℝ) (X : Lie E a) : Cm.uC E a (shift (Cm.ιC E a) r X) = shift (lie E a) r X := by
  rw [shift_apply, shift_apply, map_add (f := _), Cm.uC_ιC, ← algebraMap_smul ℂ (r * ell E a X) (1 : Cm.UC E a), map_smul,
    map_one, algebraMap_smul]

private theorem cas_mem {n : ℕ} {e : Fin n → Herm E a} (he : IsFrame e) (r : ℝ) :
    cas (shift (lie E a) r) e ∈ Zalg E a := by
  have hL : IsLieHom (shift (Cm.ιC E a) r) := (ellFacts E a).2.2.2 _ _ r Cm.isLieHom_ιC
  have hX : ∀ X, Commute (cas (shift (Cm.ιC E a) r) e) (Cm.ιC E a X) := fun X => by
    have h := casComm E a n e he _ _ hL X
    have h' : Cm.ιC E a X = shift (Cm.ιC E a) r X - (r * ell E a X) • 1 := by rw [shift_apply, add_sub_cancel_right]
    rw [h']
    exact h.sub_right ((Commute.one_right _).smul_right _)
  have hle : Algebra.adjoin ℂ {x : Cm.UC E a | ∃ τ i j, x = Cm.genC τ i j} ≤
      Subalgebra.centralizer ℂ {cas (shift (Cm.ιC E a) r) e} := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨τ, i, j, rfl⟩ _ rfl
    exact (((hX _).sub_right ((hX _).smul_right _)).smul_right _).eq
  rw [Cm.adjoin_genC] at hle
  rw [Cm.Zalg_eq_map]
  exact ⟨_, Subalgebra.mem_center_iff.2 fun x => (hle Algebra.mem_top _ rfl).symm,
    by simp only [cas, map_sum, map_sub, map_mul, uC_sh, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]⟩

private theorem cap_rt (τ : E →+* ℂ) (u : ℂ) (g : GA E a) : Commute (cap τ u) (rt E a g) := by
  rw [← infGL_mul_finGL g, map_mul]
  exact (GlobalTheory.CapAdInv.cap_commute_rt_infGL E a τ u _).mul_right (commute_cap_finRep τ u _)

private theorem sh_apply (r : ℝ) (X : Lie E a) (φ : Sm E a) :
    shift (lie E a) r X φ = lie E a X φ + ((r * ell E a X : ℝ) : ℂ) • φ := by
  rw [shift_apply]; rfl

end UpperTheory.V.Cj.H.CasimirOperatorShift

open UpperTheory.V.Cj.H.CasimirOperatorShift in
theorem UpperTheory.V.Cj.H.casOp :
    UpperTheory.V.Cj.H.CasOp := by
  intro E _ _ _ a n e he r c
  have hz := cas_mem he r
  have hc : ∀ o : Module.End ℂ (Sm E a), (∀ τ u, Commute (cap τ u) o) → Commute o (casA r c e) := fun o ho =>
    (comm_of_zalg hz ho).symm.sub_right ((Commute.one_right _).smul_right _)
  refine ⟨fun X => hc _ fun τ u => commute_cap_lie τ u X, fun g => hc _ fun τ u => cap_rt τ u g, fun N hN => ?_⟩
  have hs : ∀ X, ∀ φ ∈ N, shift (lie E a) r X φ ∈ N := fun X φ hφ => by
    rw [sh_apply]
    exact N.add_mem (hN X φ hφ) (N.smul_mem _ hφ)
  refine ⟨fun φ hφ => ?_, fun T hT φ hφ => ?_⟩
  · simp only [casA, cas, LinearMap.sub_apply, LinearMap.sum_apply, Module.End.mul_apply, LinearMap.smul_apply,
      Module.End.one_apply]
    exact N.sub_mem (N.sum_mem fun j _ => N.sub_mem (hs _ _ (hs _ _ hφ)) (hs _ _ (hs _ _ hφ))) (N.smul_mem _ hφ)
  · have ht : ∀ X, ∀ φ ∈ N, shift (lie E a) r X (T φ) = T (shift (lie E a) r X φ) := fun X φ hφ => by
      rw [sh_apply, sh_apply, hT.lie X φ hφ, map_add (f := _), map_smul]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [casA, cas, LinearMap.sub_apply, LinearMap.sum_apply, Module.End.mul_apply, LinearMap.smul_apply,
      Module.End.one_apply, map_sub, map_sum, map_smul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ht _ _ hφ, ht _ _ (hs _ _ hφ), ht _ _ hφ, ht _ _ (hs _ _ hφ)]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ConeD
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.coneD :
    UpperTheory.V.Cj.H.ConeD := by
  intro V F _ _ _ _ _ _ Y hYo hYc p hp q w hw
  have hseg : ∀ x ∈ Y, ∀ t ∈ Set.Icc (0:ℝ) 1, p + t • (x - p) ∈ Y := by
    intro x hx t ht
    have h := hYc hp hx (sub_nonneg.2 ht.2) ht.1 (by ring)
    convert h using 1
    rw [smul_sub, sub_smul, one_smul]
    abel
  let g : V × ℝ → V := fun z => p + z.2 • (z.1 - p)
  have hg : ContDiff ℝ ⊤ g := by
    exact contDiff_const.add (contDiff_snd.smul (contDiff_fst.sub contDiff_const))
  let W : Set (V × ℝ) := g ⁻¹' Y
  have hW : IsOpen W := hYo.preimage hg.continuous
  let Φ : V × ℝ → V [⋀^Fin q]→L[ℝ] F :=
    fun z => z.2 ^ q • (w (p + z.2 • (z.1 - p))).curryLeft (z.1 - p)
  have hΦ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ W := by
    have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : V × ℝ => w (g z)) W :=
      hw.comp (hg.of_le le_top).contDiffOn (fun z hz => hz)
    let L := (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := V) (F := F) (n := q)).toContinuousLinearMap
    have hfst : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : V × ℝ => z.1 - p) :=
      contDiff_fst.sub contDiff_const
    have h2 := (L.contDiff.comp_contDiffOn h1).clm_apply (hfst.contDiffOn (s := W))
    have hsnd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : V × ℝ => z.2 ^ q) :=
      contDiff_snd.pow q
    exact hsnd.contDiffOn.smul h2
  have hsub : Y ×ˢ Set.Icc (0:ℝ) 1 ⊆ W := fun z hz => hseg z.1 hz.1 z.2 hz.2
  refine ⟨UpperTheory.V.Lit.Dr.paramSmooth V (V [⋀^Fin q]→L[ℝ] F) Y W Φ hYo hW hsub hΦ, ?_⟩
  intro hcl x hx
  have hd := UpperTheory.V.Lit.Dr.paramDeriv V (V [⋀^Fin q]→L[ℝ] F) x W Φ hW (fun t ht => hseg x hx t ht) hΦ
  have hI : Set.uIcc (0:ℝ) 1 = Set.Icc 0 1 := Set.uIcc_of_le zero_le_one
  let A := ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ V F (n := q)
  have hint : IntervalIntegrable (fun t => fderiv ℝ (fun y => Φ (y, t)) x) MeasureTheory.volume 0 1 :=
    (hI ▸ hd.1).intervalIntegrable
  have hcont' : ContinuousOn (fun t => A (fderiv ℝ (fun y => Φ (y, t)) x)) (Set.uIcc 0 1) :=
    hI ▸ (A.continuous.comp_continuousOn hd.1)
  have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun r : ℝ => r ^ (q + 1) • w (p + r • (x - p))) (A (fderiv ℝ (fun y => Φ (y, t)) x)) t := by
    intro t ht
    rw [hI] at ht
    have hm := hseg x hx t ht
    have hdiff : DifferentiableAt ℝ w (p + t • (x - p)) :=
      (hw.contDiffAt (hYo.mem_nhds hm)).differentiableAt (by simp)
    exact UpperTheory.V.Lit.Dr.poinPt V F q w p x t hdiff (hcl _ hm)
  have hfd : fderiv ℝ (UpperTheory.V.Cj.H.coneOp p w) x = ∫ t in (0:ℝ)..1, fderiv ℝ (fun y => Φ (y, t)) x :=
    hd.2.fderiv
  have key : extDeriv (UpperTheory.V.Cj.H.coneOp p w) x = A (fderiv ℝ (UpperTheory.V.Cj.H.coneOp p w) x) := rfl
  rw [key, hfd, ← A.intervalIntegral_comp_comm hint,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont'.intervalIntegrable)]
  simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ConeLim
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.coneLim :
    UpperTheory.V.Cj.H.ConeLim := by
  intro V F _ _ _ _ Y hY p hp q w hw K hKY hK
  obtain ⟨C, hC⟩ := (hK.image (continuous_id.sub continuous_const :
    Continuous fun x : V => x - p)).isBounded.exists_norm_le
  set K' : Set V := (fun z : ℝ × V => p + z.1 • (z.2 - p)) '' (Set.Icc (0 : ℝ) 1 ×ˢ K)
  have hK'c : IsCompact K' := (isCompact_Icc.prod hK).image (by fun_prop)
  have hK'Y : K' ⊆ Y := by
    rintro _ ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
    exact hY.add_smul_sub_mem hp (hKY hx) ht
  have hwK := hw K' hK'Y hK'c
  rw [Metric.tendstoUniformlyOn_iff] at hwK ⊢
  intro ε hε
  have hR : 0 < |C| + 1 := by positivity
  filter_upwards [hwK (ε / 2 / (|C| + 1)) (by positivity)] with k hk x hx
  simp only [Pi.zero_apply, dist_zero_left] at hk ⊢
  have hxp : ‖x - p‖ ≤ |C| + 1 := by
    have h0 := hC (x - p) ⟨x, hx, rfl⟩
    linarith [le_abs_self C]
  have hbound : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      ‖t ^ q • (w k (p + t • (x - p))).curryLeft (x - p)‖ ≤ ε / 2 / (|C| + 1) * (|C| + 1) := by
    intro t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    have hy : p + t • (x - p) ∈ K' := ⟨(t, x), ⟨⟨ht.1.le, ht.2⟩, hx⟩, rfl⟩
    have h1 := hk _ hy
    rw [norm_smul, norm_pow, Real.norm_eq_abs, abs_of_pos ht.1]
    have h2 : t ^ q ≤ 1 := pow_le_one₀ ht.1.le ht.2
    have h3 : ‖(w k (p + t • (x - p))).curryLeft (x - p)‖
        ≤ ‖w k (p + t • (x - p))‖ * ‖x - p‖ := by
      refine (ContinuousLinearMap.le_opNorm _ _).trans_eq ?_
      rw [ContinuousAlternatingMap.norm_curryLeft]
    have h4 : ‖w k (p + t • (x - p))‖ * ‖x - p‖ ≤ ε / 2 / (|C| + 1) * (|C| + 1) :=
      mul_le_mul h1.le hxp (norm_nonneg _) (by positivity)
    calc t ^ q * ‖(w k (p + t • (x - p))).curryLeft (x - p)‖
        ≤ 1 * ‖(w k (p + t • (x - p))).curryLeft (x - p)‖ :=
          mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ ≤ ε / 2 / (|C| + 1) * (|C| + 1) := by
          rw [one_mul]
          exact h3.trans h4
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  have e : ε / 2 / (|C| + 1) * (|C| + 1) = ε / 2 := by field_simp
  rw [e] at hint
  simp only [sub_zero, abs_one, mul_one] at hint
  calc ‖UpperTheory.V.Cj.H.coneOp p (w k) x‖
      = ‖∫ t in (0 : ℝ)..1, t ^ q • (w k (p + t • (x - p))).curryLeft (x - p)‖ := rfl
    _ ≤ ε / 2 := hint
    _ < ε := by linarith
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ContrSingle
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

noncomputable section

namespace UpperTheory.V.Cj.H

private theorem multi_cont {H : Type} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H] [IsTopologicalAddGroup H]
    [ContinuousSMul ℝ H] [T2Space H] [FiniteDimensional ℝ H] {q : ℕ} (f : (Fin q → H) →ₘₗ[ℝ] ℂ) :
    Continuous f := by
  classical
  let b := Module.finBasis ℝ H
  have h : (f : (Fin q → H) → ℂ) = fun x => ∑ r : Fin q → Fin (Module.finrank ℝ H),
      (∏ i, b.coord (r i) (x i)) • f fun i => b (r i) := by
    funext x
    have e : x = fun i => ∑ j, b.coord j (x i) • b j := funext fun i => (b.sum_repr (x i)).symm
    conv_lhs => rw [e]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [f.map_sum]
    exact Finset.sum_congr rfl fun r _ => f.map_smul_univ _ _
  rw [h]
  refine continuous_finsetSum _ fun r _ => Continuous.fun_smul (continuous_finsetProd _ fun i _ => ?_) continuous_const
  exact (b.coord (r i)).continuous_of_finiteDimensional.comp (continuous_apply i)

private def contr {S : Type} [AddCommGroup S] [Module ℂ S] {d : ℕ} :
    (Fin d → ℂ) →ₗ[ℂ] S ⊗[ℂ] (Fin d → ℂ) →ₗ[ℂ] S :=
  ∑ i, (LinearMap.proj i : (Fin d → ℂ) →ₗ[ℂ] ℂ).smulRight (Bor.cmp i)

private theorem contr_tmul {S : Type} [AddCommGroup S] [Module ℂ S] {d : ℕ} (v u : Fin d → ℂ) (φ : S) :
    contr v (φ ⊗ₜ[ℂ] u) = (v ⬝ᵥ u) • φ := by
  simp [contr, LinearMap.sum_apply, dotProduct, Finset.sum_smul, smul_smul]

private theorem contr_single {S : Type} [AddCommGroup S] [Module ℂ S] {d : ℕ} (i : Fin d) (m : S ⊗[ℂ] (Fin d → ℂ)) :
    contr (Pi.single i 1) m = Bor.cmp i m := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul φ u => simp [contr_tmul]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private theorem abs_type {K H S : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [AddCommGroup H] [Module ℝ H] [TopologicalSpace H] [IsTopologicalAddGroup H]
    [ContinuousSMul ℝ H] [T2Space H] [FiniteDimensional ℝ H] [AddCommGroup S] [Module ℂ S] [Module ℝ S] [IsScalarTower ℝ ℂ S]
    {d : ℕ} (q : ℕ) (ad : K →* (H →ₗ[ℝ] H)) (had : ∀ X, Continuous fun k => ad k X)
    (M : K →* Matrix (Fin d) (Fin d) ℂ) (hM : Continuous M) (π : Representation ℂ K S) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : FiniteDimensional ℂ W)
      (ρ : Representation ℂ K W), GlobalTheory.Published.AutFin.IsContRep ρ ∧
      ∀ ω : (Fin q → H) →ₘₗ[ℝ] S ⊗[ℂ] (Fin d → ℂ),
        (∀ k X, ω (fun i => ad k (X i)) = TensorProduct.map (π k) (Matrix.toLin' (M k)) (ω X)) → ∀ X i,
      ∃ (T : W →ₗ[ℂ] S) (w : W), (∀ k v, T (ρ k v) = π k (T v)) ∧ T w = Bor.cmp i (ω X) := by
  classical
  let P := PiTensorProduct ℝ fun _ : Fin q => H
  let A : K → P →ₗ[ℝ] P := fun k => PiTensorProduct.map fun _ => ad k
  let B : K → (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ) := fun k => Matrix.toLin' (M k⁻¹)ᵀ
  let ρ : Representation ℂ K ((Fin d → ℂ) ⊗[ℝ] P) :=
    { toFun := fun k => TensorProduct.AlgebraTensorModule.map (B k) (A k)
      map_one' := by
        have h1 : A 1 = LinearMap.id := by
          simp only [A, map_one]; exact PiTensorProduct.map_one
        have h2 : B 1 = LinearMap.id := by simp [B]
        rw [h1, h2, TensorProduct.AlgebraTensorModule.map_id]; rfl
      map_mul' := fun k l => by
        have h1 : A (k * l) = A k ∘ₗ A l := by
          simp only [A, map_mul]; exact PiTensorProduct.map_mul _ _
        have h2 : B (k * l) = B k ∘ₗ B l := by simp [B, Matrix.toLin'_mul]
        rw [h1, h2, TensorProduct.AlgebraTensorModule.map_comp]; rfl }
  have hρ : ∀ k v (X : Fin q → H), ρ k (v ⊗ₜ[ℝ] PiTensorProduct.tprod ℝ X) =
      ((M k⁻¹)ᵀ *ᵥ v) ⊗ₜ[ℝ] PiTensorProduct.tprod ℝ fun i => ad k (X i) := fun k v X => by
    change TensorProduct.AlgebraTensorModule.map (B k) (A k) _ = _
    rw [TensorProduct.AlgebraTensorModule.map_tmul]
    exact congrArg₂ _ rfl (PiTensorProduct.map_tprod _ _)
  have ind : ∀ (p : (Fin d → ℂ) ⊗[ℝ] P → Prop) (h0 : p 0) (ha : ∀ x y, p x → p y → p (x + y))
      (ht : ∀ v (X : Fin q → H), p (v ⊗ₜ[ℝ] PiTensorProduct.tprod ℝ X)) (w : (Fin d → ℂ) ⊗[ℝ] P), p w := by
    intro p h0 ha ht w
    induction w using TensorProduct.induction_on with
    | zero => exact h0
    | add x y hx hy => exact ha x y hx hy
    | tmul v t =>
      induction t using PiTensorProduct.induction_on with
      | smul_tprod r X => rw [← TensorProduct.smul_tmul]; exact ht _ _
      | add x y hx hy => rw [TensorProduct.tmul_add]; exact ha _ _ hx hy
  refine ⟨(Fin d → ℂ) ⊗[ℝ] P, inferInstance, inferInstance, Module.Finite.of_restrictScalars_finite ℝ ℂ _, ρ,
    fun ℓ w => ?_, fun ω hω X i => ?_⟩
  · induction w using ind with
    | h0 => simpa using continuous_const
    | ha x y hx hy => simpa only [map_add (f := _)] using hx.fun_add hy
    | ht v X =>
      have e : (fun k => ℓ (ρ k (v ⊗ₜ[ℝ] PiTensorProduct.tprod ℝ X))) = fun k => ∑ j, ((M k⁻¹)ᵀ *ᵥ v) j *
          ((ℓ.restrictScalars ℝ ∘ₗ TensorProduct.mk ℝ (Fin d → ℂ) P (Pi.single j 1)).compMultilinearMap
            (PiTensorProduct.tprod ℝ)) fun i => ad k (X i) := by
        funext k
        rw [hρ]
        generalize (M k⁻¹)ᵀ *ᵥ v = u
        conv_lhs => rw [pi_eq_sum_univ' u]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [TensorProduct.sum_tmul, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← TensorProduct.smul_tmul', map_smul]
        rfl
      rw [e]
      refine continuous_finsetSum _ fun j _ => Continuous.mul ?_ ?_
      · exact (continuous_apply j).comp ((hM.comp continuous_inv).matrix_transpose.matrix_mulVec continuous_const)
      · exact (multi_cont _).comp (continuous_pi fun i => had _)
  · let T : (Fin d → ℂ) ⊗[ℝ] P →ₗ[ℂ] S := TensorProduct.AlgebraTensorModule.lift
      { toFun := fun v => (contr v).restrictScalars ℝ ∘ₗ PiTensorProduct.lift ω
        map_add' := fun u v => by ext; simp
        map_smul' := fun c v => by ext; simp }
    have hT : ∀ v (Y : Fin q → H), T (v ⊗ₜ[ℝ] PiTensorProduct.tprod ℝ Y) = contr v (ω Y) := fun v Y => by
      exact congrArg (contr v) (PiTensorProduct.lift.tprod (φ := ω) Y)
    refine ⟨T, Pi.single i 1 ⊗ₜ[ℝ] PiTensorProduct.tprod ℝ X, fun k w => ?_, by rw [hT, contr_single]⟩
    induction w using ind with
    | h0 => simp
    | ha x y hx hy => simp only [map_add (f := _), hx, hy]
    | ht v Y =>
      rw [hρ, hT, hT, hω]
      induction ω Y using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
      | tmul φ u =>
        rw [TensorProduct.map_tmul, contr_tmul, contr_tmul, map_smul, Matrix.toLin'_apply, Matrix.mulVec_transpose,
          ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec]

end UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.kType :
    UpperTheory.V.Cj.H.KType := by
  intro E _ _ _ a Ξ q
  let ad : Kinf E a →* (Herm E a →ₗ[ℝ] Herm E a) :=
    { toFun := fun k =>
        { toFun := adHerm k
          map_add' := fun X Y => Subtype.ext (by simp [adHerm, mul_add, add_mul])
          map_smul' := fun c X => Subtype.ext (by simp [adHerm]) }
      map_one' := LinearMap.ext fun X => Subtype.ext (by simp [adHerm])
      map_mul' := fun k l => LinearMap.ext fun X => Subtype.ext (by simp [adHerm, mul_assoc]) }
  have had : ∀ X, Continuous fun k => ad k X := fun X =>
    Continuous.subtype_mk ((continuous_subtype_val.mul continuous_const).mul continuous_subtype_val.star) _
  have hM : Continuous (Ξ.mat.comp (Unitary.toUnits : Kinf E a →* _)) := by
    refine continuous_matrix fun i j => continuous_iff_continuousAt.2 fun k => ?_
    have h := (differentiableAt_extGL (Ξ.reg i j) (x := toL (Unitary.toUnits k).val) (Unitary.toUnits k).isUnit).continuousAt
    have h2 : Continuous fun l : Kinf E a => (toL (Unitary.toUnits l).val : Lie E a) := continuous_subtype_val
    have h3 := ContinuousAt.comp (f := fun l : Kinf E a => (toL (Unitary.toUnits l).val : Lie E a)) h h2.continuousAt
    simp only [Function.comp_def, extGL_val] at h3
    exact h3
  obtain ⟨W, i1, i2, i3, ρ, h1, h2⟩ := abs_type q ad had _ hM (cptRep E a)
  exact ⟨W, i1, i2, i3, ρ, h1, fun ω hω => h2 ω.toMultilinearMap hω⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.HdHd
section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.hdHd :
    UpperTheory.V.Cj.H.HdHd := by
  intro Γ M _ _ _ ρ k b hb
  refine ⟨?_, fun x _ => UpperTheory.V.Cj.A.hdFacts.1 Γ M b x⟩
  exact UpperTheory.V.Cj.A.hdFacts.2.2.2.2.2 Γ Γ M ρ k b hb
end

