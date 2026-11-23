module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
public import GroundTheory.GlobalFields.IdeleGroups.NormOneCompact
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0282

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfBddInt
section
open UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Lit.Geo.Pf.bddInt :
    UpperTheory.V.Lit.Geo.Pf.BddInt := by
  intro E _ _ _ a μ _ F hF ⟨C, hC⟩
  haveI := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a μ
  have h := GlobalTheory.CuspQuot.memL2_of_bound (μ := μ) hF.cont
    (GlobalTheory.CuspRep.CuspidalL2GL.leftInv_latticeGL hF.left hF.centre) hC
  exact ⟨h.2.integrable one_le_two, h⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfChiOne
section
open UpperTheory.V.Lit.Geo


open NumberField Formalism.L2.Host GroundTheory.Global in
private theorem norm_of_normOne {E : Type} [Field E] [NumberField E] (χ : HChar E) {y : IdeleGroup E}
    (hy : y ∈ IdeleGroup.normOneSubgroup E) : ‖((χ.1 y : ℂˣ) : ℂ)‖ = 1 := by
  obtain ⟨D, hD, -, hxD⟩ := IdeleGroup.exists_isCompact_normOneSubgroup E
  have hc : Continuous fun z : IdeleGroup E => ((χ.1 z : ℂˣ) : ℂ) := Units.continuous_val.comp χ.2.1
  obtain ⟨M, hM⟩ := hD.exists_bound_of_continuousOn hc.continuousOn
  have hb : ∀ z ∈ IdeleGroup.normOneSubgroup E, ‖((χ.1 z : ℂˣ) : ℂ)‖ ≤ M := fun z hz => by
    obtain ⟨k, hk⟩ := hxD z hz
    have h := hM _ hk
    have h1 : χ.1 (IdeleGroup.diagonal E k) = 1 := χ.2.2 k
    have h2 : χ.1 (IdeleGroup.diagonal E k * z) = χ.1 z :=
      (map_mul χ.1 _ _).trans (by rw [h1, one_mul])
    rwa [h2] at h
  have hle : ∀ z ∈ IdeleGroup.normOneSubgroup E, ‖((χ.1 z : ℂˣ) : ℂ)‖ ≤ 1 := fun z hz => by
    by_contra h
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M (not_le.1 h)
    have h3 := hb _ (pow_mem hz n)
    have h4 : χ.1 (z ^ n) = χ.1 z ^ n := map_pow χ.1 z n
    rw [h4, Units.val_pow_eq_pow_val, norm_pow] at h3
    exact (not_le.2 hn) h3
  have h5 := hle _ (inv_mem hy)
  have h6 : χ.1 y⁻¹ = (χ.1 y)⁻¹ := map_inv χ.1 y
  rw [h6, Units.val_inv_eq_inv_val, norm_inv, inv_le_one₀ (norm_pos_iff.2 (Units.ne_zero _))] at h5
  exact le_antisymm (hle _ hy) h5

theorem UpperTheory.V.Lit.Geo.Pf.chiOne :
    UpperTheory.V.Lit.Geo.Pf.ChiOne := by
  intro E _ _ _ a χ s _ g
  exact norm_of_normOne χ g.2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfCsBdd
section
open UpperTheory.V.Lit.Geo

section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

private theorem exists_split' {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (g : GA E a) :
    ∃ t : ℝ, splitCentre E a t * g = (retractOne g : UpperTheory.V.KernelIndexFullLattice.G1 E a).1 := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact ⟨0, Units.ext (Subsingleton.elim _ _)⟩
  have h1 : (0 : ℝ) < a := Nat.cast_pos.2 ha
  have h2 : (0 : ℝ) < Module.finrank ℚ E := Nat.cast_pos.2 Module.finrank_pos
  refine ⟨Real.log ((Reduction.detModule E a g)⁻¹).1 / (a * Module.finrank ℚ E), ?_⟩
  rw [UpperTheory.V.KernelIndexFullLattice.splitEq_holds E a, coe_retractOne, ← centralSection_inv_mul_comm,
    ← map_inv (Reduction.centralSection E a)]
  refine congrArg (fun s => Reduction.centralSection E a s * g) (Subtype.ext ?_)
  change Real.exp _ = _
  rw [mul_div_cancel₀ _ (mul_pos h1 h2).ne', Real.exp_log ((Reduction.detModule E a g)⁻¹).2]

theorem UpperTheory.V.Lit.Geo.Pf.csBdd :
    UpperTheory.V.Lit.Geo.Pf.CsBdd := by
  intro E _ _ _ a F hF h
  rcases h with ⟨R, hR⟩ | ⟨C, hC⟩
  · obtain ⟨K, hK, hK'⟩ := (qhtFacts E a).2.2.2 R
    obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hF.cont.continuousOn
    refine ⟨max M 0, fun g => ?_⟩
    rcases lt_or_ge R (qht g) with hg | hg
    · rw [hR g hg, norm_zero]; exact le_max_right _ _
    · obtain ⟨γ, t, hm⟩ := hK' g hg
      have := hM _ hm
      rw [mul_assoc, hF.left, hF.centre] at this
      exact this.trans (le_max_left _ _)
  · refine ⟨C, fun g => ?_⟩
    obtain ⟨t, ht⟩ := exists_split' g
    rw [← hF.centre t g, ht]
    exact hC _

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfCsLie
section
open UpperTheory.V.Lit.Geo GlobalTheory.CuspRep Filter Topology

theorem UpperTheory.V.Lit.Geo.Pf.csLie :
    UpperTheory.V.Lit.Geo.Pf.CsLie := by
  intro E _ _ _ a φ X ⟨R, hR⟩
  obtain ⟨c, c0, -, ccont, cder, -⟩ := UpperTheory.V.Lit.Bor.oneParam E a X
  obtain ⟨h1, -, h3, -⟩ := qhtFacts E a
  obtain ⟨B, hB⟩ := h3 _ ((isCompact_Icc (a := (-1 : ℝ)) (b := 1)).image ccont.inv)
  refine ⟨B * R, fun g hg => ?_⟩
  have hd := GlobalTheory.CuspRep.hasDerivAt_curve φ g c X c0 cder
  have hz : (fun t : ℝ => φ.1 (g * infGL E a (c t))) =ᶠ[𝓝 0] fun _ => (0 : ℂ) := by
    filter_upwards [Icc_mem_nhds (show (-1 : ℝ) < 0 by norm_num) (show (0 : ℝ) < 1 by norm_num)] with t ht
    refine hR _ (not_le.1 fun hle => ?_)
    have h := hB (g * infGL E a (c t)) _ ⟨t, ht, rfl⟩
    simp only [Pi.inv_apply, mul_inv_cancel_right] at h
    have hp := h1 (g * infGL E a (c t))
    have hg1 := h1 g
    have hB0 : 0 ≤ B := by
      by_contra hn
      nlinarith [not_le.1 hn]
    exact absurd (h.trans (mul_le_mul_of_nonneg_left hle hB0)) (not_le.2 hg)
  exact hd.unique ((hasDerivAt_const (0 : ℝ) (0 : ℂ)).congr_of_eventuallyEq hz)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfInvLie
section
open UpperTheory.V.Lit.Geo

section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit UpperTheory.V.Lit.Bor

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem level_lie (X : Lie E a) (φ : Sm E a) (h : IsOpen {k | act (.fin k) φ = φ}) :
    IsOpen {k | act (.fin k) (lie E a X φ) = lie E a X φ} := by
  let S : Sm E a → Subgroup (GL (Fin a) (GlobalTheory.CuspRep.Af E)) := fun θ =>
    { carrier := {k | finRep E a k θ = θ}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [map_mul, Module.End.mul_apply, hy, hx]
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at hx ⊢
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hle : S φ ≤ S (lie E a X φ) := fun k hk => by
    have e : lie E a X (finRep E a k φ) = finRep E a k (lie E a X φ) :=
      LinearMap.congr_fun (lie_rt_fin X k) φ
    have hk' : finRep E a k φ = φ := hk
    change finRep E a k (lie E a X φ) = lie E a X φ
    rw [← e, hk']
  exact Subgroup.isOpen_mono hle h

private theorem left_lie (X : Lie E a) (φ : Sm E a) (x : GA E a) (h : ∀ g, φ.1 (x * g) = φ.1 g) (g : GA E a) :
    (lie E a X φ).1 (x * g) = (lie E a X φ).1 g := by
  obtain ⟨c, c0, -, -, cder, -⟩ := UpperTheory.V.Lit.Bor.oneParam E a X
  have h1 := hasDerivAt_curve φ (x * g) c X c0 cder
  have h2 := hasDerivAt_curve φ g c X c0 cder
  simp only [mul_assoc, h] at h1
  exact h1.unique h2

theorem UpperTheory.V.Lit.Geo.Pf.invLie :
    UpperTheory.V.Lit.Geo.Pf.InvLie := by
  intro E _ _ _ a φ h
  exact ⟨⟨ContAut.continuous_of_isOpen_stab E a φ h.level, h.left, h.centre⟩, fun X =>
    ⟨fun γ => left_lie X φ _ (h.left γ), fun t => left_lie X φ _ (h.centre t), level_lie X φ h.level⟩⟩

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfLevInv
section
open UpperTheory.V.Lit.Geo
open NumberField Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private def levSub {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) : Submodule ℂ (Sm E a) where
  carrier := {φ | IsLevelFn U Ξ φ}
  zero_mem' := ⟨fun _ _ => rfl, fun u _ => map_zero _, fun m _ => by simp⟩
  add_mem' := fun {φ ψ} h h' => ⟨fun γ g => congrArg₂ (· + ·) (h.1 γ g) (h'.1 γ g),
    fun u hu => by rw [map_add (f := _), h.2.1 u hu, h'.2.1 u hu],
    fun m hm => by rw [map_add (f := _), h.2.2 m hm, h'.2.2 m hm, smul_add]⟩
  smul_mem' := fun c φ h => ⟨fun γ g => congrArg (c • ·) (h.1 γ g),
    fun u hu => by rw [map_smul, h.2.1 u hu],
    fun m hm => by rw [map_smul, h.2.2 m hm, smul_comm]⟩

private theorem stab_open {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (v : V) {S : Set G} (hS : IsOpen S) (h1 : (1 : G) ∈ S) (h : ∀ g ∈ S, ρ g v = v) :
    IsOpen {g | ρ g v = v} := by
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  refine ⟨(fun x => g⁻¹ * x) ⁻¹' S, fun x hx => ?_, hS.preimage (by fun_prop), by simpa using h1⟩
  have e : x = g * (g⁻¹ * x) := by group
  have hg' : ρ g v = v := hg
  show ρ x v = v
  rw [e, map_mul, Module.End.mul_apply, h _ hx, hg']

theorem UpperTheory.V.Lit.Geo.Pf.levInv :
    UpperTheory.V.Lit.Geo.Pf.LevInv := by
  intro E _ _ _ a ha U hU Ξ r χ h1 hχ q α hα X j
  have hφ : IsLevelFn U Ξ (cmp j (α X)) :=
    mem_tens.1 (span_le_tens (N := levSub U Ξ) (fun φ h => h) (hα.val X)) j
  generalize cmp j (α X) = φ at hφ
  refine ⟨fun γ g => ?_, fun t g => ?_, ?_⟩
  · rw [mulChi_apply, mulChi_apply, map_mul, chiDet_ratGL, one_mul, hφ.1]
  · have hz : lie E a (oneL E a) (mulChi a χ φ) = (0 : ℂ) • mulChi a χ φ := by
      rw [hχ.2, hφ.2.2 _ h1, (ellFacts E a).1 ha, mul_one, ← add_smul, neg_add_cancel, zero_smul, map_zero, zero_smul]
    rw [aInv E a _ _ hz t g, zero_mul, Complex.exp_zero, one_mul]
  · change IsOpen {k | finRep E a k (mulChi a χ φ) = mulChi a χ φ}
    refine stab_open (finRep E a) _ (hU.inter (isOpen_ker_chiDet (a := a) χ)) ⟨U.one_mem, by simp⟩ ?_
    rintro k ⟨hk, h2⟩
    have h1' : rt E a (finGL E a k) φ = φ := hφ.2.1 k hk
    have h2' : chiDet a χ (finGL E a k) = 1 := h2
    change rt E a (finGL E a k) (mulChi a χ φ) = _
    rw [rt_mulChi, h1', h2']
    simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfProdEx
section
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit.Geo

section

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem chart_conj_mul (f h : GA E a → ℂ) (g : GA E a) :
    chart (fun x => starRingEnd ℂ (f x) * h x) g = fun y => Complex.conjCLE (chart f g y) * chart h g y := by
  funext y
  unfold chart
  split_ifs <;> simp

end

theorem UpperTheory.V.Lit.Geo.Pf.prodEx :
    UpperTheory.V.Lit.Geo.Pf.ProdEx := by
  intro E _ _ _ a φ ψ
  refine ⟨⟨fun x => starRingEnd ℂ (φ.1 x) * ψ.1 x, fun g => ?_⟩, fun _ => rfl, fun X g => ?_⟩
  · rw [chart_conj_mul]
    exact (Complex.conjCLE.contDiff.comp_contDiffOn (φ.2 g)).mul (ψ.2 g)
  · have hv : ∀ f : GA E a → ℂ, chart f g (oneL E a) = f g := fun f => by
      simpa using chart_val f g 1
    change fderiv ℝ (chart (fun x => starRingEnd ℂ (φ.1 x) * ψ.1 x) g) (oneL E a) X =
      starRingEnd ℂ (fderiv ℝ (chart φ.1 g) (oneL E a) X) * ψ.1 g +
        starRingEnd ℂ (φ.1 g) * fderiv ℝ (chart ψ.1 g) (oneL E a) X
    have h1 := (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp (oneL E a)
      (differentiableAt_chart φ.2 g).hasFDerivAt).fun_mul (differentiableAt_chart ψ.2 g).hasFDerivAt
    rw [chart_conj_mul]
    refine (congrArg (fun L => L X) h1.fderiv).trans ?_
    simp [hv, mul_comm, add_comm]
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfPtPos
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open UpperTheory.V.Lit.Geo
open scoped TensorProduct ComplexOrder

theorem UpperTheory.V.Lit.Geo.Pf.ptPos :
    UpperTheory.V.Lit.Geo.Pf.PtPos := by
  intro E _ _ _ a Ξ χ G hG n e he q α
  have hnn : ∀ v : Fin Ξ.d → ℂ, 0 ≤ star v ⬝ᵥ G *ᵥ v := fun v => hG.pos.posSemidef.dotProduct_mulVec_nonneg v
  refine ⟨fun g => ?_, fun h0 => ?_⟩
  · have h : 0 ≤ ptIp χ G e α α g :=
      mul_nonneg (Complex.zero_le_real.2 (by positivity)) (Finset.sum_nonneg fun I _ => hnn _)
    obtain ⟨h1, h2⟩ := Complex.nonneg_iff.1 h
    exact ⟨_, h1, Complex.ext rfl h2.symm⟩
  · have h2 : ∀ I : Fin q → Fin n, (α fun i => e (I i)) = 0 := fun I => by
      have hev : ∀ g, ev (α fun i => e (I i)) g = 0 := fun g => by
        have h := h0 g
        rw [ptIp, mul_eq_zero] at h
        rcases h with h | h
        · simp at h
        · have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun I _ => hnn _)).1 h I (Finset.mem_univ _)
          by_contra hne
          exact (hG.pos.dotProduct_mulVec_pos hne).ne' h1
      rw [← sum_cmp (α fun i => e (I i))]
      refine Finset.sum_eq_zero fun j _ => ?_
      have : cmp j (α fun i => e (I i)) = 0 := Subtype.ext (funext fun g => by
        rw [Pf.cmp_ev, hev]; rfl)
      rw [this, TensorProduct.zero_tmul]
    refine AlternatingMap.ext fun X => ?_
    have hX : X = fun i => ∑ j, trF (e j).1 (X i).1 • e j := funext fun i => he (X i)
    have h3 : α X = ∑ I : Fin q → Fin n, α fun i => trF (e (I i)).1 (X i).1 • e (I i) := by
      conv_lhs => rw [hX]
      exact α.toMultilinearMap.map_sum (fun i j => trF (e j).1 (X i).1 • e j)
    rw [h3, AlternatingMap.zero_apply]
    refine Finset.sum_eq_zero fun I _ => ?_
    rw [α.map_smul_univ (fun i => trF (e (I i)).1 (X i).1) (fun i => e (I i)), h2, smul_zero]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PfZeroInt
section
open UpperTheory.V.Lit.Geo
open NumberField MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC
open UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor
open scoped GlobalTheory.CuspRep.CuspidalL2GL

theorem UpperTheory.V.Lit.Geo.Pf.zeroInt :
    UpperTheory.V.Lit.Geo.Pf.ZeroInt := by
  intro E _ _ _ a μ _ F hF hpos hI h0
  have hL : GlobalTheory.AutomorphicL2Unitary.LeftInv (latticeGL E a) F := CuspidalL2GL.leftInv_latticeGL hF.left hF.centre
  have hn : ∀ g, F g = ((‖F g‖ : ℝ) : ℂ) := fun g => by
    obtain ⟨t, ht, e⟩ := hpos g
    rw [e, Complex.norm_real, Real.norm_of_nonneg ht]
  have h1 : ∫ x : GlobalTheory.AutomorphicL2Unitary.Quot (latticeGL E a), ‖F x.out‖ ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ) = 0 := by
    have h2 : Pf.qint μ F =
        ((∫ x : GlobalTheory.AutomorphicL2Unitary.Quot (latticeGL E a), ‖F x.out‖ ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure (latticeGL E a) μ) : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => hn _)
    rw [h0] at h2
    exact_mod_cast h2.symm
  have h3 := (integral_eq_zero_iff_of_nonneg (fun x => norm_nonneg _) (Integrable.norm hI)).1 h1
  have h4 : F =ᵐ[μ] fun _ => 0 := by
    filter_upwards [GlobalTheory.AutomorphicL2Unitary.ae_quotMeasure_iff.1 h3] with g hg
    have e : F (GlobalTheory.AutomorphicL2Unitary.mk (latticeGL E a) g).out = F g := hL.descend_mk g
    simpa [e] using hg
  exact fun g => congrFun ((Continuous.ae_eq_iff_eq μ hF.cont continuous_const).1 h4) g
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PtZsmulRight
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo
open scoped TensorProduct

namespace UpperTheory.V.Lit.Geo.Pf

section
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (χ : Formalism.L2.Host.HChar E) {d : ℕ}
  (G : Matrix (Fin d) (Fin d) ℂ) (g : GA E a)

private theorem ev_eq (x : Sm E a ⊗[ℂ] (Fin d → ℂ)) : ev x g = fun j => (cmp j x).1 g :=
  funext fun j => (cmp_ev x j g).symm

private theorem ev_add' (x y : Sm E a ⊗[ℂ] (Fin d → ℂ)) : ev (x + y) g = ev x g + ev y g := by
  funext j
  simp [ev_eq]

private noncomputable def ptL (y : Sm E a ⊗[ℂ] (Fin d → ℂ)) : Sm E a ⊗[ℂ] (Fin d → ℂ) →+ ℂ :=
  AddMonoidHom.mk' (fun x => pt χ G x y g) fun x x' => by
    simp only [pt, ev_add', star_add, add_dotProduct, mul_add]

private noncomputable def ptR (x : Sm E a ⊗[ℂ] (Fin d → ℂ)) : Sm E a ⊗[ℂ] (Fin d → ℂ) →+ ℂ :=
  AddMonoidHom.mk' (fun y => pt χ G x y g) fun y y' => by
    simp only [pt, ev_add', mulVec_add, dotProduct_add, mul_add]

private theorem pt_sum_left {ι : Type} (s : Finset ι) (x : ι → Sm E a ⊗[ℂ] (Fin d → ℂ)) (y : Sm E a ⊗[ℂ] (Fin d → ℂ)) :
    pt χ G (∑ i ∈ s, x i) y g = ∑ i ∈ s, pt χ G (x i) y g := map_sum (ptL χ G g y) x s

private theorem pt_sum_right {ι : Type} (s : Finset ι) (x : Sm E a ⊗[ℂ] (Fin d → ℂ)) (y : ι → Sm E a ⊗[ℂ] (Fin d → ℂ)) :
    pt χ G x (∑ i ∈ s, y i) g = ∑ i ∈ s, pt χ G x (y i) g := map_sum (ptR χ G g x) y s

private theorem pt_zsmul_left (k : ℤ) (x y : Sm E a ⊗[ℂ] (Fin d → ℂ)) :
    pt χ G (k • x) y g = k • pt χ G x y g := map_zsmul (ptL χ G g y) k x

private theorem pt_zsmul_right (k : ℤ) (x y : Sm E a ⊗[ℂ] (Fin d → ℂ)) :
    pt χ G x (k • y) g = k • pt χ G x y g := map_zsmul (ptR χ G g x) k y

end

end UpperTheory.V.Lit.Geo.Pf

open UpperTheory.V.Lit.Geo.Pf in
theorem UpperTheory.V.Lit.Geo.Pf.ptD :
    UpperTheory.V.Lit.Geo.Pf.PtD := by
  intro E _ _ _ a Ξ χ G n e q L β η g
  refine ⟨?_, ?_⟩
  · have key : ∀ i : Fin (q + 1), ∑ I : Fin (q + 1) → Fin n,
        pt χ G (β fun k => e (I k)) ((-1 : ℤ) ^ (i : ℕ) • L (toL (e (I i)).1) (η (i.removeNth fun k => e (I k)))) g =
        ∑ J : Fin q → Fin n, ∑ j,
          pt χ G (β (Matrix.vecCons (e j) fun i => e (J i))) (L (toL (e j).1) (η fun i => e (J i))) g := fun i => by
      rw [← (Fin.insertNthEquiv (fun _ => Fin n) i).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
      refine Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun j _ => ?_
      have h1 : (fun k => e ((Fin.insertNthEquiv (fun _ => Fin n) i (j, J)) k)) =
          i.insertNth (α := fun _ => Herm E a) (e j) (fun k => e (J k)) := by
        funext k
        refine Fin.succAboveCases i ?_ (fun k => ?_) k <;> simp [Fin.insertNthEquiv]
      have h2 : (Fin.insertNthEquiv (fun _ => Fin n) i (j, J)) i = j := by simp [Fin.insertNthEquiv]
      rw [h1, h2, Fin.removeNth_insertNth, AlternatingMap.map_insertNth, pt_zsmul_left, pt_zsmul_right,
        smul_smul, ← mul_pow]
      simp
    have h0 : ptIp χ G e β (dCo L η) g = ∑ i : Fin (q + 1), ∑ I : Fin (q + 1) → Fin n,
        pt χ G (β fun k => e (I k)) ((-1 : ℤ) ^ (i : ℕ) • L (toL (e (I i)).1) (η (i.removeNth fun k => e (I k)))) g := by
      rw [Finset.sum_comm, ptIp_eq]
      refine Finset.sum_congr rfl fun I _ => ?_
      rw [dCo_apply, pt_sum_right]
    rw [h0, Finset.sum_congr rfl fun i _ => key i]
    simp
  · rw [ptIp_eq]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [del_apply, pt_sum_left]
end

