module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle0003
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionPreservesThetaAndInnerProduct
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelTestFunctionFiniteSumEquivariant
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ProdLevelOneThetaEqVacuumTheta
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaVacuumUnitaryColumnChangeUnitFactor
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ShortThetaValueComplexPointEqClassicalTheta
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DualHalfLevelMarkingExistsAndMatch
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MultiplierSqMulDetUnitaryColumnChange
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RootsLevelPointsSameVacuumTranslates
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnifMetricScalar
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0176
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkings

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CmHostIdempotentTraceEqOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

namespace GlobalTheory.Phase.ChangePt

section Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g q0 n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ}

theorem cmHost_idempotent_trace_eq_one (H : Host E) : (H.w0 : E) + cc (H.w0 : E) = 1 := by
  have h2 : 2 * (H.w0 : E) = 1 + (H.rt : E) := by
    simpa [map_ofNat] using congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
  have hs : (H.rt : E) ^ 2 = -(H.d : E) := by
    simpa using congrArg (algebraMap (𝓞 E) E) H.rt_sq
  have hc : cc (H.rt : E) = -(H.rt : E) := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    have h1 : τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by rw [← map_pow, hs]; simp
    have hre : (τ (H.rt : E)).re = 0 := by
      have a1 := congrArg Complex.re h1
      have a2 := congrArg Complex.im h1
      simp [pow_two] at a1 a2
      have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
      by_contra hne
      have : (τ (H.rt : E)).im = 0 := by
        have : (τ (H.rt : E)).re * (τ (H.rt : E)).im = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left hne
      rw [this] at a1
      nlinarith [mul_self_nonneg (τ (H.rt : E)).re]
    rw [cc, IsCMField.complexEmbedding_complexConj, map_neg]
    apply Complex.ext <;> simp [hre]
  have h3 : 2 * cc (H.w0 : E) = 1 + cc (H.rt : E) := by
    have := congrArg (IsCMField.complexConj E) h2
    simpa [cc, map_ofNat] using this
  have : 2 * ((H.w0 : E) + cc (H.w0 : E)) = 2 * 1 := by linear_combination h2 + h3 + hc
  exact mul_left_cancel₀ two_ne_zero this

theorem finite_levQ {H : Host E} (Dw : Datum H) (l : Geo.Tor.Level H) : Finite (LevQ Dw l) := by
  have hM : l.Mb ≠ ⊥ := by
    intro h
    have h₁ := l.prod
    rw [h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot] at h₁
    have h₂ : l.M = 0 := by exact_mod_cast h₁
    have := l.three_le
    omega
  have := l.Mb.finiteQuotientOfFreeOfNeBot hM
  have := Dw.fin
  exact Submodule.finite_quotient_smul l.Mb (N := (⊤ : Submodule (𝓞 E) Dw.La)) Module.Finite.fg_top

theorem mem_vset (Λ : GenLat E n) {M : ℕ} (hM : 3 ≤ M) (hU : Λ.Unimod) (hT : Λ.TrivAt M) :
    Λ.La ∈ Vset E n M := by
  obtain ⟨k, hk, h1, h2⟩ := hT
  rw [GenLatCmp.std_eq, GenLatCmp.span_smul_le] at h1 h2
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [Nat.coprime_zero_left] at hk
      omega
    · exact hk0
  exact ⟨GenLatCmp.fg_of_smul_le hk0 h1, (GenLatCmp.unimod_iff Λ.La).1 hU, k, hk0, hk, h1, h2⟩

theorem thA_sum (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) {T : Type} (s : Finset T) (f : T → TF n g) (hf : ∀ i, IsSB (f i)) :
    thA X bas idx (∑ i ∈ s, f i) x = ∑ i ∈ s, thA X bas idx (f i) x := by
  induction s using Finset.induction_on with
  | empty => simpa using UnAct.thA_smul (X := X) (bas := bas) idx x 0 (0 : TF n g)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    exact UnAct.thA_add idx hs hx (hf a) (RecSum.isSB_sum s f hf)

theorem theta_sum₂ (hr : X.p0 + q0 = r) (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) {T : Type} (s : Finset T) (W : T → ℂ) (f : T → TF n g) (hf : ∀ i, IsSB (f i))
    (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) :
    thP X hr bas idx (∑ i ∈ s, W i • f i) P x = ∑ i ∈ s, W i * thP X hr bas idx (f i) P x := by
  unfold thP
  rw [← Jet.polyDeriv_sum_fun P _ s W _ fun i _ => ThetaHol.differentiable_thA idx hs (hf i) hx,
    thA_sum idx hs hx s _ fun i => TensVac.sb_smul _ (hf i)]
  congr 1
  funext w
  simp only [UnAct.thA_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem theta_finsum (hr : X.p0 + q0 = r) (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) (hn : Even n)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) {T : Type} [Fintype T] (W : T → ℂ)
    (Y : T → Matrix (Fin n) (Fin r) E) (a : ℂ) {u : TF n g} (hu : IsSB u)
    (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) :
    thP X hr bas idx (∑ᶠ q, W q • heisG X bas (Y q) (a • u)) P x =
      a * ∑ q, W q * thP X hr bas idx (heisG X bas (Y q) u) P x := by
  have h1 (q) : W q • heisG X bas (Y q) (a • u) = (a * W q) • heisG X bas (Y q) u := by
    funext t
    simp only [heisG, heisS, Pi.smul_apply, smul_eq_mul]
    ring
  simp only [h1]
  rw [finsum_eq_sum_of_fintype, theta_sum₂ hr idx hs hx _ _ _
    fun q => ((heisG_laws E r X g bas idx n hs hn).2.2.2 (Y q) u hu).1, Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ => _root_.mul_assoc _ _ _


omit [IsCMField E] in
theorem index_Ln (Λ : GenLat E n) :
    (Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index =
      (stdL E n).toAddSubgroup.relIndex Λ.La.toAddSubgroup := by
  rw [← GenLatCmp.std_eq, ← AddSubgroup.inf_relIndex_left]
  rfl


omit [IsCMField E] in
theorem zCard_eq (Λ : GenLat E n) {N M : ℕ} (hN : Λ.LevOK N M) (r : ℕ) :
    Λ.zCard N r = Λ.mIdx N r * ((stdL E n).toAddSubgroup.relIndex Λ.La.toAddSubgroup) ^ r := by
  rw [← index_Ln Λ, GenLat.zCard, GenLat.mIdx, ← mul_pow]
  congr 1
  exact (AddSubgroup.relIndex_mul_relIndex _ _ _ (Submodule.toAddSubgroup_mono hN.2.2)
    (Submodule.toAddSubgroup_mono (inf_le_left : Λ.Ln ≤ Λ.La))).symm

end Classical

theorem cancel_idx {b κ S Q : ℂ} {m z j : ℕ} (hb : b ≠ 0) (hz0 : 0 < z) (hz : z = m * j) :
    b⁻¹ * (m : ℂ)⁻¹ * Q * (z : ℂ) * κ * ((((Real.sqrt (j : ℝ) : ℝ) : ℂ))⁻¹ * S) * b =
      Q * κ * S * ((Real.sqrt (j : ℝ) : ℝ) : ℂ) := by
  subst hz
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mul_pos_right hz0).ne'
  have hj : (0 : ℝ) < j := by exact_mod_cast Nat.pos_of_mul_pos_left hz0
  have hs : ((Real.sqrt (j : ℝ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hj).ne'
  have h2 : (j : ℂ) = ((Real.sqrt (j : ℝ) : ℝ) : ℂ) * ((Real.sqrt (j : ℝ) : ℝ) : ℂ) := by
    exact_mod_cast (Real.mul_self_sqrt hj.le).symm
  rw [Nat.cast_mul]
  generalize ((Real.sqrt (j : ℝ) : ℝ) : ℂ) = s at hs h2
  rw [h2]
  field_simp

theorem change_at_point : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (q0 n : ℕ) (hr : X.p0 + q0 = r) (eL : LtN Dw n ≃ Harm.Var X.Ψ q0 X.p0 (Fin n)), IsSympl X bas → r = Dw.p + Dw.q → Even n → (∀ ℓ, letterDir X hr idx (eL ℓ) = Pi.single ℓ.2.2 (Pi.single (e.symm ⟨ℓ.1, ℓ.2.1⟩) 1)) → (∀ j, rowType X (idx j) = Formalism.L2.PjFree.relab c (algebraMap c.F ℂ) (e j).1) → ∀ [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (Λ : GenLat E n) (h : Matrix (Fin n) (Fin n) E), Λ.Unimod → IsUnitaryM h → Λ.TrivAt l.M → (actLat h Λ).TrivAt l.M → ∃ t : ℂ, ‖t‖ = 1 ∧ ∀ (x : Frame X.Ψ r) (L : Lt E r) (y : FrPt Xo c ℂ) (_ : AnFib X bas idx e x L y), x ∈ X.dom → SelfD X L → IsMu (t ^ 2 * ∏ τ : E →+* ℂ, algebraMap c.F ℂ (embF c τ h.det) ^ Dw.mult τ) ∧ ∀ (wq : (Fin n → LevQ Dw l) → c.F), FixesDatum c h wq → ∀ N N' : ℕ, Λ.LevOK N l.M → (actLat h Λ).LevOK N' l.M → ∀ (a : (E →+* ℂ) × ℕ → ℕ), ∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), ∀ (b b' : c.F) (v v' : ℂ), b ≠ 0 → b' ≠ 0 → ShortValAt Xo c nab wq Λ b N P y v → ShortValAt Xo c nab wq (actLat h Λ) b' N' (pushLet c h P) y v' → v' * algebraMap c.F ℂ b' * (Real.sqrt (((Λ).Ln.toAddSubgroup.addSubgroupOf (Λ).La.toAddSubgroup).index ^ (Dw.p + Dw.q) : ℕ) : ℝ) = t * algebraMap c.F ℂ b * (Real.sqrt (((actLat h Λ).Ln.toAddSubgroup.addSubgroupOf (actLat h Λ).La.toAddSubgroup).index ^ (Dw.p + Dw.q) : ℕ) : ℝ) * v := by
  intro hci E _ _ _ H Dw l Xo c _ r g X bas idx e q0 n hr eL hs hrr hn hdir hty _ nab hnab Λ h hU hh hT hT'
  have hw := cmHost_idempotent_trace_eq_one H
  have hwi : IsIntegral ℤ (H.w0 : E) := H.w0.isIntegral_coe
  obtain ⟨hU', hmv, hu, -⟩ := (GlobalTheory.T.pushforward_preserves_harmonic_polynomials_and_lattices E H Dw l c n 0 h hh).2 Λ
  have hΛ := mem_vset Λ l.three_le hU hT
  have hΛ' := mem_vset (actLat h Λ) l.three_le (hU' hU) hT'
  have hΛ1 : Λ.La ∈ Vset E n 1 := (GenLatCmp.genLat_vset E n _).2.2.1 1 _ (one_dvd _) hΛ
  have hΛ1' : (actLat h Λ).La ∈ Vset E n 1 := (GenLatCmp.genLat_vset E n _).2.2.1 1 _ (one_dvd _) hΛ'
  obtain ⟨t, ht, hvac⟩ := thA_vacuum_hAct E r X g bas idx n hs hn _ hwi hw h hu _ hΛ1 _ hΛ1' hmv
  refine ⟨t, ht, fun x L y A hx hL => ?_⟩
  obtain ⟨⟨v₀, hv₀⟩, -⟩ := TensVac.vacua E r X g bas idx n hs hn _ hwi hw L hL 1 _ (Base.stdL_mem_Vset n 1)
  have hcol := hvac L hL v₀ hv₀ x hx
  refine ⟨?_, ?_⟩
  · have h1 := _root_.GlobalTheory.Phase.Mult.isMu_multiplier_sq_mul_det E r X g bas idx n hs hn _ hwi hw h hu _ hΛ1 _ hΛ1' L hL v₀ hv₀ x hx t ht hcol
    have h2 : ∏ i : Fin g, rowType X (idx i) h.det =
        ∏ τ : E →+* ℂ, algebraMap c.F ℂ (embF c τ h.det) ^ Dw.mult τ := by
      simp only [hty]
      rw [e.prod_comp (fun ℓ : Lt1 Dw => Formalism.L2.PjFree.relab c (algebraMap c.F ℂ) ℓ.1 h.det), Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun τ _ => ?_
      simp [Formalism.L2.PjFree.relab]
    rwa [h2] at h1
  intro wq hwq N N' hN hN' a P hP b b' v v' hb hb' hv hv'
  obtain ⟨θ, hθ, -⟩ := (reads_existsUnique_theta E H Dw l Xo c r g X bas idx e x L y A hs hx hL 1 y.s).1
  have hθ1 := isTheta1_of_reads_generator E H Dw l Xo c r g X bas idx e x L y A hs hx hL θ hθ
  obtain ⟨κ, hκ⟩ := VacProd.prod_eq_mul_thA E r X g bas idx n hs hn _ hwi hw L hL v₀ hv₀ x hx θ hθ1
  obtain ⟨mk, hmk, hA⟩ := exists_mark E H Dw l Xo c r g X bas idx e x L y A hs hx hL
  have hroots := (DualMark.dual_marking E H Dw l r X L mk _ hL hmk
    (Complex.isPrimitiveRoot_exp _ l.odd.pos.ne')).2.2.2.2 n
  obtain ⟨Y, hY⟩ := hroots N hN.1.pos
  obtain ⟨Y', hY'⟩ := hroots N' hN'.1.pos
  have e1 := _root_.GlobalTheory.Dict.shortValAt_eq_thP hci E H Dw l Xo c r g X bas idx e x L y A hs hx hL q0 n hr eL hrr hn hdir nab hnab
    θ v₀ κ hθ hv₀ hκ mk hmk hA Λ.La hΛ N hN Y hY a P hP wq b v hv
  have e2 := _root_.GlobalTheory.Dict.shortValAt_eq_thP hci E H Dw l Xo c r g X bas idx e x L y A hs hx hL q0 n hr eL hrr hn hdir nab hnab
    θ v₀ κ hθ hv₀ hκ mk hmk hA (actLat h Λ).La hΛ' N' hN' Y' hY' a _
    ((GlobalTheory.T.pushforward_preserves_harmonic_polynomials_and_lattices E H Dw l c n a h hh).1 P hP) wq b' v' hv'
  obtain ⟨_, -, hproj⟩ := _root_.GlobalTheory.Phase.Proj.proj_phases E r X g bas idx n hs hn _ hwi hw L hL v₀ hv₀
  obtain ⟨hu1, -, hp1⟩ := hproj _ hΛ1
  obtain ⟨hu2, -, hp2⟩ := hproj _ hΛ1'
  obtain ⟨⟨σ, hσ⟩, hmove⟩ := _root_.GlobalTheory.Dict.RootsMove.roots_move E H Dw l r X g bas n hs hn L hL mk hmk h hu _ hΛ _ hΛ' hmv N N' hN hN'
    Y Y' hY hY'
  obtain ⟨-, -, -, hz1, -⟩ := ZLat.exists_reps_sum E r X g bas idx n hs hn _ hwi hw L hL _ hΛ1 N hN.1
    (hN.2.2.trans inf_le_left)
  obtain ⟨-, -, -, hz2, -⟩ := ZLat.exists_reps_sum E r X g bas idx n hs hn _ hwi hw L hL _ hΛ1' N' hN'.1
    (hN'.2.2.trans inf_le_left)
  haveI := finite_levQ Dw l
  haveI := Fintype.ofFinite (Fin n → LevQ Dw l)
  generalize unitv (projA X bas (H.w0 : E) (tens Λ.La L) v₀) = u at hcol hu1 hp1
  generalize unitv (projA X bas (H.w0 : E) (tens (actLat h Λ).La L) v₀) = u' at hcol hu2 hp2
  rw [gphi, hp1, theta_finsum hr idx hs hn hx _ _ _ hu1.1] at e1
  rw [gphi, hp2, theta_finsum hr idx hs hn hx _ _ _ hu2.1] at e2
  have hsum : ∑ q, algebraMap c.F ℂ (wq q) * thP X hr bas idx (heisG X bas (Y' q) u')
        (MvPolynomial.rename eL (MvPolynomial.map (algebraMap c.F ℂ) (pushLet c h P))) x =
      t * ∑ q, algebraMap c.F ℂ (wq q) * thP X hr bas idx (heisG X bas (Y q) u)
        (MvPolynomial.rename eL (MvPolynomial.map (algebraMap c.F ℂ) P)) x := by
    rw [← σ.sum_comp, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hsb := ((heisG_laws E r X g bas idx n hs hn).2.2.2 (Y q) u hu1.1).1
    have hsb' := ((heisG_laws E r X g bas idx n hs hn).2.2.2 (h * Y q) u' hu2.1).1
    have han := (theta_holomorphic_weight E r X g q0 hr bas idx n hs hn 0 0 _ hsb' 0 (zero_mem _)).2.2.2 x hx
    rw [hwq q _ (hσ q), hmove q _ (hσ q) u' hu2, thP, thP,
      _root_.GlobalTheory.Phase.polyDeriv_pushLet_eq_hAct E H Dw l c _ r g X idx e q0 n hr eL hdir hty h P _ han,
      funext (thA_heisG_hAct E r X g bas idx n hs hn h hu u u' hu1.1 hu2.1 t x hx hcol (Y q)),
      mul_left_comm t, ← Jet.polyDeriv_smul_fun _ _ (ThetaHol.differentiable_thA idx hs hsb hx)]
    rfl
  rw [hsum] at e2
  simp only [map_mul, map_inv₀, map_natCast] at e1 e2
  have hb0 : algebraMap c.F ℂ b ≠ 0 := (map_ne_zero _).2 hb
  have hb0' : algebraMap c.F ℂ b' ≠ 0 := (map_ne_zero _).2 hb'
  rw [index_Ln, index_Ln, ← hrr, e2, cancel_idx hb0' hz2 (zCard_eq _ hN' r), mul_right_comm _ _ v,
    _root_.mul_assoc t, _root_.mul_comm _ v, e1, cancel_idx hb0 hz1 (zCard_eq _ hN r)]
  ring

end GlobalTheory.Phase.ChangePt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsComponentsLatticesMovedToLevelFamilyStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_components_lattices_moved_to_level_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ r → l.A = 1 → d.IsLev → ∀ (W : UW U) (k₀ : U.Comp), (∀ k, SameSp (U.X k) (U.X k₀)) → ∀ (ph : (Fin n → LaJ Xo c d) → c.F) (D : SW.Level (U.X k₀)) (hn : r ≤ n), LevTie d σ ph D hn → ∃ (x0 : Fin n → Dw.La) (ga : U.Comp → GL (Fin r) E) (δ : U.Comp → (Dw.La →ₗ[𝓞 E] (Fin r → E))), (∀ rk, AdmX (l := l) rk x0) ∧ (∀ k, IsUn (U.X k₀) (ga k) ∧ mapL (ga k) (U.X k).Λ ∈ D.lats ∧ IsMark l (mapL (ga k) (U.X k).Λ) (mvMap (ga k) (W.mark k)) ∧ IsDual (U.X k₀) l (σ (zetaM c)) (mapL (ga k) (U.X k).Λ) (mvMap (ga k) (W.mark k)) (δ k) ∧ IsBaseClassLevelAdapted d D hn x0 (δ k)) ∧ ∀ k k', ∀ g' ∈ D.grp, mapL g' (mapL (ga k) (U.X k).Λ) = mapL (ga k') (U.X k').Λ → k = k' := by
  first | exact @GlobalTheory.Dict.exists_components_tied | exact GlobalTheory.Dict.exists_components_tied | (intros; apply GlobalTheory.Dict.exists_components_tied <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSabMapOfIsAH
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Dict.SameFibre

open GlobalTheory.AnVal
open GlobalTheory.UnifPoint

theorem discrete_of_im_int {g : ℕ} (Λ : AddSubgroup (Fin g → ℂ)) (M : Matrix (Fin g) (Fin g) ℂ)
    (hs : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) (pos : ∀ z, z ≠ 0 → 0 < (hermForm M z z).re)
    (hi : ∀ a ∈ Λ, ∀ b ∈ Λ, ∃ k : ℤ, (hermForm M a b).im = k) : DiscreteTopology Λ := by
  obtain ⟨s, hs', hsp, hli⟩ := exists_linearIndependent ℝ (Λ : Set (Fin g → ℂ))
  have : Finite s := hli.finite
  choose k hk using hi
  let f : Λ → (s → ℤ) := fun a b => k a a.2 b (hs' b.2)
  have hf : ∀ a b, ((f a b : ℤ) : ℝ) = (hermForm M a b).im := fun a b => (hk _ _ _ _).symm
  refine DiscreteTopology.of_continuous_injective (f := f) (continuous_pi fun b => ?_) fun a a' h => ?_
  · refine Int.isClosedEmbedding_coe_real.isEmbedding.continuous_iff.2 ?_
    have : (Int.cast ∘ fun a => f a b : Λ → ℝ) = fun a : Λ => (hermForm M a b).im := funext fun a => hf a b
    rw [this]
    unfold hermForm
    fun_prop
  · have h0 : ∀ w, (hermForm M (a - a') w).im = 0 := fun w => by
      have hw : w ∈ Submodule.span ℝ s := by rw [hsp, hs]; trivial
      induction hw using Submodule.span_induction with
      | mem w hw =>
        have := hf a ⟨w, hw⟩
        rw [h, hf] at this
        simp only [hermForm, sub_dotProduct, Complex.sub_im] at this ⊢
        rw [this, sub_self]
      | zero => simp [hermForm]
      | add x y _ _ hx hy =>
        simp only [hermForm, star_add, Matrix.mulVec_add, dotProduct_add, Complex.add_im] at hx hy ⊢
        rw [hx, hy, add_zero]
      | smul r x _ hx =>
        rw [← Complex.coe_smul]
        simp only [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul,
          Complex.star_def, Complex.conj_ofReal, Complex.im_ofReal_mul] at hx ⊢
        rw [hx, mul_zero]
    by_contra hne
    have h1 := pos (a - a') (sub_ne_zero.2 fun e => hne (Subtype.ext e))
    have h2 := h0 (Complex.I • ((a : Fin g → ℂ) - a'))
    simp only [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul,
      Complex.star_def, Complex.conj_I, neg_mul, Complex.neg_im, Complex.I_mul_im, neg_eq_zero] at h1 h2
    exact h1.ne' h2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {g : ℕ}

theorem exists_holUnif {S : Scheme.{0}} {t : SAB H S} {y : Sp ℂ ⟶ S} {t₁ : SAB H (Sp ℂ)} (m : SABMap t₁ t y)
    (Φ : AnFr t.G t.PP y g) (pos : ∀ z, z ≠ 0 → 0 < (hermForm Φ.Hm z z).re) :
    ∃ (u : HolUnif t₁.G t₁.PP.L g) (χ : u.Λ → ℂ), (∀ z, z ∈ u.Λ ↔ z ∈ Φ.lat) ∧
      (∀ z, (u.ex z).left ≫ m.φ = (Φ.e z).left) ∧ u.IsAH Φ.Hm χ := by
  obtain ⟨w, hw, -⟩ := m.lin
  obtain ⟨w', hw'⟩ := LBIso.symm ⟨w, hw⟩
  have hL := t₁.PP.isLB
  have hM := LB.isLB_pull t.PP.isLB m.φ
  let u₁ := OrthoMetric.fibreUnif m.cart Φ.e Φ.lat Φ.fr Φ.e_add Φ.e_onto Φ.e_ker
    (discrete_of_im_int Φ.lat Φ.Hm Φ.span pos fun a ha b hb => Φ.herm_im_int ha hb) Φ.span
    (fun U f => by simpa only [Set.mem_univ, true_and] using Φ.hol U f) Φ.fr_hol Φ.fr_ne Φ.fr_g
  have hA₁ : u₁.IsAH Φ.Hm fun a => Φ.χ a :=
    ⟨Φ.herm, pos, fun a => Φ.χ_norm a a.2, fun a j z hj =>
      Φ.fr_per a a.2 _ z ((OrthoMetric.lift_le m.cart _ j).1 hj)⟩
  exact ⟨ArchMetricCompare.carry u₁ hM hL hw', _, fun _ => Iff.rfl, fun z => OrthoMetric.liftPt_comp m.cart _,
    ArchMetricCompare.carry_isAH hM hL hw' hA₁⟩

theorem exists_sabMap_of_isAH {D : Datum H} {l : Geo.Tor.Level H} {b : Base l ℂ} {s : Sp ℂ ⟶ Sp ℂ}
    (o₁ o₂ : Obj D l b s) (u₁ : HolUnif o₁.t.G o₁.t.PP.L g) (u₂ : HolUnif o₂.t.G o₂.t.PP.L g)
    {M₁ M₂ : Matrix (Fin g) (Fin g) ℂ} {χ₁ : u₁.Λ → ℂ} {χ₂ : u₂.Λ → ℂ} (h₁ : u₁.IsAH M₁ χ₁) (h₂ : u₂.IsAH M₂ χ₂)
    (hΛ : ∀ z, z ∈ u₁.Λ ↔ z ∈ u₂.Λ) (hM : ∀ z w, hermForm M₁ z w = hermForm M₂ z w)
    (F : 𝓞 E → (Fin g → ℂ) → (Fin g → ℂ)) (a₁ : ∀ a z, u₁.ex (F a z) = u₁.ex z ≫ o₁.t.act.act a)
    (a₂ : ∀ a z, u₂.ex (F a z) = u₂.ex z ≫ o₂.t.act.act a) :
    ∃ m : SABMap o₁.t o₂.t (𝟙 _), ∀ z, (u₁.ex z).left ≫ m.φ = (u₂.ex z).left := by
  have hT := thetaUnifAV_all
  have hL : Out.Laws := firstFiveLaws.1
  have p₁ := obj_isAbelianScheme_dim_rigidified_sym E H D l _ _ _ _ o₁
  have p₂ := obj_isAbelianScheme_dim_rigidified_sym E H D l _ _ _ _ o₂
  obtain ⟨E₁, e₁, -, g₁, -, -, w₁⟩ := AHWeil.tangent_and_weil_of_isAH hT (objPol o₁ p₁) g u₁ M₁ χ₁ h₁
  obtain ⟨E₂, e₂, -, g₂, -, -, w₂⟩ := AHWeil.tangent_and_weil_of_isAH hT (objPol o₂ p₂) g u₂ M₂ χ₂ h₂
  obtain ⟨α, hα, hα'⟩ : ∃ α : o₁.t.G ⟶ o₂.t.G, IsMonHom α ∧ ∀ z, u₂.ex z = u₁.ex z ≫ α :=
    exists_isMonHom_of_map_lattice hT hL (objPol o₁ p₁) (objPol o₂ p₂) g u₁ u₂ LinearMap.id g₁.symm g₂.symm
      fun z hz => (hΛ z).1 hz
  obtain ⟨β, -, hβ'⟩ : ∃ β : o₂.t.G ⟶ o₁.t.G, IsMonHom β ∧ ∀ z, u₁.ex z = u₂.ex z ≫ β :=
    exists_isMonHom_of_map_lattice hT hL (objPol o₂ p₂) (objPol o₁ p₁) g u₂ u₁ LinearMap.id g₂.symm g₁.symm
      fun z hz => (hΛ z).2 hz
  have := p₁.1.smooth
  have := p₂.1.smooth
  have := p₁.1.proper
  have := p₂.1.proper
  have : IsReduced o₁.t.G.left := isReduced_of_smooth_complex _ o₁.t.G.hom inferInstance
  have : IsReduced o₂.t.G.left := isReduced_of_smooth_complex _ o₂.t.G.hom inferInstance
  let ψ : o₁.t.G ≅ o₂.t.G :=
    { hom := α
      inv := β
      hom_inv_id := ComplexPoints.over_hom_ext_of_complexPoints fun x => by
        obtain ⟨z, rfl⟩ := u₁.ex_onto x
        rw [← Category.assoc, ← hα', ← hβ', Category.comp_id]
      inv_hom_id := ComplexPoints.over_hom_ext_of_complexPoints fun x => by
        obtain ⟨z, rfl⟩ := u₂.ex_onto x
        rw [← Category.assoc, ← hβ', ← hα', Category.comp_id] }
  have hact : ∀ a, o₁.t.act.act a ≫ α = α ≫ o₂.t.act.act a := fun a =>
    ComplexPoints.over_hom_ext_of_complexPoints fun x => by
      obtain ⟨z, rfl⟩ := u₁.ex_onto x
      rw [← Category.assoc, ← Category.assoc, ← a₁, ← hα', ← hα', ← a₂]
  have hlam := lam_iso_of_weil_pairings hL ℂ (objPol o₁ p₁) (objPol o₂ p₂) α 2 1 hα Nat.prime_two inferInstance
    fun k x y c hk _ hx hy hw => by
      obtain ⟨a, rfl⟩ := CM.HermWeil.exists_eq_ex_div u₁ hk x hx
      obtain ⟨a', rfl⟩ := CM.HermWeil.exists_eq_ex_div u₁ hk y hy
      have w := w₁ k a a' (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
      obtain rfl := weilIs_unique_fieldPoint _ _ _ o₁.t.PP.isLB ℂ (𝟙 _) k _ _ _ _ hw w
      have w' := w₂ k ⟨a, (hΛ _).1 a.2⟩ ⟨a', (hΛ _).1 a'.2⟩ (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
      have e : E₂ ⟨a, (hΛ _).1 a.2⟩ ⟨a', (hΛ _).1 a'.2⟩ = E₁ a a' := by
        have h := e₁ a a'
        rw [hM, ← e₂ ⟨a, (hΛ _).1 a.2⟩ ⟨a', (hΛ _).1 a'.2⟩] at h
        exact_mod_cast h.symm
      rw [hα', hα', e] at w'
      rw [pow_one]
      exact w'
  have : IsMonHom ψ.hom := hα
  exact ⟨⟨CubeMap.ofHom α, isGrpPullback_of_iso ψ, rfl, fun a => congrArg (fun z => z.left) (hact a),
    HeckePoint.isPullCubical_of_iso hL.globalFns p₁.1 α o₁.t.cub o₂.t.cub
      (HeckePoint.iso_of_lam o₁.t o₂.t α hact hlam)⟩,
    fun z => congrArg (fun q => q.left) (hα' z).symm⟩

end GlobalTheory.Dict.SameFibre


open GlobalTheory.Dict.SameFibre GlobalTheory.UnifPoint GlobalTheory.AnVal in
theorem GlobalTheory.Dict.anFib_point_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ], l.A = 1 → ∀ (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (x : Frame X.Ψ r) (L : Lt E r) (y y' : FrPt Xo c ℂ) (A : AnFib X bas idx e x L y) (A' : AnFib X bas idx e x L y'), IsSympl X bas → x ∈ X.dom → SelfD X L → ∀ mk : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark l L mk → A.Marked mk → A'.Marked mk → y'.x = y.x := by
  intro E _ _ _ H Dw l Xo c _ hA r g X bas idx e x L y y' A A' hs hx hL mk _ hm hm'
  obtain ⟨Φ, k₁, -, l₁, m₁, -⟩ := AnFib.exists_anPt E H Dw l Xo c r g X bas idx e x L y A hs hx hL
  obtain ⟨Φ', k₂, -, l₂, m₂, -⟩ := AnFib.exists_anPt E H Dw l Xo c r g X bas idx e x L y' A' hs hx hL
  obtain ⟨-, pos, -⟩ := hx_laws E r X g bas idx 0 hs Even.zero x hx
  let σ : KA l →+* ℂ := (algebraMap c.F ℂ).comp (IntermediateField.inclusion c.le).toRingHom
  have hy : y.x ≫ Xo.s = 𝟙 _ ≫ spMap σ := y.x_over.trans (Category.id_comp _).symm
  have hy' : y'.x ≫ Xo.s = 𝟙 _ ≫ spMap σ := y'.x_over.trans (Category.id_comp _).symm
  obtain ⟨o₁, ⟨n₁⟩⟩ := obj_pull E H Dw l _ ℂ (baseKA l) (baseOfEmb σ) σ _ _ Xo.s (𝟙 _) y.x rfl rfl hy Xo.univ
  obtain ⟨o₂, ⟨n₂⟩⟩ := obj_pull E H Dw l _ ℂ (baseKA l) (baseOfEmb σ) σ _ _ Xo.s (𝟙 _) y'.x rfl rfl hy' Xo.univ
  obtain ⟨u₁, χ₁, b₁, f₁, h₁⟩ := exists_holUnif n₁.toSABMap Φ.toAnFr fun z hz => by rw [m₁]; exact pos z hz
  obtain ⟨u₂, χ₂, b₂, f₂, h₂⟩ := exists_holUnif n₂.toSABMap Φ'.toAnFr fun z hz => by rw [m₂]; exact pos z hz
  obtain ⟨m, hm₀⟩ := exists_sabMap_of_isAH o₁ o₂ u₁ u₂ h₁ h₂ (fun z => by rw [b₁, b₂, l₁, l₂])
    (fun z w => by rw [m₁, m₂]) (fun a => tyAct (fun j => rowType X (idx j)) a)
    (fun a z => OrthoMetric.pt_ext n₁.cart (by
      rw [f₁, Φ.lin, Over.comp_left, Over.comp_left, Category.assoc, n₁.act, ← Category.assoc, f₁]))
    (fun a z => OrthoMetric.pt_ext n₂.cart (by
      rw [f₂, Φ'.lin, Over.comp_left, Over.comp_left, Category.assoc, n₂.act, ← Category.assoc, f₂]))
  obtain ⟨k⟩ := exists_objMap o₁ o₂ m
    (fun a ha => by
      have c₁ : o₁.eta a = u₁.ex _ := OrthoMetric.pt_ext n₁.cart
        ((n₁.eta a).trans ((congrArg (fun q => q.left) ((hm a ha).trans (k₁ _).symm)).trans (f₁ _).symm))
      have c₂ : o₂.eta a = u₂.ex _ := OrthoMetric.pt_ext n₂.cart
        ((n₂.eta a).trans ((congrArg (fun q => q.left) ((hm' a ha).trans (k₂ _).symm)).trans (f₂ _).symm))
      rw [c₁, c₂, hm₀])
    (fun a => by
      have c₁ := o₁.etaA_ker a
      have c₂ := o₂.etaA_ker a
      rw [hA, one_smul] at c₁ c₂
      rw [c₁, c₂, ← CM.HermWeil.ex_zero u₁, ← CM.HermWeil.ex_zero u₂, hm₀])
  obtain ⟨k', -⟩ := ((ObjMaps.id_comp_cancel E H Dw l _ _ _ _ _ _ _ _ _ _ _ _ Xo.univ o₂ o₁).2 y'.x (𝟙 _) n₂).1 k
  rw [Category.id_comp] at k'
  exact (moduli_rep_of_base ObjMaps.id_comp_cancel E H Dw l Xo ℂ (baseOfEmb σ) σ _ (𝟙 _) o₁ inferInstance
    rfl rfl).unique ⟨hy', ⟨k'⟩⟩ ⟨hy, ⟨n₁⟩⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ShortThetaSeriesDominantWeightIsCuspForm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj hiding Unf GoodEmb IsUnf rdU laU
open Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

theorem shortInCusp_cusp : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), 1 ≤ r → (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → d.IsLev → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → UnitC d → (Dw.p + Dw.q ≤ n → ∃ ph ψ x₀, d.PhiPin ph ψ x₀) → ∀ (nab : NabV Xo c) (bad nV : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), ShortInCusp Xo c nab bad nV (Formalism.L2.PjFree.cusp Xo c U) a n d := by
  intro hci E _ _ _ H Dw l Xo c n d r U hr1 hU hlev hnab hunit hpin nab bad nV a hD hL f hf
  obtain ⟨hsec, Λ, N, x0, P, hun, -, htr, hN, hx0, hP, hrule⟩ := hf
  refine (mem_cusp Xo c U a n f).2 ⟨hsec, fun σ hσ => Formalism.L2.PjFree.holCusp_mem_holSub _ _ fun k => ?_⟩
  have hu := hU σ hσ
  obtain ⟨W⟩ := nonempty_uw hu
  have hsd := (GlobalTheory.Dict.uw_lattice E H Dw l Xo c σ r (U σ) hσ hu hr1 W k).2.1
  obtain ⟨Dc, hDe, hk⟩ := GlobalTheory.Dict.exists_dic E H Dw l c σ r W.g n ((U σ).X k) a W.e hσ hu.1 (hu.2.1 k).1
    (hu.2.1 k).2 hsd hD
  obtain ⟨φ, hφ, hrd⟩ := GlobalTheory.Dict.ShortRead.rdU_eq_thP hci E H Dw l Xo c n d σ r (U σ) hσ hu hr1 hlev hnab hunit hpin W k a hD
    Dc hDe Λ N _ x0 P hun htr hN hx0 hP.1 f hsec hrule
  have hrn : r ≤ n := hu.1 ▸ (GlobalTheory.admissible_columns_le_and_harmonic_map_cover E H Dw l Xo c n d).1 _ x0 hx0
  have hw : laU (U σ) a n k = wtOf ((U σ).X k) Dc.hr Dc.k Dc.k' n := Dc.wt_eq.symm
  have hs := hu.2.2.2.2.1 a n hD f hsec k
  rw [hw] at hs ⊢
  refine CuspClass.mem_SS_of_eq_thP E r ((U σ).X k) W.g Dw.p Dc.hr Dc.bas Dc.idx n Dc.sympl hD.2 Dc.k Dc.k'
    ?_ hrn φ hφ _ (Dc.mem P hP.1) _ hrd ?_
  · rcases Nat.eq_zero_or_pos Dw.p with h0 | h0
    · exact Or.inr h0
    · exact Or.inl (hk hL h0)
  · exact hs.2.2

end GlobalTheory.Dict
end

