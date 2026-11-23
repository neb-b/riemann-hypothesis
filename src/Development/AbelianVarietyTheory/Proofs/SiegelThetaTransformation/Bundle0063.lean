module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0002
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TensorLatticeVacuaExistUnique
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DualHalfLevelMarkingExistsAndMatch
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnFibLift
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CmHostUnitAddConjEqOne
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSymplOfSelfDual
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkings
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ProdLevelOneThetaEqVacuumTheta
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ShortThetaValueComplexPointEqClassicalTheta
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0040
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HalfIntegralGeneratorAddConjEqOne
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

namespace GlobalTheory.Dict.ShortRead

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g q0 n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ}

theorem halfIntegralGenerator_add_conj_eq_one (H : Host E) : (H.w0 : E) + cc (H.w0 : E) = 1 := by
  have h1 : (H.rt : E) ^ 2 = -(H.d : E) := by simpa using congrArg (algebraMap (𝓞 E) E) H.rt_sq
  have h2 : 2 * (H.w0 : E) = 1 + (H.rt : E) := by
    simpa [map_ofNat] using congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h3 : τ H.rt ^ 2 = -(H.d : ℂ) := by simpa using congrArg τ h1
  have h4 : 2 * τ H.w0 = 1 + τ H.rt := by simpa [map_ofNat] using congrArg τ h2
  have h5 : (τ H.rt).re = 0 := by
    have a := congrArg Complex.re h3
    have b := congrArg Complex.im h3
    have c : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    simp only [pow_two, mul_re, mul_im, neg_re, neg_im, natCast_re, natCast_im, neg_zero] at a b
    by_contra h
    have : (τ H.rt).im = 0 := mul_left_cancel₀ h (by linarith)
    rw [this] at a
    nlinarith [mul_self_nonneg (τ H.rt).re]
  apply τ.injective
  rw [map_add (f := _), cc, IsCMField.complexEmbedding_complexConj, map_one, Complex.add_conj]
  have h6 := congrArg Complex.re h4
  simp only [add_re, one_re, h5, add_zero, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero] at h6
  exact_mod_cast h6

theorem sb_smul (a : ℂ) {φ : TF n g} (h : IsSB φ) : IsSB (a • φ) :=
  (isSB_algebra_haar_linear ℚ _ _ φ φ h h).2.1 a

theorem sb_finsum {Q : Type} (f : Q → TF n g) (hf : ∀ q, IsSB (f q)) : IsSB (∑ᶠ q, f q) :=
  finsum_induction (fun φ : TF n g => IsSB φ) isSB_zero
    (fun φ ψ h h' => (isSB_algebra_haar_linear ℚ _ _ φ ψ h h').1) hf

theorem sb_gphi (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) (hn : Even n) {w : E}
    (hw : IsIntegral ℤ w) (hw' : w + cc w = 1) {L : Lt E r} (hL : SelfD X L) {M : ℕ} {Λ : Lt E n}
    (hΛ : Λ ∈ Vset E n M) {v : TF n g} (hv : IsSB v) {Q : Type} (W : Q → ℂ)
    (Y : Q → Matrix (Fin n) (Fin r) E) : IsSB (gphi X bas w Λ L v W Y) := by
  obtain ⟨⟨v', hv'⟩, -, h, -⟩ := TensVac.vacua E r X g bas idx n hs hn w hw hw' L hL M Λ hΛ
  refine sb_finsum _ fun q => sb_smul _ ((heisG_laws E r X g bas idx n hs hn).2.2.2 _ _ ?_).1
  rw [h v hv v' hv']
  exact sb_smul _ hv'.1

theorem theta_smul₂ (hr : X.p0 + q0 = r) (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) (hn : Even n)
    {k : X.Ψ → Fin q0 → ℕ} {k' : X.Ψ → Fin X.p0 → ℕ} {φ : TF n g} (hφ : IsSB φ)
    {P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)} (hP : P ∈ Harm.rowHighest ℂ k k') {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (a : ℂ) : thP X hr bas idx (a • φ) P x = a * thP X hr bas idx φ P x := by
  have han := (theta_holomorphic_weight E r X g q0 hr bas idx n hs hn k k' _ hφ P hP).2.2.2 x hx
  have h : thA X bas idx (a • φ) x = a • thA X bas idx φ x := by
    funext z
    simp only [thA, SW.thS, Pi.smul_apply, smul_eq_mul, _root_.mul_assoc a, tsum_mul_left]
    ring
  unfold thP
  rw [h, I2.polyDeriv_smul_fun _ _ han.contDiff]

theorem rdU_eq_thP : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ r → d.IsLev → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → UnitC d → (Dw.p + Dw.q ≤ n → ∃ ph ψ x₀, d.PhiPin ph ψ x₀) → ∀ (W : UW U) (k : U.Comp) (a : (E →+* ℂ) × ℕ → ℕ), Dom a n → ∀ Dc : Dic Dw c σ (U.X k) W.g Dw.p n a, Dc.e = W.e → ∀ (Λ : GenLat E n) (N : ℕ) (rk : Bool) (x0 : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F), Λ.Unimod → Λ.TrivAt d.l₂.M → Λ.LevOK N d.l₂.M → AdmX (l := l) rk x0 → P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ f ∈ sec Xo c a n, IsShortRule Xo c d Λ N x0 P f → ∃ φ : TF n W.g, IsSB φ ∧ ∀ x ∈ (U.X k).dom, rdU U f k x = thP (U.X k) Dc.hr Dc.bas Dc.idx φ (MvPolynomial.rename Dc.eL (MvPolynomial.map σ P)) x := by
  intro hCI E _ _ _ H Dw l Xo c n d σ r U hσ hU hr1 hlev ⟨sr, hnab⟩ hunit hpin W k a hdom Dc hDe Λ N rk x0 P
    hΛ1 hΛ2 hΛ3 hadm hP f hf hshort
  letI : Algebra c.F ℂ := σ.toAlgebra
  letI A₂ : Algebra d.c₂.F ℂ := (σ.comp (d.eF.symm : d.c₂.F →+* c.F)).toAlgebra
  have halg : ∀ t : c.F, algebraMap d.c₂.F ℂ (d.eF t) = algebraMap c.F ℂ t := fun t => by
    change σ (d.eF.symm (d.eF t)) = σ t
    rw [AlgEquiv.symm_apply_apply]
  have hn : Even n := hdom.2
  have hrpq : r = Dw.p + Dw.q := hU.1
  obtain ⟨hle, hmap⟩ := admissible_columns_le_and_harmonic_map_cover E H Dw l Xo c n d
  have hpq := hle rk x0 hadm
  obtain ⟨ph, ψ, x₀, hph⟩ := hpin hpq
  obtain ⟨-, hL, hmk, -⟩ := GlobalTheory.Dict.uw_lattice E H Dw l Xo c σ r U hσ hU hr1 W k
  have hw : IsIntegral ℤ (H.w0 : E) := H.w0.isIntegral_coe
  have hw' := halfIntegralGenerator_add_conj_eq_one H
  have hM : 0 < d.l₂.M := lt_of_lt_of_le (by norm_num) d.l₂.three_le
  have hN : 0 < N := hΛ3.1.pos
  obtain ⟨Λ⟩ := Λ
  have hΛ : Λ ∈ Vset E n d.l₂.M := (GenLatCmp.genLat_vset E n Λ).2.1 _ N hM hΛ1 hΛ2 hΛ3
  obtain ⟨v, hv⟩ := (TensVac.vacua E r _ _ Dc.bas Dc.idx n Dc.sympl hn _ hw hw' _ hL 1 _ (Base.stdL_mem_Vset n 1)).1
  obtain ⟨ρ, hρ, hnorm⟩ := GlobalTheory.Dict.VacNorm.norm_factor_eq E r _ _ Dc.bas Dc.idx n Dc.sympl hn _ hw hw' _ hL v hv
  have hroots : ∀ mk₂ : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark d.l₂ (U.X k).Λ mk₂ →
      ∃ Y : (Fin n → LevQ Dw d.l₂) → Matrix (Fin n) (Fin r) E, IsRoots d.l₂ (U.X k).Λ mk₂ N Y := fun mk₂ h =>
    (GlobalTheory.Dict.DualMark.dual_marking E H Dw d.l₂ r _ _ mk₂ _ hL h (Complex.isPrimitiveRoot_exp _ hM.ne')).2.2.2.2 n N hN

  obtain ⟨Y, hY⟩ : ∃ Y : (Fin n → LevQ Dw d.l₂) → Matrix (Fin n) (Fin r) E,
      ∀ mk₂ : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark d.l₂ (U.X k).Λ mk₂ → MarkOver l d.l₂ (U.X k).Λ (W.mark k) mk₂ →
      ∀ Y', IsRoots d.l₂ (U.X k).Λ mk₂ N Y' → ∃ t : ℂ, ‖t‖ = 1 ∧
        gphi _ Dc.bas (H.w0 : E) Λ (U.X k).Λ v (fun q => algebraMap d.c₂.F ℂ (d.w x0 q)) Y' =
          t • gphi _ Dc.bas (H.w0 : E) Λ (U.X k).Λ v (fun q => algebraMap d.c₂.F ℂ (d.w x0 q)) Y := by
    by_cases hex : ∃ mk₃ : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark d.l₂ (U.X k).Λ mk₃ ∧
        MarkOver l d.l₂ (U.X k).Λ (W.mark k) mk₃
    · obtain ⟨mk₃, h1, h2⟩ := hex
      obtain ⟨Y, hY⟩ := hroots mk₃ h1
      refine ⟨Y, fun mk₂ h3 h4 Y' hY' => ?_⟩
      obtain ⟨t, ht, h⟩ := GlobalTheory.Dict.MarkMove.gphi_move E H Dw l Xo c n d hlev ph ψ x₀ hph r _ _ Dc.bas Dc.idx Dc.sympl hn hrpq
        (hrpq ▸ hpq) _ hL (W.mark k) mk₂ mk₃ hmk h3 h1 h4 h2
      exact ⟨t, ht, h x0 v hv Λ hΛ N hΛ3 Y' Y hY' hY⟩
    · exact ⟨fun _ => 0, fun mk₂ h3 h4 => absurd ⟨mk₂, h3, h4⟩ hex⟩
  have hG := sb_gphi Dc.idx Dc.sympl hn hw hw' hL hΛ hv.1 (fun q => algebraMap d.c₂.F ℂ (d.w x0 q)) Y
  generalize gphi _ Dc.bas (H.w0 : E) Λ (U.X k).Λ v (fun q => algebraMap d.c₂.F ℂ (d.w x0 q)) Y = G at hY hG
  obtain ⟨u, hu⟩ : ∃ u : ℂ, u = algebraMap d.c₂.F ℂ ((d.eF (betaH (Dw := Dw) c ⟨Λ⟩))⁻¹ *
    (((⟨Λ⟩ : GenLat E n).mIdx N r : d.c₂.F))⁻¹ * ((Nat.card (Fin n → LevQ Dw d.l₂) : d.c₂.F))⁻¹ *
    ((⟨Λ⟩ : GenLat E n).zCard N r : d.c₂.F)) := ⟨_, rfl⟩
  have hP' := Dc.mem P hP
  have huG := sb_smul u hG
  have hsec := hU.2.2.2.2.1 a n hdom f hf k
  have hth := theta_holomorphic_weight E r _ _ _ Dc.hr Dc.bas Dc.idx n Dc.sympl hn _ _ _ huG _ hP'
  rw [Dc.wt_eq] at hth
  obtain ⟨C, -, hC⟩ := const_of_norm_factor_unitFr E r (U.X k) (laU U a n k) Unit (fun _ => rdU U f k)
    (fun _ => thP (U.X k) Dc.hr Dc.bas Dc.idx (u • G) (MvPolynomial.rename Dc.eL (MvPolynomial.map σ P))) ρ hρ
    (fun _ => ⟨hsec.1, hth.1, fun x hx b hb => ⟨hsec.2.1 x hx b hb, hth.2.1 x hx b hb⟩⟩) (by
      intro x hx hux
      obtain ⟨A, hA, θ, hθ, hmean⟩ := GlobalTheory.Dict.uw_anFib E H Dw l Xo c σ r U hσ hU hr1 W k Dc.bas Dc.idx Dc.sympl
        (hDe ▸ Dc.per_eq) (hDe ▸ Dc.ty_eq) ⟨x, hx⟩ hux
      obtain ⟨y₂, hy₂⟩ := hlev.2.2.2.2.2.2.1 ℂ halg (unC U k ⟨x, hx⟩)
      obtain ⟨B, hB, mk₂, hmk₂, hBm, hover⟩ := GlobalTheory.Dict.Lift.anFib_lift E H Dw l Xo c n d halg hlev r _ _ Dc.bas Dc.idx W.e x _
        _ A Dc.sympl hx hL y₂ hy₂ _ hA
      have hT := GlobalTheory.Dict.isTheta1_of_reads_generator E H Dw l Xo c r _ _ Dc.bas Dc.idx W.e x _ _ A Dc.sympl hx hL θ hθ
      obtain ⟨κ, hκ⟩ := GlobalTheory.Dict.VacProd.prod_eq_mul_thA E r _ _ Dc.bas Dc.idx n Dc.sympl hn _ hw hw' _ hL v hv x hx θ hT
      have hκn := hnorm x hx hux θ κ hT hmean hκ
      obtain ⟨Y', hY'⟩ := hroots mk₂ hmk₂
      obtain ⟨t, ht, hmove⟩ := hY mk₂ hmk₂ hover Y' hY'
      obtain ⟨v0, hv0, hev⟩ := hshort ℂ halg _ y₂ hy₂
      have hval := GlobalTheory.Dict.shortValAt_eq_thP hCI E H Dw d.l₂ d.Xo₂ d.c₂ r _ _ Dc.bas Dc.idx W.e x _ y₂ B Dc.sympl hx hL _ n
        Dc.hr Dc.eL hrpq hn (hDe ▸ Dc.dir_eq) d.nab₂ hnab θ v κ (hB θ hθ) hv hκ mk₂ hmk₂ hBm Λ hΛ N hΛ3 Y' hY'
        a _ (hmap a P hP) _ _ v0 hv0
      have hmm : MvPolynomial.map (algebraMap d.c₂.F ℂ) (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P) =
          MvPolynomial.map σ P := by
        rw [MvPolynomial.map_map]
        exact congrArg (fun s : c.F →+* ℂ => MvPolynomial.map s P) (RingHom.ext halg)
      rw [hmm, hmove, theta_smul₂ Dc.hr Dc.idx Dc.sympl hn hG hP' hx, ← hu] at hval
      refine ⟨evR d.Xo₂ d.c₂ d.cδ y₂ * κ * t, by rw [norm_mul, norm_mul, hunit A₂ y₂, hκn, ht]; ring, fun _ => ?_⟩
      have hrd : rdU U f k x = evR Xo c f (unC U k ⟨x, hx⟩) := dif_pos hx
      beta_reduce
      rw [hrd, hev, hval, theta_smul₂ Dc.hr Dc.idx Dc.sympl hn hG hP' hx]
      ring)
  refine ⟨C • u • G, sb_smul C huG, fun x hx => ?_⟩
  rw [theta_smul₂ Dc.hr Dc.idx Dc.sympl hn huG hP' hx]
  exact hC () x hx

end GlobalTheory.Dict.ShortRead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IteratedFDerivSmulAll
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.ShortPt

theorem iteratedFDeriv_smul_all {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] (a : ℂ) (F : W → ℂ) (k : ℕ) :
    iteratedFDeriv ℂ k (a • F) = a • iteratedFDeriv ℂ k F := by
  induction k with
  | zero => ext x m; simp
  | succ k ih =>
    rw [iteratedFDeriv_succ_eq_comp_left, iteratedFDeriv_succ_eq_comp_left, ih, fderiv_const_smul_field]
    funext x
    simp only [Function.comp_apply, Pi.smul_apply, map_smul]

theorem theta_smul₂ {E : Type} [Field E] [NumberField E] [IsCMField E] {r g q0 n : ℕ} (X : Data E r)
    (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (a : ℂ) (φ : TF n g)
    (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) (x : Frame X.Ψ r) :
    thP X hr bas idx (a • φ) P x = a * thP X hr bas idx φ P x := by
  have h : thA X bas idx (a • φ) x = a • thA X bas idx φ x := by
    funext z
    simp only [thA, SW.thS, Pi.smul_apply, smul_eq_mul, _root_.mul_assoc a, tsum_mul_left]
    ring
  unfold thP I2.polyDeriv
  rw [h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [iteratedFDeriv_smul_all]
  simp only [Pi.smul_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  ring

theorem finite_levQ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H)
    (l : Geo.Tor.Level H) : Finite (LevQ Dw l) := by
  have hne : l.Mb ≠ ⊥ := by
    intro h
    have hp := l.prod
    rw [h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero] at hp
    have := l.three_le
    omega
  haveI : Finite (𝓞 E ⧸ l.Mb) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
  haveI := Dw.fin
  exact Submodule.finite_quotient_smul l.Mb (N := (⊤ : Submodule (𝓞 E) Dw.La)) Module.Finite.fg_top

theorem vset_one {E : Type} [Field E] [NumberField E] [IsCMField E] {n M : ℕ} {Λ : Lt E n}
    (h : Λ ∈ Vset E n M) : Λ ∈ Vset E n 1 := by
  obtain ⟨h1, h2, s, hs, -, h3⟩ := h
  exact ⟨h1, h2, s, hs, Nat.coprime_one_right s, h3⟩

theorem shortRule_value : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) [Algebra c.F ℂ] [Algebra d.c₂.F ℂ], (∀ t : c.F, algebraMap d.c₂.F ℂ (d.eF t) = algebraMap c.F ℂ t) → d.IsLev → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → (∀ y₂ : FrPt d.Xo₂ d.c₂ ℂ, ‖evR d.Xo₂ d.c₂ d.cδ y₂‖ = 1) → ∀ (ph : (Fin n → LaJ Xo c d) → c.F) (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ) (x₀ : Fin n → LaJ Xo c d), d.PhiPin ph ψ x₀ → ∀ (r g q0 : ℕ) (X : Data E r) (a : (E →+* ℂ) × ℕ → ℕ) (Dc : Dic Dw c (algebraMap c.F ℂ) X g q0 n a) (D : SW.Level X) (hn : r ≤ n), Even n → r = Dw.p + Dw.q → LevTie d (algebraMap c.F ℂ) ph D hn → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X Dc.bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ x0 : Fin n → Dw.La, ∃ u : Lt E n → ℕ → ℂ, (∀ Λ ∈ Vset E n d.l₂.M, ∀ N, NOK Λ N d.l₂.M → u Λ N ≠ 0) ∧ ∀ L ∈ D.lats, ∀ mk δ : Dw.La →ₗ[𝓞 E] (Fin r → E), IsMark l L mk → IsDual X l (algebraMap c.F ℂ (zetaM c)) L mk δ → IsBaseClassLevelAdapted d D hn x0 δ → ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ X.dom, IsUnitFr X x → ∀ (y : FrPt Xo c ℂ) (A : AnFib X Dc.bas Dc.idx Dc.e x L y) (θ : (Fin g → ℂ) → ℂ), A.Marked mk → A.Reads 1 y.s θ → MeanOne X Dc.bas Dc.idx x L θ → ∃ κ : ℂ, ‖κ‖ = ρ ∧ ∀ Λ ∈ Vset E n d.l₂.M, ∀ N, NOK Λ N d.l₂.M → ∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), ∀ f : Rul Xo c, IsShortRule Xo c d (⟨Λ⟩ : GenLat E n) N x0 P f → evR Xo c f y = κ * u Λ N * thP X Dc.hr Dc.bas Dc.idx (phiF Dc.bas D (Mfr l) hn v₀ L Λ) (MvPolynomial.rename Dc.eL (MvPolynomial.map (algebraMap c.F ℂ) P)) x := by
  intro hCI E _ _ _ H Dw l Xo c n d _ _ hcomp hlev hnab hcδ ph ψ x₀ hpin r g q0 X a Dc D hn hev hr htie v₀ hv₀ x0
  obtain ⟨_, hnab⟩ := hnab
  obtain ⟨ρ₁, s, hρ₁, hg⟩ := GlobalTheory.Dict.GPhi.gphi_eq_smul_phiF E H Dw l Xo c n d hcomp hlev ph ψ x₀ hpin r g X Dc.bas Dc.idx D hn
    Dc.sympl hev hr htie v₀ hv₀ x0
  have hwi : IsIntegral ℤ (H.w0 : E) := htie.w ▸ D.w_int
  have hwt : (H.w0 : E) + cc (H.w0 : E) = 1 := htie.w ▸ D.w_tr
  have hΛ0 : SelfD X X.Λ := (GlobalTheory.SW.level_laws E r X g Dc.bas Dc.idx n Dc.sympl hev D hn).1.1
  refine ⟨fun Λ N => algebraMap d.c₂.F ℂ ((d.eF (betaH (Dw := Dw) c (⟨Λ⟩ : GenLat E n)))⁻¹ *
      (((⟨Λ⟩ : GenLat E n).mIdx N r : d.c₂.F))⁻¹ * ((Nat.card (Fin n → LevQ Dw d.l₂) : d.c₂.F))⁻¹ *
      ((⟨Λ⟩ : GenLat E n).zCard N r : d.c₂.F)) * (((if 0 < s Λ then s Λ else 1 : ℝ)) : ℂ), ?_, ?_⟩
  · intro Λ hΛ N hN
    obtain ⟨-, -, -, hz, hm, -⟩ := GlobalTheory.Dict.ZLat.exists_reps_sum E r X g Dc.bas Dc.idx n Dc.sympl hev _ hwi hwt
      X.Λ hΛ0 Λ (vset_one hΛ) N hN.1 (hN.2.2.trans inf_le_left)
    haveI := finite_levQ Dw d.l₂
    have hb : betaH (Dw := Dw) c (⟨Λ⟩ : GenLat E n) ≠ 0 := by
      unfold betaH
      split_ifs with h
      · exact h.choose_spec.1
      · exact one_ne_zero
    have hc : 0 < Nat.card (Fin n → LevQ Dw d.l₂) := Nat.card_pos
    refine mul_ne_zero ((_root_.map_ne_zero _).2 ?_) ?_
    · refine mul_ne_zero (mul_ne_zero (mul_ne_zero (inv_ne_zero ?_) (inv_ne_zero ?_)) (inv_ne_zero ?_)) ?_
      · exact (_root_.map_ne_zero _).2 hb
      · exact Nat.cast_ne_zero.2 hm.ne'
      · exact Nat.cast_ne_zero.2 hc.ne'
      · exact Nat.cast_ne_zero.2 hz.ne'
    · rw [Complex.ofReal_ne_zero]
      split_ifs with h
      · exact h.ne'
      · exact one_ne_zero
  intro L hL mk δ hmk hδ hx0
  have hLs : SelfD X L := hL.1
  obtain ⟨v, hv⟩ := (GlobalTheory.SW.TensVac.vacua E r X g Dc.bas Dc.idx n Dc.sympl hev _ hwi hwt L hLs 1 _
    (Base.stdL_mem_Vset (E := E) n 1)).1
  obtain ⟨ρ₀, hρ₀, hnorm⟩ := GlobalTheory.Dict.VacNorm.norm_factor_eq E r X g Dc.bas Dc.idx n Dc.sympl hev _ hwi hwt L hLs v hv
  refine ⟨ρ₀ * ρ₁, mul_pos hρ₀ hρ₁, ?_⟩
  intro x hx hux y A θ hA hθ hmean
  obtain ⟨y₂, hy₂⟩ := hlev.2.2.2.2.2.2.1 ℂ hcomp y
  obtain ⟨A₂, hA₂, mk₂, hmk₂, hA₂m, hover⟩ := GlobalTheory.Dict.Lift.anFib_lift E H Dw l Xo c n d hcomp hlev r g X Dc.bas Dc.idx Dc.e x L y A
    Dc.sympl hx hLs y₂ hy₂ mk hA
  have hth := GlobalTheory.Dict.isTheta1_of_reads_generator E H Dw l Xo c r g X Dc.bas Dc.idx Dc.e x L y A Dc.sympl hx hLs θ hθ
  obtain ⟨κ₀, hκ₀⟩ := GlobalTheory.Dict.VacProd.prod_eq_mul_thA E r X g Dc.bas Dc.idx n Dc.sympl hev _ hwi hwt L hLs v hv x hx θ hth
  obtain ⟨t, ht, hgt⟩ := hg L hL mk mk₂ δ v hmk hmk₂ hover hδ hx0 hv
  refine ⟨evR d.Xo₂ d.c₂ d.cδ y₂ * κ₀ * t, ?_, ?_⟩
  · rw [norm_mul, norm_mul, hcδ y₂, hnorm x hx hux θ κ₀ hth hmean hκ₀, ht, _root_.one_mul]
  intro Λ hΛ N hN P hP f hf
  obtain ⟨hs, hgt⟩ := hgt Λ hΛ
  have hM : d.l₂.M ≠ 0 := by have := d.l₂.three_le; omega
  obtain ⟨Y, hY⟩ := (GlobalTheory.Dict.DualMark.dual_marking E H Dw d.l₂ r X L mk₂ _ hLs hmk₂ (Complex.isPrimitiveRoot_exp _ hM)).2.2.2.2 n N
    hN.1.pos
  obtain ⟨v0, hv0, hfv⟩ := hf ℂ hcomp y y₂ hy₂
  have hval := GlobalTheory.Dict.shortValAt_eq_thP hCI E H Dw d.l₂ d.Xo₂ d.c₂ r g X Dc.bas Dc.idx Dc.e x L y₂ A₂ Dc.sympl hx hLs q0 n Dc.hr
    Dc.eL hr hev Dc.dir_eq d.nab₂ hnab θ v κ₀ (hA₂ θ hθ) hv hκ₀ mk₂ hmk₂ hA₂m Λ hΛ N hN Y hY a _
    ((GlobalTheory.admissible_columns_le_and_harmonic_map_cover E H Dw l Xo c n d).2 a P hP) _ _ v0 hv0
  have hmap : MvPolynomial.map (algebraMap d.c₂.F ℂ) (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P) =
      MvPolynomial.map (algebraMap c.F ℂ) P := by
    rw [MvPolynomial.map_map]
    congr 2
    exact RingHom.ext hcomp
  rw [hgt N hN Y hY, theta_smul₂, hmap] at hval
  beta_reduce
  rw [hfv, hval, if_pos hs]
  ring

end GlobalTheory.Dict.ShortPt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RatioMemRange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

namespace GlobalTheory.ConstRatio

theorem ratio_mem_range {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} (T : Type) [Field T] [IsAlgClosed T] [Algebra c.F T]
    (u u' : FrPt Xo c T → T)
    (hu : ∀ (φ : T →ₐ[c.F] T) (y z : FrPt Xo c T), FrMap φ y z → φ (u y) = u z)
    (hu' : ∀ (φ : T →ₐ[c.F] T) (y z : FrPt Xo c T), FrMap φ y z → φ (u' y) = u' z)
    (z : T) (h : ∀ y, u' y = z * u y) (y : FrPt Xo c T) (hy : u y ≠ 0) :
    z ∈ Set.range (algebraMap c.F T) := by
  refine GlobalTheory.GaloisDescent.mem_range_algebraMap_of_forall_algEquiv z fun σ => ?_
  obtain ⟨y', hy'⟩ := GlobalTheory.FramedBaseChange.exists_frMap GlobalTheory.firstFiveLaws.1 E H Dw l Xo c T T σ.toAlgHom y
  have h1 := hu _ _ _ hy'
  have h2 := hu' _ _ _ hy'
  rw [h y, h y', map_mul, ← h1] at h2
  have hne : σ.toAlgHom (u y) ≠ 0 := by
    simpa using hy
  exact mul_right_cancel₀ hne h2

theorem exists_ratio : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (s : c.F →+* ℂ) (J : Type) (u u' : J → ∀ (S : Type) [CommRing S] [Algebra c.F S], FrPt Xo c S → S), (∀ j, (∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S) (z : FrPt Xo c T), FrMap φ y z → φ (u j S y) = u j T z)) → (∀ j, (∀ (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S) (z : FrPt Xo c T), FrMap φ y z → φ (u' j S y) = u' j T z)) → ∀ z : ℂ, IsMu z → (∀ j (y : @FrPt E _ _ _ H Dw l Xo c ℂ _ s.toAlgebra), @u' j ℂ _ s.toAlgebra y = z * @u j ℂ _ s.toAlgebra y) → ∃ z₀ : c.F, (∃ k : ℕ, 0 < k ∧ z₀ ^ k = 1) ∧ ∀ j (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), u' j S y = algebraMap c.F S z₀ * u j S y := by
  intro E _ _ _ H Dw l Xo c s J u u' hu hu' z hz h
  have key : ∃ z₀ : c.F, (∃ k : ℕ, 0 < k ∧ z₀ ^ k = 1) ∧
      ∀ j (y : @FrPt E _ _ _ H Dw l Xo c ℂ _ s.toAlgebra),
        @u' j ℂ _ s.toAlgebra y = s z₀ * @u j ℂ _ s.toAlgebra y := by
    by_cases h0 : ∀ j (y : @FrPt E _ _ _ H Dw l Xo c ℂ _ s.toAlgebra), @u j ℂ _ s.toAlgebra y = 0
    · refine ⟨1, ⟨1, one_pos, one_pow 1⟩, fun j y => ?_⟩
      rw [h j y, h0 j y, mul_zero, mul_zero]
    · simp only [not_forall] at h0
      obtain ⟨j, y, hy⟩ := h0
      obtain ⟨z₀, hz₀⟩ := @ratio_mem_range E _ _ _ H Dw l Xo c ℂ _ _ s.toAlgebra
        (@u j ℂ _ s.toAlgebra) (@u' j ℂ _ s.toAlgebra)
        (@hu j ℂ ℂ _ s.toAlgebra _ s.toAlgebra) (@hu' j ℂ ℂ _ s.toAlgebra _ s.toAlgebra) z (h j) y hy
      have hz₀' : s z₀ = z := hz₀
      obtain ⟨m, hm, hzm⟩ := hz
      refine ⟨z₀, ⟨m, hm, s.injective ?_⟩, fun j y => ?_⟩
      · rw [map_pow, hz₀', hzm, map_one]
      · rw [hz₀', h j y]
  obtain ⟨z₀, hk, hz₀⟩ := key
  refine ⟨z₀, hk, fun j => ?_⟩
  refine GlobalTheory.NaturalValues.eq_of_eq_complex E H Dw l Xo c s (u' j) (fun S _ _ y => algebraMap c.F S z₀ * u j S y) (hu' j) ?_ ?_
  · intro S T _ _ _ _ φ y y' hyy
    rw [map_mul, φ.commutes, hu j S T φ y y' hyy]
  · intro y
    exact hz₀ j y

end GlobalTheory.ConstRatio
end

