module

public import Mathlib
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0005
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0076
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.FlatMemLatIffStdLat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DualHalfLevelMarkingExistsAndMatch
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaValueStandardLatticeEqClassicalTheta
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0077
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0012
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0037
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsScalarEvaluationsCuspFormsFiniteNet
section
noncomputable section

open Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.NetNorms NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory

private theorem linearIndependent_inclusion_of_le {K R ι : Type} [Field K] [AddCommGroup R] [Module K R]
    {A B : Submodule K R} (hAB : A ≤ B) (F : ι → A) (hF : LinearIndependent K F) :
    LinearIndependent K (fun i => (⟨F i, hAB (F i).2⟩ : B)) := by
  exact hF.map' (Submodule.inclusion hAB) (Submodule.ker_inclusion A B hAB)

set_option synthInstance.maxHeartbeats 200000 in
theorem exists_scalar_readings_on_net : ∀ (D : D7) (T : Top D) (h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → 16 ≤ D.R.f → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∃ (n : ℕ) (ev : Fin n → ((recB h.toLawsCore).Cusp j w →ₛₗ[σ] ℂ)), (∀ F, ∃ y, (recB h.toLawsCore).supN j w σ F / 4 ≤ ‖ev y F‖) ∧ (∀ y F, ‖ev y F‖ ≤ (recB h.toLawsCore).supN j w σ F) ∧ Real.log (16 * (n : ℝ)) ≤ 1041 * Zb D large₂ ^ 3 ∧ ∀ (m : ℕ) (F : Fin m → (recB h.toLawsCore).Cusp j w), LinearIndependent T.Q.c.F F → LinearIndependent ℂ (fun i => fun y => ev y (F i)) := by
  intro D T h hG large₂ j hj w hP hL hr hf σ hσ
  classical
  obtain ⟨NN, -, hnet, hlog⟩ :=
    GlobalTheory.RunIn.exists_net_max_at_goodEmb D T h hG large₂ j hj w hP hL hr hf σ hσ

  obtain ⟨L, hLdef⟩ : ∃ L, L = lieFac (T.Q.Dw j) (xiR D) (wtA w) := ⟨_, rfl⟩
  have hL0 : 0 < L := hLdef ▸ lieFac_pos _ _ _

  have hpn : ∀ (k : (T.U j σ).Comp) (P : Frame ((T.U j σ).X k).Ψ D.R.r → ℂ) x,
      ((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA w) w.n k) P x
        = ‖P x‖ * ((T.U j σ).X k).nfac (laU (T.U j σ) (wtA w) w.n k) x := fun _ _ _ => rfl
  have hnf : ∀ (k : (T.U j σ).Comp) x, 0 ≤ ((T.U j σ).X k).nfac (laU (T.U j σ) (wtA w) w.n k) x := by
    intro k x
    have h1 := GlobalTheory.NetNormExamples.pnorm_nonneg ((T.U j σ).X k) (laU (T.U j σ) (wtA w) w.n k)
      (fun _ => (1 : ℂ)) x
    rwa [hpn, norm_one, one_mul] at h1
  have hg : goodOf T.Q.c σ = σ := by rw [goodOf, ite_eq_left hσ]

  have hsup : ∀ F : (recB h.toLawsCore).Cusp j w, (recB h.toLawsCore).supN j w σ F =
      L * supN (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) F.1) := by
    intro F
    dsimp only [recB, cutN]
    rw [ite_eq_left hj]
    dsimp only [Formalism.L2.Pj.Core.Ns, supC]
    rw [hg, hLdef]

  have hhol : ∀ F : (recB h.toLawsCore).Cusp j w,
      rdU (T.U j σ) F.1 ∈ holSub (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) := by
    intro F
    have hC : F.1 ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA w) w.n := (Submodule.mem_inf.mp F.2).1
    exact ((mem_cusp _ _ _ _ _ _).mp hC).2 σ hσ

  let pt : Fin NN.card → FPt (T.U j σ).X := fun y => (NN.equivFin.symm y).1
  have hsurj : ∀ p ∈ NN, ∃ y, pt y = p := fun p hp =>
    ⟨NN.equivFin ⟨p, hp⟩, by simp only [pt, Equiv.symm_apply_apply]⟩
  let a : Fin NN.card → ℝ := fun y =>
    L * ((T.U j σ).X (pt y).1).nfac (laU (T.U j σ) (wtA w) w.n (pt y).1) (pt y).2
  have ha : ∀ y, 0 ≤ a y := fun y => mul_nonneg hL0.le (hnf _ _)

  let ev : Fin NN.card → ((recB h.toLawsCore).Cusp j w →ₛₗ[σ] ℂ) := fun y =>
    { toFun := fun F => (a y : ℂ) * rdU (T.U j σ) F.1 (pt y).1 (pt y).2
      map_add' := fun F G => by
        show (a y : ℂ) * rdU (T.U j σ) (F.1 + G.1) (pt y).1 (pt y).2 =
          (a y : ℂ) * rdU (T.U j σ) F.1 (pt y).1 (pt y).2 + (a y : ℂ) * rdU (T.U j σ) G.1 (pt y).1 (pt y).2
        rw [map_add (f := _), Pi.add_apply, Pi.add_apply, mul_add]
      map_smul' := fun c F => by
        show (a y : ℂ) * rdU (T.U j σ) (c • F.1) (pt y).1 (pt y).2 =
          σ c • ((a y : ℂ) * rdU (T.U j σ) F.1 (pt y).1 (pt y).2)
        rw [LinearMap.map_smulₛₗ, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
        ring }
  have hev : ∀ y F, ev y F = (a y : ℂ) * rdU (T.U j σ) F.1 (pt y).1 (pt y).2 := fun _ _ => rfl
  have hnorm : ∀ y F, ‖ev y F‖ =
      L * ((T.U j σ).X (pt y).1).pnorm (laU (T.U j σ) (wtA w) w.n (pt y).1)
        (rdU (T.U j σ) F.1 (pt y).1) (pt y).2 := by
    intro y F
    rw [hev, norm_mul, Complex.norm_of_nonneg (ha y), hpn]
    simp only [a]
    ring
  refine ⟨NN.card, ev, ?_, ?_, ?_, ?_⟩
  ·
    intro F
    obtain ⟨p, hp, hb⟩ := hnet _ (hhol F)
    obtain ⟨y, rfl⟩ := hsurj p hp
    refine ⟨y, ?_⟩
    rw [hnorm, hsup]
    have := mul_le_mul_of_nonneg_left hb hL0.le
    linarith
  ·
    intro y F
    rw [hnorm, hsup]
    exact mul_le_mul_of_nonneg_left
      (GlobalTheory.NetNormExamples.pnorm_le_supN (T.U j σ) _ (hhol F) (pt y)) hL0.le
  · exact hlog
  ·
    intro m F hF
    have hF' := linearIndependent_inclusion_of_le (B := T.C j w) inf_le_left F hF
    have hlin : LinearIndependent T.Q.c.F (fun i => (F i : T.R j)) :=
      hF'.map' (T.C j w).subtype (T.C j w).ker_subtype
    have hmem : ∀ i, (F i : T.R j) ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n := fun i =>
      Formalism.L2.Pj.cusp_le_sec (T.Q.Xo j) T.Q.c (T.U j) (wtA w) w.n
        (Submodule.mem_inf.mp (F i).2).1
    have hind : LinearIndependent ℂ (fun i => rdU (T.U j σ) (F i : T.R j)) :=
      (GlobalTheory.reading_linearIndependent_and_injective
        GlobalTheory.lawsFieldsSeparately.2.1 _ _ _ _ (T.Q.Xo j) T.Q.c σ _
        (Formalism.L2.PjFree.Unf.ofPj (T.U j σ))
        ((Formalism.L2.PjFree.isUnf_ofPj (T.U j σ)).2 (h.unf j hj σ hσ))
        (wtA w) w.n).1 m (fun i => (F i : T.R j)) hmem hlin
    rw [Fintype.linearIndependent_iff] at hind ⊢
    intro g hgz i
    refine hind g ?_ i
    show ∑ i, g i • rdU (T.U j σ) (F i).1 = 0
    obtain ⟨Q, hQ⟩ : ∃ Q, Q = ∑ i, g i • rdU (T.U j σ) (F i).1 := ⟨_, rfl⟩
    rw [← hQ]
    have hQmem : Q ∈ holSub (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) := by
      rw [hQ]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hhol (F i))
    have hval : ∀ y, (a y : ℂ) * Q (pt y).1 (pt y).2 = 0 := by
      intro y
      have h1 := congrFun hgz y
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hev] at h1
      rw [hQ, Finset.sum_apply, Finset.sum_apply, Finset.mul_sum, ← h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul]
      ring
    obtain ⟨p, hp, hb⟩ := hnet Q hQmem
    obtain ⟨y, rfl⟩ := hsurj p hp
    have h0 : ((T.U j σ).X (pt y).1).pnorm (laU (T.U j σ) (wtA w) w.n (pt y).1) (Q (pt y).1) (pt y).2 = 0 := by
      have hn := congrArg (‖·‖) (hval y)
      simp only [norm_mul, Complex.norm_of_nonneg (ha y), norm_zero] at hn
      simp only [a] at hn
      rw [hpn]
      have h2 : L * (‖Q (pt y).1 (pt y).2‖ *
          ((T.U j σ).X (pt y).1).nfac (laU (T.U j σ) (wtA w) w.n (pt y).1) (pt y).2) = 0 := by
        rw [← hn]; ring
      exact (mul_eq_zero.mp h2).resolve_left hL0.ne'
    have hS : supN (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) Q ≤ 0 := by
      rw [h0, mul_zero] at hb
      exact hb
    funext k x
    by_cases hx : x ∈ ((T.U j σ).X k).dom
    · show Q k x = 0
      apply GlobalTheory.NetNormExamples.eq_zero_of_pnorm ((T.U j σ).X k) (laU (T.U j σ) (wtA w) w.n k) _ hx
      exact le_antisymm
        ((GlobalTheory.NetNormExamples.pnorm_le_supN (T.U j σ) _ hQmem ⟨k, ⟨x, hx⟩⟩).trans hS)
        (GlobalTheory.NetNormExamples.pnorm_nonneg _ _ _ _)
    · show Q k x = 0
      rw [hQ, Finset.sum_apply, Finset.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      have hz : rdU (T.U j σ) (F i).1 k x = 0 := by
        simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, dite_eq_right hx]
      rw [Pi.smul_apply, Pi.smul_apply, hz, smul_zero]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsThetaGeneratorReadingNeZeroAtFrame
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.ThetaNoZero

theorem mem_mul_smul_top {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {I J : Ideal R}
    (h : I ⊔ J = ⊤) {x : M} (hI : x ∈ I • (⊤ : Submodule R M)) (hJ : x ∈ J • (⊤ : Submodule R M)) :
    x ∈ (I * J) • (⊤ : Submodule R M) := by
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.1 (h ▸ Submodule.mem_top : (1 : R) ∈ I ⊔ J)
  have e : x = i • x + j • x := by rw [← add_smul, hij, one_smul]
  rw [e]
  refine Submodule.add_mem _ ?_ ?_
  · rw [Submodule.mul_smul]
    exact Submodule.smul_mem_smul hi hJ
  · rw [mul_comm, Submodule.mul_smul]
    exact Submodule.smul_mem_smul hj hI

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem dmin_of_isOrtho {X : Data E r} {x : Frame X.Ψ r} (ho : X.IsOrtho x) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm x τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
  unfold dmin lminor psgn
  rw [ho τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, Complex.ofReal_prod,
    ← Fin.prod_univ_eq_prod_range fun a => ((FD.sgn X.p0 a : ℝ) : ℂ)]
  rfl

theorem psgn_mul_self (p i : ℕ) : psgn p i * psgn p i = 1 := by
  unfold psgn
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun a _ => ?_
  unfold FD.sgn
  split_ifs <;> simp

theorem isUnitFr_of_isOrtho {X : Data E r} {x : Frame X.Ψ r} (ho : X.IsOrtho x) : IsUnitFr X x := by
  intro τ i
  rw [dmin_of_isOrtho ho, Complex.norm_real, Real.norm_eq_abs]
  have h := psgn_mul_self X.p0 i
  rcases mul_self_eq_one_iff.1 h with h | h <;> simp [h]

theorem rmul_mem_dom_of_isOrtho {X : Data E r} {x b : Frame X.Ψ r} (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ r)
    (ho : X.IsOrtho (rmul x b)) : rmul x b ∈ X.dom := by
  refine fun τ => ⟨?_, fun i => ?_⟩
  · change (mat x τ * mat b τ).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero (hx τ).1 (hb τ).1
  · rw [dmin_of_isOrtho ho, Complex.ofReal_re, psgn_mul_self]
    exact one_pos

theorem mark_sub_mem {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} {L : Lt E r}
    {mk : Dw.La →ₗ[𝓞 E] (Fin r → E)} (hm : IsMark l L mk) {a a' : Dw.La}
    (ha : a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La)) (ha' : a' ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La))
    (h : a' - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) :
    ((l.M : E)⁻¹) • mk a' - ((l.M : E)⁻¹) • mk a ∈ L := by
  have h1 := mem_mul_smul_top l.coprime h (Submodule.sub_mem _ ha' ha)
  rw [l.prod, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h1
  obtain ⟨z, -, hz⟩ := h1
  have hM : (l.M : E) ≠ 0 := Nat.cast_ne_zero.2 (by have := l.three_le; omega)
  rw [← smul_sub, ← map_sub, ← hz, map_smul, Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E, smul_smul,
    inv_mul_cancel₀ hM, one_smul]
  exact hm.mem z

theorem exists_thGen_rdU_ne_zero : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → 1 ≤ r → ∀ t : ℝ, 0 < t → (∀ k τ, (U.X k).c τ = t) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → r ≤ n → 3 * Formalism.L2.Pj.DF Dw a + 2 ≤ l.M → ∀ (_ : StarRing (𝓞 E)) (nab : NabV Xo c), IsNab Xo c nab → ∀ k, ∀ x ∈ (U.X k).dom, ∃ f ∈ thGen Xo c nab a n, Formalism.L2.PjFree.rdU U f k x ≠ 0 := by
  intro hCI E _ _ _ H Dw l Xo c σ r U hσ hU hr t ht hc a n hdom hrn hM _ nab hnab k x hx
  have hrpq : r = Dw.p + Dw.q := hU.1
  obtain ⟨x₀, b, hb, ho, rfl⟩ := (GlobalTheory.UnitFrames.frame_mul_triangular_orthonormal E r (U.X k).p0 (U.X k).Ψ
    (U.X k).Gm (U.X k).Gm_herm).1 x hx
  have ho : (U.X k).IsOrtho (rmul x b) := ho
  have hx₀ := rmul_mem_dom_of_isOrtho hx hb ho
  obtain ⟨⟨P, hP, hP0⟩, hhom⟩ : (∃ P ∈ harmA (Dw := Dw) c a n, P ≠ 0) ∧ _ :=
    ⟨(GlobalTheory.exists_harmA_ne_zero_and_isHomogeneous E H Dw l c a n).1 hdom (hrpq ▸ hrn),
      (GlobalTheory.exists_harmA_ne_zero_and_isHomogeneous E H Dw l c a n).2⟩
  have hdeg : P.totalDegree ≤ Formalism.L2.Pj.DF Dw a := (hhom P hP.1).totalDegree_le
  letI : Algebra c.F ℂ := σ.toAlgebra
  obtain ⟨W, Dc, A, θ, v, κ, he, -, hw, hsd, hmk, hmarked, hreads, hth, hmean, hvac, hprod⟩ :=
    GlobalTheory.T.exists_analyticData_unitFrame_framedPoint E H Dw l Xo c σ r U hσ hU hr a n hdom k ⟨rmul x b, hx₀⟩ (isUnitFr_of_isOrtho ho)
  have hM0 : l.M ≠ 0 := by have := l.three_le; omega
  have hME : (l.M : E) ≠ 0 := Nat.cast_ne_zero.2 hM0
  obtain ⟨-, -, hconj, hmul, hroots⟩ := _root_.GlobalTheory.Dict.DualMark.dual_marking E H Dw l r (U.X k) (U.X k).Λ (W.mark k) _ hsd hmk
    (Complex.isPrimitiveRoot_exp l.M hM0)
  obtain ⟨Y, hY⟩ := hroots n l.M (Nat.pos_of_ne_zero hM0)
  have hQ0 : MvPolynomial.rename Dc.eL (MvPolynomial.map (algebraMap c.F ℂ) P) ≠ 0 := by
    intro h0
    refine hP0 (MvPolynomial.map_injective (algebraMap c.F ℂ) (algebraMap c.F ℂ).injective
      (MvPolynomial.rename_injective _ Dc.eL.injective ?_))
    rw [h0, map_zero, map_zero]
  have hQd : (MvPolynomial.rename Dc.eL (MvPolynomial.map (algebraMap c.F ℂ) P)).totalDegree ≤
      Formalism.L2.Pj.DF Dw a :=
    (((hhom P hP.1).map (algebraMap c.F ℂ)).rename_isHomogeneous (f := Dc.eL)).totalDegree_le
  obtain ⟨y, hy, hne⟩ := _root_.GlobalTheory.Dict.exists_level_translate_jet_ne_zero E r (U.X k) W.g Dw.p Dc.hr Dc.bas Dc.idx n Dc.sympl hdom.2 H.w0 hw
    (U.X k).Λ hsd (rmul x b) hx₀ ho t ht (hc k) (Mfr l) l.M l.odd (by rw [hconj, hmul]) v hvac θ κ hth hmean hprod
    _ hQ0 (by omega)
  choose xs hxs u hu hyx using fun j => hmk.surj _ (hy j)
  obtain ⟨⟨f, hf, hfs⟩, hev⟩ := GlobalTheory.thetaRule_exists_and_eval hCI E H Dw l Xo c nab hnab a n xs P hP
  have hval := _root_.GlobalTheory.Dict.thVal_eq_thP hCI E H Dw l Xo c r W.g (U.X k) Dc.bas Dc.idx W.e (rmul x b) (U.X k).Λ
    (unC U k ⟨rmul x b, hx₀⟩) A Dc.sympl hx₀ hsd Dw.p n Dc.hr Dc.eL hrpq hdom.2 (he ▸ Dc.dir_eq) nab hnab θ v κ
    hreads hvac hprod (W.mark k) hmk hmarked xs (Y fun j => Submodule.Quotient.mk (xs j))
    (fun j => by
      obtain ⟨⟨a', ha', hq, hYa⟩, hj⟩ := hY (fun j => Submodule.Quotient.mk (xs j)) j
      exact ⟨⟨a', ha', (Submodule.Quotient.eq _).1 hq, hYa⟩, hj⟩)
    a P hP _ (hev f hf ℂ (unC U k ⟨rmul x b, hx₀⟩))
  have hne' := hne (Y fun j => Submodule.Quotient.mk (xs j)) fun j => by
    obtain ⟨⟨a', ha', hq, hYa⟩, -⟩ := hY (fun j => Submodule.Quotient.mk (xs j)) j
    have h1 := mark_sub_mem hmk (hxs j) ha' ((Submodule.Quotient.eq _).1 hq)
    have h2 : y j = ((l.M : E)⁻¹) • W.mark k (xs j) + u j := by
      have := congrArg (fun z => ((l.M : E)⁻¹) • z) (hyx j)
      simp only [smul_add, smul_smul, inv_mul_cancel₀ hME, one_smul, ← Nat.cast_smul_eq_nsmul E l.M (u j)] at this
      exact this
    have h3 := Submodule.sub_mem _ (Submodule.add_mem _ hYa h1) (hu j)
    convert h3 using 1
    rw [h2]
    abel
  rw [← hval] at hne'
  refine ⟨f, ⟨xs, P, hP, hf⟩, fun h0 => hne' ?_⟩
  have hB := (hU.2.2.2.2.1 a n hdom f hfs k).2.1 x hx b hb
  rw [h0, mul_zero] at hB
  have e : Formalism.L2.PjFree.rdU U f k (rmul x b) = Formalism.L2.PjFree.toC (evR Xo c f (U.un k ⟨rmul x b, hx₀⟩)) := dif_pos hx₀
  exact e.symm.trans hB

end GlobalTheory.ThetaNoZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsThClsDDdBCIff
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FieldBC

namespace GlobalTheory.ClassSumFieldChange

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F) {n : ℕ} (d : DeltaDat Xo c n)

theorem eF_incF (a : c.F) :
    ((ddBC hle d).eF (incF c c' hle a) : (covCoeff hle d).F) =
      incF d.c₂ (covCoeff hle d) (le_covCoeff hle d) (d.eF a) := Subtype.ext rfl

theorem exists_algOver (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] :
    ∃ _ : Algebra c'.F k, AlgOver c c' hle k := by
  letI alg : Algebra c.F c'.F := (incF c c' hle).toAlgebra
  haveI : IsScalarTower ℚ c.F c'.F := IsScalarTower.of_algebraMap_eq fun q => by
    rw [eq_ratCast (algebraMap ℚ c'.F), eq_ratCast (algebraMap ℚ c.F), map_ratCast]
  haveI := c'.fin
  haveI : FiniteDimensional c.F c'.F := Module.Finite.of_restrictScalars_finite ℚ c.F c'.F
  let φ : c'.F →ₐ[c.F] k := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  exact ⟨φ.toRingHom.toAlgebra, fun a => φ.commutes a⟩

theorem thLa_iff (w : (Fin n → LevQ Dw d.l₂) → c.F) (La : GenLat E n) (N : ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (k : Type) [CommRing k] [Algebra d.c₂.F k] [A₂ : Algebra (covCoeff hle d).F k]
    (h₂ : AlgOver d.c₂ (covCoeff hle d) (le_covCoeff hle d) k) (y₂ : FrPt d.Xo₂ (covCoeff hle d) k) (v : k) :
    thLaValAt d.Xo₂ (covCoeff hle d) (nabBC (le_covCoeff hle d) d.nab₂)
        (fun q => (ddBC hle d).eF (incF c c' hle (w q))) La N
        (MvPolynomial.map ((ddBC hle d).eF : c'.F →+* (ddBC hle d).c₂.F) (MvPolynomial.map (incF c c' hle) P)) y₂ v ↔
      thLaValAt d.Xo₂ d.c₂ d.nab₂ (fun q => d.eF (w q)) La N
        (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P) (y₂.res (le_covCoeff hle d) h₂) v := by
  have h := GlobalTheory.FieldBC.shortValAt_bc E H Dw d.l₂ d.Xo₂ d.c₂ (covCoeff hle d) (le_covCoeff hle d) d.nab₂ n
    (fun q => d.eF (w q)) La 1 N (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P) k h₂ y₂ v
  have e : (MvPolynomial.map ((ddBC hle d).eF : c'.F →+* (ddBC hle d).c₂.F) (MvPolynomial.map (incF c c' hle) P) :
      MvPolynomial (LtN Dw n) (covCoeff hle d).F) =
      MvPolynomial.map (incF d.c₂ (covCoeff hle d) (le_covCoeff hle d))
        (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P) := by
    rw [MvPolynomial.map_map, MvPolynomial.map_map]
    exact congrArg (fun g => MvPolynomial.map g P) (RingHom.ext fun a => eF_incF hle d a)
  rw [map_one] at h
  unfold thLaValAt
  rw [e]
  exact h

theorem isThClsD_ddBC_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F) (n : ℕ) (d : DeltaDat Xo c n) (Cl : Type) [Fintype Cl] (w : Cl → (Fin n → LevQ Dw d.l₂) → c.F) (La : Cl → GenLat E n) (Nc gam : Cl → ℕ) (vol : c.F) (ep : Cl → c.F) (Vs : Type) [AddCommGroup Vs] [Module c.F Vs] (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (Vs' : Type) [AddCommGroup Vs'] [Module c'.F Vs'] (io' : Vs' →ₗ[c'.F] MvPolynomial (LtN Dw n) c'.F) (x : Cl → Vs) (x' : Cl → Vs'), (∀ k, io' (x' k) = MvPolynomial.map (incF c c' hle) (io (x k))) → d.cδ ∈ sec d.Xo₂ d.c₂ 0 0 → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (m : ℕ), ∀ f ∈ sec Xo c a m, (IsThClsD Xo c' (ddBC hle d) (fun k q => incF c c' hle (w k q)) La Nc gam (incF c c' hle vol) (fun k => incF c c' hle (ep k)) io' x' (rulBC hle f) ↔ IsThClsD Xo c d w La Nc gam vol ep io x f) := by
  intro E _ _ _ H Dw l Xo c c' hle n d Cl _ w La Nc gam vol ep Vs _ _ io Vs' _ _ io' x x' hio hδ a m f hf
  have hcoef : ∀ (k : Type) [Field k] [Algebra c.F k] [Algebra c'.F k], AlgOver c c' hle k → ∀ cl,
      algebraMap c'.F k (incF c c' hle vol * ((gam cl : c'.F))⁻¹ * incF c c' hle (ep cl)) =
        algebraMap c.F k (vol * ((gam cl : c.F))⁻¹ * ep cl) := by
    intro k _ _ _ h cl
    rw [← h, map_mul (incF c c' hle), map_mul (incF c c' hle), map_inv₀, map_natCast]
  have hf' := ((GlobalTheory.FieldBC.rulBC_sec_val_linear E H Dw l Xo c c' hle).1 a m f hf).2
  have hδ' := ((GlobalTheory.FieldBC.rulBC_sec_val_linear E H Dw d.l₂ d.Xo₂ d.c₂ (covCoeff hle d) (le_covCoeff hle d)).1 0 0 d.cδ hδ).2
  have hov := (_root_.GlobalTheory.FieldBC.frOver_isLev_ddBC E H Dw l Xo c c' hle n d).1
  constructor
  · intro H' k _ _ _ _ hk y y₂ hy
    obtain ⟨A, h⟩ := exists_algOver hle k
    letI A₂ : Algebra (covCoeff hle d).F k := A
    have h₂ : AlgOver d.c₂ (covCoeff hle d) (le_covCoeff hle d) k := fun b => by
      obtain ⟨b, rfl⟩ := d.eF.surjective b
      rw [hk, ← h b]
      rfl
    obtain ⟨vc, hv, he⟩ := @H' k _ _ A A₂ (fun _ => rfl) (y.ext hle h) (y₂.ext (le_covCoeff hle d) h₂)
      ((hov k h h₂ _ _).2 hy)
    refine ⟨vc, fun cl => ?_, ?_⟩
    · have := hv cl
      rw [hio] at this
      exact (thLa_iff hle d (w cl) (La cl) (Nc cl) (io (x cl)) k h₂ _ _).1 this
    · have e1 := hf' k h (y.ext hle h)
      have e2 := hδ' k h₂ (y₂.ext (le_covCoeff hle d) h₂)
      simp only [hcoef k h] at he
      rw [e1] at he
      exact he.trans (congrArg (· * _) e2)
  · intro H' k _ _ A A₂ hk y y₂ hy
    letI A₂' : Algebra (covCoeff hle d).F k := A₂
    letI := resAlg hle k
    letI := resAlg (le_covCoeff hle d) k
    have h : AlgOver c c' hle k := fun _ => rfl
    have h₂ : AlgOver d.c₂ (covCoeff hle d) (le_covCoeff hle d) k := fun _ => rfl
    obtain ⟨vc, hv, he⟩ := H' k (fun b => hk (incF c c' hle b)) (y.res hle h)
      (FrPt.res (c' := covCoeff hle d) (le_covCoeff hle d) h₂ y₂) ((hov k h h₂ y₂ y).1 hy)
    refine ⟨vc, fun cl => ?_, ?_⟩
    · rw [hio]
      exact (thLa_iff hle d (w cl) (La cl) (Nc cl) (io (x cl)) k h₂ y₂ _).2 (hv cl)
    · have e1 := hf' k h y
      have e2 := hδ' k h₂ y₂
      simp only [hcoef k h]
      rw [e1]
      exact he.trans (congrArg (· * _) e2.symm)

end GlobalTheory.ClassSumFieldChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaRuleValueTestRingEqThetaValueStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaRuleValue_testRing_eq_thetaValue : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (x : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n → ∀ f : Rul Xo c, IsThRule Xo c nab x P f → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y → ThValAt Xo c nab y x P (evR Xo c f y) := by
  first | exact @GlobalTheory.thValAt_evR_of_fromTest | exact GlobalTheory.thValAt_evR_of_fromTest | (intros; apply GlobalTheory.thValAt_evR_of_fromTest <;> assumption)
end

