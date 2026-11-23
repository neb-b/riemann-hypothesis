module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0003
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.ArcDatumIsArcPointBasis
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0038
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.Bundle0002
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.PolyConstantLeZBasePowFour

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogNormNormaliserEqHalfDegreeLog
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory

theorem normaliser_factor_mul_bar {D : D7} (EX : ErrX D) (i : Fin 2) :
    EX.piG i * piBarO EX i = ((D.host.g i : ℕ) : 𝓞 D.host.E) := by
  apply NumberField.RingOfIntegers.ext
  simpa [piBarO, NumberField.RingOfIntegers.mapRingHom_apply] using EX.piG_norm i

theorem map_piBar_eq_conj {D : D7} (EX : ErrX D) (i : Fin 2) (ρ : 𝓞 D.host.E →+* ℂ)
    (hρ : Function.Injective ρ) : ρ (piBarO EX i) = starRingEnd ℂ (ρ (EX.piG i)) := by
  let ψ : D.host.E →+* ℂ := IsFractionRing.lift hρ
  have hψ : ∀ x : 𝓞 D.host.E, ψ (x : D.host.E) = ρ x := fun x => IsFractionRing.lift_algebraMap hρ x
  rw [← hψ (piBarO EX i), ← hψ (EX.piG i), piBarO, NumberField.RingOfIntegers.mapRingHom_apply]
  exact D.host.toHostAx.conjE_apply ψ _

theorem log_norm_normaliser : ∀ (D : D7) (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (j : ℕ) (w : WeightFamilies.Wt D j) (σ : B.KO →+* ℂ), nnW B hinj EX w ≠ 0 ∧ Real.log ‖σ (nnW B hinj EX w : B.KO)‖ = (WeightAlgebra.DF w : ℝ) / 2 * Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) := by
  intro D B hinj EX j w σ
  set ρ : 𝓞 D.host.E →+* ℂ := σ.comp ((algebraMap (𝓞 B.KO) B.KO).comp (iE D hinj B)) with hρdef
  have hρ : Function.Injective ρ :=
    σ.injective.comp ((IsFractionRing.injective (𝓞 B.KO) B.KO).comp (iE_injective D hinj B))
  have hg : ∀ i : Fin 2, (0 : ℝ) < (D.host.g i : ℝ) := fun i => by
    exact_mod_cast (D.host.g_prime i).pos
  have hval : σ ((nnW B hinj EX w : 𝓞 B.KO) : B.KO) =
      ∏ i : Fin 2, ρ (EX.piG i ^ Dplus w * piBarO EX i ^ Dminus w) := by
    simp [nnW, hρdef, map_prod, map_mul, map_pow]
  have hnorm : ‖σ ((nnW B hinj EX w : 𝓞 B.KO) : B.KO)‖ =
      ∏ i : Fin 2, (D.host.g i : ℝ) ^ (((Dplus w : ℝ) + Dminus w) / 2) := by
    rw [hval, norm_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    exact norm_map_pow_mul_pow_of_mul_conj ρ _ _ _ (normaliser_factor_mul_bar EX i)
      (map_piBar_eq_conj EX i ρ hρ) _ _
  have hDF : WeightAlgebra.DF w = Dplus w + Dminus w := by
    simp only [WeightAlgebra.DF, WeightAlgebra.degP, Dplus, Dminus, Finset.sum_add_distrib]
  have h0 := Real.rpow_pos_of_pos (hg 0) (((Dplus w : ℝ) + Dminus w) / 2)
  have h1 := Real.rpow_pos_of_pos (hg 1) (((Dplus w : ℝ) + Dminus w) / 2)
  refine ⟨fun hz => ?_, ?_⟩
  · have hz' : ‖σ ((nnW B hinj EX w : 𝓞 B.KO) : B.KO)‖ = 0 := by rw [hz]; simp
    rw [hnorm, Fin.prod_univ_two] at hz'
    nlinarith [mul_pos h0 h1]
  · rw [hnorm, Fin.prod_univ_two, Real.log_mul h0.ne' h1.ne', Real.log_rpow (hg 0), Real.log_rpow (hg 1),
      Real.log_mul (hg 0).ne' (hg 1).ne', hDF]
    push_cast
    ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.MemSpanCuspReadingsIffComponents
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

namespace GlobalTheory.Shares

theorem spanMem_ssgt_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) {P : Frame X.Ψ r → ℂ} (hP : P ∈ X.SS la) : P ∈ X.SSgt la 0 := by
  refine ⟨hP, fun ξ hξ ν hν x hx => ?_⟩
  by_contra hne
  obtain ⟨⟨hsec, C, hC⟩, h0⟩ := hP
  have hpos := (moderateCoefficientPositivity_holds r X la P C 0 hsec (fun y hy => by simpa using hC y hy)).1 ξ hξ ν x hx hne
  have hsum : ∑ τ, ν τ = 0 := le_antisymm hν (Finset.sum_nonneg fun τ _ => hpos τ)
  have hz : ν = 0 := by
    funext τ
    exact (Finset.sum_eq_zero_iff_of_nonneg fun τ _ => hpos τ).1 hsum τ (Finset.mem_univ τ)
  subst hz
  exact hne (h0 ξ hξ x hx)

theorem spanMem_rdR {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (u : WeightFamilies.Wt D j)
    (F : (recB h.toLawsCore).Cusp j u) (k : (T.U j T.σ₀).Comp) :
    rdR h j F k ∈ ((T.U j T.σ₀).X k).SSgt (laR T j u k) 0 := by
  have hF : F.1 ∈ T.C j u := by
    rw [← cutR_eq T.C hj]; exact F.2
  exact spanMem_ssgt_zero _ _
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.readings_holomorphic_cuspForms (U := T.U j) siegelSpaceAlgebra_holds T.good_σ₀ (wtA u) u.n ⟨F.1, hF⟩ k)

theorem span_readings_components : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e → ∀ u : WeightFamilies.Wt D j, (∀ g ∈ R.sp u Set.univ, ∃ f : ∀ k : (T.U j T.σ₀).Comp, Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ, (∀ k, f k ∈ ((T.U j T.σ₀).X k).SSgt (laR T j u k) 0) ∧ ∀ y, g y = f (e y).1 (e y).2.1) ∧ (∀ (A : ∀ k : (T.U j T.σ₀).Comp, Set (Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ)) (s : Set ((recB h.toLawsCore).Cusp j u)), OntoBy h j u A s → ∀ f : ∀ k : (T.U j T.σ₀).Comp, Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ, (∀ k, f k ∈ A k) → (fun y => f (e y).1 (e y).2.1) ∈ R.sp u s) ∧ ∀ (F : (recB h.toLawsCore).Cusp j u) (k : (T.U j T.σ₀).Comp), rdR h j F k ∈ ((T.U j T.σ₀).X k).SSgt (laR T j u k) 0 := by
  intro D T h j hj n R e hR u
  refine ⟨fun g hg => ?_, fun A s hA f hf => ?_, fun F k => spanMem_rdR h j hj u F k⟩
  · unfold Rdg.sp at hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨F, -, rfl⟩ := hg
      exact ⟨fun k => rdR h j F k, fun k => spanMem_rdR h j hj u F k, fun y => hR.2 u F y⟩
    | zero =>
      exact ⟨fun _ => 0, fun k => (siegelSpaceAlgebra_holds _ _ (laR T j u k) (laR T j u k) 0).2.2.1.1, fun _ => rfl⟩
    | add g g' _ _ hg hg' =>
      obtain ⟨f, hf, e1⟩ := hg
      obtain ⟨f', hf', e2⟩ := hg'
      refine ⟨fun k => f k + f' k,
        fun k => (siegelSpaceAlgebra_holds _ _ (laR T j u k) (laR T j u k) 0).2.2.1.2.1 _ (hf k) _ (hf' k), fun y => ?_⟩
      simp only [Pi.add_apply, e1, e2]
    | smul a g _ hg =>
      obtain ⟨f, hf, e1⟩ := hg
      refine ⟨fun k => a • f k,
        fun k => (siegelSpaceAlgebra_holds _ _ (laR T j u k) (laR T j u k) 0).2.2.1.2.2 a _ (hf k), fun y => ?_⟩
      simp only [Pi.smul_apply, e1]
  · obtain ⟨m, a, F, hF, hsum⟩ := hA f hf
    have : (fun y => f (e y).1 (e y).2.1) = ∑ i, a i • R.ev ((recPlusN h j hj n).inc u (F i)) := by
      funext y
      rw [hsum _ _ (e y).2.2, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.smul_apply, hR.2 u (F i) y, smul_eq_mul]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨F i, hF i, rfl⟩)

end GlobalTheory.Shares
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PageTwoLeLAndSigns
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory

theorem page_two_le_L_and_signs : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), FamilyHypotheses.HypPage large₂ X H C2 A2 CR CT ka wL wF Tn nP nW h0 → ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ ka → 2 ≤ large₂.sc.L ∧ 2 ≤ D.R.f ∧ 6 ≤ D.R.r ∧ 0 ≤ lamStar D ∧ (1 ≤ j → 1 ≤ WeightFamilies.dimY D j) ∧ (FamilyHypotheses.SupBoundPageRows D large₂ ka ↔ ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ ka) := by
  intro D B P j X large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hp hc
  have hm := D.R.two_le_m
  have hk := D.R.m_add_three_le_k
  have hf : 2 ≤ D.R.f := by
    have : 0 < D.R.ord := D.R.ord_pos
    unfold Ranks.f Ranks.n; omega
  have hr : 6 ≤ D.R.r := by unfold Ranks.r; omega
  refine ⟨?_, hf, hr, ?_, ?_, Iff.rfl⟩
  · obtain ⟨-, hS, -⟩ := hp
    have hn : ka.n = D.R.nV := hS.1
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hC, hZ, -⟩ := hS
    obtain ⟨-, -, -, -, hlf, -, -, -, hln⟩ := hc
    by_contra hL
    push_neg at hL
    have hf0 : (0 : ℝ) < D.R.f := by exact_mod_cast (by omega : 0 < D.R.f)
    have hr0 : (0 : ℝ) < D.R.r := by exact_mod_cast (by omega : 0 < D.R.r)
    have hrn : (D.R.r : ℝ) ≤ ka.n := by
      rw [hn]; exact_mod_cast (by unfold Ranks.nV; omega : D.R.r ≤ D.R.nV)
    have he : Real.exp 1 ≤ 3 := (Real.exp_one_lt_d9.trans (by norm_num)).le
    have he4 : Real.exp 4 ≤ 81 := by
      have : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
      rw [this]
      calc Real.exp 1 ^ 4 ≤ 3 ^ 4 := pow_le_pow_left₀ (Real.exp_pos 1).le he 4
        _ = 81 := by norm_num
    have hf1 : (D.R.f : ℝ) ≤ 81 :=
      ((Real.log_le_iff_le_exp hf0).1 (by linarith : Real.log D.R.f ≤ 4)).trans he4
    have hr1 : (D.R.r : ℝ) ≤ 81 :=
      hrn.trans (((Real.log_le_iff_le_exp (hr0.trans_le hrn)).1
        (by linarith : Real.log ka.n ≤ 4)).trans he4)
    have hfr : (D.R.f : ℝ) * D.R.r ≤ 81 * 81 := mul_le_mul hf1 hr1 hr0.le (by norm_num)
    have hZ2 : Zb D large₂ ≤ 81 * 81 * 2 := by
      unfold Zb
      have := mul_pos hf0 hr0
      nlinarith
    have hC2 : (1000 : ℝ) ^ 20 ≤ H.C1 ^ 20 := pow_le_pow_left₀ (by norm_num) hC 20
    have : (81 * 81 * 2 : ℝ) < 1000 ^ 20 := by norm_num
    linarith
  · unfold lamStar
    have h1 := Real.log_natCast_nonneg (D.host.g 0 * D.host.g 1)
    have h2 := Real.log_natCast_nonneg (D.R.f ^ 2 * D.host.q * D.host.d)
    push_cast at h1 h2
    have e : 4 * ((D.R.f : ℝ) / 2) ^ 2 = (D.R.f : ℝ) ^ 2 := by ring
    rw [e]
    exact add_nonneg h1 h2
  · intro hj
    unfold WeightFamilies.dimY
    have hp5 : 5 ≤ (D.R.sigW j).1 := by
      show 5 ≤ D.R.k + j - 1
      omega
    have h1 : 1 ≤ (D.R.sigW j).1 * ((D.R.sigW j).1 - 1) / 2 := by
      have : 5 * 4 ≤ (D.R.sigW j).1 * ((D.R.sigW j).1 - 1) := Nat.mul_le_mul hp5 (by omega)
      omega
    exact Nat.mul_pos (by omega) (by omega)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PointsInterpolationGenericSections
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

namespace GlobalTheory.Shares

theorem addL_zero_pts {D : D7} {j : ℕ} (u wL : WeightFamilies.Wt D j) : addL u wL 0 = u := by
  show wadd u (wsmul 0 wL) = u
  cases u
  simp [wadd, wsmul]

theorem rdg_s_apply {D : D7} {T : Top D} {h : LawsP T} {j : ℕ} {hj : InR D j} {n : SecNorm (recB h.toLawsCore)}
    {R : Rdg (recPlusN h j hj n)} {e : R.Y ≃ DomPt T j} (hR : IsRdgU h j hj n R e) {N : ℕ} {wL : WeightFamilies.Wt D j}
    (w : Fin N → (recB h.toLawsCore).Cusp j wL) (t : Idx D j N → ℂ) (i : Fin (WeightFamilies.dimY D j + 1)) (y : R.Y) :
    R.s w t i y = ∑ k, t (i, k) * rdR h j (w k) (e y).1 (e y).2.1 := by
  simp only [Rdg.s, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hR.2]

theorem mem_sp_of_rdOnto {D : D7} {T : Top D} {h : LawsP T} {j : ℕ} {hj : InR D j} {n : SecNorm (recB h.toLawsCore)}
    {R : Rdg (recPlusN h j hj n)} {e : R.Y ≃ DomPt T j} (hR : IsRdgU h j hj n R e) {u : WeightFamilies.Wt D j}
    (hO : RdOnto h j u) (f : ∀ k : (T.U j T.σ₀).Comp, Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ)
    (hf : ∀ k, f k ∈ ((T.U j T.σ₀).X k).SS (laR T j u k)) :
    (fun y => f (e y).1 (e y).2.1) ∈ R.sp u Set.univ := by
  obtain ⟨m, a, F, -, hF⟩ := hO f hf
  have hfun : (fun y => f (e y).1 (e y).2.1) = ∑ i, a i • R.ev ((recPlusN h j hj n).inc u (F i)) := by
    funext y
    rw [hF _ _ (e y).2.2]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hR.2]
  rw [hfun]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨F i, Set.mem_univ _, rfl⟩)

theorem points_and_interp : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e → ∀ (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (c1 : ℝ) (A : ArchAt h j w wF Tn c1) (t : Idx D j N → ℂ) (Fl : FlatAt h j A t) (δ : ℕ) (xs : Fin δ → R.Y) (en : Fin δ ≃ Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ), (∀ q, e (xs q) = ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩) → (∀ k : ℕ, RdOnto h j (addL wF wL k)) → (∀ q, R.s w t 0 (xs q) ≠ 0 ∧ ∀ i : Fin (WeightFamilies.dimY D j), R.s w t i.succ (xs q) = 0) ∧ ∀ v : Fin δ → ℂ, ∃ f ∈ R.sp wF Set.univ, ∀ q, f (xs q) = v q := by
  intro D T h j hj n R e hR N wL wF w Tn c1 A t Fl δ xs en hxs hO

  have hvan : ∀ (k : (T.U j T.σ₀).Comp) (a : Fin (nd ((T.U j T.σ₀).X k))) (p : Fin (Fl.Fl k).δ),
      (Fl.Fl k).s a ((Fl.Fl k).xs p) = 0 := by
    intro k a p
    have hb : (fun _ => (1 : Matrix (Fin D.R.r) (Fin D.R.r) ℂ) : Frame ((T.U j T.σ₀).X k).Ψ D.R.r) ∈
        Bor ((T.U j T.σ₀).X k).Ψ D.R.r := by
      intro τ
      refine ⟨?_, fun a c hca => Matrix.one_apply_ne hca.ne'⟩
      show (1 : Matrix (Fin D.R.r) (Fin D.R.r) ℂ).det ≠ 0
      simp
    have hself : (Fl.Fl k).xs p = lact 1 (rmul ((Fl.Fl k).xs p)
        (fun _ => (1 : Matrix (Fin D.R.r) (Fin D.R.r) ℂ))) := by
      funext τ a c
      simp only [lact, rmul, mat, Units.val_one, Matrix.map_one _ (map_zero τ.1) (map_one τ.1), one_mul]
      have hm : (Matrix.of ((Fl.Fl k).xs p τ) : Matrix (Fin D.R.r) (Fin D.R.r) ℂ) * 1 =
          Matrix.of ((Fl.Fl k).xs p τ) := Matrix.mul_one _
      exact (congrFun (congrFun hm a) c).symm
    exact (((Fl.Fl k).S_eq _ ((Fl.Fl k).xs_mem p)).2
      ⟨p, 1, ((T.U j T.σ₀).X k).Γ.one_mem, _, hb, hself⟩) a
  refine ⟨fun q => ⟨?_, fun i => ?_⟩, fun v => ?_⟩
  · rw [rdg_s_apply hR, hxs q]
    dsimp only
    rw [← Fl.h0]
    exact (Fl.Fl _).w0_ne _
  · rw [rdg_s_apply hR, hxs q]
    dsimp only
    have hs := Fl.hs (en q).1 (Fin.cast (A.dim (en q).1).symm i) ((Fl.Fl (en q).1).xs (en q).2)
    have hi : Fin.cast (A.dim (en q).1) (Fin.cast (A.dim (en q).1).symm i) = i := Fin.ext rfl
    rw [hi] at hs
    rw [← hs]
    exact hvan _ _ _
  ·
    have hF : ∀ k : (T.U j T.σ₀).Comp, ∃ F ∈ ((T.U j T.σ₀).X k).SSgt (A.Xa k).Fp 0,
        ∀ p, F ((Fl.Fl k).xs p) = v (en.symm ⟨k, p⟩) := by
      intro k
      obtain ⟨bb, m, h1, h2, h3⟩ := (A.mar k).1
      exact interpStatement_holds _ _ (A.Xa k) (Fl.Fl k)
        (GlobalTheory.ClosedDiscontinuity.propDisc_closed _ _)
        ⟨bb, m, h1, h2, fun x0 hx0 z hz ξ => by simpa using h3 0 (Set.mem_insert _ _) x0 hx0 z hz ξ⟩
        (A.mar k).2.2.1 (fun P hP => by simpa using (A.mar k).2.2.2.2 0 P (by simpa using hP)) _
    choose F hFmem hFval using hF
    have hO0 : RdOnto h j wF := by
      have h0 := hO 0
      rwa [addL_zero_pts] at h0
    have hf : ∀ k, F k ∈ ((T.U j T.σ₀).X k).SS (laR T j wF k) := by
      intro k
      rw [← A.hF k]
      exact (hFmem k).1
    refine ⟨_, mem_sp_of_rdOnto hR hO0 F hf, fun q => ?_⟩
    show F (e (xs q)).1 (e (xs q)).2.1 = v q
    rw [hxs q]
    exact (hFval _ _).trans (by simp)

end GlobalTheory.Shares
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RamifiedPrimePowersSizeBounds
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory.RunIn

theorem pPow_size : ∀ (D : D7) (j : ℕ) (w : WeightFamilies.Wt D j), 1 ≤ D.host.q ∧ 1 ≤ D.host.d ∧ 0 ≤ Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2 * D.host.q * D.host.d) ∧ 0 ≤ Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) ∧ (c2 D w : ℝ) * Real.log D.host.QS + (Formalism.MainNotions.DIV.Cons.cHalf w : ℝ) * Real.log D.host.q + (Formalism.MainNotions.DIV.Cons.cHalf w : ℝ) * Real.log D.host.d ≤ ((WeightAlgebra.DF w : ℝ) + 1) * Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2 * D.host.q * D.host.d) ∧ ∀ a b c : ℕ, 1 ≤ pPow D a b c ∧ Real.log (pPow D a b c) = a * Real.log D.host.QS + b * Real.log D.host.q + c * Real.log D.host.d := by
  intro D j w
  have hq : 1 ≤ D.host.q := by have := D.host.qd_big.1; omega
  have hd : 1 ≤ D.host.d := by have := D.host.qd_big.2; omega
  have hqR : (1 : ℝ) ≤ D.host.q := by exact_mod_cast hq
  have hdR : (1 : ℝ) ≤ D.host.d := by exact_mod_cast hd
  have hlq : 0 ≤ Real.log D.host.q := Real.log_nonneg hqR
  have hld : 0 ≤ Real.log D.host.d := Real.log_nonneg hdR
  have hQ : (1 : ℝ) ≤ D.host.QS := by exact_mod_cast D.host.QS_pos
  have hl2 : 0 ≤ Real.log D.host.QS := Real.log_nonneg hQ
  have hQf : (D.host.QS : ℝ) ≤ 4 * ((D.R.f : ℝ) / 2) ^ 2 := by
    have h1 : (D.host.QS : ℝ) ≤ (D.R.n : ℝ) ^ 2 := by exact_mod_cast D.host.QS_le
    have h2 : (D.R.f : ℝ) = 2 * D.R.n := by unfold Ranks.f; push_cast; ring
    rw [h2]; nlinarith [sq_nonneg (D.R.n : ℝ)]
  have hlf : Real.log D.host.QS ≤ Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2) := Real.log_le_log (by linarith) hQf
  have hlog : Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2 * D.host.q * D.host.d) =
      Real.log (4 * ((D.R.f : ℝ) / 2) ^ 2) + Real.log D.host.q + Real.log D.host.d := by
    have h0 : (0 : ℝ) < 4 * ((D.R.f : ℝ) / 2) ^ 2 := by linarith
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul h0.ne' (by positivity)]
  have hD : (0 : ℝ) ≤ (WeightAlgebra.DF w : ℝ) := Nat.cast_nonneg _
  refine ⟨hq, hd, ?_, ?_, ?_, ?_⟩
  · rw [hlog]; linarith
  · apply Real.log_nonneg
    have h0 : (1 : ℝ) ≤ D.host.g 0 := by exact_mod_cast (D.host.g_prime 0).one_le
    have h1 : (1 : ℝ) ≤ D.host.g 1 := by exact_mod_cast (D.host.g_prime 1).one_le
    nlinarith
  · have hc2 : (c2 D w : ℝ) = (WeightAlgebra.DF w : ℝ) := rfl
    have hch : (Formalism.MainNotions.DIV.Cons.cHalf w : ℝ) ≤ (WeightAlgebra.DF w : ℝ) + 1 := by
      have h1 := (Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (WeightAlgebra.DF w : ℝ) / 2 by positivity)).le
      unfold Formalism.MainNotions.DIV.Cons.cHalf
      linarith
    have a1 := mul_le_mul_of_nonneg_left hlf hD
    have a2 := mul_le_mul_of_nonneg_right hch hlq
    have a3 := mul_le_mul_of_nonneg_right hch hld
    rw [hlog, hc2]
    nlinarith
  · intro a b c
    have hQ0 : 0 < D.host.QS := D.host.QS_pos
    refine ⟨?_, ?_⟩
    · unfold pPow
      exact Nat.one_le_iff_ne_zero.mpr (by positivity)
    · unfold pPow
      push_cast
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow, Real.log_pow]

end GlobalTheory.RunIn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShareRhoAndShareRhoTOfShareRhoR
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps GlobalTheory.Shares

namespace GlobalTheory

theorem shareRho_and_shareRhoT_of_shareRhoR :
    ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (ka wL wF : WeightFamilies.Wt D j)
      (G : GlobalFamilyData X ka wL wF) (S : Scal B) (T d : ℕ) (Gc : ℝ), ShareRhoR G S T d → G.TiedZ S T Gc →
      (∀ la, InContainZ G la S T) →
      ShareRho (D := D) (j := j) T G.rz d ∧ ShareRhoT (D := D) (j := j) T G.rz G.rq d := by
  intro D B P j X ka wL wF G S T d Gc hR hT hZ
  obtain ⟨la0⟩ := Formalism.MainNotions.Gaps.EtaleWeightGaps.exists_prime B.KO
  have hr : Module.finrank (Kp X la0 G.N) ↥(Submodule.span (Kp X la0 G.N) (zAll G la0 S T)) = G.rz :=
    rz_eq_finrank G S T Gc la0 hT (hZ la0)
  have h := hR la0
  rw [hr] at h
  refine ⟨h, ?_⟩
  unfold ShareRhoT
  have h0 : (0 : ℝ) ≤ (G.rq : ℝ) := Nat.cast_nonneg _
  linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SizePageRowsOfSizePageAt
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory

theorem pageRows_of_pageAt : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), FamilyHypotheses.HypPage large₂ X H C2 A2 CR CT ka wL wF Tn nP nW h0 → PageAt large₂ C2 A2 → 4 * H.CK ≤ WeightFamilies.PPv D large₂ C2 A2 ^ 2 * D.R.f → ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ ka ∧ 16 ≤ D.R.f := by
  intro D B P j X large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hp hPg hCK
  have hm4 := EtaleWeightGaps.lift_index_pow_four_le_degree hPg
  obtain ⟨Q, PT, -, hC, hA⟩ := hPg
  have hPP : WeightFamilies.PPv D large₂ C2 A2 = PT.PP := by rw [← hC, ← hA]; exact WeightFamilies.PPv_rec PT
  obtain ⟨hA', hS, -, h4, -⟩ := hp
  obtain ⟨-, -, -, -, hg, -, -, hp1, hp2, -⟩ := hA'
  obtain ⟨hn, -, -, -, -, -, -, hsz, -, -, -, -, -, -, -, -, -, hT, -⟩ := hS
  obtain ⟨-, -, -, hP3, -⟩ := h4
  rw [hPP] at hCK hP3
  have hL := EtaleWeightGaps.Num.Pm.one_le_L large₂
  have hf2 := EtaleWeightGaps.Num.Pm.two_le_f D
  have hr6 := EtaleWeightGaps.Num.Pm.six_le_r D
  have hm2 := EtaleWeightGaps.Num.Pm.two_le_m D
  have hkr := EtaleWeightGaps.Num.Pm.k_le_r D
  have hrt := EtaleWeightGaps.Num.Pm.r_le_alt_alt D
  have hlf := EtaleWeightGaps.Num.Pm.log_f_le Q
  have hlr := EtaleWeightGaps.Num.Pm.log_r_le Q
  obtain ⟨hlc, hlt⟩ := EtaleWeightGaps.Num.Pm.log_cond_le Q
  have hb : Real.log large₂.sc.b = large₂.sc.L := EtaleWeightGaps.Num.Pm.log_b large₂
  have hb0 : 0 < large₂.sc.b := Real.exp_pos _
  have hf0 : (0 : ℝ) < D.R.f := by linarith
  have hr0 : (0 : ℝ) < D.R.r := by linarith
  have hP0 : 0 < PT.PP := PT.PP_pos (by unfold zBase; positivity)
  refine ⟨⟨hg, ?_, ?_, ?_, ?_, hp1, hp2, ?_, ?_⟩, ?_⟩
  · rw [EtaleWeightGaps.Num.Pm.lrd_eq]; linarith [log_rdE_le_scL Q]
  · have hd := EtaleWeightGaps.Num.Pm.one_le_d D
    have hq := EtaleWeightGaps.Num.Pm.one_le_q D
    have h1 : (D.host.d : ℝ) ≤ (LevelStarExponents.condE D : ℝ) := by
      rw [EtaleWeightGaps.Num.Pm.condE_cast]
      have hS : (1 : ℝ) ≤ (D.host.QS : ℝ) := by exact_mod_cast D.host.QS_pos
      have : (1 : ℝ) ≤ (D.host.QS : ℝ) * D.host.q := by nlinarith
      nlinarith
    linarith [Real.log_le_log (by linarith) h1]
  · linarith [Q.ccK_log]
  · linarith
  · have hs : 1 + (WeightAlgebra.DF ka : ℝ) ≤ ka.size := by
      unfold WeightFamilies.Wt.size WeightAlgebra.DF degP
      have h2 : 0 ≤ (D.R.f : ℝ) * ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * (D.R.r : ℝ) * (ka.n : ℝ) := by positivity
      push_cast at h2 ⊢
      linarith
    have hk0 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
    have hT1 : (1 : ℝ) ≤ (Tn : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hT)
    have hP3' : PT.PP ^ 3 ≤ large₂.sc.b := (le_mul_of_one_le_right (by positivity) hT1).trans hP3
    have hlP : 3 * Real.log PT.PP ≤ large₂.sc.L := by
      have := Real.log_le_log (by positivity) hP3'
      rw [Real.log_pow, hb] at this
      exact_mod_cast this
    have h1 : H.CK ≤ PT.PP ^ 2 * D.R.f := by
      have : 0 ≤ PT.PP ^ 2 * D.R.f := by positivity
      linarith
    have h2 : H.CK * D.R.k ≤ PT.PP ^ 2 * D.R.f * D.R.r := mul_le_mul h1 hkr hk0 (by positivity)
    have h3 : H.CK * D.R.k * D.R.f * large₂.sc.b ≤ PT.PP ^ 2 * D.R.f * D.R.r * D.R.f * large₂.sc.b := by gcongr
    have h4 := Real.log_le_log (by positivity) (hs.trans (hsz.trans h3))
    rw [Real.log_mul (by positivity) hb0.ne', Real.log_mul (by positivity) hf0.ne',
      Real.log_mul (by positivity) hr0.ne', Real.log_mul (by positivity) hf0.ne', Real.log_pow, hb] at h4
    push_cast at h4
    linarith
  · have h1 : (ka.n : ℝ) ≤ (D.R.t : ℝ) ^ 2 := by
      rw [hn]; unfold Ranks.nV; push_cast; nlinarith
    have h2 : (0 : ℝ) < ka.n := by rw [hn]; unfold Ranks.nV; push_cast; linarith
    have h3 := Real.log_le_log h2 h1
    rw [Real.log_pow] at h3
    push_cast at h3
    linarith
  · have : (2 : ℝ) ^ 4 ≤ (D.R.m : ℝ) ^ 4 := pow_le_pow_left₀ (by norm_num) hm2 4
    have h : (16 : ℝ) ≤ D.R.f := by linarith
    exact_mod_cast h

end GlobalTheory
end

