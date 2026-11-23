module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0003
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0013
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0080
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0070
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0012
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0037
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0044
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsBlockProductMemIntegralHarmonic
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIntegralThetaCombinationNonzeroOnComponent
section
noncomputable section

namespace GlobalTheory.ThetaComb

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn ReciprocityTheory.ChartRestriction.G.Geo.Tor

private lemma card_filter_sum_eq_zero_mul_le_pow (N : ℕ) (v : Fin N → Fin N → ℂ) (hv : ∀ c, v c c ≠ 0) (c : Fin N) :
    (Finset.univ.filter (fun n : Fin N → Fin (N + 1) => ∑ i, ((n i : ℕ) : ℂ) * v i c = 0)).card * (N + 1)
      ≤ (N + 1) ^ N := by
  classical
  set S := Finset.univ.filter (fun n : Fin N → Fin (N + 1) => ∑ i, ((n i : ℕ) : ℂ) * v i c = 0) with hS
  have hinj : Set.InjOn (fun p : (Fin N → Fin (N + 1)) × Fin (N + 1) => Function.update p.1 c p.2)
      ((S ×ˢ (Finset.univ : Finset (Fin (N + 1))) : Finset _) : Set _) := by
    rintro ⟨n, k⟩ hn ⟨n', k'⟩ hn' heq
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, hS, Finset.mem_filter, Finset.mem_univ,
      true_and, and_true] at hn hn'
    simp only at heq
    have hk : k = k' := by simpa using congrFun heq c
    subst hk
    have hoff : ∀ i, i ≠ c → n i = n' i := by
      intro i hi
      simpa [Function.update_of_ne hi] using congrFun heq i
    have hrest : ∑ i ∈ Finset.univ.erase c, ((n i : ℕ) : ℂ) * v i c =
        ∑ i ∈ Finset.univ.erase c, ((n' i : ℕ) : ℂ) * v i c :=
      Finset.sum_congr rfl (fun i hi => by rw [hoff i (Finset.ne_of_mem_erase hi)])
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ c)] at hn hn'
    have hmul : ((n c : ℕ) : ℂ) * v c c = ((n' c : ℕ) : ℂ) * v c c := by
      linear_combination hn - hn' - hrest
    have hc : n c = n' c := Fin.ext (by exact_mod_cast mul_right_cancel₀ (hv c) hmul)
    refine Prod.ext ?_ rfl
    funext i
    by_cases hi : i = c
    · subst hi; exact hc
    · exact hoff i hi
  have hle := Finset.card_le_card_of_injOn _ (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) hinj
  simpa [Finset.card_product] using hle

theorem exists_box_comb_ne_zero (N : ℕ) (v : Fin N → Fin N → ℂ) (hv : ∀ c, v c c ≠ 0) :
    ∃ n : Fin N → ℕ, (∀ c, n c ≤ N) ∧ ∀ c, ∑ i, (n i : ℂ) * v i c ≠ 0 := by
  classical
  let bad : Fin N → Finset (Fin N → Fin (N + 1)) := fun c =>
    Finset.univ.filter (fun n => ∑ i, ((n i : ℕ) : ℂ) * v i c = 0)
  have hcount : ∑ c, (bad c).card < (N + 1) ^ N := by
    have h3 : (∑ c, (bad c).card) * (N + 1) ≤ N * (N + 1) ^ N := by
      rw [Finset.sum_mul]
      calc ∑ c, (bad c).card * (N + 1) ≤ ∑ _c : Fin N, (N + 1) ^ N :=
            Finset.sum_le_sum (fun c _ => card_filter_sum_eq_zero_mul_le_pow N v hv c)
        _ = N * (N + 1) ^ N := by simp
    by_contra hcon
    have h4 := Nat.mul_le_mul_right (N + 1) (not_lt.mp hcon)
    have hp : 0 < (N + 1) ^ N := pow_pos (Nat.succ_pos N) N
    nlinarith
  have hlt : (Finset.univ.biUnion bad).card < (Finset.univ : Finset (Fin N → Fin (N + 1))).card := by
    have hcard : (Finset.univ : Finset (Fin N → Fin (N + 1))).card = (N + 1) ^ N := by simp
    rw [hcard]
    exact lt_of_le_of_lt Finset.card_biUnion_le hcount
  obtain ⟨n, -, hn⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨fun i => (n i : ℕ), fun c => Nat.lt_succ_iff.mp (n c).isLt, fun c hc => hn ?_⟩
  exact Finset.mem_biUnion.2 ⟨c, Finset.mem_univ _, Finset.mem_filter.2 ⟨Finset.mem_univ _, hc⟩⟩

theorem exists_mem_Mlat_ne_zero {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j)
    (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (w : WeightFamilies.Wt D j) (hInt : ThInt X hinj EX w)
    (N : ℕ) (F : Fin N → B.Cusp j w) (hF : ∀ i, F i ∈ X.thAll w) (b : ℝ) (hb : 0 ≤ b)
    (hFi : ∀ σ i, Real.log (B.supN j w σ (F i)) ≤ b) (σ₀ : B.KO →+* ℂ) (ρ : Fin N → B.Cusp j w → ℂ)
    (hadd : ∀ c G G', ρ c (G + G') = ρ c G + ρ c G') (hsmul : ∀ c (a : B.KO) G, ρ c (a • G) = σ₀ a * ρ c G)
    (hne : ∀ c, ρ c (F c) ≠ 0) :
    ∃ th ∈ B.Mlat j w, (∀ c, ρ c th ≠ 0) ∧
      ∀ σ, Real.log (B.supN j w σ th) ≤ 2 * Real.log N + b + lamStar D * w.size := by
  classical
  obtain ⟨n, hnN, hn⟩ := exists_box_comb_ne_zero N (fun i c => ρ c (F i)) hne
  obtain ⟨hs0, hslog⟩ := sOf_ne_zero_and_log_bounds D B hinj EX j w
  set s : 𝓞 B.KO := sOf B hinj EX w with hs
  set G : B.Cusp j w := ∑ i, n i • F i with hG
  have hGmem : G ∈ X.thAll w := Submodule.sum_mem _ (fun i _ => nsmul_mem (hF i) _)
  have hsG : s • G = ((s : B.KO)) • G := (algebraMap_smul B.KO s G).symm
  have hWW : s • G ∈ X.WWc s w := by
    show s • G ∈ (X.thAll w).map (s • (LinearMap.id : B.Cusp j w →ₗ[𝓞 B.KO] B.Cusp j w))
    exact Submodule.mem_map.2 ⟨G, hGmem, by simp⟩
  have hρG : ∀ c, ρ c G = ∑ i, (n i : ℂ) * ρ c (F i) := by
    intro c
    let φ : B.Cusp j w →+ ℂ := AddMonoidHom.mk' (ρ c) (hadd c)
    have hφ : ∀ x, φ x = ρ c x := fun _ => rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hG, ← hφ, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_nsmul, hφ, nsmul_eq_mul]
  have hsne : ((s : B.KO)) ≠ 0 := fun h => hs0 (by exact_mod_cast h)
  refine ⟨s • G, hInt hWW, fun c => ?_, fun σ => ?_⟩
  · rw [hsG, hsmul, hρG]
    exact mul_ne_zero ((map_ne_zero σ₀).2 hsne) (hn c)
  · have hb1 := (GlobalTheory.LogSupMultiple.log_supN_bounds D B j w).2.1 σ N n F b hb hnN (fun i => hFi σ i)
    simp only [Nat.cast_smul_eq_nsmul] at hb1
    obtain ⟨hl0, -, -, hlup⟩ := hslog σ
    have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    have hbig := (GlobalTheory.LogSupMultiple.log_supN_bounds D B j w).1 σ (s : B.KO) G (lamStar D * w.size)
      (2 * Real.log N + b) (by linarith) hlup hb1 (by linarith) (by linarith)
    rw [hsG]
    linarith

theorem exists_integral_theta_nonzero_on_components : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → w.LastPos → WeightAlgebra.DF w + 2 ≤ qq D → ∀ (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D), ThInt (recPJ h j hj) hinj EX w → ∃ th ∈ (recB h.toLawsCore).Mlat j w, (recPJ h j hj).NonZeroComp w th ∧ ∀ σ, Real.log ((recB h.toLawsCore).supN j w σ th) ≤ 2 * Real.log (Fintype.card (T.U j T.σ₀).Comp) + (400 * Zb D large₂ + lamStar D) * w.size := by
  intro hC D T h hG large₂ j hj w hpage hL hrw hlast hDF hinj EX hInt
  classical
  have hLP : Formalism.L2.Pj.LastPos (T.Q.Dw j) (wtA w) := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.lastPos_wtA h hj w hlast
  have hα := GlobalTheory.RunIn.half_level_generator_norm D T h EX
  have hnb := _root_.GlobalTheory.NoBase.noBase hC D T h large₂ j hj w hpage hL hrw hLP hDF hα T.σ₀ T.good_σ₀
  choose x P f hP hcoef hrule x' hx' hne using hnb
  have hfth : ∀ k, f k ∈ T.th j w := fun k => ⟨x k, P k, hP k, hrule k⟩
  have hcut : ∀ k, f k ∈ T.C j w := fun k => h.thCusp j hj (wtA w) w.n (dom_wtA w) hLP (f k) (hfth k)
  have hr0 : 0 < D.R.r := by
    have := D.R.two_le_m
    have := D.R.m_add_three_le_k
    simp only [Formalism.BasicNotions.Ranks.r]
    omega
  have hn0 : 0 < w.n := by omega
  have hL0 : (0 : ℝ) ≤ large₂.sc.L := by linarith
  have hsupb : ∀ (σ : T.Q.c.F →+* ℂ) k, Real.log (T.Ns j w σ (f k)) ≤ 400 * Zb D large₂ * w.size := by
    intro σ k
    have hA : (0 : ℝ) ≤ absA w := by unfold absA; positivity
    have hℓ : (0 : ℝ) ≤ 140 * D.R.r * large₂.sc.L * absA w :=
      mul_nonneg (mul_nonneg (by positivity) hL0) hA
    have hl1 : l1At σ (P k) ≤ Real.exp (140 * D.R.r * large₂.sc.L * absA w) :=
      GlobalTheory.LogSupMultiple.le_exp_of_log_le (hcoef k σ) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    have h1 := _root_.GlobalTheory.RunIn.log_sup_theta_generator_le hC D T h hG large₂ j hj w hpage hL hrw hLP (x k) (P k) (hP k) (f k) (hrule k) σ _ hℓ hl1
    have h2 := (GlobalTheory.RunIn.sup_bounds_le_Gc D (recB h.toLawsCore) large₂ j w 0 hL hn0).1
    linarith
  have hb : (0 : ℝ) ≤ 400 * Zb D large₂ * w.size := by
    have hZ : (0 : ℝ) ≤ Zb D large₂ := by unfold Zb; exact mul_nonneg (by positivity) hL0
    exact mul_nonneg (mul_nonneg (by norm_num) hZ) (by linarith [w.one_le_size])
  have hcutR : ∀ k, f k ∈ cutR T.C j w := by
    intro k
    simp only [Formalism.L2.Pj.cutR]
    exact Submodule.mem_inf.2 ⟨hcut k, (Submodule.mem_iInf _).2 (fun hn => (hn hj).elim)⟩
  let e := Fintype.equivFin (T.U j T.σ₀).Comp
  let Fc : Fin (Fintype.card (T.U j T.σ₀).Comp) → (recB h.toLawsCore).Cusp j w :=
    fun i => ⟨f (e.symm i), hcutR (e.symm i)⟩
  have hmem : ∀ i, Fc i ∈ (recPJ h j hj).thAll w := by
    intro i
    change Fc i ∈ spanIn T.C j w (T.th j w)
    simp only [Formalism.L2.Pj.spanIn]
    exact Submodule.subset_span (hfth (e.symm i))
  have hsupF : ∀ σ i, Real.log ((recB h.toLawsCore).supN j w σ (Fc i)) ≤ 400 * Zb D large₂ * w.size := by
    intro σ i
    simp only [Formalism.L2.Pj.cutN, if_pos hj]
    exact hsupb σ (e.symm i)
  obtain ⟨th, hth, hρ, hsup⟩ := exists_mem_Mlat_ne_zero (recPJ h j hj) hinj EX w hInt _ Fc hmem
    (400 * Zb D large₂ * w.size) hb hsupF T.σ₀
    (fun c G => rdU (T.U j T.σ₀) (G : T.R j) (e.symm c) (x' (e.symm c)))
    (fun c G G' => by simp [map_add (f := _)])
    (fun c a G => by simp [map_smulₛₗ])
    (fun c => hne (e.symm c))
  refine ⟨th, hth, ?_, fun σ => (hsup σ).trans (le_of_eq (by ring))⟩
  refine ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.nonzero_divisor_of_connected D T h j hj w th T.σ₀ T.good_σ₀ (fun k => ⟨x' k, hx' k, ?_⟩)
  have key : ∀ k', e.symm (e k) = k' → rdU (T.U j T.σ₀) (th : T.R j) k' (x' k') ≠ 0 := by
    rintro k' rfl
    exact hρ (e k)
  exact key k (e.symm_apply_apply k)

end GlobalTheory.ThetaComb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsRunDataGeneratingScaledThetaLatticeWeight
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RunIn

theorem exists_tiedW_rec : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T), GamAt T.toCore → ∀ (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (Gc Prw : ℝ), FamilyHypotheses.HypPage large₂ (recPJ h j hj) H C2 A2 CR CT ka wL wF Tn nP nW h0 → ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ ka → ThInt (recPJ h j hj) hinj EX wL → EtaleWeightGaps.GrowthConstantBound large₂ (recB h.toLawsCore) Gc → 38 * large₂.sc.L + PO D large₂ ≤ Prw → ∃ G : EtaleWeightGaps.GlobalFamilyData (recPJ h j hj) ka wL wF, G.TiedW (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) Gc Prw := by
  intro hC D T h hG hinj EX p j hj large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 Gc Prw hP hR hI hG4 hPrw
  obtain ⟨hL, hf, hr, hlam, -, -⟩ := GlobalTheory.page_two_le_L_and_signs D _ _ j _ large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hP hR
  obtain ⟨hDF, hn, hrn, hLP⟩ :=
    (GlobalTheory.RunWeights.weights_below D _ _ j _ large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hj.1 hP).1 wL (by simp)
  have hL0 : 0 ≤ large₂.sc.L := by linarith
  have hRL := GlobalTheory.pageRows_of_le D large₂ j ka wL hL0 hDF hn hR
  have hn0 : 0 < wL.n := by omega
  have hO : OPO large₂ (recB h.toLawsCore) := by
    obtain ⟨-, ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hO, -⟩, -⟩ := hP
    exact hO
  obtain ⟨N, w0, hspan, hN, hsup⟩ := _root_.GlobalTheory.ThetaFamily.theta_family hC D T h hG large₂ j hj wL hRL hL hrn hLP
  have hcount := log_count_le_mul_size D _ large₂ j wL N Prw hL hn0 hRL hO hPrw hN
  have hs : (0 : ℝ) ≤ wL.size := by
    have h1 := frn_le_size_sub_one wL
    have h2 : (0 : ℝ) ≤ (D.R.f : ℝ) * D.R.r * wL.n := by positivity
    push_cast at h1
    linarith
  have hp : 0 ≤ Real.log (D.host.pde : ℝ) := Real.log_natCast_nonneg _
  have hZ : 0 ≤ Zb D large₂ := by unfold Zb; positivity
  have hnum := (_root_.GlobalTheory.RunIn.sup_bounds_le_Gc D (recB h.toLawsCore) large₂ j wL D.host.pde hL hn0).2.2
  have hGc := mul_le_mul_of_nonneg_right (hG4 D.host.pde (by simp)) hs
  have hd : 0 ≤ Real.log |((NumberField.discr (recB h.toLawsCore).KO : ℤ) : ℝ)| := by
    rw [Real.log_abs]; exact Real.log_intCast_nonneg _
  have hK : 0 ≤ Real.log (Module.finrank ℚ (recB h.toLawsCore).KO : ℝ) := Real.log_natCast_nonneg _
  refine (GlobalTheory.ScaledGenerators.scaled_family D _ _ j (recPJ h j hj) ka wL wF (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) N w0
    ((lamStar D + 2 * Real.log D.host.pde) * wL.size) _ Gc Prw (by positivity) (by positivity) (fun σ => ?_)
    hspan hsup (hnum.trans hGc)).2 hI hcount
  rw [sW_eq_sOf]
  refine ((GlobalTheory.RunIn.sOf_ne_zero_and_log_bounds D _ hinj EX j wL).2 σ).2.2.2.trans ?_
  exact mul_le_mul_of_nonneg_right (by linarith) hs

end GlobalTheory.RunIn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsShortThetaFamilyWithBlockPolynomialRules
section
noncomputable section

namespace GlobalTheory.BlockTh

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn GlobalTheory.BlockTh GlobalTheory.EtaAn ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem span_sum_elim {R M ι κ : Type} [CommRing R] [AddCommGroup M] [Module R M] (S : Submodule R M) (u : ι → M)
    (v : κ → M) (hu : Submodule.span R (Set.range u) = S) (hv : ∀ k, v k ∈ S) :
    Submodule.span R (Set.range (Sum.elim u v)) = S := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i | k, rfl⟩
    · rw [← hu]
      exact Submodule.subset_span ⟨i, rfl⟩
    · exact hv k
  · rw [← hu]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨Sum.inl i, rfl⟩

private theorem span_range_sum_elim_eq_thAll {D : D7} {Pr : ModuliIntegralCharts.Prov D} {j : ℕ} (B : WeightFamilies.Prov D) (X : PJ D B Pr j)
    (w : WeightFamilies.Wt D j) {N M' : ℕ} {ι : Type} (w0 : Fin N → B.Cusp j w) (v : ι → B.Cusp j w) (e : Fin M' ≃ Fin N ⊕ ι)
    (h0 : Submodule.span (𝓞 B.KO) (Set.range w0) = X.thAll w) (hv : ∀ q, v q ∈ X.thAll w) :
    Submodule.span (𝓞 B.KO) (Set.range (fun k => Sum.elim w0 v (e k))) = X.thAll w := by
  rw [show Set.range (fun k => Sum.elim w0 v (e k)) = Set.range (Sum.elim w0 v) from
    EquivLike.range_comp (Sum.elim w0 v) e]
  exact span_sum_elim _ w0 v h0 hv

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in
theorem theta_family_block : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → w.LastPos → D.R.f * D.R.r * (D.R.r + 1) ≤ 2 * w.n → ∃ (N : ℕ) (w0 : Fin N → (recB h.toLawsCore).Cusp j w) (P₁ : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F), P₁ ∈ harmA T.Q.c (wtA w) w.n ∧ IsBlockProd P₁ ∧ ContainsTh (T.Q.Xo j) T.Q.c (T.nab j) 1 P₁ (fun k => ((w0 k).1 : T.R j)) ∧ (fun (B : WeightFamilies.Prov D) (X : PJ D B T.G.P j) (w1 : Fin N → B.Cusp j w) => Submodule.span (𝓞 B.KO) (Set.range w1) = X.thAll w) (recB h.toLawsCore) (recPJ h j hj) w0 ∧ N ≤ 2 * ((D.host.g 0 * D.host.g 1) ^ (D.R.f * D.R.r * w.n) * (Module.finrank ℚ (recB h.toLawsCore).KO * (1 + WeightAlgebra.DF w) ^ (D.R.f * D.R.r * w.n))) ∧ ∀ k σ, Real.log ((recB h.toLawsCore).supN j w σ (w0 k)) ≤ 400 * Zb D large₂ * w.size + 3 * D.R.f * D.R.r * w.n * large₂.sc.L + 5 * Real.log (Module.finrank ℚ (recB h.toLawsCore).KO) + Real.log |((NumberField.discr (recB h.toLawsCore).KO : ℤ) : ℝ)| / Module.finrank ℚ (recB h.toLawsCore).KO + 2 := by
  intro hC D T h hG large₂ j hj w hP hL hr hlast hn
  obtain ⟨N0, w0, hspan, hN0, hsup0⟩ := _root_.GlobalTheory.ThetaFamily.theta_family hC D T h hG large₂ j hj w hP hL hr hlast
  obtain ⟨-, ⟨hM, -⟩, -, hdat⟩ := h.toLawsCore.pins
  obtain ⟨hp, hq, -⟩ := hdat j hj
  have hpq : (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r := by
    rw [hp, hq]
    exact Formalism.L2.Geo.sigW_sum D hj.1 hj.2
  have hfE : I2.PT.f D.host.E = D.R.f := by
    dsimp only [I2.PT.f]
    rw [Formalism.MainNotions.StandardLattice.finrank_host D]
    omega
  have he : ∀ {m : ℕ} (g : Fin m → ℕ), Antitone g → ∀ i k : ℕ, i ≤ k → ext0 g k ≤ ext0 g i := by
    intro m g hg i k hik
    dsimp only [ext0]
    by_cases h1 : k < m <;> by_cases h2 : i < m
    · rw [dite_eq_left h1, dite_eq_left h2]
      exact hg (Fin.mk_le_mk.2 hik)
    · exact absurd (lt_of_le_of_lt hik h1) h2
    · rw [dite_eq_right h1]
      exact Nat.zero_le _
    · rw [dite_eq_right h1, dite_eq_right h2]
  have hanti : ∀ τ i k, i ≤ k → wtA w (τ, k) ≤ wtA w (τ, i) := by
    intro τ i k hik
    dsimp only [wtA]
    apply Finset.sum_le_sum
    intro t _
    apply add_le_add
    · split_ifs
      · exact he _ (w.aPlus_antitone t) i k hik
      · exact le_rfl
    · split_ifs
      · exact he _ (w.aM_anti t) i k hik
      · exact le_rfl
  obtain ⟨P, hPh, hPb, hPdeg, hPl1⟩ := _root_.GlobalTheory.BlockProdEx.exists_blockProd_mem_harmA D.host.E T.Q.H (T.Q.Dw j) T.Q.l T.Q.c (wtA w) w.n hanti
    (by rw [hfE, hpq]; exact hn)
  have hdom : Dom (wtA w) w.n := dom_wtA w
  have hlp : LastPos (T.Q.Dw j) (wtA w) := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.lastPos_wtA h hj w hlast
  obtain ⟨_, hnab⟩ := h.nabPin j hj
  have hex : ∀ q : Fin w.n → LevQ (T.Q.Dw j) T.Q.l, ∃ f : T.R j,
      IsThRule (T.Q.Xo j) T.Q.c (T.nab j) (fun b => levRep (q b)) P f :=
    fun q => by
      obtain ⟨⟨f, hf, -⟩, -⟩ := GlobalTheory.thetaRule_exists_and_eval hC D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c
        (T.nab j) hnab (wtA w) w.n (fun b => levRep (q b)) P hPh
      exact ⟨f, hf⟩
  choose f hf using hex
  have hfC : ∀ q, f q ∈ cutR T.C j w := by
    intro q
    have h1 : f q ∈ T.C j w := h.thCusp j hj (wtA w) w.n hdom hlp (f q) ⟨fun b => levRep (q b), P, hPh, hf q⟩
    dsimp only [cutR]
    exact Submodule.mem_inf.2 ⟨h1, (Submodule.mem_iInf _).2 fun hn' => absurd hj hn'⟩
  let v : (Fin w.n → LevQ (T.Q.Dw j) T.Q.l) → (recB h.toLawsCore).Cusp j w := fun q =>
    (⟨f q, hfC q⟩ : cutR T.C j w)
  have hv1 : ∀ q, ((v q : cutR T.C j w) : T.R j) = f q := fun q => rfl
  obtain ⟨hfin, hcard⟩ := _root_.GlobalTheory.card_levQ D.host.E T.Q.H (T.Q.Dw j) T.Q.l
  let _ : Fintype (LevQ (T.Q.Dw j) T.Q.l) := Fintype.ofFinite _
  let e : Fin (N0 + Fintype.card (Fin w.n → LevQ (T.Q.Dw j) T.Q.l)) ≃ Fin N0 ⊕ (Fin w.n → LevQ (T.Q.Dw j) T.Q.l) :=
    finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl _) (Fintype.equivFin _).symm)
  let W : Fin (N0 + Fintype.card (Fin w.n → LevQ (T.Q.Dw j) T.Q.l)) → (recB h.toLawsCore).Cusp j w :=
    fun k => Sum.elim w0 v (e k)
  have hWq : ∀ q, W (e.symm (Sum.inr q)) = v q := by
    intro q
    simp only [W, Equiv.apply_symm_apply, Sum.elim_inr]
  refine ⟨_, W, P, hPh, hPb, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun q => e.symm (Sum.inr q), fun a b hab => Sum.inr_injective (e.symm.injective hab), fun q => ⟨f q, hf q, fun p y => ?_⟩⟩
    show (W (e.symm (Sum.inr q))).1 p y = _
    rw [hWq q, map_one, one_mul]
  · refine span_range_sum_elim_eq_thAll (recB h.toLawsCore) (recPJ h j hj) w w0 v e hspan fun q => ?_
    dsimp only [recPJ, mkX, spanIn]
    simp only [Submodule.mem_comap]
    exact Submodule.subset_span (show f q ∈ T.th j w from ⟨fun b => levRep (q b), P, hPh, hf q⟩)
  · have hfd : FD.fdeg D.host.E = D.R.f := by
      dsimp only [FD.fdeg]
      rw [Formalism.MainNotions.StandardLattice.finrank_host D]
      omega
    have hc : Fintype.card (Fin w.n → LevQ (T.Q.Dw j) T.Q.l) =
        (D.host.g 0 * D.host.g 1) ^ (D.R.f * D.R.r * w.n) := by
      rw [Fintype.card_fun, Fintype.card_fin, ← Nat.card_eq_fintype_card, hcard, hM, hpq, hfd, ← pow_mul]
    have hB1 : 0 < Module.finrank ℚ (recB h.toLawsCore).KO * (1 + WeightAlgebra.DF w) ^ (D.R.f * D.R.r * w.n) :=
      Nat.mul_pos Module.finrank_pos (pow_pos (by omega) _)
    have hGX := Nat.le_mul_of_pos_right ((D.host.g 0 * D.host.g 1) ^ (D.R.f * D.R.r * w.n)) hB1
    rw [hc]
    linarith
  · intro k σ
    obtain ⟨x, rfl⟩ : ∃ x, e.symm x = k := ⟨e k, e.symm_apply_apply k⟩
    rcases x with i | q
    · have h0 : W (e.symm (Sum.inl i)) = w0 i := by
        simp only [W, Equiv.apply_symm_apply, Sum.elim_inl]
      rw [h0]
      exact hsup0 i σ
    · rw [hWq q]
      have hs : (recB h.toLawsCore).supN j w σ (v q) = T.Ns j w σ (f q) := by
        change cutN T.C T.Ns j w σ (v q) = _
        dsimp only [cutN]
        rw [if_pos hj]
      rw [hs]
      have h2 : ((Formalism.MainNotions.WeightAlgebra.DF w : ℕ) : ℝ) = Formalism.MainNotions.WeightAlgebra.absA w := by
        dsimp only [Formalism.MainNotions.WeightAlgebra.DF, Formalism.MainNotions.WeightAlgebra.degP, Formalism.MainNotions.WeightAlgebra.absA]
        push_cast
        rfl
      have hDF : (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) : ℝ) ≤ Formalism.MainNotions.WeightAlgebra.absA w := by
        rw [← h2]
        exact_mod_cast ReciprocityTheory.ChartRestriction.G.PullbackSections.DF_wtA_le T j w
      have hA0 : 0 ≤ Formalism.MainNotions.WeightAlgebra.absA w := by
        rw [← h2]
        positivity
      rw [hpq] at hPl1
      have hℓ0 : 0 ≤ Real.log (max 1 ((D.R.r : ℝ) ^ Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w))) :=
        Real.log_nonneg (le_max_left _ _)
      have hℓexp : l1At σ P ≤ Real.exp (Real.log (max 1 ((D.R.r : ℝ) ^ Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w)))) := by
        rw [Real.exp_log (lt_of_lt_of_le one_pos (le_max_left _ _))]
        dsimp only [l1At]
        exact le_trans (hPl1 σ) (le_max_right _ _)
      have hℓle : Real.log (max 1 ((D.R.r : ℝ) ^ Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w))) ≤
          (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) : ℝ) * D.R.r := by
        rcases Nat.eq_zero_or_pos D.R.r with h0 | h0
        · rw [h0, Nat.cast_zero, mul_zero, max_eq_left (pow_le_one₀ le_rfl zero_le_one), Real.log_one]
        · have h1 : (1 : ℝ) ≤ (D.R.r : ℝ) ^ Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) := one_le_pow₀ (by exact_mod_cast h0)
          rw [max_eq_right h1, Real.log_pow]
          exact mul_le_mul_of_nonneg_left (Real.log_le_self (by positivity)) (by positivity)
      have hNs := _root_.GlobalTheory.RunIn.log_sup_theta_generator_le hC D T h hG large₂ j hj w hP hL hr hlp (fun b => levRep (q b)) P hPh (f q) (hf q) σ _ hℓ0 hℓexp
      have hL0 : (0 : ℝ) ≤ large₂.sc.L := by linarith
      have hr0 : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _
      have t1 : 0 ≤ 3 * (D.R.f : ℝ) * D.R.r * w.n * large₂.sc.L := mul_nonneg (by positivity) hL0
      have t2 : 0 ≤ 5 * Real.log (Module.finrank ℚ (recB h.toLawsCore).KO : ℝ) :=
        mul_nonneg (by norm_num) (Real.log_nonneg (Nat.one_le_cast.2 Module.finrank_pos))
      have t3 : 0 ≤ Real.log |((NumberField.discr (recB h.toLawsCore).KO : ℤ) : ℝ)| /
          (Module.finrank ℚ (recB h.toLawsCore).KO : ℝ) := by
        apply div_nonneg _ (Nat.cast_nonneg _)
        apply Real.log_nonneg
        rw [← Int.cast_abs]
        exact_mod_cast Int.one_le_abs (NumberField.discr_ne_zero _)
      rcases Nat.eq_zero_or_pos w.n with hn0 | hwn
      · have hr0' : D.R.r = 0 := by omega
        have hs1 : (D.R.sigW j).1 = 0 := by omega
        have hs2 : (D.R.sigW j).2 = 0 := by omega
        have hA : Formalism.MainNotions.WeightAlgebra.absA w = 0 := by
          have : IsEmpty (Fin (D.R.sigW j).1) := by rw [hs1]; infer_instance
          have : IsEmpty (Fin (D.R.sigW j).2) := by rw [hs2]; infer_instance
          simp [Formalism.MainNotions.WeightAlgebra.absA]
        have hZ0 : Zb D large₂ = 0 := by simp [Zb, hr0']
        have hrc : (D.R.r : ℝ) = 0 := by exact_mod_cast hr0'
        rw [hA, hrc] at hNs
        rw [hrc] at hℓle
        rw [hZ0]
        nlinarith
      · have h9430 := (_root_.GlobalTheory.RunIn.sup_bounds_le_Gc D (recB h.toLawsCore) large₂ j w 0 hL hwn).1
        have hk1 : (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) : ℝ) * D.R.r ≤ 140 * D.R.r * large₂.sc.L * Formalism.MainNotions.WeightAlgebra.absA w := by
          have : (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) : ℝ) * D.R.r ≤ Formalism.MainNotions.WeightAlgebra.absA w * D.R.r :=
            mul_le_mul_of_nonneg_right hDF hr0
          nlinarith [mul_nonneg hA0 hr0]
        linarith

end GlobalTheory.BlockTh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogSupNormShortThetaGeneratorLeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_supNorm_shortThetaGenerator_le : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (_h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → LastPos (T.Q.Dw j) (wtA w) → LawsSh T → (T.dδ j w.n).l₂.A = 1 → ∀ (Λ : GenLat D.host.E w.n) (N : ℕ) (x0 : Fin w.n → (T.Q.Dw j).La) (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F) (g : T.R j), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ j w.n).l₂.M → Λ.LevOK N (T.dδ j w.n).l₂.M → AdmX (l := T.Q.l) (decide (w.n = D.R.nV)) x0 → P ∈ harmL T.Q.c Λ (wtA w) → IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j w.n) Λ N x0 P g → g ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n → ∀ (σ : T.Q.c.F →+* ℂ) (ℓ : ℝ), 0 ≤ ℓ → l1At σ P ≤ Real.exp ℓ → Real.log (T.Ns j w σ g) ≤ ℓ + 10 * large₂.sc.L * absA w + 200 * D.R.f * D.R.r * w.n * large₂.sc.L := by
  first | exact @GlobalTheory.RunIn.log_sup_short_generator_le | exact GlobalTheory.RunIn.log_sup_short_generator_le | (intros; apply GlobalTheory.RunIn.log_sup_short_generator_le <;> assumption)
end

