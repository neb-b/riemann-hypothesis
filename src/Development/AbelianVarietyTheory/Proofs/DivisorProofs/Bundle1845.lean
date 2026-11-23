module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0509
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CuspStatementPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.DivCoreUpPf
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0838
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1805
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0864
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0861
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1832
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0847
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1831
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1159
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1246
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCountableCharts
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open Filter Topology

noncomputable section

namespace GlobalTheory.CountableCharts

theorem isHolTo_finChart_symm {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    (c : GlobalTheory.AlgChart p σ D) : IsHolTo c.finChart.target fun z => (c.finChart.symm z).1 := by
  have h1 := GlobalTheory.LocLift.isHolTo_comp (GlobalTheory.TrueCx.TorHolo.isHolTo_symm c) c.finChart.open_target
    (β := fun z => (EuclideanSpace.equiv (Fin D) ℂ).symm z)
    (EuclideanSpace.equiv (Fin D) ℂ).symm.differentiable.differentiableOn fun z hz => hz
  refine GlobalTheory.LocLift.isHolTo_congr h1 fun v _ => ?_
  simp [GlobalTheory.AlgChart.finChart_symm_apply]

theorem exists_countable_charts : ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (d : ℕ), SmoothOfRelativeDimension d s → QuasiCompact s → ∀ (Q : Set (Fin d → ℂ) → ((Fin d → ℂ) → (Sp ℂ ⟶ X)) → Prop), (∀ B y b₀, IsOpen B → b₀ ∈ B → (∀ b ∈ B, y b ≫ s = spMap (RingHom.id ℂ)) → IsHolTo B y → ∃ B', IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ Q B' y) → ∃ (K : Type) (_ : Countable K) (B : K → Set (Fin d → ℂ)) (y : K → (Fin d → ℂ) → (Sp ℂ ⟶ X)), (∀ i, IsOpen (B i) ∧ (∀ b ∈ B i, y i b ≫ s = spMap (RingHom.id ℂ)) ∧ IsHolTo (B i) (y i) ∧ Set.InjOn (y i) (B i) ∧ Q (B i) (y i)) ∧ ∀ x : Sp ℂ ⟶ X, x ≫ s = spMap (RingHom.id ℂ) → ∃ i, x ∈ y i '' B i := by
  intro X s d hs hq Q hQ
  haveI := hs
  haveI := hq
  haveI : Smooth s := SmoothOfRelativeDimension.smooth d s
  have hc : ∀ x : GlobalTheory.CxPts s (RingHom.id ℂ), ∃ c : GlobalTheory.AlgChart s (RingHom.id ℂ) d, x ∈ c.e.source :=
    fun x => GlobalTheory.AlgChart.exists_mem_source x
  choose c hc using hc
  have hB : ∀ x : GlobalTheory.CxPts s (RingHom.id ℂ), ∃ B', IsOpen B' ∧ (c x).finChart x ∈ B' ∧
      B' ⊆ (c x).finChart.target ∧ Q B' (fun z => ((c x).finChart.symm z).1) := fun x =>
    hQ _ _ _ (c x).finChart.open_target ((c x).finChart.map_source (hc x))
      (fun b _ => ((c x).finChart.symm b).2) (isHolTo_finChart_symm (c x))
  choose B' hB'o hB'm hB'sub hB'Q using hB
  have hN : ∀ x : GlobalTheory.CxPts s (RingHom.id ℂ),
      (c x).finChart.source ∩ (c x).finChart ⁻¹' B' x ∈ 𝓝 x := fun x =>
    ((c x).finChart.isOpen_inter_preimage (hB'o x)).mem_nhds ⟨hc x, hB'm x⟩
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.countable_cover_nhds hN
  refine ⟨T, hTc.to_subtype, fun i => B' i, fun i z => ((c i).finChart.symm z).1, fun i =>
    ⟨hB'o i, fun b _ => ((c i).finChart.symm b).2,
      GlobalTheory.LocLift.isHolTo_mono (isHolTo_finChart_symm (c i)) (hB'o i) (hB'sub i), ?_, hB'Q i⟩, ?_⟩
  · intro a ha b hb hab
    exact (c i).finChart.symm.injOn (by simpa using hB'sub i ha) (by simpa using hB'sub i hb)
      (Subtype.ext hab)
  · intro x hx
    have hmem : (⟨x, hx⟩ : GlobalTheory.CxPts s (RingHom.id ℂ)) ∈ ⋃ t ∈ T,
        (c t).finChart.source ∩ (c t).finChart ⁻¹' B' t := hTU ▸ Set.mem_univ _
    obtain ⟨t, ht, hm⟩ := Set.mem_iUnion₂.1 hmem
    exact ⟨⟨t, ht⟩, (c t).finChart ⟨x, hx⟩, hm.2, by
      show ((c t).finChart.symm ((c t).finChart ⟨x, hx⟩)).1 = x
      rw [(c t).finChart.left_inv hm.1]⟩

end GlobalTheory.CountableCharts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspNe
section
open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.ScalarPoin
open ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst MeasureTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem qS_base (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) (k : ℕ) : qS X x0 k x0 = 1 := by
  unfold qS
  refine Finset.prod_eq_one fun τ _ => ?_
  have hu : IsUnit (mat x0 τ).det := isUnit_iff_ne_zero.mpr (ExF.det_ne_of_orth X ho τ)
  rw [KU.Mx, Matrix.nonsing_inv_mul _ hu, KU.tl_one]
  have h1 : (1 : Matrix (Fin (r - X.p0) ⊕ Fin X.p0) (Fin (r - X.p0) ⊕ Fin X.p0) ℂ).toBlocks₂₂ = 1 := by
    ext i j; simp [Matrix.toBlocks₂₂, Matrix.one_apply]
  rw [h1]
  simp

end GlobalTheory.ScalarPoin

open ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst MeasureTheory GlobalTheory.ScalarPoin in
theorem GlobalTheory.ScalarPoin.exists_cusp_ne : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), 0 < X.p0 → X.p0 < r → (∀ n : ℕ, Even n → ∀ γ ∈ X.Γ, X.χ (fun (τ : X.Ψ) (j : Fin r) => if X.p0 ≤ (j : ℕ) then ((n / 2 : ℕ) : ℤ) else -((n / 2 : ℕ) : ℤ)) γ = 1) → ∀ y ∈ X.dom, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ 0 < n ∧ Even n ∧ ∃ P ∈ X.SS (fun (τ : X.Ψ) (j : Fin r) => if X.p0 ≤ (j : ℕ) then ((n / 2 : ℕ) : ℤ) else -((n / 2 : ℕ) : ℤ)), P y ≠ 0 := by
  intro E _ _ _ r X hp0 hpr hχ y hy N
  obtain ⟨x0, ho, b, hb, rfl⟩ := ortho_holds r X y hy
  have hPD := GlobalTheory.ClosedDiscontinuity.propDisc_closed r X
  have hx0 : x0 ∈ X.dom := KU.orth_dom X ho
  set bb : ℝ := 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1 with hbbdef
  have hbb : 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb := by linarith
  obtain ⟨s0, hs0⟩ := _root_.GlobalTheory.ScalarPoin.lintegral_kaF_lt_top E r X x0 ho
  obtain ⟨k0, hk0⟩ := exists_nat_ge ((s0 + bb) / 2)
  have hla : ∀ k : ℕ, (fun (τ : X.Ψ) (j : Fin r) => if X.p0 ≤ (j : ℕ) then (((2 * k) / 2 : ℕ) : ℤ)
      else -(((2 * k) / 2 : ℕ) : ℤ)) = laS X k := by
    intro k; funext τ j; simp [laS]
  have hχk : ∀ k : ℕ, ∀ γ ∈ X.Γ, X.χ (laS X k) γ = 1 := by
    intro k γ hγ
    have := hχ (2 * k) (even_two_mul k) γ hγ
    rwa [hla k] at this
  have hIn : ∀ k : ℕ, k0 ≤ k →
      InAt X x0 (fun x => ENNReal.ofReal (Real.exp (-phla X (laS X k) x))) bb (fun _ => (1 : ℂ)) := by
    intro k hk
    have hs : s0 ≤ 2 * (k : ℝ) - bb := by
      have : ((s0 + bb) / 2 : ℝ) ≤ k := le_trans hk0 (by exact_mod_cast hk)
      linarith
    unfold InAt
    refine lt_of_le_of_lt (le_of_eq ?_) (hs0 _ hs)
    refine lintegral_congr_ae ?_
    filter_upwards [ExtFPf.ae_OmF (X := X) (x0 := x0)] with z hz
    rw [_root_.GlobalTheory.ScalarPoin.phla_laS_cpt E r X x0 ho k z hz]
    simp only [norm_one, one_pow, kaF]
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [one_div, ← Real.exp_neg, ← Real.exp_add]
    congr 1; ring
  have hpo := fun k (hk : k0 ≤ k) => poin_holds r X x0 ho hPD (laS X k) _ bb (DivUpPf.metricW_exp X _)
    (DivUpPf.wLower_exp X _) hbb (fun _ => (1 : ℂ)) (qS X x0 k) (differentiableOn_const _) (hIn k hk)
    ⟨_root_.GlobalTheory.ScalarPoin.Holo.qS_holomorphicOn E r X x0 ho k, fun x _ b hb => _root_.GlobalTheory.ScalarPoin.qS_rmul E r X x0 k x b hb⟩ (fun z _ => qS_cpt X ho k z)
  set a : X.Γ → ℂ := fun γ => qS X x0 1 (lact γ.1 x0) with ha
  have ha1 : a 1 = 1 := by
    simp only [ha, OneMemClass.coe_one, KU.lact_one]
    exact qS_base X ho 1
  have hterm : ∀ k (γ : X.Γ), (X.χ (laS X k) γ.1)⁻¹ * qS X x0 k (lact γ.1 x0) = a γ ^ k := by
    intro k γ
    rw [hχk k γ.1 γ.2, inv_one, one_mul, qS_pow]
  have hsum : Summable fun γ : X.Γ => ‖a γ‖ ^ k0 := by
    have h := (hpo k0 le_rfl).1 x0 hx0
    simp_rw [hterm k0, norm_pow] at h
    exact h
  have hle : ∀ γ : X.Γ, ‖a γ‖ ≤ 1 := fun γ => (_root_.GlobalTheory.ScalarPoin.norm_qS_lact_le E r X x0 ho γ.1 γ.2).1
  have hlt : ∀ γ : X.Γ, γ ≠ 1 → ‖a γ‖ < 1 := by
    intro γ hne
    refine lt_of_le_of_ne (hle γ) fun heq => hne (Subtype.ext ?_)
    exact _root_.GlobalTheory.ScalarPoin.BlockFree.eq_one_of_gm_toBlocks₁₂ E r X x0 ho γ.1 γ.2 ((_root_.GlobalTheory.ScalarPoin.norm_qS_lact_le E r X x0 ho γ.1 γ.2).2 heq)
  obtain ⟨k, hk, hne⟩ := _root_.GlobalTheory.tsum_pow_eventually_ne_zero a 1 k0 ha1 hle hlt hsum (max N (k0 + 1))
  have hk0k : k0 ≤ k := le_trans (by omega) hk
  have hkpos : 0 < k := lt_of_lt_of_le (by omega) hk
  obtain ⟨τ0⟩ : Nonempty X.Ψ := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    by_cases hτ : τ ∈ X.Ψ
    · exact ⟨⟨τ, hτ⟩⟩
    · exact ⟨⟨_, not_not.mp ((X.cmType τ).not.mp hτ)⟩⟩
  have hB := (hpo k hk0k).2.1
  refine ⟨2 * k, le_trans (le_max_left _ _) (le_trans hk (by omega)), by omega, even_two_mul k, ?_⟩
  rw [hla k]
  refine ⟨poin X (laS X k) (qS X x0 k), ?_, ?_⟩
  · refine cuspStatement_holds r X (laS X k) τ0 hp0 hpr (fun i j hij hjp => ?_) (fun i0 i1 h0 h1 => ?_) _ hB
    · simp only [laS]
      split_ifs with h1 h2 <;> omega
    · simp only [laS]
      rw [if_neg (by omega), if_pos (by omega)]
      omega
  · rw [hB.1.2.1 x0 hx0 b hb]
    refine mul_ne_zero ?_ ?_
    · unfold bchar
      exact Finset.prod_ne_zero_iff.mpr fun τ _ => Finset.prod_ne_zero_iff.mpr fun i _ =>
        zpow_ne_zero _ (FrameDegreeData.bdiag_ne X hb τ i)
    · unfold poin
      simp_rw [hterm k]
      exact hne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameTangentVectorsOfIsGrpPullback
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSExist.FrameLift

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {K : Type} [CommRing K] {x : Sp K ⟶ Xo.X} {A : Over (Sp K)} [GrpObj A]
  {π : A.left ⟶ Xo.univ.t.G.left}

theorem one_comp (hπ : IsGrpPullback A Xo.univ.t.G x π) :
    η[A].left ≫ π = (1 : Over.mk x ⟶ Xo.univ.t.G).left := by
  have e := congrArg (fun z => z.left) (map_one (pushHom hπ (𝟙_ (Over (Sp K)))))
  have e₁ : (1 : 𝟙_ (Over (Sp K)) ⟶ A) = η[A] := by rw [Hom.one_def]; simp
  rw [e₁] at e
  refine e.trans ?_
  rw [GlobalTheory.ArcQ.NormalForm.one_left_eq, GlobalTheory.ArcQ.NormalForm.one_left_eq]
  simp

theorem exists_lift (hπ : IsGrpPullback A Xo.univ.t.G x π) {T : Over (Sp K)} (v : T.left ⟶ Xo.univ.t.G.left)
    (hv : v ≫ Xo.univ.t.G.hom = T.hom ≫ x) : ∃ w : T ⟶ A, w.left ≫ π = v :=
  ⟨Over.homMk (hπ.1.lift v T.hom hv) (hπ.1.lift_snd _ _ _), hπ.1.lift_fst _ _ _⟩

theorem tan_iff (hπ : IsGrpPullback A Xo.univ.t.G x π) (w : epsR K ⟶ A) : IsTanAt x (w.left ≫ π) ↔ IsTangent w := by
  have hw : w.left ≫ A.hom = spMap (algebraMap K (DualNumber K)) := Over.w w
  constructor
  · intro h
    apply hπ.1.hom_ext
    · rw [Category.assoc]; exact h.2.trans (one_comp hπ).symm
    · have a : η[A].left ≫ A.hom = 𝟙 _ := Over.w η[A]
      rw [Category.assoc, hw, a, ← Geo.Tor.spMap_comp]
      have : (TrivSqZeroExt.fstHom K K K).toRingHom.comp (algebraMap K (DualNumber K)) = RingHom.id K := by
        ext r; simp [TrivSqZeroExt.algebraMap_eq_inl]
      rw [this]
      exact Spec.map_id _
  · intro h
    refine ⟨by rw [Category.assoc, hπ.1.w, ← Category.assoc, hw], ?_⟩
    rw [← Category.assoc]
    exact (congrArg (· ≫ π) h).trans (one_comp hπ)

theorem eig_iff (hπ : IsGrpPullback A Xo.univ.t.G x π) {f : A ⟶ A} {g : Xo.univ.t.G ⟶ Xo.univ.t.G}
    (hf : f.left ≫ π = π ≫ g.left) (w : epsR K ⟶ A) (s : K) :
    (w.left ≫ π) ≫ g.left = spMap (epsMul s) ≫ w.left ≫ π ↔
      w ≫ f = GlobalTheory.GrpTangent.epsScale s ≫ w := by
  have hw : w.left ≫ A.hom = spMap (algebraMap K (DualNumber K)) := Over.w w
  have e : (w.left ≫ π) ≫ g.left = (w ≫ f).left ≫ π := by
    rw [Over.comp_left, Category.assoc, Category.assoc, hf]
  rw [e]
  constructor
  · intro h
    apply Over.OverMorphism.ext
    apply hπ.1.hom_ext
    · simp only [Over.comp_left, GlobalTheory.GrpTangent.epsScale_left, Category.assoc] at h ⊢
      exact h
    · rw [Over.w, Over.w]
  · intro h
    rw [h, Over.comp_left, GlobalTheory.GrpTangent.epsScale_left, Category.assoc]
    rfl

theorem push_prod (hπ : IsGrpPullback A Xo.univ.t.G x π) {n : ℕ} (u : Fin n → (epsR K ⟶ A)) :
    ((List.ofFn u).prod).left ≫ π = ((List.ofFn fun i => pushHom hπ (epsR K) (u i)).prod).left := by
  have := map_list_prod (pushHom hπ (epsR K)) (List.ofFn u)
  rw [List.map_ofFn] at this
  exact congrArg (fun q => q.left) this

theorem isLieComb_of_isCombAt (hπ : IsGrpPullback A Xo.univ.t.G x π) {n : ℕ} (v : Fin n → (epsR K ⟶ A))
    (cf : Fin n → K) (w : epsR K ⟶ A)
    (h : IsCombAt x (fun i => (v i).left ≫ π) cf (w.left ≫ π)) : IsLieComb cf v w := by
  obtain ⟨u, hu, hw⟩ := h
  choose u' hu' using fun i => exists_lift hπ (T := epsR K) (u i).left (Over.w (u i))
  have e : u = fun i => pushHom hπ (epsR K) (u' i) := funext fun i => Over.OverMorphism.ext (hu' i).symm
  refine ⟨u', fun i => ?_, Over.OverMorphism.ext ?_⟩
  · apply hπ.1.hom_ext
    · rw [Category.assoc]; exact (hu' i).trans (hu i)
    · have hv : (v i).left ≫ A.hom = spMap (algebraMap K (DualNumber K)) := Over.w (v i)
      rw [Over.w, Category.assoc, hv, ArcQ.NormalForm.ExFr.scale_over]; rfl
  · apply hπ.1.hom_ext
    · rw [e] at hw
      exact hw.symm.trans (push_prod hπ u').symm
    · rw [Over.w, Over.w]

end GlobalTheory.KSExist.FrameLift

namespace GlobalTheory.KSExist

open FrameLift

theorem exists_frame_of_isGrpPullback {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {K : Type} [Field K] [Algebra c.F K] (y : FrPt Xo c K)
    {A : Over (Sp K)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left} (hπ : IsGrpPullback A Xo.univ.t.G y.x π)
    (a : OAct (𝓞 E) A) (ha : ∀ z, (a.act z).left ≫ π = π ≫ (Xo.univ.t.act.act z).left) :
    ∃ ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR K ⟶ A), (∀ σ k, (ub σ k).left ≫ π = y.u σ k) ∧
      (∀ σ k, IsTangent (ub σ k)) ∧
      (∀ σ k z, ub σ k ≫ a.act z = GlobalTheory.GrpTangent.epsScale (algebraMap c.F K (embK c σ z)) ≫ ub σ k) ∧
      ∀ σ (w : epsR K ⟶ A), IsTangent w →
        (∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (algebraMap c.F K (embK c σ z)) ≫ w) →
        ∃ cf, IsLieComb cf (ub σ) w := by
  choose ub hub using fun σ k => exists_lift hπ (T := epsR K) (y.u σ k) (y.tan σ k).1
  refine ⟨ub, hub, fun σ k => (tan_iff hπ _).1 (by rw [hub]; exact y.tan σ k), fun σ k z => ?_, fun σ w ht he => ?_⟩
  · refine (eig_iff hπ (ha z) _ _).1 ?_
    rw [hub]
    exact y.eig σ k z
  · have e : y.u σ = fun i => (ub σ i).left ≫ π := funext fun i => (hub σ i).symm
    obtain ⟨cf, hcf, -⟩ := y.basis σ (w.left ≫ π) ((tan_iff hπ w).2 ht)
      (fun z => (eig_iff hπ (ha z) w _).2 (he z))
    rw [e] at hcf
    exact ⟨cf, isLieComb_of_isCombAt hπ _ cf w hcf⟩

end GlobalTheory.KSExist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicQuotientAlongArc
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open Filter Topology
open GlobalTheory.ShFam GlobalTheory.ShFam.BdArc GlobalTheory.Toroidal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Vanishing

section ArcQuot

variable {Y : Scheme.{0}} {W : Y.Opens}

theorem arcPt_mem_basicOpen (hW : IsAffineOpen W) (φ : Γ(Y, W) →+* ℂ) (q : Γ(Y, W)) (s : Sp ℂ) :
    (spMap φ ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) s ∈ Y.basicOpen q ↔ φ q ≠ 0 := by
  change (spMap φ) s ∈ hW.fromSpec ⁻¹ᵁ Y.basicOpen q ↔ _
  rw [hW.fromSpec_preimage_basicOpen q]
  haveI := s.isPrime
  have hs : s.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
  change q ∉ (Ideal.comap φ s.asIdeal) ↔ _
  rw [hs]
  simp [Ideal.mem_comap]

theorem evalPt_arcPt (hW : IsAffineOpen W) (φ : Γ(Y, W) →+* ℂ)
    (h : ⊤ ≤ (spMap φ ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) ⁻¹ᵁ W) :
    GlobalTheory.TangentOrigin.evalPt (spMap φ ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) W h = φ := by
  have := GlobalTheory.TangentOrigin.eq_spec_fromSpec hW _ h
  dsimp only [spMap] at this
  rw [cancel_mono] at this
  have := Spec.map_injective this
  exact (congrArg CommRingCat.Hom.hom this).symm

theorem arcPt_top_le (hW : IsAffineOpen W) (φ : Γ(Y, W) →+* ℂ) :
    ⊤ ≤ (spMap φ ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) ⁻¹ᵁ W := by
  rw [Scheme.Hom.comp_preimage]
  change ⊤ ≤ spMap φ ⁻¹ᵁ (hW.fromSpec ⁻¹ᵁ W)
  rw [hW.fromSpec_preimage_self]
  exact le_rfl

theorem exists_punctured_ne_zero {f : ℂ → ℂ} {r : ℝ} (hf : DifferentiableOn ℂ f (Metric.ball 0 r))
    {u₀ : ℂ} (hu₀ : u₀ ∈ Metric.ball (0 : ℂ) r) (h₀ : f u₀ ≠ 0) (hr : 0 < r) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ r ∧ ∀ u ∈ Metric.ball (0 : ℂ) ρ, u ≠ 0 → f u ≠ 0 := by
  have ha := hf.analyticOnNhd Metric.isOpen_ball
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) r := Metric.mem_ball_self hr
  rcases (ha 0 h0).eventually_eq_zero_or_eventually_ne_zero with hz | hz
  · exact absurd (ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball (0 : ℂ) r).isPreconnected h0 hz hu₀) h₀
  · rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff_ball] at hz
    obtain ⟨ε, hε, hz⟩ := hz
    refine ⟨min ε r, lt_min hε hr, min_le_right _ _, fun u hu hu0 => hz u ?_ hu0⟩
    exact Metric.ball_subset_ball (min_le_left _ _) hu

end ArcQuot

end GlobalTheory.Vanishing

namespace GlobalTheory.Vanishing

theorem exists_quot_along_arc : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {B : LB Y} {O : Y.Opens} (m : H0 p B O) (W : Y.Opens) (hW : IsAffineOpen W) (i : B.ι), W ≤ B.U i → ∀ (ψ : ℂ → (Γ(Y, W) →+* ℂ)) (r : ℝ), IsHolPts ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) ⁻¹ᵁ O) → ∃ (ρ : ℝ) (a b : Γ(Y, W)), 0 < ρ ∧ ρ ≤ r ∧ ∀ u ∈ Metric.ball (0 : ℂ) ρ, u ≠ 0 → ψ u b ≠ 0 ∧ ∀ (hO : ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) ⁻¹ᵁ O) (hi : ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) ⁻¹ᵁ B.U i), H0.val (spMap (ψ u) ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) i hO hi m * ψ u b = ψ u a := by
  intro k _ Y p B O m W hW i hWi ψ r hψ hout
  obtain ⟨hr, hhol⟩ := hψ
  have hu₀ : ((r / 2 : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (half_pos hr)]
    linarith
  have hu₀0 : ((r / 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (half_pos hr).ne'
  obtain ⟨s⟩ : Nonempty (Sp ℂ) := inferInstance
  have hyO : (spMap (ψ (r / 2 : ℝ)) ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) s ∈ O :=
    hout _ hu₀ hu₀0 (show s ∈ (⊤ : (Sp ℂ).Opens) from trivial)
  have hyW : (spMap (ψ (r / 2 : ℝ)) ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) s ∈ W :=
    arcPt_top_le hW (ψ (r / 2 : ℝ)) (show s ∈ (⊤ : (Sp ℂ).Opens) from trivial)
  obtain ⟨q, hqle, hqy⟩ := hW.exists_basicOpen_le (V := O ⊓ B.U i) ⟨_, hyO, hWi hyW⟩ hyW
  have hq0 : ψ (r / 2 : ℝ) q ≠ 0 := (arcPt_mem_basicOpen hW _ q s).1 hqy
  haveI := hW.isLocalization_basicOpen q
  obtain ⟨n, a, hna⟩ := IsLocalization.Away.surj q (resG Y hqle (m.loc i))
  obtain ⟨ρ, hρ, hρr, hne⟩ := exists_punctured_ne_zero (hhol q) hu₀ hq0 hr
  refine ⟨ρ, a, q ^ n, hρ, hρr, fun u hu hu0 => ?_⟩
  have hqu : ψ u q ≠ 0 := hne u hu hu0
  refine ⟨by rw [map_pow]; exact pow_ne_zero _ hqu, fun hO hi => ?_⟩
  have hD : ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y, W) ⟶ Y from hW.fromSpec)) ⁻¹ᵁ Y.basicOpen q :=
    fun s _ => (arcPt_mem_basicOpen hW (ψ u) q s).2 hqu
  have hWx := arcPt_top_le hW (ψ u)
  have e := congrArg (GlobalTheory.TangentOrigin.evalPt _ _ hD) hna
  have hres (z : Γ(Y, W)) : GlobalTheory.TangentOrigin.evalPt _ _ hD (algebraMap Γ(Y, W) Γ(Y, Y.basicOpen q) z) = ψ u z := by
    exact (GlobalTheory.TangentOrigin.evalPt_res _ (Y.basicOpen_le q) hWx hD z).trans
      (DFunLike.congr_fun (evalPt_arcPt hW (ψ u) hWx) z)
  rw [map_mul, map_pow, hres, hres] at e
  rw [H0.val_apply, ← GlobalTheory.TangentOrigin.evalPt_res _ hqle _ hD, map_pow, e]

end GlobalTheory.Vanishing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsolatedNonKltDivisorSmoothProjective
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh

namespace GlobalTheory.KollarApp

theorem sum_Icc_cast_eq_choose (n : ℕ) :
    ∑ e ∈ Finset.Icc 1 n, (e : ℝ) = (((n + 1).choose 2 : ℕ) : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Nat.choose_succ_succ (n + 1) 1]
    simp
    ring

theorem isolatedNonKlt_smooth : GlobalTheory.Published.IsolatedNonKltDivisor → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (q : X ⟶ Sp ℂ) (D : ℕ) [SmoothOfRelativeDimension D q], IsProjOver q → 1 ≤ D → letI := algebraΓOfHom q; ∀ (N₀ : LB X) (r : ℕ) (x : X), 0 < r → IsNef ℂ N₀ → IsBig ℂ N₀ → IsClosed ({x} : Set X) → (∀ (Z : Closeds X) (e : ℕ), IsIrreducible (Z : Set X) → x ∈ Z → 1 ≤ e → topologicalKrullDim (Z : Set X) = e → (((D + 1).choose 2 : ℕ) : ℝ) ^ e < (interNumRed ℂ Z (fun _ : Fin e => N₀) : ℝ) / (r : ℝ) ^ e) → ∃ (m' : ℕ) (D₀ : CartierDiv X) (U : X.Opens), 0 < m' ∧ D₀.Eff ∧ (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![toLB D₀] : ℚ) / m' = interNumRed ℂ C ![N₀] / r) ∧ x ∈ U ∧ (∀ y ∈ U, y ≠ x → KltAt q D (qWeil D₀ m') y) ∧ ¬ KltAt q D (qWeil D₀ m') x := by
  intro hK X _ _ q D _ hproj hD
  letI := algebraΓOfHom q
  intro N₀ r x hr hnef hbig hx hint
  haveI := SmoothOfRelativeDimension.smooth D q
  haveI : GlobalTheory.IsNormalScheme X := isNormalScheme_of_smooth q
  have hdim : topologicalKrullDim X = D := GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth q D inferInstance
  have hc : (0 : ℝ) < (((D + 1).choose 2 : ℕ) : ℝ) := by
    have : 0 < (D + 1).choose 2 := Nat.choose_pos (by omega)
    exact_mod_cast this
  have hsum : ∑ e ∈ Finset.Icc 1 D, (e : ℝ) / (((D + 1).choose 2 : ℕ) : ℝ) ≤ 1 := by
    rw [← Finset.sum_div, sum_Icc_cast_eq_choose, div_self hc.ne']
  obtain ⟨m, D₀, U, hm, hD₀, hnum, hxU, -, hklt, hnot⟩ :=
    hK X q D hproj hdim hD 0 r N₀ x (fun _ => (((D + 1).choose 2 : ℕ) : ℝ))
      ⟨by simp, fun z hz => absurd rfl hz, fun _ => le_rfl⟩
      (fun y => GlobalTheory.Discrepancy.kltAt_zero_of_smooth hdim y) hr hnef hbig hx (fun _ _ => hc)
      hint hsum
  refine ⟨m, D₀, U, hm, hD₀, hnum, hxU, fun y hy hyx => ?_, ?_⟩
  · simpa using hklt y hy hyx
  · simpa using hnot

end GlobalTheory.KollarApp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdlAlongEqTopOfNotMemSupport
section
open AlgebraicGeometry CategoryTheory IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.LocM

namespace GlobalTheory.LocM

theorem idlAlong_eq_top_of_notMem_support (X : Scheme.{0}) (I : X.IdealSheafData) (R : Type) [CommRing R]
    [IsLocalRing R] (ξ : Sp R ⟶ X) (h : ξ (closedPoint R) ∉ I.support) : idlAlong I ξ = ⊤ := by
  have e : FinalTheorems.stalkId I (ξ (closedPoint R)) = ⊤ :=
    not_not.1 fun h' => h ((mem_support_iff_stalkId I _).2 h')
  rw [idlAlong, e, Ideal.map_top]

end GlobalTheory.LocM
end

