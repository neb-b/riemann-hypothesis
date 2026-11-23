module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2356
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2713
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2465
public import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2686
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2607
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2722
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2654
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2703
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2694
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2602
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2617
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2734
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2669
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1885
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1890
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFramePointStalk
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2726
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1092
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1109
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2728
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2716
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2312
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2448

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedPDivGroupChartCoboundaryTwoCoord
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Katz.CobCoord

variable {p : ℕ} {k : Type} [CommRing k] {d : ℕ} {G : PDivGroup p k}

theorem connectedPDivGroupChart_eval_nilpotent_pair (c : Chart G d) (n : ℕ) {B : Type} [CommRing B] [Algebra k B] {τ : Type} [Finite τ]
    (E : MvPowerSeries τ k →ₐ[k] B) (hE : ∀ t, IsNilpotent (E (X t)))
    (u v : Fin d → MvPowerSeries τ k) (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) (g : G.A n ⊗[k] G.A n →ₐ[k] B)
    (hgu : ∀ i, E (u i) = g (c.x n i ⊗ₜ 1)) (hgv : ∀ i, E (v i) = g (1 ⊗ₜ c.x n i))
    (s : MvPowerSeries (Fin d ⊕ Fin d) k) : E (at2 s u v) = g (c.ev₂ n s) := by
  have hy : ∀ j, IsNilpotent (g (c.x₂ n j)) := fun j => (c.nil₂ n j).map g
  have h1 := (_root_.GlobalTheory.evA_subst_and_map k (Fin d ⊕ Fin d) B).1 τ E hE (Sum.elim u v)
    (by rintro (i | i) <;> simp [hu, hv]) (fun j => g (c.x₂ n j)) hy
    (by rintro (i | i) <;> simp [Chart.x₂, hgu, hgv]) s
  have h2 := (_root_.GlobalTheory.evA_subst_and_map k (Fin d ⊕ Fin d) (G.A n ⊗[k] G.A n)).2 B g (c.x₂ n) (c.nil₂ n)
    (fun j => g (c.x₂ n j)) hy (fun _ => rfl) s
  unfold at2
  rw [h1, Chart.ev₂, h2]

end GlobalTheory.Katz.CobCoord

namespace GlobalTheory.Katz.CobCoord

variable (k : Type) [CommRing k] (A : Type) [CommRing A] [Bialgebra k A]

abbrev gSumL : A ⊗[k] A →ₐ[k] A ⊗[k] (A ⊗[k] A) :=
  (Algebra.TensorProduct.assoc k k k A A A).toAlgHom.comp
    (Algebra.TensorProduct.map (Bialgebra.comulAlgHom k A) (AlgHom.id k A))

abbrev gSumR : A ⊗[k] A →ₐ[k] A ⊗[k] (A ⊗[k] A) :=
  Algebra.TensorProduct.map (AlgHom.id k A) (Bialgebra.comulAlgHom k A)

abbrev gFst : A ⊗[k] A →ₐ[k] A ⊗[k] (A ⊗[k] A) :=
  Algebra.TensorProduct.map (AlgHom.id k A) (Algebra.TensorProduct.includeLeft (S := k))

theorem algAssoc_apply (w : (A ⊗[k] A) ⊗[k] A) :
    Algebra.TensorProduct.assoc k k k A A A w = TensorProduct.assoc k A A A w := by
  induction w with
  | tmul x b =>
    induction x with
    | tmul a a' => simp
    | add x y hx hy => simp only [add_tmul, map_add (f := _), hx, hy]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem gSumL_apply (t : A ⊗[k] A) :
    gSumL k A t = TensorProduct.assoc k A A A (Coalgebra.comul.rTensor A t) := by
  induction t with
  | tmul a b => simp [algAssoc_apply]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem gSumR_apply (t : A ⊗[k] A) : gSumR k A t = Coalgebra.comul.lTensor A t := by
  induction t with
  | tmul a b => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem gFst_apply (t : A ⊗[k] A) :
    gFst k A t = ((TensorProduct.mk k A A).flip 1).lTensor A t := by
  induction t with
  | tmul a b => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem gFst_eq_assoc (t : A ⊗[k] A) :
    gFst k A t = Algebra.TensorProduct.assoc k k k A A A (t ⊗ₜ 1) := by
  induction t with
  | tmul a b => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy, add_tmul]

theorem cobTwo_eq (t : A ⊗[k] A) : cobTwo k A t =
    Algebra.TensorProduct.includeRight t - gSumL k A t + gSumR k A t - gFst k A t := by
  rw [cobTwo_apply, gSumL_apply, gSumR_apply, gFst_apply, Algebra.TensorProduct.includeRight_apply]

end GlobalTheory.Katz.CobCoord

namespace GlobalTheory.Katz.CobCoord

theorem evA_cob2_eq_cobTwo_and_op_assoc : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d),
    ∀ (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), c.IsLawOf μ →
    ∀ n (h : ∀ i, IsNilpotent ((Sum.elim (fun i => c.x n i ⊗ₜ[k] (1 : G.A n ⊗[k] G.A n))
      (fun j => (1 : G.A n) ⊗ₜ[k] c.x₂ n j)) i)),
    (∀ s, evA k _ h (cob2 μ s) = cobTwo k (G.A n) (c.ev₂ n s)) ∧
      ∀ i, evA k _ h (op μ (op μ x1 x2) x3 i) = evA k _ h (op μ x1 (op μ x2 x3) i) := by
  intro p k _ d G c μ hμ n h
  have hX := GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate k _ _ _ h
  have hE : ∀ t, IsNilpotent (evA k _ h (X t)) := fun t => by rw [hX]; exact h t
  have hμ0 := ((GlobalTheory.T.connectedPDivGroup_formalLaw_coordinates p k d G c).2 μ hμ).1
  have e1 : ∀ i, evA k _ h (x1 i) = c.x n i ⊗ₜ 1 := fun i => hX (Sum.inl i)
  have e2 : ∀ i, evA k _ h (x2 i) = 1 ⊗ₜ (c.x n i ⊗ₜ 1) := fun i => hX (Sum.inr (Sum.inl i))
  have e3 : ∀ i, evA k _ h (x3 i) = 1 ⊗ₜ (1 ⊗ₜ c.x n i) := fun i => hX (Sum.inr (Sum.inr i))
  have c1 : ∀ i, constantCoeff (x1 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k) = 0 :=
    fun _ => constantCoeff_X _
  have c2 : ∀ i, constantCoeff (x2 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k) = 0 :=
    fun _ => constantCoeff_X _
  have c3 : ∀ i, constantCoeff (x3 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k) = 0 :=
    fun _ => constantCoeff_X _
  have cop : ∀ u v : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k,
      (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) →
      ∀ i, constantCoeff (op μ u v i) = 0 := by
    intro u v hu hv i
    have hs : ∀ j, constantCoeff (Sum.elim u v j) = 0 := by rintro (j | j) <;> simp [hu, hv]
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hs) hs (hμ0 i)
  have o12 : ∀ i, evA k _ h (op μ x1 x2 i) = gFst k (G.A n) (Coalgebra.comul (c.x n i)) := by
    intro i
    rw [op, connectedPDivGroupChart_eval_nilpotent_pair c n _ hE x1 x2 c1 c2 (gFst k (G.A n)) (fun j => by rw [e1]; simp [Algebra.TensorProduct.one_def])
      (fun j => by rw [e2]; simp [Algebra.TensorProduct.one_def]), hμ n i]
  have o23 : ∀ i, evA k _ h (op μ x2 x3 i) =
      Algebra.TensorProduct.includeRight (Coalgebra.comul (c.x n i)) := by
    intro i
    rw [op, connectedPDivGroupChart_eval_nilpotent_pair c n _ hE x2 x3 c2 c3 Algebra.TensorProduct.includeRight
      (fun j => by rw [e2]; simp [Algebra.TensorProduct.one_def]) (fun j => by rw [e3]; simp [Algebra.TensorProduct.one_def]), hμ n i]
  have a2 := connectedPDivGroupChart_eval_nilpotent_pair c n _ hE (op μ x1 x2) x3 (cop _ _ c1 c2) c3 (gSumL k (G.A n))
    (fun j => by rw [o12, gFst_eq_assoc]; simp)
    (fun j => by rw [e3]; simp [Algebra.TensorProduct.one_def])
  have a3 := connectedPDivGroupChart_eval_nilpotent_pair c n _ hE x1 (op μ x2 x3) c1 (cop _ _ c2 c3) (gSumR k (G.A n))
    (fun j => by rw [e1]; simp [Algebra.TensorProduct.one_def]) (fun j => by rw [o23]; simp)
  refine ⟨fun s => ?_, fun i => ?_⟩
  · have a1 := connectedPDivGroupChart_eval_nilpotent_pair c n _ hE x2 x3 c2 c3 Algebra.TensorProduct.includeRight
      (fun j => by rw [e2]; simp [Algebra.TensorProduct.one_def]) (fun j => by rw [e3]; simp [Algebra.TensorProduct.one_def]) s
    have a4 := connectedPDivGroupChart_eval_nilpotent_pair c n _ hE x1 x2 c1 c2 (gFst k (G.A n))
      (fun j => by rw [e1]; simp [Algebra.TensorProduct.one_def]) (fun j => by rw [e2]; simp [Algebra.TensorProduct.one_def]) s
    rw [cob2, map_sub, map_add (f := _), map_sub, a1, a2, a3, a4, cobTwo_eq]
  · change evA k _ h (at2 (μ i) (op μ x1 x2) x3) = evA k _ h (at2 (μ i) x1 (op μ x2 x3))
    rw [a2, a3, hμ n i, gSumL_apply, gSumR_apply, Coalgebra.coassoc_apply]

end GlobalTheory.Katz.CobCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnDens
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCell2.LocFib

theorem continuousOn_dens {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) {α : A.Fld} (hα : A.IsForm α)
    (i : A.ι) : ContinuousOn (fun v => (dens (A.loc α i v)).re) (A.e i).target :=
  Complex.continuous_re.comp_continuousOn ((hα.smooth i Finset.univ).continuousOn.div_const _)


set_option maxHeartbeats 800000 in
theorem part_preimage : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H → ∀ α : (atlas X σ).Fld, (atlas X σ).IsForm α → (atlas Y σ).IsForm ((atlas X σ).pullback (atlas Y σ) (ptMap σ f hf) α * evalF (atlas Y σ) (grF E' (pullGram E H φ f hf)) (fibrePoint m)) → ∀ (s : ℤˣ) (c : AlgChart X.str σ X.dim) (A : Mat m X.Fn) (O : Set (CxPts X.str σ)), IsOpen O → O ⊆ c.e.source → (∀ x ∈ O, A ∈ E.S (under x)) → ∀ T, MeasurableSet T → T ⊆ O → (atlas Y σ).part ((atlas X σ).pullback (atlas Y σ) (ptMap σ f hf) α * evalF (atlas Y σ) (grF E' (pullGram E H φ f hf)) (fibrePoint m)) s (ptMap σ f hf ⁻¹' T) = (atlas X σ).part α s T := by
  intro F _ σ X Y ι _ m E E' φ f hf hR H hH α hα hβ s c A O hO hOc hOA T hT hTO
  rcases T.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · simp
  haveI : T2Space (CxPts X.str σ) := CxPts.t2Space _ _
  haveI : T2Space (CxPts Y.str σ) := CxPts.t2Space _ _
  obtain ⟨u, hu⟩ := _root_.GlobalTheory.FlagCell2.GenericCell.exists_inCell_genericPoint F X Y ι m E E' φ f hR _ A (hOA x₀ (hTO hx₀))
  have hdim := _root_.GlobalTheory.FlagCell2.Dim.main F σ X Y ι m E E' φ f hf hR
  let ε : Fin Y.dim ≃ Fin X.dim ⊕ Cell m := Fintype.equivOfCardEq (by simp [hdim])
  obtain ⟨hopen, hinj, himg⟩ := _root_.GlobalTheory.FlagCell2.cellMap_image_eq F σ X Y ι m E E' φ f hf hR c A u hu _ ε
  have hW := (_root_.GlobalTheory.FlagCell2.isOpen_inCell_and_regAt F X Y ι m E E' φ f hR A u).1
  have hπ : Continuous (ptMap σ f hf) := GlobalTheory.Points.PtsOver.continuous_map f hf _
  have hTm : MeasurableSet (ptMap σ f hf ⁻¹' T) := hπ.measurable hT
  have hnull := _root_.GlobalTheory.FlagCell2Null.part_compl_ptsIn F σ Y ((atlas X σ).pullback (atlas Y σ) (ptMap σ f hf) α *
    evalF (atlas Y σ) (grF E' (pullGram E H φ f hf)) (fibrePoint m)) ⟨_, hW⟩ hu s
  obtain ⟨μ, hμ⟩ : ∃ μ, μ = (atlas Y σ).part ((atlas X σ).pullback (atlas Y σ) (ptMap σ f hf) α *
    evalF (atlas Y σ) (grF E' (pullGram E H φ f hf)) (fibrePoint m)) s := ⟨_, rfl⟩
  rw [← hμ] at hnull ⊢
  have h1 : μ (ptMap σ f hf ⁻¹' T) = μ (ptMap σ f hf ⁻¹' T ∩ cellSet E E' φ f hf c A u) := by
    refine (measure_inter_add_diff (ptMap σ f hf ⁻¹' T) hopen.measurableSet).symm.trans ?_
    have h0 : μ (ptMap σ f hf ⁻¹' T \ cellSet E E' φ f hf c A u) = 0 :=
      by
      refine measure_mono_null (fun y hy => ?_) hnull
      intro hy'
      have h2 : under y ∈ (⟨_, hW⟩ : Y.X.Opens) := mem_ptsIn.1 hy'
      have h3 : InCell E E' φ f A u (under y) := h2
      exact hy.2 ⟨h3, hOc (hTO hy.1)⟩
    rw [h0, add_zero]
  have hmet := _root_.GlobalTheory.ChernCalc.isMetricFr_smoothUnitAt F σ X ι m 0 E H (isMetricFr_of_isMetricOn hH)
  have hG : ∀ v ∈ c.e '' O, ∀ τ, MContDiffAt ∞ (fun w => H A (c.e.symm w) τ) v ∧ (H A (c.e.symm v) τ).PosDef := by
    rintro _ ⟨x, hx, rfl⟩ τ
    exact ((hmet x A (hOA x hx) τ).2 c (hOc hx)).self_of_nhds
  have hOo : IsOpen (c.e '' O) := c.e.isOpen_image_of_subset_source hO hOc
  have hTi : MeasurableSet (c.e '' T) := by
    have e : c.e '' T = Subtype.val '' (c.e.target.restrict c.e.symm ⁻¹' T) := by
      ext v
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨_, c.e.map_source (hOc (hTO hx))⟩, by
          show c.e.symm (c.e x) ∈ T
          rwa [c.e.left_inv (hOc (hTO hx))], rfl⟩
      · rintro ⟨v, hv, rfl⟩
        exact ⟨_, hv, c.e.right_inv v.2⟩
    rw [e]
    exact (MeasurableEmbedding.subtype_coe c.e.open_target.measurableSet).measurableSet_image.2
      ((continuousOn_iff_continuous_restrict.1 c.e.continuousOn_symm).measurable hT)
  rw [h1, hμ, _root_.GlobalTheory.FlagCell2.ChangeOfVariables.part_eq_lintegral_image _ _ (atlas Y σ) _ hβ _ (cellMap ε f hf c u)
    (cellForm ε (fun v => H A (c.e.symm v)) ((atlas X σ).loc α c)) hopen hinj ?_ s _
    (hTm.inter hopen.measurableSet) Set.inter_subset_right, himg T (hTO.trans hOc) fun x hx => hOA x (hTO hx),
    show (atlas X σ).part α s T = ∫⁻ v in c.e '' T, ENNReal.ofReal (((s : ℤ) : ℝ) * (dens ((atlas X σ).loc α c v)).re)
      from _root_.GlobalTheory.FlagCell2.part_subset_chart _ _ (atlas X σ) α hα s c T hT (hTO.trans hOc),
    ← _root_.GlobalTheory.FlagCell2.setLIntegral_fibDens ι m _ _ ε (fun v => H A (c.e.symm v))
      (fun v => ((s : ℤ) : ℝ) * (dens ((atlas X σ).loc α c v)).re) (c.e '' O) (c.e '' T) hOo hTi (Set.image_mono hTO)
      (continuousOn_const.mul ((continuousOn_dens _ hα c).mono ?_))
      (fun τ i j v hv => ((hG v hv τ).1 i j).continuousAt.continuousWithinAt) fun v hv τ => (hG v hv τ).2]
  · refine setLIntegral_congr_fun ((bsL ε).continuous.measurable hTi) fun w hw => ?_
    have hw' := Set.image_mono hTO hw
    beta_reduce
    rw [_root_.GlobalTheory.FlagCell2.CellDens.dens_cellForm ι m _ _ ε _ _ w (fun τ => (hG _ hw' τ).2) fun τ => (hG _ hw' τ).1.of_le (by norm_cast),
      Complex.re_mul_ofReal, mul_assoc]
  · rintro _ ⟨x, hx, rfl⟩
    exact c.e.map_source (hOc hx)
  · intro x hx
    refine ⟨(_root_.GlobalTheory.FlagCell2.cellMap_contDiffAt F σ X Y ι m E E' φ f hf hR c A u _ ε x hx).differentiableAt two_ne_zero, ?_⟩
    rw [Pi.mul_apply, cellForm, map_mul, _root_.GlobalTheory.FlagCell2.pullback_cell F σ X Y ι m E E' φ f hf hR c A u _ ε α hα x hx]
    congr 1
    exact _root_.GlobalTheory.FlagCell2.pull_aeval_even _ _ _ _ _ _ _ (_root_.GlobalTheory.FlagCell2.GradedPull.grF_eq_pull F σ X Y ι m E E' φ f hf hR c A u H hH ε x hx)

end GlobalTheory.FlagCell2.LocFib
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormStalkIntegralFrame
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TwistVal

open GlobalTheory.FlatTw GlobalTheory.FlatLine GlobalTheory.AllWt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}
  {Z : Comp Xo c} {T : CDVR} {io : c.F →+* T.Fr} (y' : IntFr Xo c T io)

theorem evI_idem_eq_one (h : evI y' (idem Z) ≠ 0) : evI y' (idem Z) = 1 := by
  have e := evI_mul y' (idem Z) (idem Z)
  rw [idem_mul_idem] at e
  exact mul_left_cancel₀ h (by rw [mul_one]; exact e.symm)

theorem val_inv {G₀ : WTZ E} (s : TwSec U x Z G₀) (he : evI y' (idem Z) = 1) :
    evI y' s.sig ≠ 0 ∧ evI y' s.inv ≠ 0 ∧ vV T.V (evI y' s.sig) + vV T.V (evI y' s.inv) = 0 := by
  have e : evI y' s.sig * evI y' s.inv = 1 := by rw [← evI_mul, s.mul_inv, he]
  have h1 : evI y' s.sig ≠ 0 := left_ne_zero_of_mul_eq_one e
  have h2 : evI y' s.inv ≠ 0 := right_ne_zero_of_mul_eq_one e
  refine ⟨h1, h2, ?_⟩
  rw [← vV_mul h1 h2, e]
  simp [vV]

theorem val_mul {G₀ G₁ : WTZ E} (s : TwSec U x Z G₀) (t : TwSec U x Z G₁) (he : evI y' (idem Z) = 1)
    (hs : vV T.V (evI y' s.sig) = 0) (ht : vV T.V (evI y' t.sig) = 0) : vV T.V (evI y' (s.mul t).sig) = 0 := by
  show vV T.V (evI y' (s.sig * t.sig)) = 0
  rw [evI_mul, vV_mul (val_inv y' s he).1 (val_inv y' t he).1, hs, ht, add_zero]

theorem val_symm {G₀ : WTZ E} (s : TwSec U x Z G₀) (he : evI y' (idem Z) = 1)
    (hs : vV T.V (evI y' s.sig) = 0) : vV T.V (evI y' s.symm.sig) = 0 := by
  have h := (val_inv y' s he).2.2
  show vV T.V (evI y' s.inv) = 0
  omega

theorem exists_pow {e : ℤ} (s : TwSec U x Z (wtOf Dw 0 e)) (he : evI y' (idem Z) = 1)
    (hs : vV T.V (evI y' s.sig) = 0) : ∀ n : ℕ, ∃ t : TwSec U x Z (wtOf Dw 0 ((n : ℤ) * e)),
      vV T.V (evI y' t.sig) = 0 := by
  intro n
  induction n with
  | zero =>
    exact ⟨(s.mul s.symm).copy (by rw [add_neg_cancel, Nat.cast_zero, zero_mul, wtOf_zero]),
      val_mul y' s s.symm he hs (val_symm y' s he hs)⟩
  | succ n ih =>
    obtain ⟨t, ht⟩ := ih
    exact ⟨(t.mul s).copy (by rw [← wtOf_add, add_zero]; push_cast; ring_nf), val_mul y' t s he ht hs⟩

theorem exists_zpow (s : TwSec U x Z (wtOf Dw 0 1)) (he : evI y' (idem Z) = 1)
    (hs : vV T.V (evI y' s.sig) = 0) (k : ℤ) : ∃ t : TwSec U x Z (wtOf Dw 0 k), vV T.V (evI y' t.sig) = 0 := by
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · obtain ⟨t, ht⟩ := exists_pow y' s he hs n
    exact ⟨t.copy (by rw [mul_one]), ht⟩
  · have hneg : -wtOf Dw 0 1 = wtOf Dw 0 (-1) :=
      neg_eq_of_add_eq_zero_right (by rw [← wtOf_add, add_zero, add_neg_cancel, wtOf_zero])
    obtain ⟨t, ht⟩ := exists_pow y' (s.symm.copy hneg) he (val_symm y' s he hs) n
    exact ⟨t.copy (by rw [mul_neg_one]), ht⟩

end GlobalTheory.TwistVal


end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeEqIntegralTopChernFormComplex
section
namespace GlobalTheory.ChernDegree

theorem chernDegreeComplex : GlobalTheory.Published.ChernDegreeComplex := fun Y Δ L r hr φ hφ =>
  ⟨(_root_.GlobalTheory.chernInt_one_eq_mInt Y L φ hφ).1, by
    rw [_root_.GlobalTheory.MassDegree.chernInt_eq_topSelf Y L φ hφ, _root_.GlobalTheory.ChernDegree.inter_const_eq_topSelf_of_presents Y Δ L r φ.isLB hr]⟩

end GlobalTheory.ChernDegree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneBaseChangeBasis
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu.Base


set_option maxHeartbeats 800000 in
theorem exists_mem_span_red_eq (p : ℕ) [Fact p.Prime] (P : ∀ (k : Type) [CommRing k], PDivGroup p k → Prop)
    (B : Base p P) (k k' : Type) [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p]
    [PerfectRing k' p] [Algebra k k'] (G : PDivGroup p k) (hG : P k G) (hG' : P k' (G.baseChange k'))
    (ι : Type) (b : Module.Basis ι (WittVector p k) (B.M G hG)) (z : (G.baseChange k').RigExt) :
    ∃ n ∈ Submodule.span (WittVector p k') (Set.range fun i => B.smap hG' hG (G.toBase k') (b i)),
      B.red _ hG' n = z := by
  obtain ⟨x, rfl⟩ := G.liftSemi_rig_bijective k' (CharP.cast_eq_zero k p) (.inl inferInstance) |>.2 z
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    obtain ⟨n, hn, h1⟩ := hx
    obtain ⟨n', hn', h2⟩ := hy
    refine ⟨n + n', add_mem hn hn', ?_⟩
    rw [LinearMap.map_add (B.red _ hG') n n', h1, h2, LinearMap.map_add (f := _)]
  | tmul r y =>
    obtain ⟨m, rfl⟩ := B.red_surjective G hG y
    obtain ⟨R, rfl⟩ := (WittVector.constantCoeff_surjective p : Function.Surjective
      (WittVector.constantCoeff : WittVector p k' →+* k')) r
    refine ⟨R • B.smap hG' hG (G.toBase k') m, Submodule.smul_mem _ _ ?_, ?_⟩
    · set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.linearCombination_repr m, Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
      exact Submodule.sum_mem _ fun i _ => by
        rw [B.smap_smul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · set_option backward.isDefEq.respectTransparency false in
      rw [liftSemi_tmul, LinearMap.map_smulₛₗ (B.red _ hG') R, B.red_smap]

set_option synthInstance.maxHeartbeats 200000 in
theorem smap_toBase_basis (p : ℕ) [Fact p.Prime] (P : ∀ (k : Type) [CommRing k], PDivGroup p k → Prop)
    (B : Base p P) (k k' : Type) [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p]
    [PerfectRing k' p] [Algebra k k'] (G : PDivGroup p k) (hG : P k G) (hG' : P k' (G.baseChange k'))
    (ι : Type) [Fintype ι] (b : Module.Basis ι (WittVector p k) (B.M G hG)) :
    ∃ b' : Module.Basis ι (WittVector p k') (B.M (G.baseChange k') hG'),
      ∀ i, b' i = B.smap hG' hG (G.toBase k') (b i) := by
  have := B.free G hG
  have := B.finite G hG
  have := B.free _ hG'
  have := B.finite _ hG'
  have hp : (p : k) = 0 := CharP.cast_eq_zero k p
  have hp' : (p : k') = 0 := CharP.cast_eq_zero k' p
  obtain ⟨-, hr⟩ := finrank_eq_of_semilinear_surjective (WittVector.constantCoeff_surjective p) hp
    (B.red G hG) (B.red_surjective G hG) fun m h => (B.red_eq_zero G hG m).1 h
  obtain ⟨-, hr'⟩ := finrank_eq_of_semilinear_surjective (WittVector.constantCoeff_surjective p) hp'
    (B.red _ hG') (B.red_surjective _ hG') fun m h => (B.red_eq_zero _ hG' m).1 h
  change Module.finrank k G.RigExt = _ at hr
  change Module.finrank k' (G.baseChange k').RigExt = _ at hr'
  have hrank : Module.finrank k' (G.baseChange k').RigExt = Module.finrank k G.RigExt := by
    rw [← (LinearEquiv.ofBijective _ (G.liftSemi_rig_bijective k' hp (.inl inferInstance))).finrank_eq,
      Module.finrank_baseChange]
  have hmax : (p : WittVector p k') ∈ IsLocalRing.maximalIdeal (WittVector p k') := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := hu.map (WittVector.constantCoeff : WittVector p k' →+* k')
    rw [map_natCast, hp'] at this
    exact not_isUnit_zero this
  have hjac : Ideal.span {(p : WittVector p k')} ≤ Ring.jacobson (WittVector p k') := by
    rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
    exact Ideal.span_le.2 (Set.singleton_subset_iff.2 hmax)
  have hspan : ⊤ ≤ Submodule.span (WittVector p k')
      (Set.range fun i => B.smap hG' hG (G.toBase k') (b i)) := by
    refine Submodule.le_of_le_smul_of_le_jacobson Module.Finite.fg_top hjac fun m _ => ?_
    obtain ⟨n, hn, h1⟩ := exists_mem_span_red_eq p P B k k' G hG hG' ι b (B.red _ hG' m)
    obtain ⟨q, hq⟩ := (B.red_eq_zero _ hG' (m - n)).1 (by
      rw [LinearMap.map_sub (B.red _ hG') m n, h1, sub_self])
    have hm : m = n + (p : WittVector p k') • q := by
      rw [← Nat.cast_smul_eq_nsmul (WittVector p k')] at hq
      rw [← hq, add_sub_cancel]
    rw [hm]
    exact Submodule.add_mem_sup hn (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _)
      Submodule.mem_top)
  have hcard : Fintype.card ι = Module.finrank (WittVector p k') (B.M (G.baseChange k') hG') := by
    rw [← hr', hrank, hr, Module.finrank_eq_card_basis b]
  exact ⟨Module.Basis.mk (linearIndependent_of_top_le_span_of_card_eq_finrank hspan hcard) hspan,
    fun i => Module.Basis.mk_apply _ _ i⟩

end GlobalTheory.Dieu.Base
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteThetaSectionsThickeningCoverStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_theta_sections_thickening_cover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k → ∃ (n : ℕ) (τ : Fin n → H0 U.LG.L k), ∀ w : (thickObj R (maximalIdeal R) 0 G).left, ∃ (j : Fin n) (i : Fin 1 → U.LG.L.ι) (N : (thickObj R (maximalIdeal R) 0 G).left.Opens) (r : Fin n → Γ((thickObj R (maximalIdeal R) 0 G).left, N)), w ∈ N ∧ IsAffineOpen N ∧ N ≤ (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart U.LG.L i ∧ (∀ y ∈ N, IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (τ j) i) ∧ ∀ l, secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (τ l) i = gs (𝟙 _) y N (r l) * secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (τ j) i) ∧ ∀ g : Γ((thickObj R (maximalIdeal R) 0 G).left, N), ∃ P Q : MvPolynomial (Fin n) R, IsUnit (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q) ∧ g * MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q = MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r P := by
  first | exact @GlobalTheory.Mum.exists_ratio_gen_closed | exact GlobalTheory.Mum.exists_ratio_gen_closed | (intros; apply GlobalTheory.Mum.exists_ratio_gen_closed <;> assumption)
end

