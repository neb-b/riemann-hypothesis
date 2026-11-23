module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0983
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0053
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsQProjOverOfIsProjOver
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatLocA
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2610
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2573
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2584
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2622
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPosPullbackGenericallyBirational
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SemiPullBir

theorem exists_isIso_restrict {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (π : Y ⟶ X)
    [IsSeparated π] [LocallyOfFiniteType π] (hη : π (genericPoint Y) = genericPoint X)
    (hd : π.residueDegree (genericPoint Y) = 1) :
    ∃ U : X.Opens, (U : Set X).Nonempty ∧ IsIso (π ∣_ U) := by
  have hFX : IsField (X.presheaf.stalk (π (genericPoint Y))) := by
    rw [hη]
    exact Field.toIsField X.functionField
  have hFY : IsField (Y.presheaf.stalk (genericPoint Y)) := Field.toIsField Y.functionField
  have hrX : Function.Bijective (X.residue (π (genericPoint Y))).hom := by
    refine ⟨?_, IsLocalRing.residue_surjective⟩
    letI := hFX.toField
    exact RingHom.injective _
  have hrY : Function.Bijective (Y.residue (genericPoint Y)).hom := by
    refine ⟨?_, IsLocalRing.residue_surjective⟩
    letI := hFY.toField
    exact RingHom.injective _
  have hκ : Function.Bijective (π.residueFieldMap (genericPoint Y)).hom := by
    letI := (π.residueFieldMap (genericPoint Y)).hom.toAlgebra
    have h1 : Module.finrank (X.residueField (π (genericPoint Y))) (Y.residueField (genericPoint Y)) = 1 := hd
    refine ⟨RingHom.injective _, fun y => ?_⟩
    have htop := Subalgebra.bot_eq_top_iff_finrank_eq_one.2 h1
    have hy : y ∈ (⊥ : Subalgebra (X.residueField (π (genericPoint Y))) (Y.residueField (genericPoint Y))) := by
      rw [htop]; exact Algebra.mem_top
    obtain ⟨a, ha⟩ := Algebra.mem_bot.1 hy
    exact ⟨a, ha⟩
  have hst : Function.Bijective (π.stalkMap (genericPoint Y)).hom := by
    have e := Scheme.residue_residueFieldMap (f := π) (genericPoint Y)
    have e' : (Y.residue (genericPoint Y)).hom.comp (π.stalkMap (genericPoint Y)).hom =
        (π.residueFieldMap (genericPoint Y)).hom.comp (X.residue (π (genericPoint Y))).hom := by
      rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, ← e]
    have hc : Function.Bijective ((Y.residue (genericPoint Y)).hom.comp (π.stalkMap (genericPoint Y)).hom) := by
      rw [e']; exact hκ.comp hrX
    refine (Function.Bijective.of_comp_iff' hrY _).1 hc
  have : IsIso (π.stalkMap (genericPoint Y)) := (ConcreteCategory.isIso_iff_bijective _).2 hst
  let φ : Spec (X.presheaf.stalk (π (genericPoint Y))) ⟶ Y :=
    Spec.map (inv (π.stalkMap (genericPoint Y))) ≫ Y.fromSpecStalk (genericPoint Y)
  have hφ : φ ≫ π = X.fromSpecStalk (π (genericPoint Y)) ≫ 𝟙 X := by
    simp only [φ, Category.assoc, Category.comp_id]
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc, ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id,
      Category.id_comp]
  obtain ⟨U, hU, g, hg₁, hg₂⟩ := spread_out_of_isGermInjective' (𝟙 X) π φ hφ
  rw [Category.comp_id] at hg₂
  have : IsDominant (Y.fromSpecStalk (genericPoint Y)) :=
    ⟨((dense_iff_closure_eq.2 (genericPoint_spec Y)).mono
      (Set.singleton_subset_iff.2 ⟨_, Scheme.fromSpecStalk_closedPoint⟩))⟩
  have : IsDominant φ := inferInstance
  have : IsDominant g := by
    rw [hg₁] at this
    exact IsDominant.of_comp (U.fromSpecStalkOfMem _ hU) g
  exact ⟨U, ⟨_, hU⟩, GlobalTheory.ZH.isIso_morphismRestrict_of_local_dominant_sections π U fun y hy =>
    ⟨U, U.ι, inferInstance, g, ⟨⟨y, hy⟩, rfl⟩, by simp, ‹_›, hg₂⟩⟩

theorem semiPos_pull : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsArithVar q D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) = 1 → ∀ L : HermLB p, L.SemiPos D → (L.pull π hπ).SemiPos D := by
  intro k _ X _ p D hp Y _ q hq π hπ hη hd L hL
  have hpr : IsProper q := GlobalTheory.SchemeWords.isProper_of_isProjOver hq.isProjOver
  have hsep : IsSeparated (π ≫ p) := by rw [hπ]; infer_instance
  have hft : LocallyOfFiniteType (π ≫ p) := by rw [hπ]; infer_instance
  have : IsSeparated π := IsSeparated.of_comp π p
  have : LocallyOfFiniteType π := locallyOfFiniteType_of_comp π p
  obtain ⟨U, hU, hi⟩ := exists_isIso_restrict π hη hd
  exact (GlobalTheory.SemiPosBir.semiPos_iff_pull k X Y p q D hp hq π hπ U hU hi L).1 hL

end GlobalTheory.SemiPullBir
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPosRaiseWeightSegmentSmul
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem semiPos_up_smul : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ) (L : HermLB p) (u : SmFn p)
    (t : ℝ), 0 ≤ t → t ≤ 1 → L.SemiPos D → (up L u).SemiPos D → (up L (u.smul t)).SemiPos D := by
  intro k _ X p D L u t h0 h1 hL hLu σ i c y hy ξ
  set f : ReciprocityTheory.L2DbarEstimates.V D → ℝ := fun v => (L.φ σ).φ i (c.e.symm v) with hfdef
  set g : ReciprocityTheory.L2DbarEstimates.V D → ℝ := fun v => u.u σ (c.e.symm v) with hgdef
  have hf : ContDiffAt ℝ 2 f (c.e y) := (L.cInf σ).contDiffAt c hy.1 hy.2
  have hfg : ContDiffAt ℝ 2 (fun v => f v + g v) (c.e y) := ((up L u).cInf σ).contDiffAt c hy.1 hy.2
  have a : 0 ≤ (ReciprocityTheory.L2DbarEstimates.leviV D (fun v => (f v : ℂ)) (c.e y) ξ).re := hL σ i c y hy ξ
  have b : 0 ≤ (ReciprocityTheory.L2DbarEstimates.leviV D (fun v => ((f v + g v : ℝ) : ℂ)) (c.e y) ξ).re := hLu σ i c y hy ξ
  have e : (fun v => (((up L (u.smul t)).φ σ).φ i (c.e.symm v) : ℂ)) =
      fun v => ((((1 - t) * f v + 0) + (t * (f v + g v) + 0) : ℝ) : ℂ) := by
    funext v
    show ((((L.φ σ).φ i (c.e.symm v) + t * u.u σ (c.e.symm v)) : ℝ) : ℂ) = _
    congr 1
    simp only [hfdef, hgdef]
    ring
  rw [e, ReciprocityTheory.L2DbarEstimates.Y.flA_leviV_add, ReciprocityTheory.L2DbarEstimates.Y.leviV_const_mul hf,
    ReciprocityTheory.L2DbarEstimates.Y.leviV_const_mul (f := fun v => f v + g v) hfg]
  · rw [Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    have : 0 ≤ 1 - t := by linarith
    positivity
  · exact (hf.const_smul (1 - t)).add contDiffAt_const
  · exact (hfg.const_smul t).add contDiffAt_const

end GlobalTheory.HSAmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetLIntegralFlagCellFibreDensityEqBase
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCell2

theorem aemeasurable_fibDens {ι : Type} [Fintype ι] {m : ι → ℕ} {d : ℕ} (G : V d → Mat m ℂ) (O : Set (V d))
    (hO : IsOpen O) (hG : ∀ τ i j, ContinuousOn (fun v => G v τ i j) O) :
    AEMeasurable (fun x : V d × (Cell m → ℂ) => fibDens (G x.1) x.2)
      (volume.restrict (O ×ˢ (Set.univ : Set (Cell m → ℂ)))) := by
  have hS : MeasurableSet (O ×ˢ (Set.univ : Set (Cell m → ℂ))) := hO.measurableSet.prod MeasurableSet.univ
  have hGτ : ∀ τ, ContinuousOn (fun x : V d × (Cell m → ℂ) => G x.1 τ) (O ×ˢ Set.univ) := by
    intro τ
    have h : ContinuousOn (fun v => G v τ) O :=
      continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => hG τ i j
    exact h.comp continuous_fst.continuousOn fun x hx => hx.1
  unfold fibDens
  apply Finset.aemeasurable_fun_prod
  intro τ _
  refine AEMeasurable.mul (AEMeasurable.mul aemeasurable_const ?_) ?_
  · have h := ((continuous_id.matrix_det).comp_continuousOn (hGτ τ))
    exact ((Complex.continuous_re.comp_continuousOn h).aemeasurable hS).pow_const _
  · unfold GlobalTheory.FlagFibre.dens
    apply Finset.aemeasurable_fun_prod
    intro i _
    refine AEMeasurable.pow_const (AEMeasurable.norm ?_) _
    have hc : Continuous fun p : Matrix (Fin (m τ)) (Fin (m τ)) ℂ × (Low (m τ) → ℂ) =>
        ReciprocityTheory.ChartRestriction.G.FD.lminor ((GlobalTheory.FlagFibre.uni p.2)ᴴ * p.1ᵀ * GlobalTheory.FlagFibre.uni p.2) i.castSucc := by
      unfold ReciprocityTheory.ChartRestriction.G.FD.lminor
      exact ((((GlobalTheory.FlagFibre.continuous_uni.comp continuous_snd).matrix_conjTranspose.matrix_mul
        continuous_fst.matrix_transpose).matrix_mul (GlobalTheory.FlagFibre.continuous_uni.comp continuous_snd)).matrix_submatrix
        _ _).matrix_det
    have h2 : ContinuousOn (fun x : V d × (Cell m → ℂ) => (G x.1 τ, fun s => x.2 ⟨τ, s⟩)) (O ×ˢ Set.univ) :=
      (hGτ τ).prodMk (by fun_prop : Continuous fun x : V d × (Cell m → ℂ) => fun s => x.2 ⟨τ, s⟩).continuousOn
    exact (hc.comp_continuousOn h2).aemeasurable hS

end GlobalTheory.FlagCell2

namespace GlobalTheory.FlagCell2

theorem setLIntegral_fibDens : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (n d : ℕ) (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (δ : V d → ℝ) (O K : Set (V d)), IsOpen O → MeasurableSet K → K ⊆ O → ContinuousOn δ O → (∀ τ i j, ContinuousOn (fun v => G v τ i j) O) → (∀ v ∈ O, ∀ τ, (G v τ).PosDef) → ∫⁻ w in bsL ε ⁻¹' K, ENNReal.ofReal (δ (bsL ε w) * fibDens (G (bsL ε w)) (fb ε w)) = ∫⁻ v in K, ENNReal.ofReal (δ v) := by
  intro ι _ m n d ε G δ O K hO hK hKO hδ hG hpos
  have hmp := (GlobalTheory.FlagCell2.measurePreserving_pt_split n d (Cell m) ε).1
  have hb : Measurable (bsL ε) := (bsL ε).continuous.measurable
  have hm := hmp.restrict_preimage (hb hK)
  have hs : (fun x : V d × (Cell m → ℂ) => pt ε x.1 x.2) ⁻¹' (bsL ε ⁻¹' K) = K ×ˢ Set.univ := by
    ext x
    simp [bsL_pt]
  rw [hs, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ] at hm
  set F : V d × (Cell m → ℂ) → ℝ≥0∞ := fun x => ENNReal.ofReal (δ x.1 * fibDens (G x.1) x.2) with hF
  have hS : MeasurableSet (O ×ˢ (Set.univ : Set (Cell m → ℂ))) := hO.measurableSet.prod MeasurableSet.univ
  have hFO : AEMeasurable F (volume.restrict (O ×ˢ (Set.univ : Set (Cell m → ℂ)))) := by
    refine ENNReal.measurable_ofReal.comp_aemeasurable (AEMeasurable.mul ?_ (aemeasurable_fibDens G O hO hG))
    exact (hδ.comp continuous_fst.continuousOn (fun x (hx : x ∈ O ×ˢ (Set.univ : Set (Cell m → ℂ))) => hx.1)).aemeasurable hS
  have hFK : AEMeasurable F ((volume.restrict K).prod volume) := by
    rw [← Measure.restrict_univ (μ := (volume : Measure (Cell m → ℂ))), Measure.prod_restrict,
      ← Measure.volume_eq_prod]
    exact hFO.mono_measure (Measure.restrict_mono (Set.prod_mono hKO subset_rfl) le_rfl)
  have e1 : (fun w => ENNReal.ofReal (δ (bsL ε w) * fibDens (G (bsL ε w)) (fb ε w))) ∘
      (fun x : V d × (Cell m → ℂ) => pt ε x.1 x.2) = F := by
    funext x
    simp [hF, bsL_pt, fb_pt]
  have hH : AEMeasurable (fun w => ENNReal.ofReal (δ (bsL ε w) * fibDens (G (bsL ε w)) (fb ε w)))
      (Measure.map (fun x : V d × (Cell m → ℂ) => pt ε x.1 x.2) ((volume.restrict K).prod volume)) := by
    rw [(GlobalTheory.FlagCell2.measurePreserving_pt_split n d (Cell m) ε).2.aemeasurable_map_iff, e1]
    exact hFK
  rw [← hm.map_eq, lintegral_map' hH hm.measurable.aemeasurable]
  refine (lintegral_congr fun a => congrFun e1 a).trans ?_
  rw [lintegral_prod _ hFK]
  refine setLIntegral_congr_fun hK fun v hv => ?_
  obtain ⟨h0, h1⟩ := GlobalTheory.FlagCell2.fibDens_mass ι m (G v) (hpos v (hKO hv))
  simp only [hF]
  simp_rw [ENNReal.ofReal_mul' (h0 _)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, h1, mul_one]

end GlobalTheory.FlagCell2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFibrePowerPointEqOfMatchingLowerData
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

theorem GlobalTheory.TInj.low_eq_of_match : ∀ {o : Type} [CommRing o] {ζ : o} {n : ℕ} (L : LowBase ζ n), 3 ≤ n → IsUnit ζ → IsUnit (n : o) → ∀ {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin L.T.r → ℤ)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D₁ D₂ : DegPre V) (ω₁ : L.W →+* V) (s₁ : I → V) (e₁ : D₁.X ≃+ (Fin L.T.r → ℤ)) (β₁ : D₁.P.A.left ⟶ L.T.B.left) (ββ₁ : (G2 D₁.P.A).left ⟶ (G2 L.T.B).left) (w₁ : LB.Iso (abelian₂ D₁.P.A D₁.P.L) ((abelian₂ L.T.B L.T.M.L).pull ββ₁)) (ω₂ : L.W →+* V) (s₂ : I → V) (e₂ : D₂.X ≃+ (Fin L.T.r → ℤ)) (β₂ : D₂.P.A.left ⟶ L.T.B.left) (ββ₂ : (G2 D₂.P.A).left ⟶ (G2 L.T.B).left) (w₂ : LB.Iso (abelian₂ D₂.P.A D₂.P.L) ((abelian₂ L.T.B L.T.M.L).pull ββ₂)) (b : D₁.P.A ⟶ D₂.P.A) (φ : D₁.X ≃+ D₂.X) (F : Type) [Field F] [Algebra (FractionRing V) F], D₁.TauBimult → D₂.TauBimult → From L.T ω₁ s₁ ε n D₁ e₁ β₁ ββ₁ w₁ → From L.T ω₂ s₂ ε n D₂ e₂ β₂ ββ₂ w₂ → ω₁.comp L.T.b = ω₂.comp L.T.b → Match D₁ D₂ b φ F → (∀ y, e₂ (φ y) = e₁ y) → (∀ a : Fin L.T.r → ℤ, ∃ (p₁ : QkPt D₁ F n) (p₂ : QkPt D₂ F n), p₁.y = e₁.symm a ∧ TautPt L.T ω₁ s₁ ε n D₁ e₁ β₁ ββ₁ w₁ F a p₁.g ∧ p₂.y = e₂.symm a ∧ TautPt L.T ω₂ s₂ ε n D₂ e₂ β₂ ββ₂ w₂ F a p₂.g ∧ QImg b φ p₁ p₂) → (∀ l : Fin L.h ⊕ Fin L.h → ℤ, ∃ (p₁ : QkPt D₁ F n) (p₂ : QkPt D₂ F n), p₁.y = 0 ∧ p₁.g.b.left ≫ β₁ ≫ L.β = (TF (R := V) F).hom ≫ spMap ω₁ ≫ L.u ≫ (GlobalTheory.LowChart.powA L.F L.T.r).hom ≫ (L.F.univ.lev l).left ∧ p₂.y = 0 ∧ p₂.g.b.left ≫ β₂ ≫ L.β = (TF (R := V) F).hom ≫ spMap ω₂ ≫ L.u ≫ (GlobalTheory.LowChart.powA L.F L.T.r).hom ≫ (L.F.univ.lev l).left ∧ QImg b φ p₁ p₂) → spMap ω₁ ≫ L.u = spMap ω₂ ≫ L.u ∧ (ω₁ = ω₂ → b.left ≫ β₂ = β₁) := by
  intro o _ ζ n L hn hζ hnu I _ ε V _ _ _ D₁ D₂ ω₁ s₁ e₁ β₁ ββ₁ w₁ ω₂ s₂ e₂ β₂ ββ₂ w₂ b φ F _ _ hτ₁ hτ₂ hF₁ hF₂ hω hM he
    hco hlev
  have himg : ∀ (p₁ : QkPt D₁ F n) (p₂ : QkPt D₂ F n), QImg b φ p₁ p₂ → p₂.y = φ p₁.y →
      p₂.g.b.left = p₁.g.b.left ≫ b.left := by
    rintro p₁ p₂ ⟨p', hp'y, hact, heqv⟩ hy
    have hg : p'.g = p₂.g := _root_.GlobalTheory.TInj.qkPt_g_eq_of_equiv V D₂ hτ₂ F n (by omega) p' p₂ (hp'y.trans hy.symm) heqv
    rw [← hg, hact.1, Over.comp_left]
  haveI := hM.2.1
  haveI : IsMonHom (asIso b).hom := hM.1
  set t₁ : Sp V ⟶ L.F.X := spMap ω₁ ≫ L.u ≫ (GlobalTheory.LowChart.powA L.F L.T.r).hom with ht₁
  set t₂ : Sp V ⟶ L.F.X := spMap ω₂ ≫ L.u ≫ (GlobalTheory.LowChart.powA L.F L.T.r).hom with ht₂
  let a₁ : D₁.P.A.left ⟶ L.F.univ.A.left := β₁ ≫ L.β
  let a₂ : D₁.P.A.left ⟶ L.F.univ.A.left := b.left ≫ β₂ ≫ L.β
  let bb : (G2 D₁.P.A).left ⟶ (G2 D₂.P.A).left :=
    (lift (fst D₁.P.A D₁.P.A ≫ b) (snd D₁.P.A D₁.P.A ≫ b) : G2 D₁.P.A ⟶ G2 D₂.P.A).left
  let aa₁ : (G2 D₁.P.A).left ⟶ (G2 L.F.univ.A).left := ββ₁ ≫ L.β₂
  let aa₂ : (G2 D₁.P.A).left ⟶ (G2 L.F.univ.A).left := bb ≫ ββ₂ ≫ L.β₂
  have hpb₁ : IsGrpPullback D₁.P.A L.F.univ.A t₁ a₁ := IsGrpPullback.comp hF₁.1 L.cart
  have hpb₂ : IsGrpPullback D₁.P.A L.F.univ.A t₂ a₂ :=
    (IsGrpPullback.comp (ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_of_iso (asIso b))
      (IsGrpPullback.comp hF₂.1 L.cart)).congr (Category.id_comp _) rfl
  have hbsq : IsSquare b.left bb :=
    ⟨by rw [← Over.comp_left, lift_fst, Over.comp_left], by rw [← Over.comp_left, lift_snd, Over.comp_left]⟩
  have hsq₁ : IsSquare a₁ aa₁ := GlobalTheory.PolDeg.isSquare_comp hF₁.2.1 L.sq
  have hsq₂ : IsSquare a₂ aa₂ := GlobalTheory.PolDeg.isSquare_comp hbsq (GlobalTheory.PolDeg.isSquare_comp hF₂.2.1 L.sq)
  have hLam : ∀ D : DegPre V, (abelian₂ D.P.A D.P.L).IsLB := fun D => LB.isLB_linComb D.P.isLB _ _
  have hLamT : (abelian₂ L.T.B L.T.M.L).IsLB := LB.isLB_linComb L.T.M.isLB _ _
  have hU := L.F.univ.isLB
  have hA₁ : LBIso (abelian₂ D₁.P.A D₁.P.L) (L.F.univ.P.pull aa₁) :=
    LBIso.trans (hLam D₁) (pull_isLB hLamT ββ₁) (pull_isLB hU _) ⟨w₁, hF₁.2.2.1⟩
      (GlobalTheory.PolDeg.lbIso_pull_comp L.lb ββ₁ rfl)
  have hA₂' : LBIso (abelian₂ D₂.P.A D₂.P.L) (L.F.univ.P.pull (ββ₂ ≫ L.β₂)) :=
    LBIso.trans (hLam D₂) (pull_isLB hLamT ββ₂) (pull_isLB hU _) ⟨w₂, hF₂.2.2.1⟩
      (GlobalTheory.PolDeg.lbIso_pull_comp L.lb ββ₂ rfl)
  have hA₂ : LBIso (abelian₂ D₁.P.A D₁.P.L) (L.F.univ.P.pull aa₂) :=
    LBIso.trans (hLam D₁) (pull_isLB (hLam D₂) bb) (pull_isLB hU _) hM.2.2.1
      (GlobalTheory.PolDeg.lbIso_pull_comp hA₂' bb rfl)
  have hP : LBIso (L.F.univ.P.pull aa₁) (L.F.univ.P.pull aa₂) :=
    LBIso.trans (pull_isLB hU _) (hLam D₁) (pull_isLB hU _) hA₁.symm hA₂
  have hs : t₁ ≫ L.F.s = t₂ ≫ L.F.s := by
    have hb : spMap ω₁ ≫ spMap L.T.b = spMap ω₂ ≫ spMap L.T.b := by
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hω]
    have e : ∀ ω : L.W →+* V, (spMap ω ≫ L.u ≫ (GlobalTheory.LowChart.powA L.F L.T.r).hom) ≫ L.F.s = spMap ω ≫ spMap L.T.b := by
      intro ω
      rw [Category.assoc, Category.assoc, ← L.u_base]
      rfl
    rw [ht₁, ht₂, e, e, hb]
  have hlev' : ∀ l, ∃ x : TF (R := V) F ⟶ D₁.P.A,
      x.left ≫ a₁ = (TF (R := V) F).hom ≫ t₁ ≫ (L.F.univ.lev l).left ∧
      x.left ≫ a₂ = (TF (R := V) F).hom ≫ t₂ ≫ (L.F.univ.lev l).left := by
    intro l
    obtain ⟨p₁, p₂, hy₁, hb₁, hy₂, hb₂, hQ⟩ := hlev l
    have h21 := himg p₁ p₂ hQ (by rw [hy₂, hy₁, map_zero])
    refine ⟨p₁.g.b, ?_, ?_⟩
    · simpa only [a₁, ht₁, Category.assoc] using hb₁
    · have : p₁.g.b.left ≫ a₂ = p₂.g.b.left ≫ β₂ ≫ L.β := by
        simp only [a₂, h21, Category.assoc]
      rw [this, hb₂]
      simp only [ht₂, Category.assoc]
  obtain ⟨ht, ha⟩ := GlobalTheory.T.eq_of_presentations_same_polarisation_level L.F hn hζ hnu V D₁.P.A t₁ t₂ a₁ a₂ aa₁ aa₂ hpb₁ hpb₂ hsq₁ hsq₂ hP hs F hlev'
  have hcoordEq : ∀ i, (spMap ω₁ ≫ L.u) ≫ (GlobalTheory.LowChart.coord L.F i).left =
      (spMap ω₂ ≫ L.u) ≫ (GlobalTheory.LowChart.coord L.F i).left := by
    intro i
    obtain ⟨p₁, p₂, hy₁, hT₁, hy₂, hT₂, hQ⟩ := hco (Pi.single i 1)
    have hφ : p₂.y = φ p₁.y := by
      rw [hy₂, hy₁]
      apply e₂.injective
      rw [he, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    have h21 := himg p₁ p₂ hQ hφ
    have c1 : (TF (R := V) F).hom ≫ (spMap ω₁ ≫ L.u) ≫ (GlobalTheory.LowChart.coord L.F i).left = p₁.g.b.left ≫ a₁ := by
      simp only [a₁, Category.assoc, ← L.coord i]
      rw [← Category.assoc p₁.g.b.left, hT₁.1]
      simp only [Category.assoc]
    have c2 : (TF (R := V) F).hom ≫ (spMap ω₂ ≫ L.u) ≫ (GlobalTheory.LowChart.coord L.F i).left = p₁.g.b.left ≫ a₂ := by
      simp only [a₂, Category.assoc, ← L.coord i]
      rw [← Category.assoc p₁.g.b.left, ← h21, ← Category.assoc p₂.g.b.left, hT₂.1]
      simp only [Category.assoc]
    have hgen : (TF (R := V) F).hom ≫ (spMap ω₁ ≫ L.u) ≫ (GlobalTheory.LowChart.coord L.F i).left =
        (TF (R := V) F).hom ≫ (spMap ω₂ ≫ L.u) ≫ (GlobalTheory.LowChart.coord L.F i).left := by
      rw [c1, c2, ha]
    have : IsProper L.F.univ.A.hom := L.F.univ.ab.proper
    haveI : IsDominant (TF (R := V) F).hom := ReciprocityTheory.ChartRestriction.G.DVR.GC.isDominant_jFR (V := V) F
    refine ext_of_isDominant_of_isSeparated L.F.univ.A.hom ?_ (TF (R := V) F).hom hgen
    simp only [Category.assoc, Over.w]
    exact ht
  refine ⟨GlobalTheory.LowChart.hom_ext _ _ (by simpa only [Category.assoc] using ht) hcoordEq, ?_⟩
  rintro rfl
  apply L.cart.1.hom_ext
  · simpa only [a₁, a₂, Category.assoc] using ha.symm
  · rw [Category.assoc, hF₂.1.1.w, ← Category.assoc, Over.w b, hF₁.1.1.w]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelSetWittFrameSchwartzBoundStatement
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_set_witt_frame_schwartz_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E),
    GlobalTheory.SiegelSet.IsWittFrame σ ((1 : E) • X.J.map σ) Xf Yf → ∀ c : ℝ, 0 < c →
    ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ t ∈ GlobalTheory.SiegelSet.cone r₀ c, ∀ a,
      GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • X.J.map σ) Xf Yf t a → ∀ a' : UA σ X.J,
      (a' : GL (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = HA.mat (AF F) σ ((1 : E) • X.J.map σ) a → ∀ (y : UA σ X.J) (h : UA σ W.J),
      ‖theta om Φ (a' * y) h‖ ≤ C * ((ht y : ℝ) * ht h) ^ k * ∏ i, t i ^ (Module.finrank ℚ F * d) := by
  first | exact @GlobalTheory.TorusTheta.theta_torus_le | exact GlobalTheory.TorusTheta.theta_torus_le | (intros; apply GlobalTheory.TorusTheta.theta_torus_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothDimTensor
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.ProdDim

theorem smoothDim_tensor {S : Scheme.{0}} {A B : Over S} {g g' : ℕ} (hg : SmoothOfRelativeDimension g A.hom)
    (hg' : SmoothOfRelativeDimension g' B.hom) : SmoothOfRelativeDimension (g' + g) (A ⊗ B).hom := by
  have : SmoothOfRelativeDimension g' (Limits.pullback.fst A.hom B.hom) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g').of_isPullback
      (IsPullback.of_hasPullback A.hom B.hom).flip hg'
  rw [Over.tensorObj_hom]
  exact smoothOfRelativeDimension_comp g' g _ _

theorem g_eq_add : ∀ (S : Scheme.{0}) (P P₁ P₂ : PolAV S) (a₁ : P.A ⟶ P₁.A) (a₂ : P.A ⟶ P₂.A),
    Nonempty S → IsIso (lift a₁ a₂) → P.g = P₁.g + P₂.g := by
  intro S P P₁ P₂ a₁ a₂ ⟨s⟩ hi
  have h := smoothDim_tensor P₁.smoothDim P₂.smoothDim
  haveI : IsIso (lift a₁ a₂).left := inferInstanceAs (IsIso ((Over.forget S).map (lift a₁ a₂)))
  have hw : (lift a₁ a₂).left ≫ (P₁.A ⊗ P₂.A).hom = P.A.hom := Over.w _
  have h2 : SmoothOfRelativeDimension (0 + (P₂.g + P₁.g)) P.A.hom := by
    rw [← hw]
    exact smoothOfRelativeDimension_comp 0 (P₂.g + P₁.g) _ _
  have := ReciprocityTheory.ChartRestriction.G.H1.dim_unique P.A.hom P.smoothDim h2 (eSec P.A s)
  omega

end GlobalTheory.ProdDim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVolumeDensityFiniteIsOpenPos
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp.VolFin

open GlobalTheory.ChartGlue
open scoped ENNReal

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

theorem meas_eq [SecondCountableTopology (CxPts p σ)] (ω : VolDens p σ D) (c : AlgChart p σ D)
    {S : Set (CxPts p σ)} (hS : MeasurableSet S) (hc : S ⊆ c.e.source) :
    ω.meas S = ∫⁻ v in c.e '' S, ENNReal.ofReal (ω.dens c (c.e.symm v)) := by
  rw [VolDens.meas, glueMeas_apply _ _ (fun c c' => c.holo_trans c') (fun c c' y hy hy' => by
    rw [ω.trans c c' y hy hy', ENNReal.ofReal_mul (sq_nonneg _)]) c hS hc,
    chartMeas_apply_of_subset _ _ hS hc]

theorem continuousOn_dens (ω : VolDens p σ D) (c : AlgChart p σ D) :
    ContinuousOn (fun v => ω.dens c (c.e.symm v)) c.e.target :=
  (ω.cont c).comp c.e.continuousOn_symm fun _ hv => c.e.map_target hv

theorem exists_open_lt_top [SecondCountableTopology (CxPts p σ)] (ω : VolDens p σ D)
    (c : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source) :
    ∃ O : Set (CxPts p σ), IsOpen O ∧ y ∈ O ∧ ω.meas O < ∞ := by
  set g := fun v => ω.dens c (c.e.symm v)
  have hv0 : c.e y ∈ c.e.target := c.e.map_source hy
  have hg : ContinuousAt g (c.e y) :=
    (continuousOn_dens ω c).continuousAt (c.e.open_target.mem_nhds hv0)
  have h1 : ∀ᶠ v in 𝓝 (c.e y), g v < g (c.e y) + 1 :=
    hg.eventually (gt_mem_nhds (lt_add_one _))
  have h2 : ∀ᶠ v in 𝓝 (c.e y), v ∈ c.e.target := c.e.open_target.mem_nhds hv0
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (h1.and h2)
  refine ⟨c.e.source ∩ c.e ⁻¹' Metric.ball (c.e y) ε,
    c.e.isOpen_inter_preimage Metric.isOpen_ball, ⟨hy, Set.mem_preimage.mpr (Metric.mem_ball_self hε)⟩, ?_⟩
  have hO : MeasurableSet (c.e.source ∩ c.e ⁻¹' Metric.ball (c.e y) ε) :=
    (c.e.isOpen_inter_preimage Metric.isOpen_ball).measurableSet
  rw [meas_eq ω c hO Set.inter_subset_left]
  have hsub : c.e '' (c.e.source ∩ c.e ⁻¹' Metric.ball (c.e y) ε) ⊆ Metric.ball (c.e y) ε := by
    rintro _ ⟨z, hz, rfl⟩; exact hz.2
  calc ∫⁻ v in c.e '' (c.e.source ∩ c.e ⁻¹' Metric.ball (c.e y) ε), ENNReal.ofReal (g v)
      ≤ ∫⁻ v in Metric.ball (c.e y) ε, ENNReal.ofReal (g v) :=
        lintegral_mono' (Measure.restrict_mono hsub le_rfl) le_rfl
    _ ≤ ∫⁻ _ in Metric.ball (c.e y) ε, ENNReal.ofReal (g (c.e y) + 1) := by
        refine lintegral_mono_ae (ae_restrict_of_forall_mem Metric.isOpen_ball.measurableSet
          fun v hv => ENNReal.ofReal_le_ofReal (hball v hv).1.le)
    _ = ENNReal.ofReal (g (c.e y) + 1) * volume (Metric.ball (c.e y) ε) := setLIntegral_const _ _
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top

theorem meas_pos [SecondCountableTopology (CxPts p σ)] (ω : VolDens p σ D)
    (c : AlgChart p σ D) {U : Set (CxPts p σ)} (hU : IsOpen U) {y : CxPts p σ} (hy : y ∈ c.e.source)
    (hyU : y ∈ U) : ω.meas U ≠ 0 := by
  set g := fun v => ω.dens c (c.e.symm v)
  have hv0 : c.e y ∈ c.e.target := c.e.map_source hy
  have hg : ContinuousAt g (c.e y) :=
    (continuousOn_dens ω c).continuousAt (c.e.open_target.mem_nhds hv0)
  have hpos : 0 < g (c.e y) := by
    simp only [g, c.e.left_inv hy]; exact ω.pos c y hy
  have h1 : ∀ᶠ v in 𝓝 (c.e y), g (c.e y) / 2 < g v :=
    hg.eventually (lt_mem_nhds (half_lt_self hpos))
  have h2 : ∀ᶠ v in 𝓝 (c.e y), v ∈ c.e.target ∩ c.e.symm ⁻¹' U :=
    (isOpen_over c.e hU).mem_nhds (mem_over c.e hy hyU)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (h1.and h2)
  have hA : MeasurableSet (c.e.source ∩ U) := (c.e.open_source.inter hU).measurableSet
  have hsub : Metric.ball (c.e y) ε ⊆ c.e '' (c.e.source ∩ U) := by
    rw [c.e.image_source_inter_eq']; exact fun v hv => (hball v hv).2
  refine (lt_of_lt_of_le ?_ (measure_mono (μ := ω.meas) (Set.inter_subset_right :
    c.e.source ∩ U ⊆ U))).ne'
  rw [meas_eq ω c hA Set.inter_subset_left]
  calc (0 : ℝ≥0∞) < ENNReal.ofReal (g (c.e y) / 2) * volume (Metric.ball (c.e y) ε) :=
        ENNReal.mul_pos (ENNReal.ofReal_pos.2 (half_pos hpos)).ne' (Metric.measure_ball_pos _ _ hε).ne'
    _ = ∫⁻ _ in Metric.ball (c.e y) ε, ENNReal.ofReal (g (c.e y) / 2) := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ v in Metric.ball (c.e y) ε, ENNReal.ofReal (g v) :=
        lintegral_mono_ae (ae_restrict_of_forall_mem Metric.isOpen_ball.measurableSet
          fun v hv => ENNReal.ofReal_le_ofReal (hball v hv).1.le)
    _ ≤ ∫⁻ v in c.e '' (c.e.source ∩ U), ENNReal.ofReal (g v) :=
        lintegral_mono' (Measure.restrict_mono hsub le_rfl) le_rfl

end GlobalTheory.HSAmp.VolFin


open GlobalTheory.HSAmp.VolFin in
theorem GlobalTheory.HSAmp.volDens_meas_finite_openPos : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (σ : k →+* ℂ) (ω : VolDens p σ D),
    IsFiniteMeasure ω.meas ∧ ω.meas.IsOpenPosMeasure := by
  intro k _ X _ p D hX hS σ ω
  haveI := CxPts.secondCountableTopology_of_isProjOver σ hX.isProjOver
  haveI := hX.compactSpace σ
  obtain ⟨R⟩ := hS σ
  haveI : IsLocallyFiniteMeasure ω.meas := ⟨fun y => by
    obtain ⟨i, hi⟩ := R.cover y
    obtain ⟨O, hO, hyO, hfin⟩ := exists_open_lt_top ω (R.chart i) hi
    exact ⟨O, hO.mem_nhds hyO, hfin⟩⟩
  refine ⟨inferInstance, ⟨fun U hU ⟨y, hyU⟩ => ?_⟩⟩
  obtain ⟨i, hi⟩ := R.cover y
  exact meas_pos ω (R.chart i) hU hi hyU
end
end

