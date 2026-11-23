module

public import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.Bundle0005
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
public import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Action
public import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Places
public import Development.AutomorphicArithmetic.AdelicQuotients.Bundle0007
public import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.CentralSectionBaseChange
section
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.IdeleGroup

noncomputable section


open Classical in
private def psi {K : Type} [Field K] (w : InfinitePlace K) : ℝ →+* w.Completion :=
  if hw : w.IsReal then ((ringEquivRealOfIsReal hw).symm : ℝ ≃+* w.Completion).toRingHom
  else ((ringEquivComplexOfIsComplex (not_isReal_iff_isComplex.1 hw)).symm : ℂ ≃+* w.Completion).toRingHom.comp
    Complex.ofRealHom

private theorem continuous_psi {K : Type} [Field K] (w : InfinitePlace K) : Continuous (psi w) := by
  unfold psi
  split_ifs with hw
  · exact (isometryEquivRealOfIsReal hw).symm.continuous
  · exact (isometryEquivComplexOfIsComplex (not_isReal_iff_isComplex.1 hw)).symm.continuous.comp
      Complex.continuous_ofReal

private theorem posRealElem_eq {K : Type} [Field K] (w : InfinitePlace K) {ρ : ℝ} (hρ : 0 < ρ) :
    posRealElem w (ρ ^ w.mult) = psi w ρ := by
  unfold posRealElem psi
  split_ifs with hw
  · simp [InfinitePlace.mult, hw]
  · simp [InfinitePlace.mult, hw, Real.sqrt_sq hρ.le]

private theorem real_hom_unique {A : Type} [Field A] [TopologicalSpace A] [T2Space A] (f g : ℝ →+* A)
    (hf : Continuous f) (hg : Continuous g) : f = g := by
  have h := Rat.denseRange_cast (𝕜 := ℝ) |>.equalizer hf hg (funext fun q => by simp)
  exact RingHom.ext (congrFun h)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem posIdele_fst {K : Type} [Field K] [NumberField K] (ρ : ℝ) (hρ : 0 < ρ) (w : InfinitePlace K) :
    ((posIdele ρ hρ : IdeleGroup K) : NumberField.AdeleRing (𝓞 K) K).1 w = psi w ρ := by
  rw [← coe_infiniteProj, infiniteProj_posIdele]
  exact posRealElem_eq w hρ

private theorem inf_posIdele (ρ : ℝ) (hρ : 0 < ρ) (w : InfinitePlace E) :
    InfinitePlace.infiniteAdeleRingMap (K := F) (L := E) (((posIdele ρ hρ : IdeleGroup F) : NumberField.AdeleRing (𝓞 F) F).1) w =
      ((posIdele ρ hρ : IdeleGroup E) : NumberField.AdeleRing (𝓞 E) E).1 w := by
  have hx : ((posIdele ρ hρ : IdeleGroup F) : NumberField.AdeleRing (𝓞 F) F).1 =
      (RingHom.pi fun v : InfinitePlace F => psi v) ρ := funext fun v => posIdele_fst ρ hρ v
  rw [hx, posIdele_fst]
  have hc : Continuous (((Pi.evalRingHom (fun w : InfinitePlace E => w.Completion) w).comp
      (InfinitePlace.infiniteAdeleRingMap (K := F) (L := E))).comp
        (RingHom.pi fun v : InfinitePlace F => psi v)) :=
    (continuous_apply w).comp (InfinitePlace.continuous_infiniteAdeleRingMap.comp
      (continuous_pi fun v => continuous_psi v))
  exact congrArg (fun f : ℝ →+* w.Completion => f ρ) (real_hom_unique _ (psi w) hc (continuous_psi w))

private theorem fin_posIdele {K : Type} [Field K] [NumberField K] (ρ : ℝ) (hρ : 0 < ρ) :
    ((posIdele ρ hρ : IdeleGroup K) : NumberField.AdeleRing (𝓞 K) K).2 = 1 :=
  IsDedekindDomain.FiniteAdeleRing.ext K fun v => posIdele_finite ρ hρ v

private theorem adeleMap_posIdele (ρ : ℝ) (hρ : 0 < ρ) :
    AdeleBaseChange.adeleMap F E ((posIdele ρ hρ : IdeleGroup F) : NumberField.AdeleRing (𝓞 F) F) =
      ((posIdele ρ hρ : IdeleGroup E) : NumberField.AdeleRing (𝓞 E) E) := by
  rw [AdeleBaseChange.adeleMap_apply]
  refine Prod.ext (funext fun w => inf_posIdele ρ hρ w) ?_
  change AdeleBaseChange.finiteAdeleMap F E _ = _
  rw [fin_posIdele, fin_posIdele, map_one]

private theorem exponent (n : ℕ) (hn : 0 < n) (s : {r : ℝ // 0 < r}) :
    rpowHom ((n * Module.finrank ℚ E : ℝ))⁻¹ (s ^ Module.finrank F E) =
      rpowHom ((n * Module.finrank ℚ F : ℝ))⁻¹ s := by
  refine Subtype.ext ?_
  change ((s ^ Module.finrank F E : {r : ℝ // 0 < r}) : ℝ) ^ ((n * Module.finrank ℚ E : ℝ))⁻¹ =
    (s : ℝ) ^ ((n * Module.finrank ℚ F : ℝ))⁻¹
  have hk : Module.finrank ℚ F * Module.finrank F E = Module.finrank ℚ E := Module.finrank_mul_finrank ℚ F E
  have hk0 : (Module.finrank F E : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have hd : (Module.finrank ℚ F : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  rw [Positive.val_pow, ← Real.rpow_natCast, ← Real.rpow_mul s.2.le, ← hk]
  congr 1
  push_cast
  field_simp

theorem UpperTheory.centralSection_baseChange :
    CentBC := by
  intro F E _ _ _ _ _ n s
  refine Units.ext (Matrix.ext fun i j => ?_)
  have hn : 0 < n := i.pos
  have h1 : centralSection E n (s ^ Module.finrank F E) =
      diagUnits n fun _ => posIdeleHom E (rpowHom ((n * Module.finrank ℚ F : ℝ))⁻¹ s) := by
    rw [centralSection, MonoidHom.comp_apply, MonoidHom.comp_apply, exponent n hn, scalarUnits_apply]
  have h2 : centralSection F n s =
      diagUnits n fun _ => posIdeleHom F (rpowHom ((n * Module.finrank ℚ F : ℝ))⁻¹ s) := by
    rw [centralSection, MonoidHom.comp_apply, MonoidHom.comp_apply, scalarUnits_apply]
  rw [h1, h2, coe_diagUnits]
  change AdeleBaseChange.adeleMap F E (((diagUnits n fun _ => posIdeleHom F _ : AdelicGLn.AdelicGL F n)).val i j) = _
  rw [coe_diagUnits]
  by_cases h : i = j
  · subst h
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, posIdeleHom_apply, posIdeleHom_apply]
    exact adeleMap_posIdele _ _
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h, map_zero]
end
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.CentralSectionLocalScalar
section
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4

open NumberField IsDedekindDomain GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global.SemiLocal

private theorem centralSection_val (K : Type) [Field K] [NumberField K] (n : ℕ) (s : {r : ℝ // 0 < r}) :
    ∃ u : GroundTheory.Global.IdeleGroup K, (∀ v, ((u : GroundTheory.Global.IdeleGroup K) : AdeleRing (𝓞 K) K).2 v = 1) ∧
      ((centralSection K n s : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) (AdeleRing (𝓞 K) K)) =
        Matrix.diagonal fun _ => ((u : GroundTheory.Global.IdeleGroup K) : AdeleRing (𝓞 K) K) := by
  refine ⟨posIdeleHom K (rpowHom ((n * Module.finrank ℚ K : ℝ))⁻¹ s), fun v => ?_, ?_⟩
  · rw [posIdeleHom_apply]
    exact posIdele_finite _ _ v
  · rw [centralSection, MonoidHom.comp_apply, MonoidHom.comp_apply, scalarUnits_apply, coe_diagUnits]

theorem UpperTheory.centralSection_local_scalar :
    CentLoc := by
  intro K _ _ n s
  obtain ⟨u, hf, hu⟩ := centralSection_val K n s
  have hI : ∀ i j, ((pI K n (centralSection K n s) : GL (Fin n) (InfiniteAdeleRing K)) :
      Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)) i j =
      (Matrix.diagonal fun _ => ((u : GroundTheory.Global.IdeleGroup K) : AdeleRing (𝓞 K) K).1 :
        Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)) i j := by
    intro i j
    change (((centralSection K n s : AdelicGLn.AdelicGL K n) :
      Matrix (Fin n) (Fin n) (AdeleRing (𝓞 K) K)) i j).1 = _
    rw [hu]
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h]
      rfl
  have hI' : ((pI K n (centralSection K n s) : GL (Fin n) (InfiniteAdeleRing K)) :
      Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)) =
      Matrix.diagonal fun _ => ((u : GroundTheory.Global.IdeleGroup K) : AdeleRing (𝓞 K) K).1 :=
    Matrix.ext hI
  have hF : ∀ (i j : Fin n), (((centralSection K n s : AdelicGLn.AdelicGL K n) :
      Matrix (Fin n) (Fin n) (AdeleRing (𝓞 K) K)) i j).2 =
      ((1 : Matrix (Fin n) (Fin n) (AdeleRing (𝓞 K) K)) i j).2 := by
    intro i j
    rw [hu]
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      exact FiniteAdeleRing.ext K hf
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
  refine ⟨⟨Units.map (RingHom.toMonoidHom (α := AdeleRing (𝓞 K) K) (β := InfiniteAdeleRing K) (RingHom.fst _ _)) u, fun g => ?_⟩,
    fun g => ?_, fun v => ?_, fun F _ _ _ v => ?_⟩
  · rw [Units.val_mul, hI']
    ext i j
    rw [Matrix.diagonal_mul]
    rfl
  · refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, hI']
    ext i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]
  · refine Units.ext (Matrix.ext fun i j => ?_)
    rw [pF_apply]
    change (((centralSection K n s : AdelicGLn.AdelicGL K n) :
      Matrix (Fin n) (Fin n) (AdeleRing (𝓞 K) K)) i j).2 v = (1 : Matrix (Fin n) (Fin n) _) i j
    rw [hF]
    by_cases h : i = j
    · subst h
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
      rfl
    · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h]
      rfl
  · refine Units.ext (Matrix.ext fun i j => funext fun w => ?_)
    change (((centralSection K n s : AdelicGLn.AdelicGL K n) :
      Matrix (Fin n) (Fin n) (AdeleRing (𝓞 K) K)) i j).2 w.1 = (1 : Matrix (Fin n) (Fin n) (CompletionsOver K v)) i j w
    rw [hF]
    by_cases h : i = j
    · subst h
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
      rfl
    · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h]
      rfl
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.FinAtMapGLGalAdMemIwahori
section
open NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped NumberField.AdeleRing

private theorem val_lt_iff' {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (y : w.adicCompletion E) : ValuativeRel.valuation (w.adicCompletion E) y < 1 ↔ ‖y‖ < 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [(ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))).lt_one_iff_lt_one,
    Valued.toNormedField.norm_lt_one_iff]

private theorem val_le_iff' {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (y : w.adicCompletion E) : ValuativeRel.valuation (w.adicCompletion E) y ≤ 1 ↔ ‖y‖ ≤ 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [(ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))).le_one_iff_le_one,
    Valued.toNormedField.norm_le_one_iff]

private theorem val_eq_iff' {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (y : w.adicCompletion E) : ValuativeRel.valuation (w.adicCompletion E) y = 1 ↔ ‖y‖ = 1 := by
  rw [le_antisymm_iff, le_antisymm_iff, val_le_iff', not_iff_not.1 (by
    rw [not_le, not_le]; exact val_lt_iff' w y : ¬ (1 ≤ ValuativeRel.valuation (w.adicCompletion E) y) ↔ ¬ (1 ≤ ‖y‖))]

theorem UpperTheory.finAt_mapGL_galAd_mem_iwahori :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (n : ℕ) (w : HeightOneSpectrum (𝓞 E)) (g : AdelicGLn.AdelicGL E n),
        finAt w g ∈ GLnLocal.iwahori (w.adicCompletion E) n →
        finAt (σ • w) (mapGL n (galAd σ) g : AdelicGLn.AdelicGL E n) ∈ GLnLocal.iwahori ((σ • w).adicCompletion E) n := by
  intro F E _ _ _ _ _ σ n w g hg
  have key : ∀ i j, ‖finAt (σ • w) (mapGL n (galAd σ) g : AdelicGLn.AdelicGL E n) i j‖ = ‖finAt w g i j‖ :=
    fun i j => (UpperTheory.norm_galois_smul_adele_component_at_smul_place F E σ (g i j)).1 w
  obtain ⟨h1, h2, h3⟩ := (GLnLocal.mem_iwahori_iff _ n).1 hg
  refine (GLnLocal.mem_iwahori_iff _ n).2 ⟨fun i j => ?_, fun i j hij => ?_, fun i => ?_⟩
  · rw [val_le_iff', key]; exact (val_le_iff' w _).1 (h1 i j)
  · rw [val_lt_iff', key]; exact (val_lt_iff' w _).1 (h2 i j hij)
  · rw [val_eq_iff', key]; exact (val_eq_iff' w _).1 (h3 i)
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.GlobalOrbitalComparisonOfSplit
section
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.AdeleBaseChange PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc

private theorem cenClosed {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (g : G) :
    IsClosed ((Subgroup.centralizer {g} : Subgroup G) : Set G) := by
  have h : ((Subgroup.centralizer {g} : Subgroup G) : Set G) = {x | g * x = x * g} := by
    ext x
    exact Subgroup.mem_centralizer_singleton_iff.trans eq_comm
  rw [h]
  exact isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)

private theorem cenLC {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] (g : G) : LocallyCompactSpace (Subgroup.centralizer {g} : Subgroup G) :=
  (cenClosed g).isClosedEmbedding_subtypeVal.locallyCompactSpace

private theorem diag_mem {E : Type} [Field E] [NumberField E] {n : ℕ} (δ : GL (Fin n) E) :
    detModule E n (AdelicGLn.diagonal E n δ) = 1 :=
  mem_normOneGL_iff_detModule.1 (rationalGL_le_normOneGL ⟨δ, rfl⟩)

theorem UpperTheory.globalOrbitalComparison_of_split :
    QSub → SplitQ → UniOf → TComm → Spl → N3 → N5 → CentBC → Glob := by
  intro hQ hS hU hT hSpl hN3 hN5 _ F E _ _ _ _ _ _ σ hσ n hn μE μF hE hF
  obtain ⟨⟨eE, heE⟩, hG⟩ := hSpl F E σ hσ n hn
  let l : Measure {r : ℝ // 0 < r} := Measure.haar
  have hl : Uni l := (hU _ l inferInstance).2 mul_comm
  have hUE : Uni μE := (hU _ μE hE).1 inferInstance
  have hUF : Uni μF := (hU _ μF hF).1 inferInstance
  let eF : G1 F n × {r : ℝ // 0 < r} ≃ₜ* GA F n := (glNormOneSplitting (K := F) hn).symm
  refine ⟨(μE.prod l).map eE, (μF.prod l).map eF, ?_, ?_, ?_⟩
  · exact (hS (G1 E n) (G1 E n) _ (GA E n) (GA E n) μE (MonoidHom.id _) μE l
      ⟨hUE, Topology.IsClosedEmbedding.id, hUE⟩ hl eE eE (MonoidHom.id _) (fun _ => rfl)).1.1
  · exact (hS (G1 F n) (G1 F n) _ (GA F n) (GA F n) μF (MonoidHom.id _) μF l
      ⟨hUF, Topology.IsClosedEmbedding.id, hUF⟩ hl eF eF (MonoidHom.id _) (fun _ => rfl)).1.1
  intro γ γ₁ hγ hreg ν hν
  obtain ⟨⟨eT, heT⟩, j, hj, hjv⟩ := hG γ γ₁ hγ
  haveI : LocallyCompactSpace (Subgroup.centralizer {γ₁} : Subgroup (G1 F n)) := cenLC γ₁
  haveI : SecondCountableTopology (Subgroup.centralizer {γ₁} : Subgroup (G1 F n)) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  haveI : LocallyCompactSpace (TA γ) := cenLC _
  haveI : SecondCountableTopology (TA γ) := TopologicalSpace.Subtype.secondCountableTopology _
  have hUν : Uni ν := (hU _ ν hν).2 ((hT F n γ hreg).2.2.2 γ₁ hγ)
  have hPF : Pair μF (Subgroup.centralizer {γ₁} : Subgroup (G1 F n)).subtype ν :=
    ⟨hUF, (cenClosed γ₁).isClosedEmbedding_subtypeVal, hUν⟩
  have sF := hS (G1 F n) (Subgroup.centralizer {γ₁} : Subgroup (G1 F n)) _ (GA F n) (TA γ) μF
    (Subgroup.centralizer {γ₁} : Subgroup (G1 F n)).subtype ν l hPF hl eF eT (TA γ).subtype
    (fun x => heT x)
  have hPE : Pair μE j ν := ⟨hUE, hj, hUν⟩
  have sE := hS (G1 E n) (Subgroup.centralizer {γ₁} : Subgroup (G1 F n)) _ (GA E n) (TA γ) μE j ν l hPE hl eE eT
    ((mapGL n (adeleMap F E)).comp (TA γ).subtype)
    (fun x => by
      rw [heE, MonoidHom.comp_apply, Subgroup.subtype_apply, heT, map_mul, hjv])
  refine ⟨(ν.prod l).map eT, sF.1.2.2.1, ?_, ?_⟩
  · intro Φ hΦ
    have inv : ∀ (t : TA γ) (g : GA F n), FF γ Φ ((TA γ).subtype t * g) = FF γ Φ g := by
      intro t g
      have ht : (t : GA F n) * AdelicGLn.diagonal F n γ = AdelicGLn.diagonal F n γ * t :=
        Subgroup.mem_centralizer_singleton_iff.1 t.2
      have hc : ((t : GA F n) * g)⁻¹ * AdelicGLn.diagonal F n γ * ((t : GA F n) * g) =
          g⁻¹ * AdelicGLn.diagonal F n γ * g := by
        rw [_root_.mul_inv_rev, mul_assoc g⁻¹, mul_assoc g⁻¹, mul_assoc, ← mul_assoc _ (t : GA F n) g, ← ht]
        group
      simp only [FF, Subgroup.subtype_apply, hc]
    rw [← (sF.2 (FF γ Φ) hΦ inv)]
    have hx : (fun x : G1 F n => FF γ Φ (eF (x, 1))) = fun x => avg Φ (x⁻¹ * γ₁ * x) := by
      funext x
      have h1 : eF (x, 1) = (x : GA F n) := by
        change (x : GA F n) * centralSection F n 1 = x
        rw [map_one, mul_one]
      rw [h1]
      simp only [FF, avg, Subgroup.coe_mul, Subgroup.coe_inv, hγ]
    rw [hx]
    rfl
  · intro δ hδ Φ hΦ
    have inv : ∀ (t : TA γ) (g : GA E n),
        FE σ δ Φ (((mapGL n (adeleMap F E)).comp (TA γ).subtype) t * g) = FE σ δ Φ g := by
      intro t g
      have ht : (t : GA F n) * AdelicGLn.diagonal F n γ = AdelicGLn.diagonal F n γ * t :=
        Subgroup.mem_centralizer_singleton_iff.1 t.2
      have h3 := (hN3 F E σ hσ n hn δ γ hreg hδ (mapGL n (adeleMap F E) (t : GA F n))).2 ⟨t, ht, rfl⟩
      have hc : (mapGL n (adeleMap F E) (t : GA F n) * g)⁻¹ * AdelicGLn.diagonal E n δ *
            mapGL n (galAd σ) (mapGL n (adeleMap F E) (t : GA F n) * g) =
          g⁻¹ * AdelicGLn.diagonal E n δ * mapGL n (galAd σ) g := by
        rw [map_mul, _root_.mul_inv_rev]
        calc _ = g⁻¹ * ((mapGL n (adeleMap F E) (t : GA F n))⁻¹ * AdelicGLn.diagonal E n δ *
              mapGL n (galAd σ) (mapGL n (adeleMap F E) (t : GA F n))) * mapGL n (galAd σ) g := by group
          _ = _ := by rw [h3]
      simp only [FE, MonoidHom.comp_apply, Subgroup.subtype_apply, hc]
    rw [← (sE.2 (FE σ δ Φ) hΦ inv)]
    have h1 : ∀ x : G1 E n, eE (x, 1) = (x : GA E n) := by
      intro x
      rw [heE]
      simp only [map_one, mul_one]
    have hm : ∀ x : G1 E n, (x : GA E n)⁻¹ * AdelicGLn.diagonal E n δ * mapGL n (galAd σ) (x : GA E n) ∈
        normOneGL (K := E) (n := n) := by
      intro x
      have hx : detModule E n (x : GA E n) = 1 := mem_normOneGL_iff_detModule.1 x.2
      rw [mem_normOneGL_iff_detModule, map_mul, map_mul, map_inv, (hN5 F E σ hσ n hn).2.2, hx, diag_mem]
      simp
    have hx : (fun x : G1 E n => ext0 (avg Φ) ((x : GA E n)⁻¹ * AdelicGLn.diagonal E n δ *
        mapGL n (galAd σ) (x : GA E n))) = fun x => FE σ δ Φ (eE (x, 1)) := by
      funext x
      rw [h1, ext0, dite_eq_left (hm x)]
      rfl
    rw [hx]
    have hmeas : Measurable fun x : G1 E n => FE σ δ Φ (eE (x, 1)) := by
      simp only [h1]
      exact hΦ.comp measurable_subtype_coe
    have hinv : ∀ (t : Subgroup.centralizer {γ₁}) (g : G1 E n),
        FE σ δ Φ (eE (j t * g, 1)) = FE σ δ Φ (eE (g, 1)) := by
      intro t g
      have h2 := inv (eT (t, 1)) (g : GA E n)
      have h4 : ((mapGL n (adeleMap F E)).comp (TA γ).subtype) (eT (t, 1)) = (j t : GA E n) := by
        rw [MonoidHom.comp_apply, Subgroup.subtype_apply, heT, hjv]
        simp only [map_one, mul_one]
      rw [h4] at h2
      rw [h1, h1]
      simpa using h2
    have hq := hQ (GA E n) (Subgroup.centralizer {γ₁} : Subgroup (G1 F n)) (normOneGL (K := E) (n := n)) isClosed_normOneGL
      μE j ν hPE _ hmeas hinv
    have hj' : (fun t : Subgroup.centralizer {γ₁} => (j t : GA E n)) =
        fun t : Subgroup.centralizer {γ₁} => mapGL n (adeleMap F E) ((t : G1 F n) : GA F n) := funext hjv
    rw [hj'] at hq
    exact hq
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.HaarQuotientSubgroup
section
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open MeasureTheory

theorem UpperTheory.haar_quotient_subgroup :
    QSub := by
  intro G _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ H hH μ j ν hp Φ hΦ hi
  haveI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology (H : Set G)
  obtain ⟨ρ₀, -, hρ₀, -⟩ := normEx H T μ j ν hp
  have hemb : MeasurableEmbedding (Subtype.val : H → G) := MeasurableEmbedding.subtype_coe hH.measurableSet
  have hinj : Function.Injective (Subtype.val : H → G) := Subtype.val_injective
  have hex : ∃ ρ, IsNormAlong (fun x : H => (x : G)) (fun t => (j t : G)) ν ρ := by
    refine ⟨Function.extend Subtype.val (fun x : H => (ρ₀ x : ENNReal)) 0,
      hemb.measurable_extend hρ₀.1 measurable_const, fun x => ?_⟩
    have e : ∀ t, Function.extend Subtype.val (fun x : H => (ρ₀ x : ENNReal)) 0 ((j t : G) * (x : G))
        = (ρ₀ (j t * x) : ENNReal) := fun t => by
      rw [← Subgroup.coe_mul]
      exact hinj.extend_apply _ _ _
    simp only [e]
    exact hρ₀.2 x
  unfold quotInt
  rw [dite_eq_left hex]
  have hn : IsNrm j ν (fun x : H => hex.choose (x : G)) :=
    ⟨hex.choose_spec.1.comp measurable_subtype_coe, fun x => by
      simpa only [Subgroup.coe_mul] using hex.choose_spec.2 x⟩
  exact ((quotEq H T μ j ν hp Φ hΦ hi _ hn).2.2).symm
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.HeightOffMapGLGalAd
section
open NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped NumberField.AdeleRing

private theorem locHeight_congr {A B : Type*} [NormedField A] [NormedField B] {n : ℕ}
    (g : GL (Fin n) A) (h : GL (Fin n) B)
    (h₁ : ∀ i j, ‖(g : Matrix (Fin n) (Fin n) A) i j‖ = ‖(h : Matrix (Fin n) (Fin n) B) i j‖)
    (h₂ : ∀ i j, ‖((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) i j‖ =
      ‖((h⁻¹ : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) i j‖) :
    AutomorphicForm.locHeight g = AutomorphicForm.locHeight h :=
  le_antisymm
    (AutomorphicForm.locHeight_le (AutomorphicForm.one_le_locHeight h)
      (fun i j => (h₁ i j).le.trans (AutomorphicForm.norm_apply_le_locHeight h i j))
      (fun i j => (h₂ i j).le.trans (AutomorphicForm.norm_inv_apply_le_locHeight h i j)))
    (AutomorphicForm.locHeight_le (AutomorphicForm.one_le_locHeight g)
      (fun i j => (h₁ i j).ge.trans (AutomorphicForm.norm_apply_le_locHeight g i j))
      (fun i j => (h₂ i j).ge.trans (AutomorphicForm.norm_inv_apply_le_locHeight g i j)))

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem fin_norm (σ : E ≃ₐ[F] E) {n : ℕ} (w : HeightOneSpectrum (𝓞 E))
    (g : AdelicGLn.AdelicGL E n) (i j : Fin n) :
    ‖(finAt (σ • w) (mapGL n (galAd σ) g)).val i j‖ = ‖(finAt w g).val i j‖ :=
  (UpperTheory.norm_galois_smul_adele_component_at_smul_place F E σ ((g : Matrix (Fin n) (Fin n) 𝔸[E]) i j)).1 w

private theorem inf_norm (σ : E ≃ₐ[F] E) {n : ℕ} (w : InfinitePlace E)
    (g : AdelicGLn.AdelicGL E n) (i j : Fin n) :
    ‖(infAt (σ • w) (mapGL n (galAd σ) g)).val i j‖ = ‖(infAt w g).val i j‖ :=
  (UpperTheory.norm_galois_smul_adele_component_at_smul_place F E σ ((g : Matrix (Fin n) (Fin n) 𝔸[E]) i j)).2 w

private theorem locHeight_fin (σ : E ≃ₐ[F] E) {n : ℕ} (w : HeightOneSpectrum (𝓞 E))
    (g : AdelicGLn.AdelicGL E n) :
    AutomorphicForm.locHeight (finAt (σ • w) (mapGL n (galAd σ) g)) =
      AutomorphicForm.locHeight (finAt w g) := by
  refine locHeight_congr _ _ (fin_norm σ w g) fun i j => ?_
  rw [← finAt_inv, ← finAt_inv, ← map_inv]
  exact fin_norm σ w g⁻¹ i j

private theorem locHeight_inf (σ : E ≃ₐ[F] E) {n : ℕ} (w : InfinitePlace E)
    (g : AdelicGLn.AdelicGL E n) :
    AutomorphicForm.locHeight (infAt (σ • w) (mapGL n (galAd σ) g)) =
      AutomorphicForm.locHeight (infAt w g) := by
  refine locHeight_congr _ _ (inf_norm σ w g) fun i j => ?_
  rw [← infAt_inv, ← infAt_inv, ← map_inv]
  exact inf_norm σ w g⁻¹ i j

private theorem mult_smul (σ : E ≃ₐ[F] E) (w : InfinitePlace E) : (σ • w).mult = w.mult := by
  have h : (σ • w).IsReal ↔ w.IsReal := InfinitePlace.isReal_smul_iff
  unfold InfinitePlace.mult
  by_cases hw : w.IsReal
  · rw [if_pos (h.2 hw), if_pos hw]
  · rw [if_neg (fun h' => hw (h.1 h')), if_neg hw]

private theorem inf_prod (σ : E ≃ₐ[F] E) {n : ℕ} (g : AdelicGLn.AdelicGL E n) :
    (∏ w : InfinitePlace E, AutomorphicForm.locHeight (infAt w (mapGL n (galAd σ) g)) ^ w.mult) =
      ∏ w : InfinitePlace E, AutomorphicForm.locHeight (infAt w g) ^ w.mult := by
  refine (Equiv.prod_comp (MulAction.toPerm σ) (fun w : InfinitePlace E =>
    AutomorphicForm.locHeight (infAt w (mapGL n (galAd σ) g)) ^ w.mult)).symm.trans
    (Finset.prod_congr rfl fun w _ => ?_)
  change AutomorphicForm.locHeight (infAt (σ • w) (mapGL n (galAd σ) g)) ^ (σ • w).mult = _
  rw [locHeight_inf, mult_smul]

private theorem fin_prod (σ : E ≃ₐ[F] E) {n : ℕ} (q : HeightOneSpectrum (𝓞 F))
    (g : AdelicGLn.AdelicGL E n) :
    (∏ᶠ (w : HeightOneSpectrum (𝓞 E)) (_ : below F w ≠ q),
      AutomorphicForm.locHeight (finAt w (mapGL n (galAd σ) g))) =
      ∏ᶠ (w : HeightOneSpectrum (𝓞 E)) (_ : below F w ≠ q),
        AutomorphicForm.locHeight (finAt w g) := by
  refine (finprod_comp_equiv (MulAction.toPerm σ : Equiv.Perm (HeightOneSpectrum (𝓞 E)))
    (f := fun w : HeightOneSpectrum (𝓞 E) => ∏ᶠ (_ : below F w ≠ q),
      AutomorphicForm.locHeight (finAt w (mapGL n (galAd σ) g)))).symm.trans
    (finprod_congr fun w => ?_)
  change (∏ᶠ (_ : below F (σ • w) ≠ q),
    AutomorphicForm.locHeight (finAt (σ • w) (mapGL n (galAd σ) g))) = _
  have hb : below F (σ • w) = below F w :=
    HeightOneSpectrum.ext (Ideal.under_smul (𝓞 F) w.asIdeal σ)
  rw [locHeight_fin, hb]

end

theorem UpperTheory.heightOff_mapGL_galAd :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (n : ℕ) (q : HeightOneSpectrum (𝓞 F)) (g : AdelicGLn.AdelicGL E n),
        heightOff q (mapGL n (galAd σ) g : AdelicGLn.AdelicGL E n) = heightOff q g := by
  intro F E _ _ _ _ _ σ n q g
  unfold heightOff
  rw [inf_prod, fin_prod]
end

