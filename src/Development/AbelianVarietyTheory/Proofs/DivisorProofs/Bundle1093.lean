module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1073
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1080
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1077
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1088
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1089
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMassLineBundleWeightOfIso
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
open ReciprocityTheory.L2DbarEstimates (V cHess)
open GlobalTheory.ChartGlue
open scoped ContDiff

namespace GlobalTheory.ChernIso

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
  {A B : LB X} {φ : Weight p σ B} {D : ℕ}

theorem cInfAt_log_normSq {W : X.Opens} (g : Γ(X, W)) {y : CxPts p σ} (hy : y ∈ ptsIn p σ W)
    (h0 : ev p σ W g y ≠ 0) : CInfAt (fun z => Real.log (‖ev p σ W g z‖ ^ 2)) y := by
  have hs : ContDiff ℝ ∞ fun v : Unit → ℂ => ‖v ()‖ ^ 2 := (contDiff_apply ℝ (fun _ => ℂ) ()).norm_sq ℂ
  refine ⟨W, Unit, inferInstance, fun _ => g, fun v => Real.log (‖v ()‖ ^ 2),
    {v | ‖v ()‖ ^ 2 ≠ 0}, hy, isOpen_ne_fun hs.continuous continuous_const,
    pow_ne_zero _ (norm_ne_zero_iff.2 h0), hs.contDiffOn.log fun _ h => h, EventuallyEq.rfl⟩

theorem ofIso_apply (hA : A.IsLB) (w : LB.Iso B A) (hw : w.IsGen) {a : A.ι} {b : B.ι}
    {y : CxPts p σ} (ha : y ∈ ptsIn p σ (A.U a)) (hb : y ∈ ptsIn p σ (B.U b)) :
    (φ.ofIso hA w hw).φ a y = φ.φ b y + Real.log (‖ev p σ _ (w.s (a, b)).val y‖ ^ 2) := by
  rw [Weight.ofIso, Weight.ofPairs_φ ha hb]

theorem isCInf_ofIso (h : φ.IsCInf) (hA : A.IsLB) (w : LB.Iso B A) (hw : w.IsGen) :
    (φ.ofIso hA w hw).IsCInf := fun a y ha => by
  have hb := mem_pick φ.isLB y
  refine ((h _ y hb).add (cInfAt_log_normSq (w.s (a, pick φ.isLB y)).val
    (mem_ptsIn_inf.2 ⟨ha, hb⟩) (ev_iso_ne_zero w hb ha))).congr ?_
  filter_upwards [(isOpen_ptsIn _).mem_nhds ha, (isOpen_ptsIn _).mem_nhds hb] with z h₁ h₂
  exact ofIso_apply hA w hw h₁ h₂

theorem hess_ofIso (h : φ.IsCInf) (hA : A.IsLB) (w : LB.Iso B A) (hw : w.IsGen)
    (c : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source) {a : A.ι} {b : B.ι}
    (ha : y ∈ ptsIn p σ (A.U a)) (hb : y ∈ ptsIn p σ (B.U b)) :
    c.hess (φ.ofIso hA w hw) a y = c.hess φ b y := by
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (A.U a ⊓ B.U b))
  have hm := mem_over c.e hy (mem_ptsIn_inf.2 ⟨ha, hb⟩)
  have hg := c.holo (A.U a ⊓ B.U b) (w.s (a, b)).val
  have h0 : ∀ v ∈ c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (A.U a ⊓ B.U b),
      (ev p σ (A.U a ⊓ B.U b) (w.s (a, b)).val ∘ c.e.symm) v ≠ 0 := fun v hv =>
    ev_iso_ne_zero w (mem_ptsIn_inf.1 hv.2).2 (mem_ptsIn_inf.1 hv.2).1
  have e := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul ho
    ((contDiffOn_chart (h b) c).mono fun v hv => ⟨hv.1, (mem_ptsIn_inf.1 hv.2).2⟩)
    (contDiffOn_log_normSq ho hg h0) 1 hm
  have e₀ : cHess D (fun v => ((Real.log (‖(ev p σ (A.U a ⊓ B.U b) (w.s (a, b)).val ∘
      c.e.symm) v‖ ^ 2) : ℝ) : ℂ)) (c.e y) = 0 := by
    ext i j
    exact ReciprocityTheory.L2DbarEstimates.Y.cmpa_hess_log ho hm hg h0 i j
  rw [e₀, smul_zero, add_zero] at e
  refine Eq.trans (ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr ?_) e
  filter_upwards [ho.mem_nhds hm] with v hv
  rw [ofIso_apply hA w hw (mem_ptsIn_inf.1 hv.2).1 (mem_ptsIn_inf.1 hv.2).2, one_mul]
  rfl

theorem chernPart_ofIso (h : φ.IsCInf) (hA : A.IsLB) (w : LB.Iso B A) (hw : w.IsGen) (ε : ℤˣ) :
    (φ.ofIso hA w hw).chernPart D ε = φ.chernPart D ε := by
  refine iSup_congr fun c => Measure.ext fun S hS => ?_
  rw [chartMeas_apply _ _ hS, chartMeas_apply _ _ hS]
  refine setLIntegral_congr_fun (measurableSet_image c.e
    (c.e.open_source.measurableSet.inter hS) inter_subset_left) ?_
  rintro _ ⟨y, hy, rfl⟩
  simp only [c.e.left_inv hy.1]
  rw [AlgChart.chernDens, AlgChart.chernDens,
    hess_ofIso h hA w hw c hy.1 (mem_pick _ y) (mem_pick φ.isLB y)]

theorem chernInt_ofIso (h : φ.IsCInf) (hA : A.IsLB) (w : LB.Iso B A) (hw : w.IsGen)
    (S : Set (CxPts p σ)) (f : CxPts p σ → ℝ) :
    (φ.ofIso hA w hw).chernInt D S f = φ.chernInt D S f := by
  rw [Weight.chernInt, Weight.chernInt, chernPart_ofIso h, chernPart_ofIso h]

theorem chernMass_ofIso : ∀ (Y : Var ℂ) (L A : LB Y.X) (φ : Weight Y.str (RingHom.id ℂ) L)
    (hA : A.IsLB) (w : L.Iso A) (hw : w.IsGen), φ.IsCInf → (φ.ofIso hA w hw).IsCInf ∧
      Weight.chernInt (φ.ofIso hA w hw) Y.dim Set.univ (fun _ => 1) =
        Weight.chernInt φ Y.dim Set.univ (fun _ => 1) :=
  fun _ _ _ _ hA w hw h => ⟨isCInf_ofIso h hA w hw, chernInt_ofIso h hA w hw _ _⟩

end GlobalTheory.ChernIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommGroupDivEqMulDivMulInvDiv
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.ConsEta

def unitDir : ℂˣ →* ℂˣ where
  toFun z := Units.mk0 ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) (div_ne_zero z.ne_zero (by simp))
  map_one' := by ext; simp
  map_mul' a b := by
    ext
    simp only [Units.val_mul, Units.val_mk0, norm_mul, Complex.ofReal_mul]
    field_simp

variable (E : Type) [Field E] [NumberField E]

def infSign : Neutral.B1.Ideles E →* ℂˣ :=
  ∏ w : InfinitePlace E, unitDir.comp ((Units.map (InfinitePlace.Completion.extensionEmbedding w).toMonoidHom).comp
    (Units.map (GlobalTheory.IdeleNormChar.infEval w)))

def conjQuot [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) : Neutral.B1.Ideles E →* (w.adicCompletion E)ˣ :=
  (Units.map (GlobalTheory.IdeleNormChar.finEval w)).comp
    (MonoidHom.id _ / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E)

theorem norm_unitDir (z : ℂˣ) : ‖((unitDir z : ℂˣ) : ℂ)‖ = 1 := by
  change ‖(z : ℂ) / (‖(z : ℂ)‖ : ℂ)‖ = 1
  rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 z.ne_zero)]

theorem norm_infSign (x : Neutral.B1.Ideles E) : ‖((infSign E x : ℂˣ) : ℂ)‖ = 1 := by
  rw [infSign, MonoidHom.finsetProd_apply, Units.coe_prod, norm_prod]
  exact Finset.prod_eq_one fun w _ => norm_unitDir _

end GlobalTheory.ConsEta

namespace GlobalTheory.ConsEta
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem nsUnits_le_unitIdl : GlobalTheory.MuExist.nsUnits E ≤ GlobalTheory.Mem.Chr.unitIdl E := by
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨w, u, -, hu, rfl⟩ v
  by_cases hv : v = w
  · subst hv
    rw [Neutral.B1.localIdele_snd_self]; exact hu
  · rw [((Neutral.B1.localIdele_isSupportedAt E w u).2 v hv)]; exact map_one _

theorem infSign_localIdele (w : HeightOneSpectrum (𝓞 E)) (u : (w.adicCompletion E)ˣ) :
    infSign E (Neutral.B1.localIdele E w u) = 1 := by
  rw [infSign, MonoidHom.finsetProd_apply]
  refine Finset.prod_eq_one fun v _ => ?_
  have : Units.map (GlobalTheory.IdeleNormChar.infEval v) (Neutral.B1.localIdele E w u) = 1 := Units.ext rfl
  simp only [MonoidHom.comp_apply, this, map_one]

theorem infSign_nsUnits {u : Neutral.B1.Ideles E} (hu : u ∈ GlobalTheory.MuExist.nsUnits E) : infSign E u = 1 := by
  have : GlobalTheory.MuExist.nsUnits E ≤ (infSign E).ker := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨w, u, -, -, rfl⟩
    exact infSign_localIdele w u
  exact this hu

theorem commGroup_div_eq_mul_div_mul_inv_div {G : Type} [CommGroup G] (d dc i u cu : G) :
    d / dc = (d * i * u) / (dc * i * cu) * (u / cu)⁻¹ := by
  simp only [div_eq_mul_inv, mul_inv, inv_inv]
  rw [show d * i * u * (dc⁻¹ * i⁻¹ * cu⁻¹) * (u⁻¹ * cu) = d * dc⁻¹ * (i * i⁻¹) * (u * u⁻¹) * (cu⁻¹ * cu) by ac_rfl]
  simp

theorem continuous_unitDir : Continuous unitDir := by
  have h1 : Continuous fun z : ℂˣ => ((unitDir z : ℂˣ) : ℂ) := by
    change Continuous fun z : ℂˣ => (z : ℂ) / (‖(z : ℂ)‖ : ℂ)
    exact Units.continuous_val.div (Complex.continuous_ofReal.comp Units.continuous_val.norm)
      fun z => by simp
  refine Units.continuous_iff.2 ⟨h1, ?_⟩
  have h2 : (fun z : ℂˣ => (((unitDir z)⁻¹ : ℂˣ) : ℂ)) = fun z => ((unitDir z⁻¹ : ℂˣ) : ℂ) := by
    funext z; rw [map_inv]
  change Continuous fun z : ℂˣ => (((unitDir z)⁻¹ : ℂˣ) : ℂ)
  rw [h2]
  exact h1.comp continuous_inv

theorem continuous_infSign : Continuous (infSign E) := by
  rw [infSign]
  have : ⇑(∏ w : InfinitePlace E, unitDir.comp ((Units.map (InfinitePlace.Completion.extensionEmbedding w).toMonoidHom).comp
      (Units.map (GlobalTheory.IdeleNormChar.infEval w)))) = fun x => ∏ w : InfinitePlace E, unitDir
        (Units.map (InfinitePlace.Completion.extensionEmbedding w).toMonoidHom
          (Units.map (GlobalTheory.IdeleNormChar.infEval (K := E) w) x)) := by
    funext x; rw [MonoidHom.finsetProd_apply]; rfl
  rw [this]
  refine continuous_finsetProd _ fun w _ => continuous_unitDir.comp ?_
  refine Continuous.units_map _ ?_ |>.comp (Continuous.units_map _ ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous
  · exact (continuous_apply w).comp continuous_fst

theorem continuous_conjQuot (w : HeightOneSpectrum (𝓞 E)) : Continuous (conjQuot E w) := by
  have hC : Continuous (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E) :=
    @GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_ideleMap E E _ _ _ _ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E).toRingEquiv.toRingHom.toAlgebra
  refine (Continuous.units_map _ ?_).comp (continuous_id.div' hC)
  exact (RestrictedProduct.continuous_eval w).comp continuous_snd

end GlobalTheory.ConsEta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompLinearAutLocallyConstantCompactSupportMatrix
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LeviDesc

theorem comp_linearAut_smooth_compact : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (a b : ℕ) (L : Matrix (Fin a) (Fin b) (w.adicCompletion E) →ₗ[w.adicCompletion E] Matrix (Fin a) (Fin b) (w.adicCompletion E)) (φ : Matrix (Fin a) (Fin b) (w.adicCompletion E) → ℂ), LinearMap.det L ≠ 0 → (∃ U : AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)), IsOpen (U : Set (Matrix (Fin a) (Fin b) (w.adicCompletion E))) ∧ ∀ x, ∀ y ∈ U, φ (x + y) = φ x) → HasCompactSupport φ → (∃ U : AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)), IsOpen (U : Set (Matrix (Fin a) (Fin b) (w.adicCompletion E))) ∧ ∀ x, ∀ y ∈ U, φ (L (x + y)) = φ (L x)) ∧ HasCompactSupport (fun x => φ (L x)) ∧ LocallyCompactSpace (Matrix (Fin a) (Fin b) (w.adicCompletion E)) := by
  intro E _ _ w a b L φ hdet hlc hcs
  haveI hMT : IsModuleTopology (w.adicCompletion E) (Matrix (Fin a) (Fin b) (w.adicCompletion E)) :=
    inferInstanceAs (IsModuleTopology (w.adicCompletion E) (Fin a → Fin b → w.adicCompletion E))
  haveI hLC : LocallyCompactSpace (Matrix (Fin a) (Fin b) (w.adicCompletion E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin a → Fin b → w.adicCompletion E))
  let e := LinearMap.equivOfDetNeZero L hdet
  have he : ∀ x, e x = L x := fun x => rfl
  have hc : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have hc' : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let h : Matrix (Fin a) (Fin b) (w.adicCompletion E) ≃ₜ Matrix (Fin a) (Fin b) (w.adicCompletion E) :=
    { toEquiv := e.toEquiv, continuous_toFun := hc, continuous_invFun := hc' }
  obtain ⟨U, hUo, hU⟩ := hlc
  refine ⟨⟨U.comap L.toAddMonoidHom, ?_, ?_⟩, ?_, hLC⟩
  · exact hUo.preimage (IsModuleTopology.continuous_of_linearMap L)
  · intro x y hy
    rw [map_add (f := _)]
    exact hU (L x) (L y) hy
  · exact hcs.comp_homeomorph h

end GlobalTheory.LeviDesc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactPartCentralizerLeConjIntegralUnitary
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CptCent

theorem mem_GLint_of_entries' {K : Type} [Field K] {n : ℕ} (O : Subring K) (g : GL (Fin n) K)
    (h1 : ∀ a b, g.val a b ∈ O) (h2 : ∀ a b, (g⁻¹).val a b ∈ O) : g ∈ Formalism.UG.GLint (Fin n) O := by
  have inj : Function.Injective (O.subtype.mapMatrix (m := Fin n)) :=
    fun A B h => by ext i j; exact congrFun (congrFun h i) j
  let A : Matrix (Fin n) (Fin n) O := fun i j => ⟨g.val i j, h1 i j⟩
  let B : Matrix (Fin n) (Fin n) O := fun i j => ⟨(g⁻¹).val i j, h2 i j⟩
  have hA : O.subtype.mapMatrix A = g.val := rfl
  have hB : O.subtype.mapMatrix B = (g⁻¹).val := rfl
  refine ⟨⟨A, B, inj ?_, inj ?_⟩, Units.ext rfl⟩
  · rw [map_mul, hA, hB, map_one, Units.mul_inv]
  · rw [map_mul, hA, hB, map_one, Units.inv_mul]

theorem entry_mem_of_mem_GLint' {K : Type} [Field K] {n : ℕ} (O : Subring K) {g : GL (Fin n) K}
    (hg : g ∈ Formalism.UG.GLint (Fin n) O) (a b : Fin n) : g.val a b ∈ O := by
  obtain ⟨h, rfl⟩ := hg
  exact (h.val a b).2

theorem conj_zpow' {G : Type} [Group G] (g t : G) (k : ℤ) : (g⁻¹ * t * g) ^ k = g⁻¹ * t ^ k * g := by
  have := map_zpow (MulAut.conj g⁻¹) t k
  simpa [MulAut.conj_apply] using this.symm

theorem cptPart_le_conj_KL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E)
    (P₀ : (w.adicCompletionIntegers E)[X]), IsCoprime P₀ (derivative P₀) →
    ∀ γ : UL n w, γ.1.val.charpoly = P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) →
    ∀ g : UL n w, g⁻¹ * γ * g ∈ KL n w →
    cptPart (twCent (MonoidHom.id (UL n w)) γ) ≤ (KL n w).map (MulAut.conj g).toMonoidHom := by
  intro E _ _ _ n w P₀ hP₀ γ hγ g hg
  have hgK : ((g⁻¹ * γ * g : UL n w) : GLw n w) ∈ GlobalTheory.LFun.KGL w (n := n) := (Subgroup.mem_subgroupOf).1 hg
  set A : Matrix (Fin n) (Fin n) (w.adicCompletion E) := ((g⁻¹ * γ * g : UL n w) : GLw n w).val with hAdef
  have hA : ∀ i j, A i j ∈ w.adicCompletionIntegers E := fun i j => entry_mem_of_mem_GLint' _ hgK i j
  have hAc : A.charpoly = P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) := by
    rw [← hγ, hAdef]
    have : ((g⁻¹ * γ * g : UL n w) : GLw n w).val = ((g : GLw n w)⁻¹).val * (γ : GLw n w).val * (g : GLw n w).val := by
      simp
    rw [this, Matrix.coe_units_inv]
    exact Matrix.charpoly_units_conj' (g : GLw n w) ((γ : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E))
  show Subgroup.closure _ ≤ _
  rw [Subgroup.closure_le]
  rintro t ⟨ht, hcpt⟩
  have htγ : t * γ = γ * t := by simpa [twCent] using ht
  obtain ⟨B, hB⟩ := _root_.GlobalTheory.BCT.powers_entries_bdd E n w t g hcpt
  set x : UL n w := g⁻¹ * t * g with hx
  have hxA : x * (g⁻¹ * γ * g) = (g⁻¹ * γ * g) * x := by
    simp only [hx, mul_assoc, mul_inv_cancel_left]
    rw [← mul_assoc t, htγ, mul_assoc]
  have val_pow : ∀ (y : UL n w) (k : ℕ), ((y ^ k : UL n w) : GLw n w).val = ((y : GLw n w).val) ^ k := by
    intro y k; simp
  have entries : ∀ (y : UL n w), y * (g⁻¹ * γ * g) = (g⁻¹ * γ * g) * y →
      (∀ k : ℕ, ∃ m : ℤ, y ^ k = g⁻¹ * t ^ m * g) → ∀ i j, (y : GLw n w).val i j ∈ w.adicCompletionIntegers E := by
    intro y hy hpow
    refine _root_.GlobalTheory.IntMatSep.integral_of_commute_sep E w n P₀ hP₀ A _ hA hAc ?_ ⟨B, fun k i j => ?_⟩
    · have := congrArg (fun z : UL n w => (z : GLw n w).val) hy
      simpa [Commute, SemiconjBy, hAdef] using this
    · obtain ⟨m, hm⟩ := hpow k
      rw [← val_pow, hm]
      exact hB m i j
  have hxO := entries x hxA (fun k => ⟨k, by rw [hx, ← conj_zpow']; simp⟩)
  have hxiO := entries x⁻¹ (by
      have := congrArg (fun z => x⁻¹ * z * x⁻¹) hxA
      simpa [mul_assoc] using this.symm)
    (fun k => ⟨-(k : ℤ), by rw [hx, ← conj_zpow', _root_.zpow_neg, zpow_natCast, inv_pow]⟩)
  refine ⟨x, ?_, ?_⟩
  · show x ∈ KL n w
    refine (Subgroup.mem_subgroupOf).2 (mem_GLint_of_entries' _ _ hxO fun a b => ?_)
    have := hxiO a b
    simpa using this
  · simp [hx, MulAut.conj_apply, mul_assoc]

end GlobalTheory.CptCent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsSmoothProjVarietyCompactManifold
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
namespace GlobalTheory

theorem cxPts_var_compact_manifold : ∀ Y : Var ℂ, CompactSpace (CxPts Y.str (RingHom.id ℂ)) ∧ T2Space (CxPts Y.str (RingHom.id ℂ)) ∧ SecondCountableTopology (CxPts Y.str (RingHom.id ℂ)) ∧ ∃ A : FinHolAtlas Y.dim (CxPts Y.str (RingHom.id ℂ)), IsAlgAtlas A := fun Y =>
  haveI : CompactSpace (CxPts Y.str (RingHom.id ℂ)) := CxPts.compactSpace (RingHom.id ℂ) Y.isProjOver
  ⟨this, t2Space_cxPts_of_isProjOver _ Y.isProjOver, secondCountableTopology_of_isProjOver _ Y.isProjOver,
    (AnRead.all Y.str (RingHom.id ℂ) Y.dim).finAtlas, AnRead.isAlgAtlas_finAtlas _⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMemPrincipalCongruenceSubgroupIff
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical

noncomputable section

namespace GlobalTheory.KapOrb.CongNorm

variable {E : Type} [Field E] [NumberField E]

theorem val_mul_mul_le {R Γ : Type} [CommRing R] [LinearOrderedCommMonoidWithZero Γ] (v : Valuation R Γ) {n : ℕ}
    (A X B : Matrix (Fin n) (Fin n) R) (c : Γ) (hA : ∀ i j, v (A i j) ≤ 1) (hB : ∀ i j, v (B i j) ≤ 1)
    (hX : ∀ i j, v (X i j) ≤ c) (i j : Fin n) : v ((A * X * B) i j) ≤ c := by
  rw [Matrix.mul_apply]
  refine v.map_sum_le fun l _ => ?_
  rw [Matrix.mul_apply, v.map_mul]
  have h1 : v (∑ m, A i m * X m l) ≤ c := v.map_sum_le fun m _ => by
    rw [v.map_mul]
    calc v (A i m) * v (X m l) ≤ 1 * c := mul_le_mul' (hA i m) (hX m l)
      _ = c := one_mul c
  calc v (∑ m, A i m * X m l) * v (B l j) ≤ c * 1 := mul_le_mul' h1 (hB l j)
    _ = c := mul_one c

theorem val_le_one_of_mem_KGL (w : Pl E) {n : ℕ} {g : GLw n w} (hg : g ∈ GlobalTheory.LFun.KGL w (n := n)) (i j : Fin n) :
    Valued.v (g.val i j) ≤ 1 := by
  obtain ⟨y, rfl⟩ := hg
  have : ((Formalism.UG.bc (n := Fin n) (Ov E w).subtype y).val i j) = ((y.val i j : Ov E w) : w.adicCompletion E) := rfl
  rw [this]
  exact (HeightOneSpectrum.mem_adicCompletionIntegers (K := E) (v := w)).1 (y.val i j).2

theorem conj_bound (w : Pl E) {n : ℕ} (c : WithZero (Multiplicative ℤ)) {a x : GLw n w} (ha : a ∈ GlobalTheory.LFun.KGL w (n := n))
    (hx : ∀ i j, Valued.v ((x.val - 1) i j) ≤ c) (i j : Fin n) :
    Valued.v (((a⁻¹ * x * a).val - 1) i j) ≤ c := by
  have e : (a⁻¹ * x * a).val - 1 = (a⁻¹).val * (x.val - 1) * a.val := by
    have h1 : (a⁻¹).val * a.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1, Units.val_mul, Units.val_mul]
  rw [e]
  exact val_mul_mul_le Valued.v _ _ _ c (val_le_one_of_mem_KGL w (inv_mem ha))
    (val_le_one_of_mem_KGL w ha) hx i j

end GlobalTheory.KapOrb.CongNorm

namespace GlobalTheory.KapOrb

theorem conj_mem_congSet_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (n m : ℕ)
    (h k : GLw n w), k ∈ GlobalTheory.LFun.KGL w (n := n) → (k⁻¹ * h * k ∈ congSet w n m ↔ h ∈ congSet w n m) := by
  intro E _ _ _ w n m h k hk
  have hmem : k⁻¹ * h * k ∈ GlobalTheory.LFun.KGL w (n := n) ↔ h ∈ GlobalTheory.LFun.KGL w (n := n) := by
    rw [Subgroup.mul_mem_cancel_right _ hk, Subgroup.mul_mem_cancel_left _ (inv_mem hk)]
  have hb : ∀ g : GLw n w, (∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤
      WithZero.exp (-(m : ℤ))) ↔ ∀ i j, Valued.v ((g.val - 1) i j) ≤ WithZero.exp (-(m : ℤ)) := fun g => by
    simp only [Matrix.sub_apply]
  simp only [congSet, Set.mem_ofPred_eq, hb, hmem]
  refine and_congr_right fun _ => ⟨fun H => ?_, fun H => CongNorm.conj_bound w _ hk H⟩
  have e : h = k⁻¹⁻¹ * (k⁻¹ * h * k) * k⁻¹ := by group
  rw [e]
  exact CongNorm.conj_bound w _ (inv_mem hk) H

end GlobalTheory.KapOrb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjSrcMemOrb
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerTw.Comm

open GlobalTheory.EulerTw

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem thF_thF (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) : thF E n (thF E n g) = g :=
  GlobalTheory.ThetaPull.thetaGL_thetaGL _ GlobalTheory.ThetaPull.cFin_cFin g

theorem thF_ratF (g : GL (Fin n) E) : ratF E n (thE E n g) = thF E n (ratF E n g) :=
  GlobalTheory.ThetaPull.map_thetaGL _ _ _ (fun x => (conjFin_algebraMap (IsCMField.complexConj E).toRingEquiv x).symm) g

end GlobalTheory.EulerTw.Comm

namespace GlobalTheory.EulerTw

end GlobalTheory.EulerTw
end
end

