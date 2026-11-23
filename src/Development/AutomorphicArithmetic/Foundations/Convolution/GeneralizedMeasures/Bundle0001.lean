module

public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0004
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0039
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.BcPoly
section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM

private theorem bc_at {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (w : Pl E) (p : MvPolynomial (Fin n) ℂ) :
    bcPR F (map C (atPl w p) : PR E n) = map C (atPl (w.under (𝓞 F)) (aeval (powE (resDeg F w)) p)) := by
  unfold atPl
  induction p using MvPolynomial.induction_on with
  | C a => simp [bcPR]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp]
    simp [bcPR]

private theorem bc_mono {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (wd : List (Option (Ix E n))) : bcPR F (C (mono wd) : PR E n) = C (mono (wd.map (resIx F))) := by
  unfold mono
  induction wd with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, ih]
    simp [bcPR, resIx]

theorem UpperTheory.ConvolutionTheory.GM.bcPoly :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (κ : Finset (Pl E)) (κF : Finset (Pl F)), (∀ w ∈ κ, w.under (𝓞 F) ∈ κF) →
    ∀ (p : Pl E → MvPolynomial (Fin n) ℂ) (wd : List (Option (Ix E n))) [DecidableEq (Pl F)],
      bcPR F (C (mono wd) * map C (∏ w ∈ κ, atPl w (p w))) = C (mono (wd.map (resIx F))) *
        map C (∏ v ∈ κF, atPl v (∏ w ∈ κ.filter fun w => w.under (𝓞 F) = v, aeval (powE (resDeg F w)) (p w))) := by
  intro F E _ _ _ _ _ n κ κF hκ p wd _
  rw [map_mul, bc_mono, map_prod, map_prod]
  congr 1
  simp only [bc_at]
  rw [← map_prod, ← Finset.prod_fiberwise_of_maps_to hκ]
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  unfold atPl
  rw [map_prod]
  refine Finset.prod_congr rfl fun w hw => ?_
  rw [(Finset.mem_filter.1 hw).2]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.ContinuousMapGL
section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM

open scoped RestrictedProduct

namespace UpperTheory.ConvolutionTheory.GM.CompactClopenAverage

section Gen

private theorem rp_compact {ι : Type*} {R : ι → Type*} [∀ i, TopologicalSpace (R i)] {A : ∀ i, Set (R i)}
    (D : ∀ i, Set (R i)) (hD : ∀ i, IsCompact (D i)) (T : Set ι) (hT : T.Finite)
    (hDA : ∀ i, i ∉ T → D i ⊆ A i) : IsCompact {x : Πʳ i, [R i, A i] | ∀ i, x i ∈ D i} := by
  have hle : (Filter.cofinite : Filter ι) ≤ Filter.principal Tᶜ := by
    rw [Filter.le_principal_iff, Filter.mem_cofinite, compl_compl]
    exact hT
  have Y : IsCompact ((↑) ⁻¹' (Set.univ.pi D) : Set (Πʳ i, [R i, A i]_[Filter.principal Tᶜ])) := by
    refine RestrictedProduct.isEmbedding_coe_of_principal.isCompact_preimage_iff ?_ |>.mpr
      (isCompact_univ_pi hD)
    rw [RestrictedProduct.range_coe_principal]
    intro f hf i hi
    exact hDA i hi (hf i trivial)
  convert Y.image (RestrictedProduct.continuous_inclusion hle) using 1
  ext x
  constructor
  · intro hx
    refine ⟨⟨x, Filter.eventually_principal.2 fun i hi => hDA i hi (hx i)⟩, fun i _ => hx i, rfl⟩
  · rintro ⟨y, hy, rfl⟩ i
    exact hy i trivial

private theorem isLC_prod {X ι : Type*} [TopologicalSpace X] (T : Finset ι) (f : ι → X → ℂ)
    (h : ∀ i ∈ T, IsLocallyConstant (f i)) : IsLocallyConstant fun x => ∏ i ∈ T, f i x :=
  _root_.UpperTheory.Reformulated.B.Qf48.isLC_prod T f h

private theorem continuous_mapGL' {m : ℕ} {R S : Type*} [CommRing R] [CommRing S] [TopologicalSpace R]
    [TopologicalSpace S] (f : R →+* S) (hf : Continuous f) : Continuous (mapGL m f) :=
  Continuous.units_map _ (Continuous.matrix_map continuous_id hf)

end Gen

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

private theorem liesOver_under (w : Pl E) : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩

private theorem under_eq {v : Pl F} (w : PlacesOver E v) : w.1.under (𝓞 F) = v :=
  HeightOneSpectrum.ext w.2.over.symm

private theorem finite_under (S : Set (Pl F)) (hS : S.Finite) :
    {w : Pl E | w.under (𝓞 F) ∈ S}.Finite := by
  refine (hS.biUnion fun v _ => Set.finite_range (Subtype.val : PlacesOver E v → Pl E)).subset ?_
  intro w hw
  exact Set.mem_biUnion hw ⟨⟨w, liesOver_under w⟩, rfl⟩

private noncomputable def pv (v : Pl F) (x : AdelicGLn.FiniteAdelicGL E n) : GL (Fin n) (CompletionsOver E v) :=
  mapGL n (atFin v) (finEmb E n x)

private theorem finEmb_entry (x : AdelicGLn.FiniteAdelicGL E n) (a b : Fin n) :
    ((finEmb E n x : AdelicGLn.AdelicGL E n) a b).2 = x a b := by
  have h := AdelicGLn.prodEquiv_apply_snd E n (finEmb E n x) a b
  rw [prodEquiv_finEmb] at h
  exact h.symm

private theorem cmp_pv {v : Pl F} (w : PlacesOver E v) (x : AdelicGLn.FiniteAdelicGL E n) :
    cmp w (pv v x) = AdelicGLn.finiteRestrictedEquiv E n x w.1 := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  change ((finEmb E n x : AdelicGLn.AdelicGL E n) a b).2 w.1 = _
  rw [finEmb_entry]
  rfl

private theorem continuous_atFin (v : Pl F) : Continuous (atFin (E := E) v) :=
  continuous_pi fun w => (RestrictedProduct.continuous_eval w.1).comp continuous_snd

private theorem continuous_pv (v : Pl F) : Continuous (pv (E := E) (n := n) v) :=
  (continuous_mapGL' _ (continuous_atFin v)).comp continuous_finEmb

private theorem continuous_cmp {v : Pl F} (w : PlacesOver E v) : Continuous (cmp (n := n) w) :=
  continuous_mapGL' _ (continuous_apply w)

private def U (S : Finset (Pl F)) : Set (AdelicGLn.FiniteAdelicGL E n) :=
  {x | ∀ w : Pl E, w.under (𝓞 F) ∉ S →
    AdelicGLn.finiteRestrictedEquiv E n x w ∈ GLnLocal.integralGL (w.adicCompletion E) n}

private theorem isClopen_U (S : Finset (Pl F)) : IsClopen (U (E := E) (n := n) S) := by
  constructor
  · simp only [U, Set.setOf_forall]
    refine isClosed_iInter fun w => isClosed_iInter fun _ => ?_
    exact (GLnLocal.isCompact_integralGL (w.adicCompletion E) n).isClosed.preimage
      ((RestrictedProduct.continuous_eval w).comp (AdelicGLn.finiteRestrictedEquiv E n).continuous)
  · have h := RestrictedProduct.isOpen_forall_imp_mem
      (R := fun w : Pl E => GL (Fin n) (w.adicCompletion E))
      (A := fun w => (GLnLocal.integralGL (w.adicCompletion E) n : Set _))
      (fun w => GLnLocal.isOpen_integralGL (w.adicCompletion E) n) (p := fun w => w.under (𝓞 F) ∉ S)
    exact h.preimage (AdelicGLn.finiteRestrictedEquiv E n).continuous

private theorem e_formula (S : Finset (Pl F)) (φ : ∀ v : Pl F, GL (Fin n) (CompletionsOver E v) → ℂ)
    (hφ : ∀ v ∉ S, φ v = (unitSet E n v).indicator 1) (x : AdelicGLn.FiniteAdelicGL E n) :
    ∏ᶠ v, φ v (pv v x) = (∏ v ∈ S, φ v (pv v x)) * (U S).indicator 1 x := by
  classical
  by_cases hx : x ∈ U (E := E) (n := n) S
  · rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one]
    refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
    by_contra hvS
    refine hv ?_
    have hvS' : v ∉ S := hvS
    change φ v (pv v x) = 1
    rw [hφ v hvS', Set.indicator_of_mem, Pi.one_apply]
    intro w
    have := hx w.1 (by rw [under_eq]; exact hvS')
    rw [← cmp_pv] at this
    exact this
  · rw [Set.indicator_of_notMem hx, mul_zero]
    simp only [U, Set.mem_setOf_eq, not_forall] at hx
    obtain ⟨w, hwS, hw⟩ := hx
    have hB : {w : Pl E | AdelicGLn.finiteRestrictedEquiv E n x w ∉
        GLnLocal.integralGL (w.adicCompletion E) n}.Finite :=
      Filter.eventually_cofinite.1 (AdelicGLn.finiteRestrictedEquiv E n x).2
    refine finprod_eq_zero _ (w.under (𝓞 F)) ?_ ?_
    · rw [hφ _ hwS, Set.indicator_of_notMem]
      intro h
      refine hw ?_
      have h1 : cmp (⟨w, liesOver_under w⟩ : PlacesOver E (w.under (𝓞 F))) (pv _ x) ∈
          GLnLocal.integralGL (w.adicCompletion E) n := h ⟨w, liesOver_under w⟩
      rw [cmp_pv] at h1
      exact h1
    · refine (S.finite_toSet.union (hB.image fun w : Pl E => w.under (𝓞 F))).subset fun v hv => ?_
      by_cases hvS : v ∈ S
      · exact Or.inl hvS
      · right
        have hnot : pv v x ∉ unitSet E n v := by
          intro h
          refine hv ?_
          change φ v (pv v x) = 1
          rw [hφ v hvS, Set.indicator_of_mem h, Pi.one_apply]
        simp only [unitSet, Set.mem_setOf_eq, not_forall] at hnot
        obtain ⟨w', hw'⟩ := hnot
        refine ⟨w'.1, ?_, under_eq w'⟩
        intro h
        refine hw' ?_
        have : cmp w' (pv v x) ∈ GLnLocal.integralGL (w'.1.adicCompletion E) n := by
          rw [cmp_pv]
          exact h
        exact this

private theorem e_compact (S : Finset (Pl F)) (φ : ∀ v : Pl F, GL (Fin n) (CompletionsOver E v) → ℂ)
    (hS : ∀ v ∈ S, HasCompactSupport (φ v)) :
    ∃ C : Set (AdelicGLn.FiniteAdelicGL E n), IsCompact C ∧
      ∀ x ∈ U S, (∀ v ∈ S, φ v (pv v x) ≠ 0) → x ∈ C := by
  classical
  let D : ∀ w : Pl E, Set (GL (Fin n) (w.adicCompletion E)) := fun w =>
    if w.under (𝓞 F) ∈ S then
      cmp (⟨w, liesOver_under w⟩ : PlacesOver E (w.under (𝓞 F))) '' tsupport (φ (w.under (𝓞 F)))
    else (GLnLocal.integralGL (w.adicCompletion E) n : Set _)
  have hD : ∀ w, IsCompact (D w) := fun w => by
    by_cases h : w.under (𝓞 F) ∈ S
    · simp only [D, if_pos h]
      exact (hS _ h).isCompact.image (continuous_cmp _)
    · simp only [D, if_neg h]
      exact GLnLocal.isCompact_integralGL _ n
  have hK := rp_compact (A := fun w : Pl E => (GLnLocal.integralGL (w.adicCompletion E) n : Set _)) D hD
    {w : Pl E | w.under (𝓞 F) ∈ S} (finite_under _ S.finite_toSet) (fun w hw => by
      have h : w.under (𝓞 F) ∉ S := hw
      simp only [D, if_neg h]
      exact subset_rfl)
  refine ⟨_, (AdelicGLn.finiteRestrictedEquiv E n).toHomeomorph.isCompact_preimage.2 hK, ?_⟩
  intro x hx hne w
  by_cases h : w.under (𝓞 F) ∈ S
  · change _ ∈ D w
    simp only [D, if_pos h]
    exact ⟨pv _ x, subset_tsupport _ (hne _ h), cmp_pv _ x⟩
  · change _ ∈ D w
    simp only [D, if_neg h]
    exact hx w h

private theorem pv_finPart (v : Pl F) (g : AdelicGLn.AdelicGL E n) :
    pv v (CuspidalSpectrum.finPart E n g) = mapGL n (atFin v) g := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  funext w
  change ((finEmb E n (CuspidalSpectrum.finPart E n g) : AdelicGLn.AdelicGL E n) a b).2 w.1 = (g a b).2 w.1
  rw [finEmb_entry]
  rfl

end Main

end UpperTheory.ConvolutionTheory.GM.CompactClopenAverage

open UpperTheory.ConvolutionTheory.GM.CompactClopenAverage in
theorem UpperTheory.ConvolutionTheory.GM.avgE :
    AvgE := by
  intro F E _ _ _ _ _ n hn S β φ hS hoff
  classical
  let e₀ : AdelicGLn.FiniteAdelicGL E n → ℂ := fun x => ∏ᶠ v, φ v (pv v x)
  have hform : ∀ x, e₀ x = (∏ v ∈ S, φ v (pv v x)) * (U S).indicator 1 x :=
    fun x => e_formula S φ hoff x
  have hlc : IsLocallyConstant e₀ := by
    have h1 : IsLocallyConstant fun x : AdelicGLn.FiniteAdelicGL E n => ∏ v ∈ S, φ v (pv v x) :=
      isLC_prod S (fun v x => φ v (pv v x)) fun v hv => (hS v hv).1.comp_continuous (continuous_pv v)
    have h2 : IsLocallyConstant ((U (E := E) (n := n) S).indicator (1 : AdelicGLn.FiniteAdelicGL E n → ℂ)) := by
      rw [← LocallyConstant.coe_charFn ℂ (isClopen_U S)]
      exact LocallyConstant.isLocallyConstant _
    have h3 := h1.mul h2
    have : e₀ = _ := funext hform
    rw [this]
    exact h3
  have hcs : HasCompactSupport e₀ := by
    obtain ⟨C, hC, hsub⟩ := e_compact S φ fun v hv => (hS v hv).2
    have hsupp : IsClosed (Function.support e₀) := isClosed_compl_iff.mpr (hlc.isOpen_fiber 0)
    refine IsCompact.of_isClosed_subset hC (isClosed_tsupport e₀) ?_
    change closure (Function.support e₀) ⊆ C
    rw [hsupp.closure_eq]
    intro x hx
    have hx' : e₀ x ≠ 0 := hx
    rw [hform] at hx'
    have hU : x ∈ U (E := E) (n := n) S := by
      by_contra h
      exact hx' (by rw [Set.indicator_of_notMem h, mul_zero])
    refine hsub x hU fun v hv h0 => hx' ?_
    rw [Finset.prod_eq_zero hv h0, zero_mul]
  let e : TF E n := ⟨⟨e₀, hlc.continuous⟩, hcs⟩
  refine ⟨e, hlc, fun x => rfl, fun x => ?_⟩
  have hinf := (UpperTheory.ConvolutionTheory.Tf.avgTens E n hn β e _ fun _ => rfl).2
  have hΦ : ∀ g, tensE (onInf β) φ g = β (infPart E n g) * e (CuspidalSpectrum.finPart E n g) := by
    intro g
    change onInf β _ * _ = β _ * ∏ᶠ v, φ v (pv v _)
    simp only [pv_finPart]
    congr 1
  exact ((UpperTheory.ConvolutionTheory.Tf.avgTens E n hn β e _ hΦ).1 x).symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.ConvSpec
section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM

theorem UpperTheory.ConvolutionTheory.GM.convSpec :
    ConvSpec := by
  intro K _ _ n _ ν _ β γ
  obtain ⟨g, hg, -, hop⟩ := UpperTheory.ConvolutionTheory.Tf.homConv (archGroup K n) (archGroup K n) (MonoidHom.id _) continuous_id ν ν β γ
  have hex : ∃ δ : TI K n, ∀ x, δ x = ∫ y, β y * γ (y⁻¹ * x) ∂ν := ⟨g, hg⟩
  have h1 : ∀ x, GM.conv ν β γ x = ∫ y, β y * γ (y⁻¹ * x) ∂ν := by
    intro x
    unfold GM.conv
    rw [dite_eq_left hex]
    exact hex.choose_spec x
  refine ⟨h1, fun μ _ => ?_⟩
  have h2 : GM.conv ν β γ = g := by
    ext x
    exact (h1 x).trans (hg x).symm
  rw [h2]
  exact hop (LL μ) ((rightRegularRep (rationalGLOne (K := K) (n := n)) μ).compHom (archP K n) continuous_archP)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.LocHeightDiagPowLe
section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM

private theorem locHeight_diagPow_le {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ)
    (ν : Fin n → ℤ) (j : ℕ) :
    locHeight (Cartan.diagPow (w.adicCompletion E) n fun i => (j : ℤ) * ν i) ≤
      locHeight (Cartan.diagPow (w.adicCompletion E) n ν) ^ j := by
  induction j with
  | zero =>
    have h : Cartan.diagPow (w.adicCompletion E) n (fun i => ((0 : ℕ) : ℤ) * ν i) = 1 :=
      Units.ext (by simp [Cartan.coe_diagPow])
    rw [h, locHeight_one, pow_zero]
  | succ j ih =>
    have h : Cartan.diagPow (w.adicCompletion E) n (fun i => ((j + 1 : ℕ) : ℤ) * ν i) =
        Cartan.diagPow (w.adicCompletion E) n (fun i => (j : ℤ) * ν i) *
          Cartan.diagPow (w.adicCompletion E) n ν := by
      refine Units.ext ?_
      rw [Units.val_mul, Cartan.coe_diagPow, Cartan.coe_diagPow, Cartan.coe_diagPow,
        Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      push_cast
      rw [add_mul, one_mul, zpow_add₀ (Cartan.uniformizer_ne_zero _)]
    rw [h, pow_succ]
    exact (locHeight_mul_le_of_ultrametric _ _).trans
      (mul_le_mul_of_nonneg_right ih (locHeight_pos _).le)

private theorem locHeight_iwahori {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
    {a : GL (Fin n) (w.adicCompletion E)} (ha : a ∈ GLnLocal.iwahori (w.adicCompletion E) n) :
    locHeight a = 1 :=
  locHeight_eq_one_of_mem_integralGL (GLnLocal.iwahori_le_integralGL _ _ ha)

theorem UpperTheory.ConvolutionTheory.GM.htTot :
    HtTot := by
  classical
  intro F E _ _ _ _ _ n q w₀ ν
  refine ⟨locHeight (Cartan.diagPow (w₀.1.adicCompletion E) n ν), one_le_locHeight _, ?_⟩
  intro j Y f hS g hg
  obtain ⟨h1, h2, h3⟩ := hS g hg
  have hfin := finite_mulSupport_locHeight_finAt (g : AdelicGLn.AdelicGL E n)
  have hbelow : ∀ x : HeightOneSpectrum (𝓞 E), x.asIdeal.LiesOver q.asIdeal →
      AdeleBaseChange.below F x = q := by
    intro x hx
    refine HeightOneSpectrum.ext ?_
    have e1 := (AdeleBaseChange.liesOver_below (K := F) x).over
    have e2 := hx.over
    exact e1.trans e2.symm
  have split : (∏ᶠ w : HeightOneSpectrum (𝓞 E), locHeight (finAt w (g : AdelicGLn.AdelicGL E n))) =
      (∏ᶠ (w : HeightOneSpectrum (𝓞 E)) (_ : AdeleBaseChange.below F w ≠ q),
        locHeight (finAt w (g : AdelicGLn.AdelicGL E n))) *
      ∏ᶠ (w : HeightOneSpectrum (𝓞 E)) (_ : AdeleBaseChange.below F w = q),
        locHeight (finAt w (g : AdelicGLn.AdelicGL E n)) := by
    have h := finprod_mem_union' (f := fun w : HeightOneSpectrum (𝓞 E) =>
        locHeight (finAt w (g : AdelicGLn.AdelicGL E n)))
      (s := {w | AdeleBaseChange.below F w ≠ q}) (t := {w | AdeleBaseChange.below F w = q})
      (Set.disjoint_left.2 fun w h₁ h₂ => h₁ h₂) (hfin.inter_of_right _) (hfin.inter_of_right _)
    have hu : {w : HeightOneSpectrum (𝓞 E) | AdeleBaseChange.below F w ≠ q} ∪
        {w | AdeleBaseChange.below F w = q} = Set.univ := by
      ext w
      simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact (em _).symm
    rw [hu, finprod_mem_univ] at h
    exact h
  have hC : (∏ᶠ (w : HeightOneSpectrum (𝓞 E)) (_ : AdeleBaseChange.below F w = q),
        locHeight (finAt w (g : AdelicGLn.AdelicGL E n))) ≤
      locHeight (Cartan.diagPow (w₀.1.adicCompletion E) n ν) ^ j := by
    rw [finprod_eq_single _ w₀.1 ?_, finprod_eq_if, if_pos (hbelow _ w₀.2)]
    · obtain ⟨a, ha, b, hb, e⟩ := h2
      rw [e]
      refine (locHeight_mul_le_of_ultrametric _ _).trans ?_
      rw [locHeight_iwahori hb, mul_one]
      refine (locHeight_mul_le_of_ultrametric _ _).trans ?_
      rw [locHeight_iwahori ha, one_mul]
      exact locHeight_diagPow_le _ _ _ _
    · intro x hx
      rw [finprod_eq_if]
      split_ifs with hq
      · have hl : x.asIdeal.LiesOver q.asIdeal := hq ▸ AdeleBaseChange.liesOver_below x
        exact locHeight_iwahori (h3 ⟨x, hl⟩ fun h => hx (congrArg Subtype.val h))
      · rfl
  have hB : 0 ≤ ∏ᶠ (w : HeightOneSpectrum (𝓞 E)) (_ : AdeleBaseChange.below F w ≠ q),
      locHeight (finAt w (g : AdelicGLn.AdelicGL E n)) :=
    finprod_nonneg fun _ => finprod_nonneg fun _ => (locHeight_pos _).le
  have hC0 : 0 ≤ ∏ᶠ (w : HeightOneSpectrum (𝓞 E)) (_ : AdeleBaseChange.below F w = q),
      locHeight (finAt w (g : AdelicGLn.AdelicGL E n)) :=
    finprod_nonneg fun _ => finprod_nonneg fun _ => (locHeight_pos _).le
  have hoff : 0 ≤ heightOff q (g : AdelicGLn.AdelicGL E n) :=
    mul_nonneg (zero_le_one.trans (one_le_prod_locHeight _)) hB
  have key : AutomorphicForm.height (g : AdelicGLn.AdelicGL E n) =
      heightOff q (g : AdelicGLn.AdelicGL E n) *
        ∏ᶠ (w : HeightOneSpectrum (𝓞 E)) (_ : AdeleBaseChange.below F w = q),
          locHeight (finAt w (g : AdelicGLn.AdelicGL E n)) := by
    rw [AutomorphicForm.height, split, heightOff, mul_assoc]
  rw [key]
  exact mul_le_mul h1 hC hC0 (hoff.trans h1)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.PolyMem
section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM

private theorem haar_one {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (U : Subgroup G) (hc : IsCompact (U : Set G)) (ho : IsOpen (U : Set G)) :
    ∃ m : Measure G, m.IsHaarMeasure ∧ m U = 1 := by
  let K₀ : TopologicalSpace.PositiveCompacts G := ⟨⟨U, hc⟩, by
    rw [TopologicalSpace.Compacts.carrier_eq_coe, TopologicalSpace.Compacts.coe_mk, ho.interior_eq]
    exact ⟨1, U.one_mem⟩⟩
  exact ⟨Measure.haarMeasure K₀, inferInstance, Measure.haarMeasure_self (K₀ := K₀)⟩

private theorem poly_mem {n : ℕ} (p : MvPolynomial (Fin n) ℂ) :
    polyEmb (n := n) (aeval (fun i : Fin n => esymm (Fin n) ℂ (i + 1)) p) ∈
      symmetricLaurent (n := n) := fun σ => by
  rw [← polyEmb_rename]
  congr 1
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  congr 2
  funext i
  exact MvPolynomial.esymm_isSymmetric (Fin n) ℂ _ σ

theorem UpperTheory.ConvolutionTheory.GM.sphEx :
    SphEx := by
  intro K _ _ n _ w
  refine ⟨fun p => ?_, ?_, ?_⟩
  · borelize (GL (Fin n) (w.adicCompletion K))
    obtain ⟨m, hm, h1⟩ := haar_one (GLnLocal.integralGL (w.adicCompletion K) n) (GLnLocal.isCompact_integralGL _ n)
      (GLnLocal.isOpen_integralGL _ n)
    obtain ⟨H, hH⟩ := (AlgHom.mem_range _).1 (symmetricLaurent_le_range (μ := m) (F := w.adicCompletion K) (poly_mem p))
    exact ⟨fun x => (H : HeckeAlgebra m) x, _, inferInstance, m, hm, h1, H, fun _ => rfl, hH⟩
  · borelize (GL (Fin n) (w.adicCompletion K))
    obtain ⟨m, hm, h1⟩ := haar_one (GLnLocal.integralGL (w.adicCompletion K) n) (GLnLocal.isCompact_integralGL _ n)
      (GLnLocal.isOpen_integralGL _ n)
    refine ⟨_, inferInstance, m, hm, h1, 1, fun x => ?_, by rw [map_one, map_one, map_one]⟩
    rw [HeckeAlgebra.HeckeAlgebraLevel.val_one]
    have hr : m.real (GLnLocal.integralGL (w.adicCompletion K) n : Set (GL (Fin n) (w.adicCompletion K))) = 1 := by
      simp [Measure.real, h1]
    rw [HeckeAlgebra.idem_apply, hr]
    simp only [Complex.ofReal_one, inv_one]
    rfl
  · rintro p h ⟨_, _, m, _, -, H, hH, -⟩
    obtain rfl : (fun x => (H : HeckeAlgebra m) x) = h := funext hH
    exact ⟨(H : HeckeAlgebra m).mem.1, (H : HeckeAlgebra m).mem.2,
      fun k hk x => HeckeAlgebra.HeckeAlgebraLevel.val_mem _ _ H k hk x⟩
end

