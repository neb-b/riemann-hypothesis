module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchPowAlt
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.Bundle0001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.ResidualSpectrumHilbertSum.ResidualSpectrumTensors.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.NormUnr
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.ChiBasic
section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt.G

private theorem isOpen_ker_chiAt {K : Type} [Field K] [NumberField K] (n : ℕ) (χ : HChar K) (v : Pl K) :
    IsOpen {g : Gw n v | χ.loc v (Matrix.GeneralLinearGroup.det g) = 1} := by
  have h := (isOpen_ker_finIdele K (χ.1.comp (finId K)) (χ.2.1.comp (continuous_finId K))).preimage
    ((Matrix.GeneralLinearGroup.continuous_det (n := Fin n)).comp (CuspSub.continuous_locGL (a := n) v))
  convert h using 1
  ext g
  exact Iff.of_eq (congrArg (fun u => χ.1 u = 1) (finId_det_locGL v g).symm)

private theorem isLocallyConstant_chiAt {K : Type} [Field K] [NumberField K] (n : ℕ) (χ : HChar K) (v : Pl K) :
    IsLocallyConstant (chiAt n χ v) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hc : Continuous fun y : Gw n v => x⁻¹ * y := continuous_const.mul continuous_id
  have hm : (fun y : Gw n v => x⁻¹ * y) ⁻¹' {g : Gw n v | χ.loc v (Matrix.GeneralLinearGroup.det g) = 1} ∈ nhds x :=
    ((isOpen_ker_chiAt n χ v).preimage hc).mem_nhds (by simp)
  filter_upwards [hm] with y hy
  have hy' : χ.loc v (Matrix.GeneralLinearGroup.det (x⁻¹ * y)) = 1 := hy
  rw [map_mul, map_mul, map_inv, map_inv] at hy'
  have e : χ.loc v (Matrix.GeneralLinearGroup.det y) = χ.loc v (Matrix.GeneralLinearGroup.det x) :=
    (inv_mul_eq_one.1 hy').symm
  simp only [chiAt, e]

theorem chiBasic : ChiBasic := by
  intro K _ _ n χ v
  refine ⟨isLocallyConstant_chiAt n χ v, fun g => ?_, fun f hf => ?_⟩
  · simp [chiAt, HChar.loc, ← Units.val_mul]
  · exact ⟨hf.1.mul (isLocallyConstant_chiAt n χ v), hf.2.mul_right⟩

end UpperTheory.Gal.InertialTypesAlt.G
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.CmpIso
section
noncomputable section

open NumberField IsDedekindDomain
open GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

namespace UpperTheory.Gal.InertialTypesAlt.G

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private def evalEquiv {v : Pl F} (w : PlacesOver E v) (hw : ∀ u : PlacesOver E v, u = w) :
    CompletionsOver E v ≃+* w.1.adicCompletion E :=
  letI : Unique (PlacesOver E v) := ⟨⟨w⟩, hw⟩
  RingEquiv.piUnique fun u : PlacesOver E v => u.1.adicCompletion E

private theorem evalEquiv_symm_cont {v : Pl F} (w : PlacesOver E v) (hw : ∀ u : PlacesOver E v, u = w) :
    Continuous (evalEquiv w hw).symm :=
  letI : Unique (PlacesOver E v) := ⟨⟨w⟩, hw⟩
  (Homeomorph.piUnique fun u : PlacesOver E v => u.1.adicCompletion E).symm.continuous

private def cmpEquiv (n : ℕ) {v : Pl F} (w : PlacesOver E v) (hw : ∀ u : PlacesOver E v, u = w) :
    GL (Fin n) (CompletionsOver E v) ≃ₜ* Gw n w.1 where
  toFun := GM.cmp w
  invFun := mapGL n ((evalEquiv w hw).symm : w.1.adicCompletion E →+* CompletionsOver E v)
  left_inv g := Units.ext (Matrix.ext fun _ _ => (evalEquiv w hw).symm_apply_apply _)
  right_inv g := Units.ext (Matrix.ext fun _ _ => (evalEquiv w hw).apply_symm_apply _)
  map_mul' := map_mul _
  continuous_toFun := Continuous.units_map _ (continuous_id.matrix_map (continuous_apply w))
  continuous_invFun := Continuous.units_map _ (continuous_id.matrix_map (evalEquiv_symm_cont w hw))

end

theorem cmpIso : CmpIso := by
  intro F E _ _ _ _ _ n v w hw
  refine ⟨⟨cmpEquiv n w hw, fun _ => rfl⟩, fun g => ⟨fun h => h w, fun h u => ?_⟩, fun h => funext fun g => ?_⟩
  · obtain rfl := hw u
    exact h
  · letI : Unique (PlacesOver E v) := ⟨⟨w⟩, hw⟩
    exact finprod_unique _

end UpperTheory.Gal.InertialTypesAlt.G
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.IsIntegralOpUntw
section
open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open UpperTheory.Gal.InertialTypesAlt.G

private theorem hasFinTrace_conj {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (e : V ≃ₗ[ℂ] W) {A : V →ₗ[ℂ] V} {c : ℂ} (h : HasFinTrace A c) :
    HasFinTrace ((e : V →ₗ[ℂ] W) ∘ₗ A ∘ₗ (e.symm : W →ₗ[ℂ] V)) c := by
  obtain ⟨hfd, rfl⟩ := h
  set B : W →ₗ[ℂ] W := (e : V →ₗ[ℂ] W) ∘ₗ A ∘ₗ (e.symm : W →ₗ[ℂ] V) with hB
  have hr : (LinearMap.range A).map (e : V →ₗ[ℂ] W) = LinearMap.range B := by
    ext y
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨e x, by simp [hB]⟩
    · rintro ⟨y, rfl⟩
      exact ⟨A (e.symm y), ⟨_, rfl⟩, by simp [hB]⟩
  let f : LinearMap.range A ≃ₗ[ℂ] LinearMap.range B :=
    (e.submoduleMap (LinearMap.range A)).trans (LinearEquiv.ofEq _ _ hr)
  refine ⟨f.finiteDimensional, ?_⟩
  rw [← LinearMap.trace_conj' _ f]
  congr 1

private theorem isIntegralOp_tw {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] {m : Measure G}
    {χ : G → ℂ} {τ τ₁ : SmIrr G} {e : τ.V ≃ₗ[ℂ] τ₁.V} (hT : TwOf χ τ τ₁ e) {f : G → ℂ} {A : τ.V →ₗ[ℂ] τ.V}
    (hA : IsIntegralOp m τ.ρ (fun g => f g * χ g) A) :
    IsIntegralOp m τ₁.ρ f ((e : τ.V →ₗ[ℂ] τ₁.V) ∘ₗ A ∘ₗ (e.symm : τ₁.V →ₗ[ℂ] τ.V)) := by
  intro w l
  have key : (fun g => f g * l (τ₁.ρ g w)) =
      fun g => f g * χ g * (l ∘ₗ (e : τ.V →ₗ[ℂ] τ₁.V)) (τ.ρ g (e.symm w)) := by
    funext g
    have := hT g (e.symm w)
    rw [LinearEquiv.apply_symm_apply] at this
    rw [← this, map_smul, map_smul, smul_eq_mul]
    simp [mul_assoc]
  obtain ⟨h₁, h₂⟩ := hA (e.symm w) (l ∘ₗ (e : τ.V →ₗ[ℂ] τ₁.V))
  rw [key]
  refine ⟨h₁, ?_⟩
  rw [← h₂]
  simp

private theorem isIntegralOp_untw {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] {m : Measure G}
    {χ : G → ℂ} {τ τ₁ : SmIrr G} {e : τ.V ≃ₗ[ℂ] τ₁.V} (hT : TwOf χ τ τ₁ e) {f : G → ℂ} {B : τ₁.V →ₗ[ℂ] τ₁.V}
    (hB : IsIntegralOp m τ₁.ρ f B) :
    IsIntegralOp m τ.ρ (fun g => f g * χ g) ((e.symm : τ₁.V →ₗ[ℂ] τ.V) ∘ₗ B ∘ₗ (e : τ.V →ₗ[ℂ] τ₁.V)) := by
  intro v l
  have key : (fun g => f g * χ g * l (τ.ρ g v)) =
      fun g => f g * (l ∘ₗ (e.symm : τ₁.V →ₗ[ℂ] τ.V)) (τ₁.ρ g (e v)) := by
    funext g
    rw [← hT g v]
    simp [mul_assoc]
  obtain ⟨h₁, h₂⟩ := hB (e v) (l ∘ₗ (e.symm : τ₁.V →ₗ[ℂ] τ.V))
  rw [key]
  refine ⟨h₁, ?_⟩
  rw [← h₂]
  simp

theorem UpperTheory.Gal.InertialTypesAlt.G.trTw :
    UpperTheory.Gal.InertialTypesAlt.G.TrTw := by
  intro G _ _ _ m χ τ τ₁ e hT f z
  refine ⟨⟨?_, ?_⟩, fun I => ⟨?_, ?_⟩⟩
  · rintro ⟨A, hA, hF⟩
    exact ⟨_, isIntegralOp_tw hT hA, hasFinTrace_conj e hF⟩
  · rintro ⟨B, hB, hF⟩
    exact ⟨_, isIntegralOp_untw hT hB, hasFinTrace_conj e.symm hF⟩
  · rintro ⟨A, hA, hF⟩
    refine ⟨_, isIntegralOp_tw hT hA, ?_⟩
    convert hasFinTrace_conj e hF using 1
    ext x
    simp
  · rintro ⟨B, hB, hF⟩
    refine ⟨_, isIntegralOp_untw hT hB, ?_⟩
    convert hasFinTrace_conj e.symm hF using 1
    ext x
    simp
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.LevEx
section
open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open UpperTheory.Gal.InertialTypesAlt.G

theorem UpperTheory.Gal.InertialTypesAlt.G.levEx :
    UpperTheory.Gal.InertialTypesAlt.G.LevEx := by
  intro G _ _ _ K f hK hN hf
  obtain ⟨hlc, hcs⟩ := hf
  have h1 : ∀ x : G, ∃ V : Subgroup G, IsOpen (V : Set G) ∧ ∀ a ∈ V, f (a * x) = f x := by
    intro x
    have hopen : IsOpen ((fun a : G => a * x) ⁻¹' (f ⁻¹' {f x})) :=
      (hlc.isOpen_fiber (f x)).preimage (continuous_mul_const x)
    obtain ⟨V, hV, hVs⟩ := hN _ (hopen.mem_nhds (by simp))
    exact ⟨V, hV, fun a ha => by simpa using hVs (SetLike.mem_coe.2 ha)⟩
  choose V hVo hVc using h1
  obtain ⟨t, -, hcov⟩ := hcs.isCompact.elim_nhds_subcover
    (fun x => (fun y : G => y * x⁻¹) ⁻¹' (V x : Set G))
    (fun x _ => ((hVo x).preimage (continuous_mul_const x⁻¹)).mem_nhds (by simp [one_mem]))
  have hz : ∀ y, (∀ x ∈ t, y * x⁻¹ ∉ V x) → f y = 0 := by
    intro y hy
    by_contra h
    have hm := hcov (subset_tsupport f (Function.mem_support.2 h))
    simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe, exists_prop] at hm
    obtain ⟨x, hx, hxy⟩ := hm
    exact hy x hx hxy
  have hNU : (K : Set G) ∩ ⋂ x ∈ t, (V x : Set G) ∈ nhds (1 : G) :=
    inter_mem (hK.mem_nhds K.one_mem)
      ((Filter.biInter_finset_mem t).2 fun x _ => (hVo x).mem_nhds (V x).one_mem)
  obtain ⟨U, hU, hUs⟩ := hN _ hNU
  refine ⟨U, hU, fun u hu => (hUs hu).1, fun u hu g => ?_⟩
  have hUV : ∀ x ∈ t, u ∈ V x := fun x hx => by
    have h2 := (hUs hu).2
    simp only [Set.mem_iInter, SetLike.mem_coe] at h2
    exact h2 x hx
  by_cases hg : ∃ x ∈ t, g * x⁻¹ ∈ V x
  · obtain ⟨x, hx, hgx⟩ := hg
    have e1 := hVc x _ hgx
    have e2 := hVc x _ ((V x).mul_mem (hUV x hx) hgx)
    have r1 : g * x⁻¹ * x = g := by group
    have r2 : u * (g * x⁻¹) * x = u * g := by group
    rw [r1] at e1
    rw [r2] at e2
    rw [e1, e2]
  · push_neg at hg
    rw [hz g hg, hz (u * g)]
    intro x hx hm
    apply hg x hx
    have h3 := (V x).mul_mem ((V x).inv_mem (hUV x hx)) hm
    have r3 : u⁻¹ * (u * g * x⁻¹) = g * x⁻¹ := by group
    rwa [r3] at h3
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.LocTw
section
open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open UpperTheory.Gal.InertialTypesAlt.G

theorem UpperTheory.Gal.InertialTypesAlt.G.locTw :
    UpperTheory.Gal.InertialTypesAlt.G.LocTw := by
  intro K _ _ _ n _ π χ v τ hτ
  have h' : (π.twist χ).IsLocComp v (τ.twist (CuspSub.locDet n χ v) (CuspSub.isOpen_ker_locDet χ v)) :=
    PositivityTheory.RSHS.LocalComponentTwist.isLocComp_twist π χ hτ
  refine ⟨⟨_, h'⟩, fun τ₁ h₁ => ?_⟩
  obtain ⟨e⟩ := GlobalTheory.CuspRep.LocUniq.isLocComp_unique (π.twist χ) v _ τ₁ h' h₁
  refine ⟨e.toLinearEquiv, fun g x => ?_⟩
  exact LinearMap.congr_fun (e.isIntertwining' g) x
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.NormInt
section
open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open UpperTheory.Gal.InertialTypesAlt.G

private theorem valued_le_one {F : Type} [Field F] [NumberField F] (v : Pl F) {x : v.adicCompletion F}
    (h : x ∈ (ValuativeRel.valuation (v.adicCompletion F)).integer) : Valued.v x ≤ 1 := by
  haveI : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation _) Valued.v).le_one_iff_le_one.1
    ((Valuation.mem_integer_iff _ _).1 h)

private theorem isUnitAt_det {F : Type} [Field F] [NumberField F] (v : Pl F) (n : ℕ)
    {g : GL (Fin n) (v.adicCompletion F)} (hg : g ∈ GLnLocal.integralGL (v.adicCompletion F) n) :
    IsUnitAt v (Matrix.GeneralLinearGroup.det g) := by
  obtain ⟨u, rfl⟩ := hg
  have e : ((Matrix.GeneralLinearGroup.det (GLnLocal.integralGLHom (v.adicCompletion F) n u) :
      (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      ((Matrix.GeneralLinearGroup.det u).val : v.adicCompletion F) := by
    show ((RingHom.mapMatrix (ValuativeRel.valuation (v.adicCompletion F)).integer.subtype)
      (u : Matrix (Fin n) (Fin n) _)).det = _
    rw [← RingHom.map_det]
    rfl
  change Valued.v _ = 1
  rw [e]
  generalize Matrix.GeneralLinearGroup.det u = d
  have h1 := valued_le_one v d.val.2
  have h2 := valued_le_one v (d⁻¹).val.2
  have h3 : Valued.v (d.val : v.adicCompletion F) * Valued.v ((d⁻¹).val : v.adicCompletion F) = 1 := by
    rw [← map_mul, ← Subring.coe_mul, Units.mul_inv]
    simp
  exact le_antisymm h1 (h3 ▸ mul_le_of_le_one_right' h2)

theorem UpperTheory.Gal.InertialTypesAlt.G.normInt :
    UpperTheory.Gal.InertialTypesAlt.G.NormInt := by
  intro F E _ _ _ _ _ _ _ _ σ _ _ n _ v hv g hg η hη
  exact UpperTheory.ConvolutionTheory.Sph.normUnr F E η hη v hv _ (isUnitAt_det v n hg)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.NormTriv
section
open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC Formalism.ConjugateSelfDual UpperTheory.ConvolutionTheory.T
open scoped Classical
open UpperTheory.Gal.InertialTypesAlt.G

private theorem loc_one_of' {L : Type} [Field L] [NumberField L] (ψ : HChar L) (w : HeightOneSpectrum (𝓞 L))
    (hu : ψ.UnrAt w) (hv : ψ.val w = 1) (x : (w.adicCompletion L)ˣ) : ψ.loc w x = 1 := by
  refine GlobalTheory.FrobDense.eq_one_of_unif (ψ.loc w) (fun y hy => ?_) x
  have h2 := unif_spec w
  have h3 := hu (y * (atFin w (unif w))⁻¹) (by
    unfold IsUnitAt
    unfold IsUnifAt at hy h2
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hy, h2]
    exact mul_inv_cancel₀ WithZero.exp_ne_zero)
  rw [map_mul, map_inv, mul_inv_eq_one] at h3
  exact h3.trans hv

theorem UpperTheory.Gal.InertialTypesAlt.G.normTriv :
    UpperTheory.Gal.InertialTypesAlt.G.NormTriv := by
  intro F E _ _ _ _ _ η hη x
  let ψ : HChar E := ⟨η.1.comp (GroundTheory.Global.ideleNorm F E), η.2.1.comp GroundTheory.Global.continuous_ideleNorm, fun k =>
    (congrArg η.1 (GroundTheory.Global.ideleNorm_diagonal (K := F) k)).trans (η.2.2 _)⟩
  have hψ : ∀ x, ψ.1 x = η.1 (GroundTheory.Global.ideleNorm F E x) := fun _ => rfl
  have hev : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ψ.UnrAt w ∧ ψ.val w = 1 := by
    filter_upwards [hη.2.2, (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under F E).eventually
      (Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified η))] with w h1 h2
    have hf := GlobalTheory.ArtinTransport.normV_eq_pow (E := F) (E' := E) (v := w.under (𝓞 F)) (w := w) rfl
    obtain ⟨a, b⟩ := GlobalTheory.NormValGen.unrAt_val_of_comp_norm F E η ψ hψ w _ hf h2
    exact ⟨a, b.trans (h1 _ hf)⟩
  have h1 : ψ.1 = 1 := GlobalTheory.FrobDense.eq_one_of_away ψ.1 ψ.2.1 ψ.2.2 (Filter.eventually_cofinite.1 hev).toFinset
    fun w hw y => by
      have := not_not.1 (fun h => hw ((Set.Finite.mem_toFinset _).2 h))
      exact loc_one_of' ψ w this.1 this.2 y
  rw [← hψ, h1]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.PowNe
section
open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open UpperTheory.Gal.InertialTypesAlt.G

theorem UpperTheory.Gal.InertialTypesAlt.G.powNe :
    UpperTheory.Gal.InertialTypesAlt.G.PowNe := by
  intro Z hZ h0
  by_contra h
  rw [Filter.not_frequently] at h
  obtain ⟨ζ, hζ⟩ := Multiset.exists_mem_of_ne_zero hZ
  have h1 := UpperTheory.ConvolutionTheory.C.powIndep Unit (fun _ => 1) (fun _ => Z) (fun _ => h0)
    (h.mono fun j hj => by simpa using hj) ζ
  have h2 : ((Multiset.filter (· = ζ) Z).card : ℂ) = 0 := by simpa only [Finset.univ_unique, Finset.sum_singleton, one_mul] using h1
  have h3 : (Multiset.filter (· = ζ) Z).card = 0 := by exact_mod_cast h2
  have h4 : 0 < (Multiset.filter (· = ζ) Z).card :=
    Multiset.card_pos_iff_exists_mem.2 ⟨ζ, Multiset.mem_filter.2 ⟨hζ, rfl⟩⟩
  exact h4.ne' h3
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.TrBasic
section
open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open UpperTheory.Gal.InertialTypesAlt.G

namespace UpperTheory.Gal.InertialTypesAlt.G.FiniteTraces

private theorem finTrace_zero {V : Type} [AddCommGroup V] [Module ℂ V] :
    HasFinTrace (0 : V →ₗ[ℂ] V) 0 := by
  have key : ∀ (R : Submodule ℂ V) (h : ∀ v ∈ R, (0 : V →ₗ[ℂ] V) v ∈ R),
      LinearMap.trace ℂ R ((0 : V →ₗ[ℂ] V).restrict h) = 0 := by
    intro R h
    have e : (0 : V →ₗ[ℂ] V).restrict h = 0 := rfl
    rw [e, map_zero]
  exact ⟨by rw [LinearMap.range_zero]; infer_instance, key _ _⟩

private theorem finTrace_smul {V : Type} [AddCommGroup V] [Module ℂ V] (A : V →ₗ[ℂ] V) {c : ℂ} (b : ℂ)
    (h : HasFinTrace A c) : HasFinTrace (b • A) (b * c) := by
  by_cases hb : b = 0
  · subst hb
    rw [zero_smul, zero_mul]
    exact finTrace_zero
  obtain ⟨hf, rfl⟩ := h
  have key : ∀ (R : Submodule ℂ V) (_ : R = LinearMap.range A) (h1 : ∀ v ∈ R, (b • A) v ∈ R)
      (h2 : ∀ v ∈ LinearMap.range A, A v ∈ LinearMap.range A),
      LinearMap.trace ℂ R ((b • A).restrict h1) = b * LinearMap.trace ℂ (LinearMap.range A) (A.restrict h2) := by
    intro R hR h1 h2
    subst hR
    have e : (b • A).restrict h1 = b • A.restrict h2 := rfl
    rw [e, map_smul, smul_eq_mul]
  have hr : LinearMap.range (b • A) = LinearMap.range A := LinearMap.range_smul _ _ hb
  exact ⟨by rw [hr]; exact hf, key _ hr _ _⟩

private theorem isInt_smul {G V : Type} [Group G] [MeasurableSpace G] [AddCommGroup V] [Module ℂ V]
    {m : Measure G} {ρ : Representation ℂ G V} {f : G → ℂ} {A : V →ₗ[ℂ] V} (d : ENNReal) (hdt : d ≠ ⊤)
    (hA : IsIntegralOp m ρ f A) : IsIntegralOp (d • m) ρ f ((d.toReal : ℂ) • A) := fun v l =>
  ⟨(hA v l).1.smul_measure hdt, by
    rw [integral_smul_measure, LinearMap.smul_apply, map_smul, (hA v l).2, Complex.real_smul, smul_eq_mul]⟩

private theorem finite_comp {V : Type} [AddCommGroup V] [Module ℂ V] (A : V →ₗ[ℂ] V) (I : V ≃ₗ[ℂ] V)
    (h : FiniteDimensional ℂ (LinearMap.range A)) :
    FiniteDimensional ℂ (LinearMap.range (A ∘ₗ (I : V →ₗ[ℂ] V))) := by
  have e : LinearMap.range (A ∘ₗ (I : V →ₗ[ℂ] V)) = LinearMap.range A :=
    LinearMap.range_comp_of_range_eq_top A (LinearEquiv.range I)
  rw [e]
  exact h

end UpperTheory.Gal.InertialTypesAlt.G.FiniteTraces

open UpperTheory.Gal.InertialTypesAlt.G.FiniteTraces in
theorem UpperTheory.Gal.InertialTypesAlt.G.trBasic :
    UpperTheory.Gal.InertialTypesAlt.G.TrBasic := by
  intro G _ _ _ m τ I f
  refine ⟨?_, ?_, ?_⟩
  · rintro z ⟨A, hA, hF⟩
    exact ⟨_, A, hA, finite_comp A I hF.1, rfl⟩
  · rintro t t' ⟨A, hA, -, rfl⟩ ⟨B, hB, -, rfl⟩
    obtain rfl := hA.unique hB
    rfl
  · intro d hd
    refine ⟨?_, ?_⟩
    · rintro z ⟨A, hA, hF⟩
      exact ⟨_, isInt_smul d hd hA, finTrace_smul A _ hF⟩
    · rintro t ⟨B, hB, hF⟩
      refine ⟨_, isInt_smul d hd hB, ?_⟩
      have e : ((d.toReal : ℂ) • B) ∘ₗ (I : τ.V →ₗ[ℂ] τ.V) = (d.toReal : ℂ) • (B ∘ₗ (I : τ.V →ₗ[ℂ] τ.V)) := rfl
      rw [e]
      exact finTrace_smul _ _ hF
end

