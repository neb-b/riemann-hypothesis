module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchPowAlt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.Bundle0005
public import Development.AutomorphicArithmetic.TwistedTraces.ExistsUniqueEigenlineOfRankOneOccurs
public import Development.AutomorphicArithmetic.TwistedTraces.Bundle0012
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.CarryLift
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.IsoEq
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.NormCharPowHolds
public import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.EllipticTorusNorm
public import GroundTheory.GlobalFields.NormResidueSymbol.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Bundle0002
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.SelmerRankBoundLaurent
public import GroundTheory.GlobalFields.IdeleGroups.Bundle0003
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.BaseTw
section
open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open scoped ComplexConjugate

namespace UpperTheory.Gal.InertialTypesAlt.G.StableBaseChangeTwists

private theorem test_ind {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {J : Subgroup G} (hJ : CO J)
    {χ : G → ℂ} (hχ : IsChr J χ) : Test ((J : Set G).indicator fun x => conj (χ x)) := by
  refine ⟨(IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_,
    HasCompactSupport.intro hJ.1 fun x hx => Set.indicator_of_notMem hx _⟩
  by_cases hx : x ∈ (J : Set G)
  · filter_upwards [hJ.2.mem_nhds hx, (IsLocallyConstant.iff_eventually_eq _).1 hχ.1 x] with y hy hy2
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx, hy2]
  · have hcl : IsClosed (J : Set G) := Subgroup.isClosed_of_isOpen J hJ.2
    filter_upwards [hcl.isOpen_compl.mem_nhds hx] with y hy
    rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

section Loc
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

private theorem cmp_surj {v : Pl F} (w : PlacesOver E v) (h : ∀ u : PlacesOver E v, u = w) :
    Function.Surjective (GM.cmp (n := n) w) := by
  have hev : Function.Bijective (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w) := by
    letI : Unique (PlacesOver E v) := ⟨⟨w⟩, h⟩
    constructor
    · intro a b e
      funext u
      obtain rfl := h u
      exact e
    · intro z
      refine ⟨fun u => (h u).symm ▸ z, ?_⟩
      show ((h w).symm ▸ z : (w.1.adicCompletion E)) = z
      rfl
  let e := RingEquiv.ofBijective _ hev
  intro y
  refine ⟨mapGL n (e.symm : _ →+* _) y, ?_⟩
  exact Units.ext (Matrix.ext fun a b => e.apply_symm_apply _)

variable [IsGalois F E] {σ : E ≃ₐ[F] E} {q : Pl F} {w₀ : PlacesOver E q}

private theorem stabV (T : Ty σ n q w₀) (v : Pl F) (h : ∀ u : PlacesOver E v, u = T.mk' v)
    {a : Gw n (T.mk' v).1 →* Gw n (T.mk' v).1} (ha : IsLocGal σ (T.mk' v) a) (x : Gw n (T.mk' v).1) (hx : x ∈ T.J (T.mk' v).1) :
    a x ∈ T.J (T.mk' v).1 ∧ T.χ (T.mk' v).1 (a x) = T.χ (T.mk' v).1 x := by
  obtain ⟨g, rfl⟩ := cmp_surj (T.mk' v) h x
  letI : Unique (PlacesOver E v) := ⟨⟨T.mk' v⟩, h⟩
  have hall : ∀ u : PlacesOver E v, GM.cmp u g ∈ T.J u.1 := fun u => by
    obtain rfl := h u
    exact hx
  obtain ⟨h1, h2⟩ := T.stable v g hall
  rw [finprod_unique, finprod_unique] at h2
  have e : (default : PlacesOver E v) = T.mk' v := rfl
  rw [e] at h2
  rw [← ha]
  exact ⟨h1 _, h2⟩

end Loc

end UpperTheory.Gal.InertialTypesAlt.G.StableBaseChangeTwists

open UpperTheory.Gal.InertialTypesAlt.G.StableBaseChangeTwists in
theorem UpperTheory.Gal.InertialTypesAlt.G.baseTw :
    UpperTheory.Gal.InertialTypesAlt.G.BaseTw := by
  intro F E _ _ _ _ _ _ _ _ σ hgen hpr n hn μ _ V hV q w₀ T v hU hrk hne _ _ m hm τ s I hocc hs hI
  haveI := hm
  have hco := T.co (T.mk' v).1
  have hch := T.chr (T.mk' v).1
  have hT := test_ind hco hch
  refine ⟨hT, ?_⟩
  have h0 : m (T.J (T.mk' v).1) ≠ 0 := (hco.2.measure_pos m ⟨1, Subgroup.one_mem _⟩).ne'
  have ht : m (T.J (T.mk' v).1) ≠ ⊤ := hco.1.measure_lt_top.ne
  have hd0 : (m (T.J (T.mk' v).1))⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 ht
  have hdt : (m (T.J (T.mk' v).1))⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 h0
  obtain ⟨mm, hmm⟩ : ∃ mm, mm = (m (T.J (T.mk' v).1))⁻¹ • m := ⟨_, rfl⟩
  haveI hmmH : mm.IsHaarMeasure := hmm ▸ Measure.IsHaarMeasure.smul _ hd0 hdt
  have hmm1 : mm (T.J (T.mk' v).1) = 1 := by
    rw [hmm, Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 ht]
  have hback : (m (T.J (T.mk' v).1)) • mm = m := by
    rw [hmm, smul_smul, ENNReal.mul_inv_cancel h0 ht, one_smul]
  obtain ⟨e, he0, he1, he2⟩ := UpperTheory.exists_unique_eigenline_of_rankOne_occurs E n μ V hV (T.mk' v).1 τ hocc (T.J (T.mk' v).1) (T.χ (T.mk' v).1)
    hco hch hrk hne
  obtain ⟨-, -, h3⟩ := UpperTheory.ConvolutionTheory.C.occursBasics E n μ V (T.mk' v).1 mm hV
  obtain ⟨_, A, hA, -⟩ := h3 τ hocc _ hT
  obtain ⟨t, ht0, htt⟩ := UpperTheory.integralOp_eigenline_scalar_of_twist (Gw n (T.mk' v).1) mm τ I s (T.J (T.mk' v).1) (T.χ (T.mk' v).1) A e hco hch
    hmm1 hA he0 he1 he2 (stabV T v hU hs) hI
  have hsc := ((UpperTheory.Gal.InertialTypesAlt.G.trBasic _ mm τ I _).2.2 _ ht).2 t htt
  rw [hback] at hsc
  refine ⟨_, mul_ne_zero (Complex.ofReal_ne_zero.2 (ENNReal.toReal_ne_zero.2 ⟨h0, ht⟩)) ht0, hsc⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.FibTrace
section
open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open UpperTheory.Gal.InertialTypesAlt.G

theorem UpperTheory.Gal.InertialTypesAlt.G.fibTrace :
    UpperTheory.Gal.InertialTypesAlt.G.FibTrace := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn μE _ μF _ π P V Λ t hC hAt hW V₀ Λ₀ t₀ hS hAt₀ hΛ ht v _ m τ τ₀ hτ hO f z hf hz
  obtain ⟨π₀, hπ₀, -⟩ := Dp.exCusp F n μF V₀ hS
  obtain ⟨-, -, hcl, -⟩ := T.carryLift F E σ hσ hp n hn μE μF
  have hl := hcl π₀ P V₀ V Λ₀ t₀ Λ t hπ₀ hC hAt₀ hAt hΛ ht
  obtain ⟨η, hη, hiso⟩ := (R.fibre_holds F E hp n hn (.cx π₀) (.cx P) hl.1).2 (.cx π) hW
  have he : π₀.twist η = π := (Dp.isoEq F n _ _).1 hiso
  subst he
  have hτ₀ : (Cusp.cx π₀).locComp v τ₀ :=
    ((Dp.locIff F n μF π₀ V₀ hπ₀ v τ₀).trans (occursIff F n μF V₀ hπ₀.summand v τ₀).symm).2 hO
  obtain ⟨e, hTw⟩ := (locTw F n hn π₀ η v τ₀ hτ₀).2 τ hτ
  have hfe : (fun g => f g * chiAt n η v g) = f := by
    funext g
    by_cases h0 : f g = 0
    · simp [h0]
    · have h1 : chiAt n η v g = 1 := by
        rcases hη with rfl | hη
        · rfl
        · simp only [chiAt]
          rw [(hf g h0) η hη]
          rfl
      rw [h1, mul_one]
  have h := ((trTw (Gw n v) m (chiAt n η v) τ₀ τ e hTw f z).1).2 hz
  rwa [hfe] at h
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchPow
section
open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open UpperTheory.Gal.InertialTypesAlt.G

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem pow_loc {K : Type} [Field K] [NumberField K] {χ : HChar K} {s : ℂ} (h : T.IsPow χ s)
    (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    ((χ.loc v x : ℂˣ) : ℂ) = ((‖(x : v.adicCompletion K)‖ : ℝ) : ℂ) ^ s := by
  rw [← GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding v x]
  exact h _

private theorem norm_incl {v : Pl F} (w : PlacesOver E v) (hw : ∀ u : PlacesOver E v, u = w)
    (x : (v.adicCompletion F)ˣ) :
    ‖completionMap v w.1 (x : v.adicCompletion F)‖ = ‖(x : v.adicCompletion F)‖ ^ Module.finrank F E := by
  have hrk : Module.finrank (v.adicCompletion F) (w.1.adicCompletion E) = Module.finrank F E := by
    rw [← sum_finrank_eq E v, Finset.sum_eq_single w (fun b _ hb => absurd (hw b) hb) (by simp)]
  clear hw
  obtain ⟨w, hwv⟩ := w
  obtain rfl : GroundTheory.Global.AdeleBaseChange.below F w = v := (GroundTheory.Global.AdeleBaseChange.below_eq_iff w v).2 hwv
  haveI := hwv
  let y : (w.adicCompletion E)ˣ := Units.map (algebraMap ((GroundTheory.Global.AdeleBaseChange.below F w).adicCompletion F) (w.adicCompletion E)).toMonoidHom x
  have hn : GroundTheory.LocalField.normUnits ((GroundTheory.Global.AdeleBaseChange.below F w).adicCompletion F) (w.adicCompletion E) y = x ^ Module.finrank F E := by
    apply Units.ext
    rw [GroundTheory.LocalField.coe_normUnits]
    change Algebra.norm _ (algebraMap _ (w.adicCompletion E) (x : (GroundTheory.Global.AdeleBaseChange.below F w).adicCompletion F)) = _
    rw [Algebra.norm_algebraMap, hrk, Units.val_pow_eq_pow_val]
  have h2 := GroundTheory.Global.ideleNorm_finiteEmbedding (K := F) w y
  rw [hn] at h2
  have h3 := GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := F) (GroundTheory.Global.IdeleGroup.finiteEmbedding w y)
  rw [h2] at h3
  have h4 := congrArg Subtype.val h3
  rw [GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding, GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding,
    Units.val_pow_eq_pow_val, norm_pow] at h4
  exact h4.symm

private theorem norm_gal (σ : E ≃ₐ[F] E) {v : Pl F} (w : PlacesOver E v) (hw : ∀ u : PlacesOver E v, u = w)
    (y : CompletionsOver E v) : ‖galFin σ v y w‖ = ‖y w‖ := by
  have hfix : w.1 = σ • w.1 := (congrArg Subtype.val (hw (σ • w))).symm
  have h0 : galFin σ v y w = galEquiv v σ w.1 w.1 hfix (y w) := by
    obtain ⟨t, rfl⟩ := (tensorEquiv' E v).surjective y
    have h1 : galFin σ v (tensorEquiv' E v t) =
        tensorEquiv' E v (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F (v.adicCompletion F)) t) := by
      simp [galFin, galOf]
    rw [h1]
    clear h1
    induction t with
    | add a b ha hb => simp only [map_add (f := _), Pi.add_apply, ha, hb]
    | tmul x a =>
      rw [Algebra.TensorProduct.map_tmul, tensorEquiv'_tmul, tensorEquiv'_tmul, Pi.mul_apply, Pi.mul_apply, map_mul]
      congr 1
      · exact (galEquiv_algebraMap v σ w.1 w.1 hfix x).symm
      · exact ((galEquiv v σ w.1 w.1 hfix).commutes a).symm
  rw [h0]
  have hk : ∀ x : E, ‖algebraMap E (w.1.adicCompletion E) (σ x)‖ = ‖algebraMap E (w.1.adicCompletion E) x‖ := by
    intro x
    have key : ∀ u : HeightOneSpectrum (𝓞 E), u = σ • w.1 →
        ‖algebraMap E (u.adicCompletion E) (σ x)‖ = ‖algebraMap E (w.1.adicCompletion E) x‖ := by
      rintro _ rfl
      exact norm_algebraMap_smul σ w.1 x
    exact key _ hfix
  refine congrFun ((HeightOneSpectrum.denseRange_algebraMap E w.1).equalizer
    (continuous_norm.comp (continuous_galEquiv v σ w.1 w.1 hfix)) continuous_norm ?_) (y w)
  funext x
  simp only [Function.comp_apply, galEquiv_algebraMap, hk]

private theorem quotInt_mul_const {G T X : Type*} [Group G] [MeasurableSpace G] [MeasurableSpace T] [MeasurableSpace X]
    (μ : Measure X) (u : X → G) (j : T → G) (ν : Measure T) (Φ : X → ℂ) (c : ℂ) :
    quotInt μ u j ν (fun x => Φ x * c) = quotInt μ u j ν Φ * c := by
  unfold quotInt
  split_ifs with h
  · rw [← integral_mul_const]
    congr 1
    funext x
    ring
  · simp

private theorem det_mapGL {R S : Type*} [CommRing R] [CommRing S] (n : ℕ) (f : R →+* S) (g : GL (Fin n) R) :
    ((Matrix.GeneralLinearGroup.det (mapGL n f g) : Sˣ) : S) = f ((Matrix.GeneralLinearGroup.det g : Rˣ) : R) :=
  (RingHom.map_det f g.val).symm

private theorem chiAt_conj {K : Type} [Field K] [NumberField K] (n : ℕ) (χ : HChar K) (v : Pl K) (x γ : Gw n v) :
    chiAt n χ v (x⁻¹ * γ * x) = chiAt n χ v γ := by
  unfold chiAt
  simp only [map_mul, map_inv]
  rw [mul_comm _ (χ.loc v (Matrix.GeneralLinearGroup.det x)), mul_inv_cancel_left]

private theorem hom_twNorm {G : Type*} [Group G] (N : G → ℝ) (h0 : N 1 = 1) (h1 : ∀ a b, N (a * b) = N a * N b)
    (θ : Monoid.End G) (hθ : ∀ y, N (θ y) = N y) (m : ℕ) (δ : G) :
    N (PositivityTheory.Rg.Tf.Loc.twNorm θ m δ) = N δ ^ m := by
  have hp : ∀ (k : ℕ) (y : G), N ((θ ^ k) y) = N y := by
    intro k y
    induction k with
    | zero => rfl
    | succ k ih => rw [PositivityTheory.Rg.Tf.Loc.pow_succ_apply', hθ, ih]
  induction m with
  | zero => simp [h0]
  | succ m ih => rw [PositivityTheory.Rg.Tf.Loc.twNorm_succ, h1, ih, hp, pow_succ]

end SlopeTestRemainingChoices

theorem UpperTheory.Gal.InertialTypesAlt.G.matchPow :
    UpperTheory.Gal.InertialTypesAlt.G.MatchPow := by
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn z χ χ' h h' v w hw

  let N : GL (Fin n) (CompletionsOver E v) → ℝ := fun g =>
    ‖((Matrix.GeneralLinearGroup.det g : (CompletionsOver E v)ˣ) : CompletionsOver E v) w‖
  have hN0 : N 1 = 1 := by simp [N]
  have hN1 : ∀ a b, N (a * b) = N a * N b := fun a b => by simp [N]
  have hNθ : ∀ y, N (mapGL n (galFin σ v) y) = N y := fun y => by
    simp only [N]
    rw [det_mapGL, norm_gal σ w hw]
  have hχ' : ∀ g, chiAt n χ' w.1 (GM.cmp w g) = ((N g : ℝ) : ℂ) ^ z := fun g => by
    unfold chiAt
    rw [pow_loc h']
    have e : ((Matrix.GeneralLinearGroup.det (GM.cmp w g) : (w.1.adicCompletion E)ˣ) : w.1.adicCompletion E) =
        ((Matrix.GeneralLinearGroup.det g : (CompletionsOver E v)ˣ) : CompletionsOver E v) w :=
      det_mapGL n (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w) g
    rw [e]
  have hθ : ∀ x, chiAt n χ' w.1 (GM.cmp w (mapGL n (galFin σ v) x)) = chiAt n χ' w.1 (GM.cmp w x) := fun x => by
    rw [hχ', hχ', hNθ]
  have hsurj : ∀ g : Gw n w.1, ∃ g₀, GM.cmp w g₀ = g := fun g => by
    obtain ⟨⟨e, he⟩, -, -⟩ := cmpIso F E n v w hw
    exact ⟨e.symm g, by rw [← he, e.apply_symm_apply]⟩
  have hl : Module.finrank F E ≠ 0 := hp.ne_zero

  have hnorm : ∀ (γ : Gw n v) (δ : GL (Fin n) (CompletionsOver E v)),
      PositivityTheory.Rg.Tf.Loc.twNorm (mapGL n (galFin σ v)) (Module.finrank F E) δ = mapGL n (incFin E v) γ →
      chiAt n χ' w.1 (GM.cmp w δ) = chiAt n χ v γ := fun γ δ hδ => by
    have h1 := hom_twNorm N hN0 hN1 (mapGL n (galFin σ v)) hNθ (Module.finrank F E) δ
    rw [hδ] at h1
    have h2 : N (mapGL n (incFin E v) γ) =
        ‖((Matrix.GeneralLinearGroup.det γ : (v.adicCompletion F)ˣ) : v.adicCompletion F)‖ ^ Module.finrank F E := by
      simp only [N]
      rw [det_mapGL]
      exact norm_incl w hw _
    rw [h2] at h1
    have h3 := (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hl).1 h1
    rw [hχ']
    unfold chiAt
    rw [pow_loc h, h3]
  refine ⟨fun s hs g => ?_, ?_⟩
  · obtain ⟨g₀, rfl⟩ := hsurj g
    rw [← hs g₀, hθ]
  intro c φ f hm _ _ _ _ mE mF hE hF h1 h2 γ hγ ν hν
  obtain ⟨ha, hb⟩ := hm mE mF hE hF h1 h2 γ hγ ν hν
  have horb : orb mF γ ν (fun g => f g * chiAt n χ v g) = orb mF γ ν f * chiAt n χ v γ := by
    unfold orb
    rw [← quotInt_mul_const]
    congr 1
    funext x
    beta_reduce
    rw [chiAt_conj]
  refine ⟨fun δ hδ => ?_, fun hne => ?_⟩
  · have htw : twOrb (incFin E v) (galFin σ v) mE γ ν δ (fun g => φ (GM.cmp w g) * chiAt n χ' w.1 (GM.cmp w g)) =
        twOrb (incFin E v) (galFin σ v) mE γ ν δ (fun g => φ (GM.cmp w g)) * chiAt n χ' w.1 (GM.cmp w δ) := by
      unfold twOrb
      rw [← quotInt_mul_const]
      congr 1
      funext x
      beta_reduce
      have e : N x⁻¹ * N x = 1 := by rw [← hN1, inv_mul_cancel, hN0]
      have hc : N (x⁻¹ * δ * mapGL n (galFin σ v) x) = N δ := by
        rw [hN1, hN1, hNθ]
        linear_combination (N δ) * e
      rw [hχ' (x⁻¹ * δ * mapGL n (galFin σ v) x), hc, ← hχ' δ]
    rw [htw, horb, ha δ hδ, hnorm γ δ hδ]
    ring
  · rw [horb, hb hne, zero_mul]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.NormLoc
section
open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open UpperTheory.Gal.InertialTypesAlt.G

namespace UpperTheory.Gal.InertialTypesAlt.G.NL

open GroundTheory.Global.AdeleBaseChange PositivityTheory.Rg.Tf.Loc
open scoped NumberField.AdeleRing TensorProduct

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem galOf_tmul {A B : Type*} [CommRing A] [Algebra F A] [CommRing B] [Algebra E B]
    (e : E ⊗[F] A ≃ₐ[E] B) (σ : E ≃ₐ[F] E) (l : E) (a : A) :
    galOf e σ (e (l ⊗ₜ a)) = e (σ l ⊗ₜ a) := by
  simp [galOf]

private theorem tensor_atFin (v : HeightOneSpectrum (𝓞 F)) (l : E) (x : 𝔸[F]) :
    atFin v (adeleTensorEquiv F E (l ⊗ₜ x)) = tensorEquiv' E v (l ⊗ₜ x.2 v) := by
  funext ⟨w, hw⟩
  obtain rfl : below F w = v := (below_eq_iff w v).2 hw
  exact adeleTensorEquiv_tmul_snd l x w

private theorem atFin_galAd (σ : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (a : 𝔸[E]) :
    atFin v (galAd σ a) = galFin σ v (atFin v a) := by
  obtain ⟨t, rfl⟩ := (adeleTensorEquiv F E).surjective a
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul l x => rw [galAd, galOf_tmul, tensor_atFin, tensor_atFin, galFin, galOf_tmul]
  | add s t hs ht => simp only [map_add (f := _), hs, ht]

private theorem atFin_adeleMap (v : HeightOneSpectrum (𝓞 F)) (a : 𝔸[F]) :
    atFin v (adeleMap F E a) = incFin E v (a.2 v) := by
  funext ⟨w, hw⟩
  obtain rfl : below F w = v := (below_eq_iff w v).2 hw
  rfl

private theorem galAd_eq_smul (σ : E ≃ₐ[F] E) (a : 𝔸[E]) : galAd σ a = σ • a := by
  have h1 : (MulSemiringAction.toRingHom (E ≃ₐ[F] E) 𝔸[E] σ) = Formalism.L2.Host.CT.adMap σ.toRingEquiv :=
    UpperTheory.ConvolutionTheory.K.adUnique E σ.toRingEquiv _ (continuous_const_smul σ) fun x => smul_algebraMap σ x
  rw [UpperTheory.ConvolutionTheory.K.galAdEq, ← h1]
  rfl

private theorem atFin_pow_smul (σ : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (i : ℕ) (a : 𝔸[E]) :
    atFin v ((σ ^ i) • a) = (galFin σ v)^[i] (atFin v a) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ', mul_smul, ← galAd_eq_smul, atFin_galAd, ih, Function.iterate_succ_apply']

private theorem prod_gal [IsGalois F E] {M : Type*} [CommMonoid M] (σ : E ≃ₐ[F] E) (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ)
    (f : (E ≃ₐ[F] E) → M) : ∏ τ, f τ = ∏ i ∈ Finset.range (Module.finrank F E), f (σ ^ i) := by
  have ho : orderOf σ = Module.finrank F E := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hσ, IsGalois.card_aut_eq_finrank]
  have hinj : Function.Injective fun i : Fin (Module.finrank F E) => σ ^ (i : ℕ) := fun i j h =>
    Fin.ext (pow_injOn_Iio_orderOf (by simpa [ho] using i.2) (by simpa [ho] using j.2) h)
  have hbij : Function.Bijective fun i : Fin (Module.finrank F E) => σ ^ (i : ℕ) := by
    refine (Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, ?_⟩
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
  rw [← Fin.prod_univ_eq_prod_range (fun i => f (σ ^ i))]
  exact (Fintype.prod_bijective _ hbij _ _ fun _ => rfl).symm

private theorem det_iter {R : Type*} [CommRing R] (s : R →+* R) (n : ℕ) (θ : Monoid.End (GL (Fin n) R))
    (hθ : ∀ g, θ g = mapGL n s g) (i : ℕ) (δ : GL (Fin n) R) :
    ((Matrix.GeneralLinearGroup.det (θ^[i] δ) : Rˣ) : R) = s^[i] ((Matrix.GeneralLinearGroup.det δ : Rˣ) : R) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih, hθ]
    simp [Matrix.GeneralLinearGroup.det, RingHom.map_det]

private theorem det_twNorm {R : Type*} [CommRing R] (s : R →+* R) (n : ℕ) (θ : Monoid.End (GL (Fin n) R))
    (hθ : ∀ g, θ g = mapGL n s g) (l : ℕ) (δ : GL (Fin n) R) :
    ((Matrix.GeneralLinearGroup.det (twNorm θ l δ) : Rˣ) : R) =
      ∏ i ∈ Finset.range l, s^[i] ((Matrix.GeneralLinearGroup.det δ : Rˣ) : R) := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [twNorm_succ, map_mul, Units.val_mul, ih, Finset.prod_range_succ, Monoid.End.coe_pow, det_iter s n θ hθ]

end

end UpperTheory.Gal.InertialTypesAlt.G.NL

open UpperTheory.Gal.InertialTypesAlt.G.NL GroundTheory.Global.AdeleBaseChange PositivityTheory.Rg.Tf.Loc in
open scoped NumberField.AdeleRing in
theorem UpperTheory.Gal.InertialTypesAlt.G.normLoc :
    UpperTheory.Gal.InertialTypesAlt.G.NormLoc := by
  intro F E _ _ _ _ _ _ _ _ σ hσ _ n _ v γ δ h η hη
  set d : (CompletionsOver E v)ˣ := Matrix.GeneralLinearGroup.det δ with hd
  let du : ∀ u : PlacesOver E v, (u.1.adicCompletion E)ˣ := fun u =>
    Units.map (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) u).toMonoidHom d
  let x : IdeleGroup E := ∏ u : PlacesOver E v, IdeleGroup.finiteEmbedding u.1 (du u)
  have hc : ∀ u : PlacesOver E v, ∃ c : (v.adicCompletion F)ˣ,
      ideleNorm F E (IdeleGroup.finiteEmbedding u.1 (du u)) = IdeleGroup.finiteEmbedding v c := by
    rintro ⟨w, hw⟩
    obtain rfl : below F w = v := (below_eq_iff w v).2 hw
    exact ⟨_, ideleNorm_finiteEmbedding w _⟩
  choose c hc using hc
  have hx : ideleNorm F E x = IdeleGroup.finiteEmbedding v (∏ u, c u) := by
    simp only [x, map_prod, hc]
  have hat : atFin v (x : 𝔸[E]) = (d : CompletionsOver E v) := by
    funext w
    change (((IdeleGroup.finiteProj w.1 x : (w.1.adicCompletion E)ˣ)) : w.1.adicCompletion E) = _
    have : IdeleGroup.finiteProj w.1 x = du w := by
      simp only [x, map_prod]
      rw [Finset.prod_eq_single w (fun b _ hb => IdeleGroup.finiteProj_finiteEmbedding_of_ne
        (fun e => hb (Subtype.ext e.symm)) _) (by simp), IdeleGroup.finiteProj_finiteEmbedding]
    rw [this]
    rfl
  have hy : ∏ u, c u = Matrix.GeneralLinearGroup.det γ := by
    haveI := (GroundTheory.Global.nonempty_placesOver E v)
    apply Units.ext
    apply (incFin E v).injective
    have h1 : incFin E v ((∏ u, c u : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
        atFin v (adeleMap F E ((ideleNorm F E x : IdeleGroup F) : 𝔸[F])) := by
      rw [hx, atFin_adeleMap]
      congr 1
      exact (congrArg Units.val (IdeleGroup.finiteProj_finiteEmbedding v _)).symm
    rw [h1, coe_ideleNorm, adeleMap_norm, map_prod, prod_gal σ hσ]
    simp only [atFin_pow_smul, hat]
    rw [hd, ← det_twNorm (galFin σ v) n _ (fun _ => rfl), h]
    simp [Matrix.GeneralLinearGroup.det, RingHom.map_det]
  have h3 := UpperTheory.Gal.InertialTypesAlt.G.normTriv F E η hη x
  rw [hx, hy] at h3
  exact h3
end

