module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0665
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0659
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0672
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0560
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0341
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleClassesPropsOfFlatCoefficient
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleStd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0372
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0664
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0666
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0244
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0670
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0152
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0260
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSumsTwistsCharactersExpectedJumpsStatement
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_sums_twists_characters_expected_jumps : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ S : TopSit P, S.CrysCalc := by
  first | exact @GlobalTheory.TopSteps.CrysRules.crysCalc | exact GlobalTheory.TopSteps.CrysRules.crysCalc | (intros; apply GlobalTheory.TopSteps.CrysRules.crysCalc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionGroupActsResiduesFrobeniusPowerStatement
section
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.decompositionGroup_acts_residues_frobeniusPower : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (_h : IsPlaceOver A w),
    ∀ d ∈ Dec (F := E) A, ∀ y : Ω, ∃ K : IntermediateField E Ω, FiniteDimensional E K ∧ y ∈ K ∧
      ∃ j : ℕ, ∀ z ∈ K, A.valuation z ≤ 1 → A.valuation (d z - z ^ (normV w ^ j)) < 1 := by
  first | exact @GlobalTheory.DecFrobPow.exists_field_cong_pow | exact GlobalTheory.DecFrobPow.exists_field_cong_pow | (intros; apply GlobalTheory.DecFrobPow.exists_field_cong_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeterminantRecCompatible
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a}
  {e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ} {rc : IrrGL (k := w.adicCompletion E) → WD h}

theorem LawsLit.nu_eq_lpTw (H : LawsLit a ha e rc) (x : IrrGL (k := w.adicCompletion E)) (s : ℝ) :
    rc (x.nu s) = (rc x).lpTw s := by
  rw [IrrGL.nu, H.twist, H.one, lpChar_lpOfChar, WD.lpTw]
  congr 1
  exact ha.absPow_comp s

end GlobalTheory.LocLanglands

namespace GlobalTheory

theorem lawsLit_det : StandardCosocleGL → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ) (rc : IrrGL (k := w.adicCompletion E) → WD h), LawsLit a ha e rc → ∀ (t : ℕ) χ hχ, rc (cls (IrrRep.det (Fin t) χ hχ)) = sumList ((List.range t).map fun j : ℕ => (rc (.ofChar χ hχ)).lpTw (((t : ℝ) - 1) / 2 - j)) := by
  intro hSC E Ω _ _ _ _ _ A w h a ha e rc H t χ hχ
  haveI : CharZero (w.adicCompletion E) :=
    charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
  have hL := _root_.GlobalTheory.LocGL.isL_det hSC (w.adicCompletion E) t χ hχ
  obtain ⟨φ⟩ := (IrrRep.det (Fin t) χ hχ).nonempty_equiv_rep
  have hL' := hL.of_equiv φ.symm
  rw [H.langlands _ (cls (IrrRep.det (Fin t) χ hχ)) hL', segSum, List.map_map]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  simp only [Function.comp_apply]
  show ((rc ((IrrGL.ofChar χ hχ).nu ((((t : ℝ) - 1) / 2 - j : ℝ) : ℂ))).lpTw ((((1 : ℕ) : ℝ) - 1) / 2)).lpChar
      (WD.lpSp (h := h) 1) = _
  have h0 : ((((1 : ℕ) : ℝ) - 1) / 2) = 0 := by norm_num
  rw [h0, (GlobalTheory.T.weilDeligne_charpoly_twist_special E Ω A w h _).1, H.nu_eq_lpTw]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EquivariantIsoTransportCocyclesExtensions
section
open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

namespace GlobalTheory.TransportCoef

open Formalism.MainNotions.N (twistRep coefRep)
open ReciprocityTheory.Def (d0 d1 C1)

variable {O G : Type} [CommRing O] [Group G] {M M' : Type} [AddCommGroup M] [Module O M] [AddCommGroup M']
  [Module O M']

theorem rTensor_coefRep (W : Representation O G M) (W' : Representation O G M') (e : M →ₗ[O] M')
    (he : ∀ g x, e (W g x) = W' g (e x)) (X : Type) [AddCommGroup X] [Module O X] (g : G) (y : M ⊗[O] X) :
    LinearMap.rTensor X e (coefRep W X g y) = coefRep W' X g (LinearMap.rTensor X e y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul m x => rw [coefRep_tmul, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, coefRep_tmul, he]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _), map_add (f := _)]

theorem twist_intertwine (W : Representation O G M) (W' : Representation O G M') (e : M →ₗ[O] M')
    (he : ∀ g x, e (W g x) = W' g (e x)) (χ : G →* Oˣ) (g : G) (x : M) :
    e (twistRep W χ g x) = twistRep W' χ g (e x) := by
  rw [twistRep_apply, twistRep_apply, map_smul, he]

variable [TopologicalSpace G]

section General

variable {P P' : Type} [AddCommGroup P] [Module O P] [AddCommGroup P'] [Module O P']
  (π : Representation O G P) (π' : Representation O G P') (F : P →ₗ[O] P')
  (hF : ∀ g y, F (π g y) = π' g (F y))
include hF

theorem mem_Z1_comp {z : G → P} (hz : z ∈ Z1 π ⊤) : (fun g => F (z g)) ∈ Z1 π' ⊤ := by
  rw [Z1, Submodule.mem_inf] at hz ⊢
  obtain ⟨h1, h2⟩ := hz
  refine ⟨⟨h1.1.comp F, fun _ => Submodule.mem_top⟩, ?_⟩
  rw [LinearMap.mem_ker] at h2 ⊢
  funext x
  have := congrFun h2 x
  simp only [d1, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at this ⊢
  rw [← hF, ← map_sub, ← map_add (f := _), this, map_zero]

theorem cob_comp {z : G → P} (S : Set G) (b : P) (hb : ∀ g ∈ S, z g = π g b - b) :
    ∀ g ∈ S, F (z g) = π' g (F b) - F b := by
  intro g hg
  rw [hb g hg, map_sub, hF]

theorem mem_B1_comp {z : G → P} (hz : z ∈ B1 π ⊤) : (fun g => F (z g)) ∈ B1 π' ⊤ := by
  rw [ReciprocityTheory.Def.B1, Submodule.mem_map] at hz ⊢
  obtain ⟨b, -, rfl⟩ := hz
  refine ⟨F b, Submodule.mem_top, ?_⟩
  funext g
  simp only [d0, LinearMap.coe_mk, AddHom.coe_mk]
  rw [map_sub, hF]

end General

end GlobalTheory.TransportCoef

namespace GlobalTheory.TransportCoef
open Formalism.MainNotions.N (twistRep coefRep)

theorem transport {O G : Type} [CommRing O] [Group G] [TopologicalSpace G] {M M' : Type} [AddCommGroup M]
    [Module O M] [AddCommGroup M'] [Module O M'] (W : Representation O G M) (W' : Representation O G M')
    (e : M ≃ₗ[O] M') (he : ∀ g x, e (W g x) = W' g (e x)) :
    ∀ (χ : G →* Oˣ) (X : Type) [AddCommGroup X] [Module O X] (z : G → M ⊗[O] X) (z' : G → M' ⊗[O] X),
      (∀ g, z' g = LinearEquiv.rTensor X e (z g)) →
      (z ∈ Z1 (twCoef W χ X) ⊤ ↔ z' ∈ Z1 (twCoef W' χ X) ⊤) ∧
      (∀ (hz : z ∈ Z1 (twCoef W χ X) ⊤) (hz' : z' ∈ Z1 (twCoef W' χ X) ⊤) {c : O} (hc : ∀ x : X, c • x = 0),
        ∃ f : ((M ⊗[O] X) × (O ⧸ Ideal.span {c})) ≃ₗ[O] ((M' ⊗[O] X) × (O ⧸ Ideal.span {c})),
          ∀ g x, f (Ea W χ hc ⟨z, hz⟩ g x) = Ea W' χ hc ⟨z', hz'⟩ g (f x)) ∧
      (z ∈ B1 (twCoef W χ X) ⊤ ↔ z' ∈ B1 (twCoef W' χ X) ⊤) ∧
      ∀ I : Subgroup G, (∃ b, ∀ g ∈ I, z g = twCoef W χ X g b - b) ↔
        (∃ b', ∀ g ∈ I, z' g = twCoef W' χ X g b' - b') := by
  intro χ X _ _ z z' hzz
  have he' : ∀ g x, e.symm (W' g x) = W g (e.symm x) := fun g x => by
    apply e.injective
    rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  let E := LinearEquiv.rTensor X e
  have hE : ∀ y, E y = LinearMap.rTensor X (e : M →ₗ[O] M') y := fun _ => rfl
  have hEs : ∀ y, E.symm y = LinearMap.rTensor X (e.symm : M' →ₗ[O] M) y := by
    intro y
    apply E.injective
    rw [LinearEquiv.apply_symm_apply, hE, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
    simp
  have key : ∀ g y, (E : M ⊗[O] X →ₗ[O] M' ⊗[O] X) (twCoef W χ X g y) = twCoef W' χ X g (E y) := fun g y =>
    rTensor_coefRep (twistRep W χ⁻¹) (twistRep W' χ⁻¹) (e : M →ₗ[O] M')
      (twist_intertwine W W' (e : M →ₗ[O] M') he χ⁻¹) X g y
  have keys : ∀ g y, (E.symm : M' ⊗[O] X →ₗ[O] M ⊗[O] X) (twCoef W' χ X g y) = twCoef W χ X g (E.symm y) :=
    fun g y => by
      show E.symm _ = _
      rw [hEs, hEs]
      exact rTensor_coefRep (twistRep W' χ⁻¹) (twistRep W χ⁻¹) (e.symm : M' →ₗ[O] M)
        (twist_intertwine W' W (e.symm : M' →ₗ[O] M) he' χ⁻¹) X g y
  have keyc : ∀ g y, E (coefRep W X g y) = coefRep W' X g (E y) := fun g y =>
    rTensor_coefRep W W' (e : M →ₗ[O] M') he X g y
  have hz'f : z' = fun g => (E : M ⊗[O] X →ₗ[O] M' ⊗[O] X) (z g) := funext hzz
  have hzf : z = fun g => (E.symm : M' ⊗[O] X →ₗ[O] M ⊗[O] X) (z' g) := by
    funext g; show z g = E.symm (z' g); rw [hzz, LinearEquiv.symm_apply_apply]
  refine ⟨⟨fun hz => ?_, fun hz' => ?_⟩, ?_, ⟨fun hz => ?_, fun hz' => ?_⟩, fun I => ⟨?_, ?_⟩⟩
  · rw [hz'f]; exact mem_Z1_comp _ _ _ key hz
  · rw [hzf]; exact mem_Z1_comp _ _ _ keys hz'
  · intro hz hz' c hc
    refine ⟨E.prodCongr (LinearEquiv.refl O _), fun g x => ?_⟩
    obtain ⟨m, q⟩ := x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [LinearEquiv.prodCongr_apply, Ea_apply, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply,
      LinearEquiv.refl_apply, Ea_apply]
    simp only [Prod.mk.injEq, and_true]
    rw [map_add (f := _), map_smul, keyc, hzz]
  · rw [hz'f]; exact mem_B1_comp _ _ _ key hz
  · rw [hzf]; exact mem_B1_comp _ _ _ keys hz'
  · rintro ⟨b, hb⟩
    refine ⟨E b, fun g hg => ?_⟩
    rw [hzz]
    exact cob_comp _ _ _ key (I : Set G) b hb g hg
  · rintro ⟨b, hb⟩
    refine ⟨E.symm b, fun g hg => ?_⟩
    rw [hzf]
    exact cob_comp _ _ _ keys (I : Set G) b hb g hg

end GlobalTheory.TransportCoef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinFrameSemistablePeriodsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_breuilKisinFrame_semistablePeriods : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])), (∀ g, IsUnit (ρ g)) → ∀ (s : WSeed bk d ρ τ), ∃ (N : ℕ) (F : Frame bk N d ρ), F.IsDR ∧ ((∀ g, s.κ g = 1) → F.IsCr) := by
  first | (exact @GlobalTheory.semistablePeriodFrame) | (exact GlobalTheory.semistablePeriodFrame) | (intros; apply GlobalTheory.semistablePeriodFrame  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivStableLatticeIntegralCharacter
section
open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

namespace GlobalTheory.CharLat

theorem nonempty_equiv_of_free {O K : Type} [CommRing O] [IsDomain O] [Field K] [Module O K]
    (φ : O →+* K) (hsm : ∀ (o : O) (x : K), o • x = φ o * x)
    (hfr : ∀ z : K, ∃ a d : O, d ≠ 0 ∧ z * φ d = φ a)
    (T : Submodule O K) [Module.Free O T] (hT : T ≠ ⊥) :
    Nonempty (O ≃ₗ[O] T) := by
  let b := Module.Free.chooseBasis O T
  haveI hsub : Subsingleton (Module.Free.ChooseBasisIndex O T) := by
    constructor
    intro i j
    by_contra hij
    have hi : ((b i : T) : K) ≠ 0 := fun h0 => b.ne_zero i (Subtype.ext h0)
    obtain ⟨a, d, hd0, hd⟩ := hfr (((b j : T) : K) / ((b i : T) : K))
    have hrel : d • b j + (-a) • b i = 0 := by
      apply Subtype.ext
      rw [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul, hsm, hsm, ZeroMemClass.coe_zero,
        map_neg, ← hd]
      field_simp
      ring
    have hinj : Function.Injective ![j, i] := by
      intro x y hxy
      fin_cases x <;> fin_cases y
      · rfl
      · exact absurd (hxy : j = i).symm hij
      · exact absurd (hxy : i = j) hij
      · rfl
    have hli : LinearIndependent O ![b j, b i] := by
      have := b.linearIndependent.comp ![j, i] hinj
      convert this using 1
      ext k
      fin_cases k <;> rfl
    have h2 := LinearIndependent.pair_iff.1 hli d (-a) hrel
    exact hd0 h2.1
  haveI hne : Nonempty (Module.Free.ChooseBasisIndex O T) := by
    by_contra h
    rw [not_nonempty_iff] at h
    apply hT
    rw [eq_bot_iff]
    intro x hx
    have h0 : (⟨x, hx⟩ : T) = 0 := b.repr.injective (Subsingleton.elim _ _)
    simpa using congrArg Subtype.val h0
  haveI : Unique (Module.Free.ChooseBasisIndex O T) := uniqueOfSubsingleton (Classical.arbitrary _)
  exact ⟨(LinearEquiv.funUnique (Module.Free.ChooseBasisIndex O T) O O).symm.trans b.equivFun.symm⟩

end GlobalTheory.CharLat

namespace GlobalTheory.CharLat


set_option maxHeartbeats 2000000 in
theorem exists_equiv_charLattice : ∀ {l : ℕ} [Fact l.Prime] (LL : FinExt l) {G : Type} [Group G] [TopologicalSpace G]
    (θ : G →* (↥(OL LL))ˣ) (Lc : Lattice (O := ↥(OL LL)) (charRep (tableLineDegreeTwo.charL (LL := ↥LL.1) θ))),
    ∃ e : ↥(OL LL) ≃ₗ[↥(OL LL)] ↥Lc.T, ∀ g a, e (Formalism.GaloisCohomology.scalRep (↥(OL LL)) θ g a) = latRep Lc g (e a) := by
  intro l _ LL G _ _ θ Lc
  haveI := LL.2
  haveI hF : IsFractionRing (↥(OL LL)) (↥LL.1) :=
    integralClosure.isFractionRing_of_finite_extension (A := ℤ_[l]) (K := ℚ_[l]) (L := ↥LL.1)
  haveI := Lc.free
  have hT : Lc.T ≠ ⊥ := by
    intro h
    have hs := Lc.span
    rw [h, Submodule.bot_coe, Submodule.span_zero_singleton] at hs
    exact bot_ne_top hs
  have hsm : ∀ (o : ↥(OL LL)) (x : ↥LL.1), o • x = algebraMap (↥(OL LL)) (↥LL.1) o * x :=
    fun o x => rfl
  have hfr : ∀ z : ↥LL.1, ∃ a d : ↥(OL LL), d ≠ 0 ∧ z * algebraMap (↥(OL LL)) (↥LL.1) d =
      algebraMap (↥(OL LL)) (↥LL.1) a := by
    intro z
    obtain ⟨⟨a, d⟩, hd⟩ := IsLocalization.surj (nonZeroDivisors (↥(OL LL))) z
    exact ⟨a, d, nonZeroDivisors.coe_ne_zero d, hd⟩
  obtain ⟨e⟩ := nonempty_equiv_of_free (algebraMap (↥(OL LL)) (↥LL.1)) hsm hfr Lc.T hT
  refine ⟨e, fun g a => ?_⟩
  rw [Formalism.GaloisCohomology.scalRep_apply, map_smul]
  apply Subtype.ext
  rw [Submodule.coe_smul, hsm]
  rfl

end GlobalTheory.CharLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInverseLocalArtinWeilGroupHom
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InvLocalArtin

theorem exists_invLocalArtin : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (art : Neutral.B1.Ideles E →* GlobalTheory.HeckeGal.Gab E Ω), GlobalTheory.HeckeGal.IsGlobalArtin art → ∃ a : Weil h →* (w.adicCompletion E)ˣ, Function.Surjective a ∧ (∀ σ, ord (w.adicCompletion E) (a σ) = -deg σ) ∧ ∀ σ : Weil h, art (Neutral.B1.localIdele E w (a σ)) = GlobalTheory.HeckeGal.toAb E Ω σ := by
  intro E Ω _ _ _ _ _ A w h art ha
  have hinj := GlobalTheory.ArtinLocalInj.artin_localIdele_injective GlobalTheory.Published.chevalleyUnits' E Ω art ha w
  set f : (w.adicCompletion E)ˣ →* GlobalTheory.HeckeGal.Gab E Ω := art.comp (Neutral.B1.localIdele E w) with hf
  have hfi : Function.Injective f := hinj
  let o : (w.adicCompletion E)ˣ →* Multiplicative ℤ :=
    MonoidHom.mk' (fun x => .ofAdd (ord (w.adicCompletion E) x)) fun x y => by rw [SmGL.ord_mul, ofAdd_add]
  have ho : ∀ x, ord (w.adicCompletion E) x = Multiplicative.toAdd (o x) := fun _ => rfl
  have unit_iff : ∀ x, Formalism.L2.Host.IsUnitAt w x ↔ ord (w.adicCompletion E) x = 0 := by
    intro x
    unfold Formalism.L2.Host.IsUnitAt
    rw [GlobalTheory.CompletionNorm.valued_eq_exp, ← WithZero.exp_zero, WithZero.exp_inj]
    omega
  have unif_ord : ∀ x, Formalism.L2.Host.IsUnifAt w x → ord (w.adicCompletion E) x = 1 := by
    intro x hx
    unfold Formalism.L2.Host.IsUnifAt at hx
    rw [GlobalTheory.CompletionNorm.valued_eq_exp, WithZero.exp_inj] at hx
    omega

  obtain ⟨π, hπ, hπf⟩ := (ha.frob w A h (GlobalTheory.HeckeGal.toAb E Ω (frob h : G E Ω)⁻¹)).2 ⟨_, isFrob_frob, rfl⟩
  have hπo : ord (w.adicCompletion E) π = 1 := unif_ord π hπ
  have hπf' : f π⁻¹ = GlobalTheory.HeckeGal.toAb E Ω (frob h : G E Ω) := by
    rw [map_inv]; show (art (Neutral.B1.localIdele E w π))⁻¹ = _; rw [hπf, map_inv, inv_inv]
  have ordpow : ∀ n : ℤ, ord (w.adicCompletion E) (π⁻¹ ^ n) = -n := by
    intro n
    rw [ho, map_zpow, map_inv, toAdd_zpow, toAdd_inv, ← ho, hπo]; simp
  have hex : ∀ σ : Weil h, ∃ x, ord (w.adicCompletion E) x = -deg σ ∧ f x = GlobalTheory.HeckeGal.toAb E Ω σ := by
    intro σ
    obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul deg_frob σ
    obtain ⟨u, hu, huf⟩ := (ha.ine w A h (GlobalTheory.HeckeGal.toAb E Ω τ)).2 ⟨τ, τ.2, rfl⟩
    refine ⟨π⁻¹ ^ deg σ * u, ?_, ?_⟩
    · rw [SmGL.ord_mul, ordpow, (unit_iff u).1 hu, add_zero]
    · rw [map_mul, map_zpow, hπf']
      show _ * art (Neutral.B1.localIdele E w u) = _
      rw [huf, ← map_zpow, ← map_mul]
      congr 1
      conv_rhs => rw [hτ]
      simp [Subgroup.coe_mul, Subgroup.coe_zpow]
  choose g hgo hgf using hex
  let a : Weil h →* (w.adicCompletion E)ˣ :=
    { toFun := g
      map_one' := hfi (by rw [hgf, map_one, Subgroup.coe_one, map_one])
      map_mul' := fun σ τ => hfi (by rw [hgf, map_mul, hgf, hgf, Subgroup.coe_mul, map_mul]) }
  refine ⟨a, ?_, hgo, fun σ => hgf σ⟩
  intro x
  set n := ord (w.adicCompletion E) x
  have hu : Formalism.L2.Host.IsUnitAt w (x * π⁻¹ ^ n) := by
    rw [unit_iff, SmGL.ord_mul, ordpow]; simp [n]
  obtain ⟨τ, hτ, hτf⟩ := (ha.ine w A h (f (x * π⁻¹ ^ n))).1 ⟨_, hu, rfl⟩
  refine ⟨ineIncl h ⟨τ, hτ⟩ * frob h ^ (-n), hfi ?_⟩
  show f (g _) = f x
  rw [hgf, Subgroup.coe_mul, Subgroup.coe_zpow, coe_ineIncl, map_mul, map_zpow, hτf, ← hπf', ← map_zpow, ← map_mul]
  congr 1
  rw [mul_assoc, ← _root_.zpow_add, add_neg_cancel, zpow_zero, mul_one]

end GlobalTheory.InvLocalArtin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSupportedAtSplitPlaceUnitaryMatrixEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit

noncomputable section

namespace GlobalTheory.DownLift.GenSplit

theorem exists_suppAt_grpCo_eq : ∀ (D : D7) (V : HSp D) (v : FinPl D) (φ : SplitProj D v) (e : Formalism.L2.Theta.AE D),
    IsIdemOf φ e → ∀ (B g : GL (Fin V.rank) (Fv D.host.F v)), ∃ h : GA D V, Formalism.L2.Theta.SuppAt e V h ∧ grpCo φ V B h = g := by
  intro D V v φ e he B g
  obtain ⟨h, hs, hr⟩ := GlobalTheory.SplitOnto.exists_suppAt_rho_eq e v (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) he.1
    (GlobalTheory.SplitProjChart.chart_rdA D v φ e he).1 V B g
  refine ⟨h, hs, ?_⟩
  rw [← hr]
  apply Units.ext
  rw [GlobalTheory.SplitHecke.rho_val]
  rfl

end GlobalTheory.DownLift.GenSplit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodProjectorConvMirabolicAvgEqZeroStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodProjector_conv_mirabolicAvg_eq_zero : GlobalTheory.MirAvg.SeriesKillsAvg → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
    (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (F : Face D A), GlobalTheory.LiftRows.Given R F → ∀ (i : Fin D.R.m) (PP : R.Pg) (a : Fin D.R.r → kP PP.1), a ≠ 0 →
    ∀ (b : Bool) (ε : ℤ), (ε = 1 ∨ ε = -1) → ∀ x : G,
      ∑ y : G, GlobalTheory.DownLift.mirC R i PP a b ε y * RealDat.eC (A := A) (sg0 D A) (y⁻¹ * x) = 0 := by
  first | exact @GlobalTheory.GoodNoChiTr.conv_mirC_eC | exact GlobalTheory.GoodNoChiTr.conv_mirC_eC | (intros; apply GlobalTheory.GoodNoChiTr.conv_mirC_eC <;> assumption)
end

