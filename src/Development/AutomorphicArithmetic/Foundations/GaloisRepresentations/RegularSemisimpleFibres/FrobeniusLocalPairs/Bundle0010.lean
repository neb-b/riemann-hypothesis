module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.MatchOfSum
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.TraceRangeEq
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.TwScale
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.Bundle0007
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Bundle0002
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.Bundle0003
public import Development.WeilBound.CuspidalAdmissibility.OccursIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0350
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.NormDiag
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.InflTrace
section
open MeasureTheory NumberField IsDedekindDomain ValuativeRel Matrix GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Geo (incFin galFin mapGL)
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DZA UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt.L.InflationTrace

private theorem exists_trace {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)] (m : Measure (GL (Fin n) k)) [m.IsHaarMeasure]
    (τ : SmIrr (GL (Fin n) k)) (φ : GL (Fin n) k → ℂ) (hφ : Test φ) : ∃ z, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace m τ.ρ φ z := by
  obtain ⟨l1, -, t1, -⟩ := UpperTheory.V.Z.Tf.Orb.gLTop_of k n
  have hA := (GlobalTheory.CompanionTheory.AdmDict.isAdmissible_iff τ.ρ).1 (PositivityTheory.Exh.irreducibleAdmissibleGL k n τ.V τ.ρ τ.smooth τ.irred)
  obtain ⟨A, hA1, hA2⟩ := PositivityTheory.TfC.OccursIff.exists_integralOp_of_admissible m τ.ρ hA φ hφ.1 hφ.2
  exact ⟨_, A, hA1, hA2, rfl⟩

private theorem fin_fixed {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    (τ : SmIrr (GL (Fin n) k)) (U : Subgroup (GL (Fin n) k)) (ho : IsOpen (U : Set (GL (Fin n) k)))
    (hc : IsCompact (U : Set (GL (Fin n) k))) : FiniteDimensional ℂ (fixed τ.ρ U) :=
  (PositivityTheory.Exh.irreducibleAdmissibleGL k n τ.V τ.ρ τ.smooth τ.irred).2 U ho hc

private theorem twKer_keep {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (U : Subgroup G)
    (θ : G → G) (hθ : ∀ u ∈ U, θ u ∈ U) (I : V →ₗ[ℂ] V) (hI : ∀ g x, I (ρ g x) = ρ (θ g) (I x)) :
    ∀ x ∈ twKer ρ U 1, I x ∈ twKer ρ U 1 := by
  have h : twKer ρ U 1 ≤ (twKer ρ U 1).comap I := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, x, rfl⟩
    refine Submodule.subset_span ⟨⟨θ u, hθ u u.2⟩, I x, ?_⟩
    simp [hI]
  exact fun x hx => h hx

private theorem cmp_onto {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} {v : Pl F}
    (w : PlacesOver E v) (hw : ∀ w' : PlacesOver E v, w' = w) (g : Gw n w.1) :
    ∃ y : GL (Fin n) (CompletionsOver E v), GM.cmp w y = g := by
  letI : Unique (PlacesOver E v) := ⟨⟨w⟩, hw⟩
  let e := RingEquiv.piUnique (fun w : PlacesOver E v => w.1.adicCompletion E)
  refine ⟨mapGL n (e.symm : _ →+* _) g, ?_⟩
  refine Units.ext (Matrix.ext fun i j => ?_)
  exact e.apply_symm_apply (g i j)

end UpperTheory.Gal.InertialTypesAlt.L.InflationTrace

open UpperTheory.Gal.InertialTypesAlt.L.InflationTrace

theorem UpperTheory.Gal.InertialTypesAlt.L.inflTrace :
    GlobalTheory.DZA.InflMatching → UpperTheory.Gal.InertialTypesAlt.G.VarEx → UpperTheory.Gal.InertialTypesAlt.G.VarTrace → UpperTheory.Gal.InertialTypesAlt.G.NormInt → UpperTheory.Gal.InertialTypesAlt.L.InflTrace := by
  intro hIM hVE hVT hNI F E _ _ _ _ _ _ _ _ hp n hn π P hconj hweak v w hw hunr _ _ _ _ hcm F₀ F₁ _ _ _ _ _ rk rK s sb hres τ τ' hτ hτ'
  haveI : CharZero (v.adicCompletion F) := charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
  obtain ⟨hgen, hfr⟩ := UpperTheory.Gal.InertialTypesAlt.L.frobFacts _ _ F₀ F₁ rk rK s sb hres
  obtain ⟨hns, hdeg, hglob⟩ := UpperTheory.Gal.InertialTypesAlt.L.globOf F E hp v w hw hcm
  obtain ⟨σ, hσg, hσs⟩ := hglob s hgen
  obtain ⟨s', hs', hI⟩ := hVE F E σ hσg hp n hn P hconj v w hns
  obtain ⟨I₀, hI₀⟩ := hI τ' hτ'

  have hsg : ∀ g : Gw n w.1, s' g = GlobalTheory.LBC.galAct s n g := by
    intro g
    obtain ⟨y, rfl⟩ := cmp_onto w hw g
    have e := hs' y
    change (s' : Gw n w.1 →* Gw n w.1) (GM.cmp w y) = _
    rw [← e]
    refine Units.ext (Matrix.ext fun i j => ?_)
    exact hσs (y i j)

  obtain ⟨a, ha, hTw⟩ := UpperTheory.Gal.InertialTypesAlt.L.twScale _ _ s hgen n τ'.V τ'.ρ τ'.smooth τ'.irred I₀
    (fun g x => by rw [hI₀, hsg])
  let I₂ : τ'.V ≃ₗ[ℂ] τ'.V := I₀.trans (LinearEquiv.smulOfNeZero ℂ τ'.V a ha)
  have hI₂c : (I₂ : τ'.V →ₗ[ℂ] τ'.V) = a • (I₀ : τ'.V →ₗ[ℂ] τ'.V) := rfl
  have hI₂ : ∀ g x, I₂ (τ'.ρ g x) = τ'.ρ (s' g) (I₂ x) := fun g x => by
    change a • I₀ (τ'.ρ g x) = τ'.ρ (s' g) (a • I₀ x)
    rw [hI₀, map_smul]

  obtain ⟨i1, i2, i3, i4, mE, mF, hE, hF, h1, h2⟩ := (UpperTheory.ConvolutionTheory.GM.matchOne F E σ n v).1
  letI : MeasurableSpace (GL (Fin n) (w.1.adicCompletion E)) := borel _
  haveI : BorelSpace (GL (Fin n) (w.1.adicCompletion E)) := ⟨rfl⟩
  obtain ⟨hH, hP⟩ := @UpperTheory.V.Z.Tf.Orb.placeOfLocal_holds F E _ _ _ _ _ _ σ hσg v w hw _ _ _ _ s hgen hdeg hcm hσs n _ _ _ _ mE mF hE hF _ _
  have hUS := UpperTheory.V.Z.Tf.Orb.unitSB_holds
  have hPI := UpperTheory.V.Z.Tf.Orb.placeInt_holds
  have hcmp : Continuous (mapGL n (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w)) :=
    Continuous.units_map _ (continuous_id.matrix_map (continuous_apply w))
  have hE1 : (mE.map (mapGL n (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w)))
      (PositivityTheory.Rg.Tf.Loc.unitGL (n := Fin n) (w.1.adicCompletion E) : Set (GL (Fin n) (w.1.adicCompletion E))) = 1 := by
    rw [Measure.map_apply hcmp.measurable (hUS _ n).1.measurableSet, ← hPI.2 F E v w hw n, h1]
  have hF1 : mF (PositivityTheory.Rg.Tf.Loc.unitGL (n := Fin n) (v.adicCompletion F) : Set (GL (Fin n) (v.adicCompletion F))) = 1 := by
    rw [hPI.1 F v n, h2]
  obtain ⟨c, hc, hcT⟩ := hVT F E σ hσg hp n hn π P hconj hweak v w hns mF _ hF hH τ τ' hτ hτ' (s' : Gw n w.1 →* Gw n w.1) I₂ hs' hI₂
  refine ⟨(I₂ : τ'.V →ₗ[ℂ] τ'.V), c, by rw [hI₂c]; exact hTw, hc, fun fb hfb => ?_⟩
  obtain ⟨hKk, hUko, hUkc, hUkle, -, hfk⟩ := UpperTheory.Gal.InertialTypesAlt.L.inflFacts _ F₀ rk hres.onto₀ n
  obtain ⟨hKK, hUKo, hUKc, hUKle, -, hfK⟩ := UpperTheory.Gal.InertialTypesAlt.L.inflFacts _ F₁ rK hres.onto₁ n
  obtain ⟨hHk, hTk, hSk⟩ := hfk fb
  obtain ⟨hHK, hTK, -⟩ := hfK (normLift sb fb)
  obtain ⟨hst1, -, -⟩ := hfr n
  have hstab : ∀ u ∈ K1 rK n, GlobalTheory.LBC.galAct s n u ∈ K1 rK n := fun u hu => by
    have : GlobalTheory.LBC.galAct s n u ∈ (K1 rK n).map (GlobalTheory.LBC.galAct s n) := Subgroup.mem_map_of_mem _ hu
    rwa [hst1] at this
  obtain ⟨hm1, hm2⟩ := hIM _ _ (UpperTheory.V.Z.Tf.Orb.extCont_of _ _).1 inferInstance F₀ F₁ hres.deg rk rK hres.onto₀ hres.onto₁
    hres.inc s sb hres.gal hres.frob n fb hfb
  rw [hKk, hKK] at hm1
  rw [hKk] at hm2
  have hM := UpperTheory.Gal.InertialTypesAlt.L.matchOfSum _ _ s hgen n _ mF hH hF hE1 hF1 (K1 rK n) (K1 rk n) _ _
    ⟨hUKo, hKK ▸ hUKle, hstab⟩ ⟨hUko, hKk ▸ hUkle, fun _ h => h⟩ hHK hHk hm1 hm2
  have hMA : GM.MatchAt σ v 1 (fun g => infl rK (normLift sb fb) (GM.cmp w g)) (infl rk fb) :=
    @(UpperTheory.ConvolutionTheory.GM.matchOne F E σ n v).2 i1 i2 i3 i4 mE mF hE hF h1 h2 _ _ _ (hP _ hTK _ hTk hM)
  have hsupp : ∀ g, infl rk fb g ≠ 0 → g ∈ UpperTheory.Gal.InertialTypesAlt.G.normSet E n v := fun g hg =>
    hNI F E σ hσg hp n hn v hunr g (by
      have h3 : g ∈ (PositivityTheory.Rg.Tf.Loc.unitGL (n := Fin n) (v.adicCompletion F) : Set (GL (Fin n) (v.adicCompletion F))) := by
        have := hSk g hg
        rwa [hKk] at this
      rw [hPI.1 F v n] at h3
      exact h3)
  obtain ⟨z, hz⟩ := exists_trace mF τ _ hTk
  obtain ⟨B, hB, hBt⟩ := hcT _ _ 1 z hTK hTk hMA hsupp hz
  obtain ⟨A, hA, hAt⟩ := hz
  obtain ⟨l1, s1, t1, -⟩ := UpperTheory.V.Z.Tf.Orb.gLTop_of (v.adicCompletion F) n
  obtain ⟨l2, s2, t2, -⟩ := UpperTheory.V.Z.Tf.Orb.gLTop_of (w.1.adicCompletion E) n
  have e1 := UpperTheory.Gal.InertialTypesAlt.L.trSum _ _ hH (KO _ n) (by rw [hKK]; exact (hUS _ n).1) (by rw [hKK]; exact (hUS _ n).2.1)
    (by rw [hKK]; exact hE1) _ τ'.ρ τ'.smooth (K1 rK n) hUKo hUKle _ hHK (I₂ : τ'.V →ₗ[ℂ] τ'.V)
    (fun x hx => by rw [hI₂c]; exact hTw.mem_fixed hst1 hx)
    (twKer_keep _ _ (GlobalTheory.LBC.galAct s n) hstab _ (fun g x => (hI₂ g x).trans (congrArg (fun h => τ'.ρ h (I₂ x)) (hsg g))))
    B _ hB hBt (fin_fixed τ' _ hUKo hUKc)
  have e2 := UpperTheory.Gal.InertialTypesAlt.L.trSum _ _ hF (KO _ n) (by rw [hKk]; exact (hUS _ n).1) (by rw [hKk]; exact (hUS _ n).2.1)
    (by rw [hKk]; exact hF1) _ τ.ρ τ.smooth (K1 rk n) hUko hUkle _ hHk LinearMap.id (fun _ h => h) (fun _ h => h)
    A z hA hAt (fin_fixed τ _ hUko hUkc)
  rw [← e1, ← e2, mul_one]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.NormAdic
section
namespace UpperTheory.Gal.InertialTypesAlt.L

private theorem unit_of_sub_mem {A : Type} [CommRing A] (I : Ideal A) [IsAdicComplete I A]
    {x z : A} (hx : IsUnit x) (h : z - x ∈ I) : IsUnit z := by
  have hj := (Ideal.mem_jacobson_bot.mp (IsAdicComplete.le_jacobson_bot I h)) (↑hx.unit⁻¹ : A)
  have e : z = x * ((z - x) * ↑hx.unit⁻¹ + 1) := by
    linear_combination (-(z - x)) * hx.mul_val_inv
  rw [e]
  exact hx.mul hj

private theorem prod_one_add {A : Type} [CommRing A] (b : ℕ → A) (r : A) (d : ℕ) :
    ∃ c, ∏ i ∈ Finset.range d, (1 + b i * r) =
      1 + (∑ i ∈ Finset.range d, b i) * r + r ^ 2 * c := by
  induction d with
  | zero => exact ⟨0, by simp⟩
  | succ d ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨c + (∑ i ∈ Finset.range d, b i) * b d + r * c * b d, ?_⟩
    rw [Finset.prod_range_succ, Finset.sum_range_succ, hc]
    ring

private theorem itN_mul {A : Type} [CommRing A] (τ : A ≃+* A) (d : ℕ) (y w : A) :
    itN τ d (y * w) = itN τ d y * itN τ d w := by
  have key : ∀ i, (⇑τ)^[i] (y * w) = (⇑τ)^[i] y * (⇑τ)^[i] w := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_mul]
  simp only [itN, key, Finset.prod_mul_distrib]

private theorem itN_fixed {A : Type} [CommRing A] (τ : A ≃+* A) (d : ℕ)
    (hd : ∀ x, τ^[d] x = x) (y : A) : τ (itN τ d y) = itN τ d y := by
  unfold itN
  rw [map_prod]
  simp only [← Function.iterate_succ_apply' (⇑τ)]
  cases d with
  | zero => simp
  | succ m =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ' (fun i => (⇑τ)^[i] y), hd y]
    rfl

private theorem step {A : Type} [CommRing A] (I : Ideal A) (τ : A ≃+* A) (d : ℕ)
    (hd : ∀ x, τ^[d] x = x) (a : A) (ha : ∑ i ∈ Finset.range d, τ^[i] a = 1)
    (x : A) (hτx : τ x = x) (n : ℕ) (hn : n ≠ 0) (y : A) (hu : IsUnit (itN τ d y))
    (h : itN τ d y - x ∈ I ^ n) :
    ∃ y', y' - y ∈ I ^ n ∧ itN τ d y' - x ∈ I ^ (n + 1) := by
  set N := itN τ d y with hN
  set v : A := ↑hu.unit⁻¹ with hv
  have hNv : N * v = 1 := hu.mul_val_inv
  have hNfix : τ N = N := itN_fixed τ d hd y
  have hvfix : τ v = v := by
    have h1 : τ N * τ v = 1 := by rw [← map_mul, hNv, map_one]
    rw [hNfix] at h1
    calc τ v = (N * v) * τ v := by rw [hNv, one_mul]
      _ = v * (N * τ v) := by ring
      _ = v := by rw [h1, mul_one]
  have hwfix : τ ((x - N) * v) = (x - N) * v := by rw [map_mul, map_sub, hτx, hNfix, hvfix]
  have hit : ∀ i (z : A), (⇑τ)^[i] z = ((τ : A →+* A) ^ i) z := by
    intro i z
    rw [RingHom.coe_pow]
    rfl
  have hwit : ∀ i, (⇑τ)^[i] ((x - N) * v) = (x - N) * v := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih => rw [Function.iterate_succ_apply', ih, hwfix]
  have hwI : (x - N) * v ∈ I ^ n := by
    apply Ideal.mul_mem_right
    rw [← neg_sub]
    exact neg_mem h
  obtain ⟨c, hc⟩ := prod_one_add (fun i => (⇑τ)^[i] a) ((x - N) * v) d
  beta_reduce at hc
  refine ⟨y * (1 + a * ((x - N) * v)), ?_, ?_⟩
  · have e : y * (1 + a * ((x - N) * v)) - y = (y * a) * ((x - N) * v) := by ring
    rw [e]
    exact Ideal.mul_mem_left _ _ hwI
  · have e1 : itN τ d (1 + a * ((x - N) * v)) = ∏ i ∈ Finset.range d, (1 + (⇑τ)^[i] a * ((x - N) * v)) := by
      unfold itN
      apply Finset.prod_congr rfl
      intro i _
      rw [hit, map_add (f := _), map_one, map_mul, ← hit, ← hit, hwit]
    rw [itN_mul, ← hN, e1, hc, ha]
    have e2 : N * (1 + 1 * ((x - N) * v) + ((x - N) * v) ^ 2 * c) - x = N * c * ((x - N) * v) ^ 2 := by
      linear_combination (x - N) * hNv
    rw [e2]
    apply Ideal.mul_mem_left
    have h2 : ((x - N) * v) ^ 2 ∈ I ^ (n * 2) := by
      rw [pow_mul]
      exact Ideal.pow_mem_pow hwI 2
    exact Ideal.pow_le_pow_right (by omega) h2

private theorem tau_pow_mem {A : Type} [CommRing A] (I : Ideal A) (τ : A ≃+* A)
    (hI : ∀ x ∈ I, τ x ∈ I) (n : ℕ) {z : A} (h : z ∈ I ^ n) : τ z ∈ I ^ n := by
  have h1 : Ideal.map τ I ≤ I := Ideal.map_le_iff_le_comap.mpr (fun x hx => hI x hx)
  have h2 : τ z ∈ Ideal.map τ (I ^ n) := Ideal.mem_map_of_mem τ h
  rw [Ideal.map_pow] at h2
  exact Ideal.pow_right_mono h1 n h2

private theorem iter_pow_mem {A : Type} [CommRing A] (I : Ideal A) (τ : A ≃+* A)
    (hI : ∀ x ∈ I, τ x ∈ I) (n i : ℕ) {z : A} (h : z ∈ I ^ n) : τ^[i] z ∈ I ^ n := by
  induction i with
  | zero => exact h
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact tau_pow_mem I τ hI n ih

private theorem itN_sub_mem {A : Type} [CommRing A] (I : Ideal A) (τ : A ≃+* A)
    (hI : ∀ x ∈ I, τ x ∈ I) (d n : ℕ) {u v : A} (h : u - v ∈ I ^ n) :
    itN τ d u - itN τ d v ∈ I ^ n := by
  have hs : ∀ i, (⇑τ)^[i] u - (⇑τ)^[i] v ∈ I ^ n := by
    intro i
    have e : ∀ j, (⇑τ)^[j] u - (⇑τ)^[j] v = (⇑τ)^[j] (u - v) := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply', ← map_sub, ih]
    rw [e]
    exact iter_pow_mem I τ hI n i h
  unfold itN
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    have e2 : (∏ i ∈ Finset.range d, (⇑τ)^[i] u) * (⇑τ)^[d] u - (∏ i ∈ Finset.range d, (⇑τ)^[i] v) * (⇑τ)^[d] v
        = (∏ i ∈ Finset.range d, (⇑τ)^[i] u - ∏ i ∈ Finset.range d, (⇑τ)^[i] v) * (⇑τ)^[d] u
          + (∏ i ∈ Finset.range d, (⇑τ)^[i] v) * ((⇑τ)^[d] u - (⇑τ)^[d] v) := by
      ring
    rw [e2]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ ih) (Ideal.mul_mem_left _ _ (hs d))

private theorem mem_smul_top {A : Type} [CommRing A] (I : Ideal A) (n : ℕ) (z : A) :
    z ∈ (I ^ n • ⊤ : Submodule A A) ↔ z ∈ I ^ n := by
  simp

theorem normAdic : NormAdic := by
  intro A _ I _ τ d hd hI a ha x y hx hτx hy
  have hunit : ∀ n : ℕ, ∀ z : A, itN τ d z - x ∈ I ^ (n + 1) → IsUnit (itN τ d z) := by
    intro n z hz
    exact unit_of_sub_mem I hx (Ideal.pow_le_self (Nat.succ_ne_zero n) hz)
  have hstep : ∀ n : ℕ, ∀ z : A, itN τ d z - x ∈ I ^ (n + 1) →
      ∃ z', z' - z ∈ I ^ (n + 1) ∧ itN τ d z' - x ∈ I ^ (n + 1 + 1) := by
    intro n z hz
    exact step I τ d hd a ha x hτx (n + 1) (Nat.succ_ne_zero n) z (hunit n z hz) hz
  choose! g hg1 hg2 using hstep
  let f : ℕ → A := fun k => Nat.rec (motive := fun _ => A) y (fun k z => g k z) k
  have hf0 : f 0 = y := rfl
  have hfs : ∀ k, f (k + 1) = g k (f k) := fun k => rfl
  have hfN : ∀ k, itN τ d (f k) - x ∈ I ^ (k + 1) := by
    intro k
    induction k with
    | zero => simpa [hf0] using hy
    | succ k ih =>
      rw [hfs]
      exact hg2 k (f k) ih
  have hfd : ∀ k, f (k + 1) - f k ∈ I ^ (k + 1) := by
    intro k
    rw [hfs]
    exact hg1 k (f k) (hfN k)
  have hcauchy : ∀ m k, f m - f (m + k) ∈ I ^ m := by
    intro m k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : f m - f (m + (k + 1)) = (f m - f (m + k)) - (f (m + k + 1) - f (m + k)) := by
        rw [← add_assoc]
        ring
      rw [e]
      refine Ideal.sub_mem _ ih ?_
      exact Ideal.pow_le_pow_right (by omega) (hfd (m + k))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := I) (M := A) inferInstance (f := f) (by
    intro m n hmn
    rw [SModEq.sub_mem, mem_smul_top]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    exact hcauchy m k)
  refine ⟨L, ?_⟩
  have hzero := IsHausdorff.haus (I := I) (M := A) inferInstance (itN τ d L - x) (by
    intro n
    rw [SModEq.sub_mem, sub_zero, mem_smul_top]
    have h1 : itN τ d L - itN τ d (f n) ∈ I ^ n := by
      apply itN_sub_mem I τ hI d n
      have h0 := SModEq.sub_mem.mp (hL n)
      rw [mem_smul_top] at h0
      rw [← neg_sub]
      exact neg_mem h0
    have h2 : itN τ d (f n) - x ∈ I ^ n := Ideal.pow_le_pow_right (by omega) (hfN n)
    have e : itN τ d L - x = (itN τ d L - itN τ d (f n)) + (itN τ d (f n) - x) := by ring
    rw [e]
    exact Ideal.add_mem _ h1 h2)
  exact sub_eq_zero.mp hzero

end UpperTheory.Gal.InertialTypesAlt.L
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.StrictMap
section
open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc
open GlobalTheory.SmGL hiding iwahori

private theorem map_diag {E F : Type} [Field E] [Field F] {n : ℕ} (f : E →+* F) (u : Fin n → Eˣ) :
    Matrix.GeneralLinearGroup.map f (diagT E (Fin n) u) = diagT F (Fin n) fun i => Units.map (f : E →* F) (u i) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [val_diagT]
  · simp [val_diagT, Matrix.diagonal_apply, hij]

private theorem diag_comm {E : Type} [Field E] {n : ℕ} (u v : Fin n → Eˣ) :
    diagT E (Fin n) u * diagT E (Fin n) v = diagT E (Fin n) v * diagT E (Fin n) u := by
  rw [← map_mul, ← map_mul, mul_comm]

private theorem strict_map {k E : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    [Algebra k E] [ValuativeExtension k E] {n : ℕ} {t : Fin n → kˣ} (ht : Strict t) :
    Strict fun i => Units.map (algebraMap k E : k →* E) (t i) := by
  intro i j hij
  have h := ht i j hij
  rw [← (valuation k).vlt_iff_lt] at h
  rw [← (valuation E).vlt_iff_lt]
  simp only [Units.coe_map, MonoidHom.coe_coe]
  intro hle
  exact h (ValuativeExtension.vle_iff_vle.mp hle)

theorem UpperTheory.Gal.InertialTypesAlt.L.align :
    UpperTheory.Gal.InertialTypesAlt.L.Align := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ σ hσ n δ h y γ d hd hnorm hy
  obtain ⟨hcyc, -, hb⟩ := bridge k E σ
  obtain ⟨hsg, hnrm, -, -, -⟩ := hb n
  obtain ⟨hND, -, -⟩ := normDiag k E σ hσ n
  obtain ⟨hN, hstr, hreg⟩ := hND d
  have e := nrm_conj hcyc.ord δ y
  rw [hsg y, hy, hnrm, hnrm, hN, hnorm] at e
  set T := diagT k (Fin n) (UpperTheory.Gal.InertialTypesAlt.L.nrmT k d) with hTdef
  obtain ⟨z, hz⟩ := conjDesc k E n T γ (hreg hd) ⟨h⁻¹ * y, by rw [e]; group⟩
  refine ⟨z, by rw [hz]; group, ?_⟩
  intro t ht
  have hct : γ * t = t * γ := Subgroup.mem_centralizer_iff.mp ht γ rfl
  set m : Fin n → Eˣ := fun i => Units.map (algebraMap k E : k →* E) (UpperTheory.Gal.InertialTypesAlt.L.nrmT k d i) with hm
  have hms : Strict m := strict_map (hstr hd)
  have hT : (incl T : GL (Fin n) E) = diagT E (Fin n) m := map_diag (algebraMap k E) _
  have hrefl : Cyc (RingEquiv.refl E) 1 := ⟨fun x => rfl, one_pos, fun x => rfl⟩
  have hsgr : ∀ g : GL (Fin n) E, sg (RingEquiv.refl E) g = g := by
    intro g
    ext i j
    rfl
  set u := z⁻¹ * t * z with hu
  have huc : u * T = T * u := by
    have hz' : T = z⁻¹ * γ * z := by rw [hz]; group
    rw [hz', hu]
    calc z⁻¹ * t * z * (z⁻¹ * γ * z) = z⁻¹ * (t * γ) * z := by group
      _ = z⁻¹ * (γ * t) * z := by rw [hct]
      _ = z⁻¹ * γ * z * (z⁻¹ * t * z) := by group
  obtain ⟨s2, hs2⟩ := strictNormal E n (RingEquiv.refl E) 1 hrefl m m hms hms (incl u) (by
    rw [hsgr, ← hT, ← map_inv, ← map_mul, ← map_mul, mul_assoc, ← huc]
    congr 1
    group)
  set w := y⁻¹ * h * incl z with hw
  have hg : (incl γ : GL (Fin n) E) = incl z * incl T * (incl z)⁻¹ := by
    rw [hz]
    simp only [map_mul, map_inv]
  have hwc0 : (incl T : GL (Fin n) E) = w * incl T * w⁻¹ := by
    conv_lhs => rw [e]
    rw [hg, hw]
    group
  have hwc : w⁻¹ * diagT E (Fin n) m * w = diagT E (Fin n) m := by
    rw [← hT]
    conv_lhs => rw [hwc0]
    group
  obtain ⟨s1, hs1⟩ := strictNormal E n (RingEquiv.refl E) 1 hrefl m m hms hms w (by rw [hsgr]; exact hwc)
  have ht' : (incl t : GL (Fin n) E) = incl z * incl u * (incl z)⁻¹ := by
    rw [hu]
    simp only [map_mul, map_inv]
    group
  have key : y⁻¹ * (h * incl t * h⁻¹) * y = w * incl u * w⁻¹ := by
    rw [ht', hw]
    group
  rw [key, hs1, hs2, diag_comm]
  group
end

