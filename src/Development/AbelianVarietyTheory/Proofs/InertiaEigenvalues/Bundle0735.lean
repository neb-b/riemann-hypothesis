module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0605
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0727
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0690
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0202
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0197
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NatCastMemPlaceAt
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0981
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0720
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0729
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedOfSphericalVectorDictionary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0331

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodRankinSelbergPlaceSetSupersetTotallyCo
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG GlobalTheory.RSNonvan

noncomputable section

namespace GlobalTheory.RSNonvan.GoodSet

variable {E : Type} [Field E] [NumberField E]

theorem psiLoc_cond (w : HeightOneSpectrum (𝓞 E))
    (hw : FractionalIdeal.count E w ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 E)) E) = 0) (x : w.adicCompletion E) :
    (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w := by
  have key : (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔
      ∀ a ∈ w.adicCompletionIntegers E, GroundTheory.Global.localAdelicChar E w (a * x) = 1 := by
    refine forall_congr' fun y => imp_congr Iff.rfl ?_
    change GlobalTheory.StdCharConductor.psi E (sFin E (sLoc E w (x * y))) = 1 ↔ _
    rw [GlobalTheory.StdCharConductor.psi_loc_eq_one_iff, mul_comm]
  rw [key, GroundTheory.Global.forall_localAdelicChar_mul_eq_one_iff, GroundTheory.Global.mem_localInvDifferent_iff_valued, hw]
  change _ ↔ x ∈ w.adicCompletionIntegers E
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  rfl

theorem finite_sameBelow (u : HeightOneSpectrum (𝓞 E)) :
    {w' : HeightOneSpectrum (𝓞 E) | Ideal.comap (algebraMap ℤ (𝓞 E)) w'.asIdeal =
      Ideal.comap (algebraMap ℤ (𝓞 E)) u.asIdeal}.Finite := by
  set N : ℕ := Ideal.absNorm u.asIdeal
  have hN : N ≠ 0 := by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm u
    omega
  have hI : Ideal.span {(N : 𝓞 E)} ≠ 0 := by
    rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN
  refine (Ideal.finite_factors hI).subset fun w' hw' => ?_
  simp only [Set.mem_setOf_eq] at hw' ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]
  have h1 : ((N : ℤ)) ∈ Ideal.comap (algebraMap ℤ (𝓞 E)) u.asIdeal := by
    rw [Ideal.mem_comap, map_natCast]
    exact Ideal.absNorm_mem u.asIdeal
  rw [← hw', Ideal.mem_comap, map_natCast] at h1
  exact h1

variable [_root_.NumberField.IsTotallyComplex E]

theorem exists_isGood_superset (T : Finset (HeightOneSpectrum (𝓞 E))) :
    ∃ T' : Finset (HeightOneSpectrum (𝓞 E)), T ⊆ T' ∧ IsGood T' := by
  classical
  have hD : {w : HeightOneSpectrum (𝓞 E) | FractionalIdeal.count E w ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0}.Finite :=
    FractionalIdeal.finite_factors (K := E) ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
  set T₁ : Finset (HeightOneSpectrum (𝓞 E)) := T ∪ hD.toFinset
  set S : Set (HeightOneSpectrum (𝓞 E)) := {w' | ∃ u ∈ T₁, Ideal.comap (algebraMap ℤ (𝓞 E)) w'.asIdeal =
      Ideal.comap (algebraMap ℤ (𝓞 E)) u.asIdeal}
  have hS : S.Finite := by
    have : S = ⋃ u ∈ T₁, {w' : HeightOneSpectrum (𝓞 E) | Ideal.comap (algebraMap ℤ (𝓞 E)) w'.asIdeal =
        Ideal.comap (algebraMap ℤ (𝓞 E)) u.asIdeal} := by
      ext w'
      simp [S]
    rw [this]
    exact T₁.finite_toSet.biUnion fun u _ => finite_sameBelow u
  have hT₁ : ∀ w ∈ T₁, w ∈ hS.toFinset := fun w hw => by
    rw [Set.Finite.mem_toFinset]
    exact ⟨w, hw, rfl⟩
  refine ⟨hS.toFinset, fun w hw => hT₁ w (Finset.mem_union_left _ hw), ?_, ?_⟩
  · intro w hw w' hw'
    rw [Set.Finite.mem_toFinset] at hw ⊢
    obtain ⟨u, hu, hwu⟩ := hw
    exact ⟨u, hu, hw'.trans hwu⟩
  · intro w hw x
    refine psiLoc_cond w ?_ x
    by_contra h
    exact hw (hT₁ w (Finset.mem_union_right _ (by simpa using h)))

end GlobalTheory.RSNonvan.GoodSet

theorem GlobalTheory.RSNonvan.exists_isGood_superset_all : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]
    (T : Finset (HeightOneSpectrum (𝓞 E))), ∃ T' : Finset (HeightOneSpectrum (𝓞 E)), T ⊆ T' ∧ IsGood T' :=
  fun _ _ _ _ T => GlobalTheory.RSNonvan.GoodSet.exists_isGood_superset T

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHalfOfAuxiliarySplitLevel
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.MainNotions.StandardLattice Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.CoverRead

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HalfCharacter

theorem exists_half_of_auxiliary_split_level : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ pd : ℕ, GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.IsAuxiliarySplitSquarefreeLevel D T.Q.l.M pd →
  ∃ I : Ideal (𝓞 D.host.E), I = Ideal.span {x | x ∈ I ∧ x ∈ Algebra.adjoin ℤ {T.Q.H.w0}} ∧
    I * I.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = Ideal.span {(pd : 𝓞 D.host.E)} ∧
    I ⊔ I.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = ⊤ := by
  intro D T hJ pd haux
  obtain ⟨hodd, -, hjac, -, -⟩ := haux
  have hH : T.Q.PinHost := hJ.toLawsM.pins.1
  have hw : T.Q.H.w0 = w0E D := by
    have h1 := T.Q.H.two_weight_eq_one_add_root
    have h3 : T.Q.H.rt = rtE D := RingOfIntegers.ext hH.2.1
    rw [h3, ← two_w0E D] at h1
    exact mul_left_cancel₀ two_ne_zero h1
  have hb : (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = bH D :=
    RingHom.ext fun a => RingOfIntegers.ext (T.Q.H.bar_eq a)
  have hsp : ∀ p ∈ pd.primeFactorsList, SplitOK D p := by
    intro p hp
    have hpr := Nat.prime_of_mem_primeFactorsList hp
    have hdvd := Nat.dvd_of_mem_primeFactorsList hp
    refine ⟨hpr, ?_, hjac p hpr hdvd⟩
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdvd)
  have hpd0 : pd ≠ 0 := hodd.pos.ne'
  refine ⟨MbOf D pd.primeFactorsList, ?_, ?_, ?_⟩
  · rw [hw]; exact MbOf_fromK D _
  · rw [hb]
    have h := MbProd_of D pd.primeFactorsList hsp
    unfold MbProdLaw at h
    rw [h, Nat.prod_primeFactorsList hpd0]
  · rw [hb]; exact MbCop_of D _ hsp

end GlobalTheory.HalfCharacter
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInertDatumOfInvolutionUniformizer
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertDatumGiven

open scoped TensorProduct

theorem continuous_of_valued_eq {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (s : K →+* K) (hs : ∀ x, Valued.v (s x) = Valued.v x) : Continuous s := by
  have h : Filter.Tendsto s (nhds 0) (nhds 0) := by
    rw [(Valued.hasBasis_nhds_zero K Γ₀).tendsto_iff (Valued.hasBasis_nhds_zero K Γ₀)]
    intro γ _
    refine ⟨γ, trivial, fun x hx => ?_⟩
    simp only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding] at hx ⊢
    rwa [hs]
  exact continuous_of_continuousAt_zero s (by simpa [ContinuousAt] using h)

theorem exists_inertDatum_of : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield L)) w.asIdeal → ¬ IsSplitAt w → ∀ (s : w.adicCompletion L →+* w.adicCompletion L) (ϖ : w.adicCompletion L), (∀ x : L, s (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) → Formalism.UG.IsUnramInv ϖ s (Formalism.UG.qV (maximalRealSubfield L) v) → ∃ Dv : InertDatum L n v w, Dv.σw = s ∧ Dv.ϖ = ϖ := by
  intro L _ _ _ n v w hov hu hns s ϖ hs hU
  classical
  have hunder : w.under (𝓞 (maximalRealSubfield L)) = v := HeightOneSpectrum.ext hov
  have hw : Formalism.UG.IsInertAt (maximalRealSubfield L) L v w := by
    have h := GlobalTheory.InertPlaceConj.isInertAt_of_not_split w hu hns
    rwa [hunder] at h
  obtain ⟨c, hc, -⟩ := GlobalTheory.LFun.InertChart.existsUnique_isConjAt
    (IsCMField.complexConj L).toAlgHom hw hunder
  obtain ⟨ϖ', hU'⟩ := GlobalTheory.LFun.InertChart.exists_isUnramInv (GlobalTheory.InertDatumExist.isCMExt L) hw hc
  have hsc : s = c := by
    apply DFunLike.coe_injective
    refine GlobalTheory.UnramCompletion.ringHom_ext_of_continuous w (continuous_of_valued_eq s hU.2.1)
      (continuous_of_valued_eq c hU'.2.1) fun k => ?_
    rw [hs, GlobalTheory.LFun.InertChart.conj_algebraMap hc]
    rfl
  subst hsc
  obtain ⟨k, hk, hke⟩ := GlobalTheory.LFun.InertChart.exists_congr_antiJ (n := n) hU (B := 1) (one_mem _)
    (by simp [Formalism.UG.cT, Matrix.map_one])
  have hO : Formalism.UG.Ov L w = Formalism.UG.intL (w.adicCompletion L) := Subring.ext fun _ => Iff.rfl
  let e := (Algebra.TensorProduct.comm (maximalRealSubfield L) L
    (v.adicCompletion (maximalRealSubfield L))).toRingEquiv.trans (GlobalTheory.LFun.InertChart.complEquiv hw hunder)
  refine ⟨⟨e, s, ϖ, k, ?_, hU, ?_, ?_, ?_⟩, rfl, rfl⟩
  · intro x
    show GlobalTheory.LFun.toCompl hunder (Algebra.TensorProduct.comm _ _ _
        (Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom _ x)) =
      s (GlobalTheory.LFun.toCompl hunder (Algebra.TensorProduct.comm _ _ _ x))
    rw [hc]
    congr 1
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · intro x
    rw [GlobalTheory.InertDatumExist.mem_tensInt_iff, GlobalTheory.LFun.InertChart.mem_intLoc_iff hw hunder, hO]
    exact Iff.rfl
  · rw [← hO]; exact hk
  · simpa using hke

end GlobalTheory.InertDatumGiven

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsIotaAt
section
open NumberField
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DivPtLocal

variable {E : Type} [Field E] [NumberField E] (w : IsDedekindDomain.HeightOneSpectrum (𝓞 E))

def locDiv (N m n : ℕ) : AddSubgroup (Matrix (Fin m) (Fin n) (w.adicCompletion E)) where
  carrier := {X | ∀ i j, (N : w.adicCompletion E) * X i j ∈ w.adicCompletionIntegers E}
  add_mem' := by
    intro X Y hX hY i j
    simpa [mul_add] using add_mem (hX i j) (hY i j)
  zero_mem' := by intro i j; simp
  neg_mem' := by
    intro X hX i j
    simpa [mul_neg] using neg_mem (hX i j)

def locInt (m n : ℕ) : AddSubgroup (Matrix (Fin m) (Fin n) (w.adicCompletion E)) where
  carrier := {X | ∀ i j, X i j ∈ w.adicCompletionIntegers E}
  add_mem' := by
    intro X Y hX hY i j
    simpa using add_mem (hX i j) (hY i j)
  zero_mem' := by intro i j; simp
  neg_mem' := by
    intro X hX i j
    simpa using neg_mem (hX i j)

theorem mem_locInt {m n : ℕ} {X : Matrix (Fin m) (Fin n) (w.adicCompletion E)} :
    X ∈ locInt w m n ↔ ∀ i j, X i j ∈ w.adicCompletionIntegers E := Iff.rfl

abbrev LocQ (N m n : ℕ) : Type :=
  ↥(locDiv w N m n) ⧸ (locInt w m n).addSubgroupOf (locDiv w N m n)


open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta in
def IsIotaAt {D : D7} {q : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.FinPl D} {w : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)}
    (h : w.under (𝓞 D.host.F) = q) (ι : w.adicCompletion D.host.E →+ AE D) : Prop :=
  Continuous ι ∧ (∀ x, GlobalTheory.Core.Rk.SWQ.cw h (ι x) = x) ∧ (∀ x, GlobalTheory.Core.Rk.SWQ.cw h (cA D (ι x)) = 0) ∧
    (∀ x, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (GlobalTheory.AdelicU.singleFin q 1)) * ι x = ι x) ∧
    (∀ a x, a * ι x = ι (GlobalTheory.Core.Rk.SWQ.cw h a * x)) ∧
    (∀ a, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (GlobalTheory.AdelicU.singleFin q 1)) * a =
      ι (GlobalTheory.Core.Rk.SWQ.cw h a) + cA D (ι (GlobalTheory.Core.Rk.SWQ.cw h (cA D a)))) ∧
    IsSplitIdem D (ι 1) ∧ Continuous (GlobalTheory.Core.Rk.SWQ.cw h)

theorem exists_isIotaAt {D : D7} {q : GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.FinPl D} {w : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)}
    (h : w.under (𝓞 D.host.F) = q) (hs : Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) q) :
    ∃ ι : w.adicCompletion D.host.E →+ Formalism.L2.Theta.AE D, IsIotaAt h ι :=
  GlobalTheory.Core.Rk.SplitIota.exists_iota D q w h hs

end GlobalTheory.DivPtLocal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNormEqOfMemClosure
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KurValue

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GeoTie Polynomial

theorem exists_norm_eq_of_mem_closure {K : Type*} [NormedField K] [IsUltrametricDist K] {S : Set K} {x : K}
    (hx : x ∈ closure S) (h0 : x ≠ 0) : ∃ y ∈ S, ‖x‖ = ‖y‖ := by
  obtain ⟨y, hy, hd⟩ := Metric.mem_closure_iff.1 hx ‖x‖ (norm_pos_iff.2 h0)
  refine ⟨y, hy, ?_⟩
  rw [dist_comm, dist_eq_norm] at hd
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := y - x) (y := x) hd.ne
  rw [sub_add_cancel, max_eq_right hd.le] at this
  exact this.symm

variable {p : ℕ} [Fact p.Prime]

theorem mem_range_of_isIntegral {x : ℂ_[p]} (hx : IsIntegral (PadicAlgCl p) x) :
    x ∈ (algebraMap (PadicAlgCl p) ℂ_[p]).range :=
  minpoly.mem_range_of_degree_eq_one _ x (IsAlgClosed.degree_eq_one_of_irreducible _ (minpoly.irreducible hx))

theorem exists_lift {F : Type} [Field F] [NumberField F] (φ : F →+* ℂ_[p]) :
    ∃ ψ : F →+* PadicAlgCl p, ∀ a, algebraMap (PadicAlgCl p) ℂ_[p] (ψ a) = φ a := by
  have h : ∀ a : F, φ a ∈ (algebraMap (PadicAlgCl p) ℂ_[p]).range := fun a => by
    have h1 : IsIntegral ℚ (φ a) := (Algebra.IsIntegral.isIntegral (R := ℚ) a).map φ.toRatAlgHom
    exact mem_range_of_isIntegral h1.tower_top
  choose f hf using h
  have hi := (algebraMap (PadicAlgCl p) ℂ_[p]).injective
  refine ⟨⟨⟨⟨f, hi ?_⟩, fun a b => hi ?_⟩, hi ?_, fun a b => hi ?_⟩, hf⟩
  · rw [hf, map_one, map_one]
  · simp only [map_mul, hf]
  · simp only [map_zero, hf]
  · simp only [map_add (f := _), hf]

theorem exists_finite {F : Type} [Field F] [NumberField F] (ψ : F →+* PadicAlgCl p) :
    ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K ∧ (∀ a, ψ a ∈ K) ∧
      ∀ x ∈ K, ∃ a, ‖x‖ = ‖ψ a‖ := by
  let b := Module.finBasis ℚ F
  refine ⟨IntermediateField.adjoin ℚ_[p] (Set.range fun i => ψ (b i)), ?_, fun a => ?_, fun x hx => ?_⟩
  · exact IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [← b.sum_repr a, map_sum]
      refine sum_mem fun i _ => ?_
      rw [Rat.smul_def, map_mul, map_ratCast]
      exact mul_mem (SubfieldClass.ratCast_mem _ _) (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  · let M : IntermediateField ℚ_[p] (PadicAlgCl p) :=
      ψ.fieldRange.topologicalClosure.toIntermediateField fun r => by
        have hc : IsClosed {r : ℚ_[p] | algebraMap ℚ_[p] (PadicAlgCl p) r ∈ ψ.fieldRange.topologicalClosure} :=
          (Subfield.isClosed_topologicalClosure _).preimage (continuous_algebraMap _ _)
        refine (Padic.denseRange_ratCast p).induction_on r hc fun q => ?_
        rw [map_ratCast]
        exact SubfieldClass.ratCast_mem _ _
    have hM : IntermediateField.adjoin ℚ_[p] (Set.range fun i => ψ (b i)) ≤ M := by
      refine IntermediateField.adjoin_le_iff.2 ?_
      rintro _ ⟨i, rfl⟩
      exact Subfield.le_topologicalClosure ψ.fieldRange ⟨b i, rfl⟩
    by_cases h0 : x = 0
    · exact ⟨0, by simp [h0]⟩
    obtain ⟨_, ⟨a, rfl⟩, h⟩ := exists_norm_eq_of_mem_closure (S := (ψ.fieldRange : Set (PadicAlgCl p))) (hM hx) h0
    exact ⟨a, h⟩

theorem exists_norm_eq {F : Type} [Field F] [NumberField F] (φ : F →+* ℂ_[p]) {x : ℂ_[p]} (hx : x ∈ kurC φ) :
    ∃ a : F, ‖x‖ = ‖φ a‖ := by
  obtain ⟨ψ, hψ⟩ := exists_lift φ
  obtain ⟨K, hK, hmem, hnorm⟩ := exists_finite ψ
  let M : Subfield ℂ_[p] := (ReciprocityTheory.DiscreteGroups.LocalClassField.MaximalUnramifiedExtension p K).toSubfield.map (algebraMap (PadicAlgCl p) ℂ_[p])
  have hle : kurC φ ≤ M.topologicalClosure := by
    refine Subfield.topologicalClosure_minimal _ (sup_le ?_ ?_) (Subfield.isClosed_topologicalClosure _)
    · rintro _ ⟨a, rfl⟩
      exact M.le_topologicalClosure ⟨ψ a, ReciprocityTheory.DiscreteGroups.LocalClassField.le_Kur (hmem a), hψ a⟩
    · refine Subfield.topologicalClosure_minimal _ (Subfield.closure_le.2 ?_) (Subfield.isClosed_topologicalClosure _)
      rintro ζ ⟨n, hn, hpn, hζ⟩
      obtain ⟨ξ, rfl⟩ := mem_range_of_isIntegral (IsIntegral.of_pow hn (by rw [hζ]; exact isIntegral_one))
      refine M.le_topologicalClosure ⟨ξ, ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Kur_of_pow hK hpn ?_, rfl⟩
      apply (algebraMap (PadicAlgCl p) ℂ_[p]).injective
      rw [map_pow, hζ, map_one]
  by_cases h0 : x = 0
  · exact ⟨0, by simp [h0]⟩
  obtain ⟨_, ⟨y, hy, rfl⟩, h⟩ := exists_norm_eq_of_mem_closure (S := (M : Set ℂ_[p])) (hle hx) h0
  obtain ⟨n, hn, hyn⟩ := (ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Kur_iff hK y).1 hy
  obtain ⟨z, hz, hyz⟩ := ReciprocityTheory.DiscreteGroups.LocalClassField.norm_Kn p K hK hn hyn
  obtain ⟨a, ha⟩ := hnorm z hz
  refine ⟨a, ?_⟩
  rw [h, ← hψ, norm_algebraMap', norm_algebraMap', ← ha, hyz]

theorem exists_near {F : Type} [Field F] (φ : F →+* ℂ_[p]) {x : ℂ_[p]} (hx : ‖x‖ ≤ 1) :
    ∃ y ∈ kurC φ, ‖x - y‖ < 1 := by
  rcases hx.lt_or_eq with hlt | heq
  · exact ⟨0, zero_mem _, by rwa [sub_zero]⟩
  obtain ⟨z, hz⟩ := (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl p)).exists_dist_lt x one_pos
  rw [dist_eq_norm, PadicComplex.coe_eq] at hz
  have hz1 : ‖z‖ = 1 := by
    have h1 : ‖algebraMap (PadicAlgCl p) ℂ_[p] z - x‖ < ‖x‖ := by rwa [norm_sub_rev, heq]
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h1.ne
    rwa [sub_add_cancel, max_eq_right h1.le, heq, norm_algebraMap'] at this
  obtain ⟨ζ, m, hm, hζ, h⟩ := ReciprocityTheory.DiscreteGroups.LocalClassField.exists_teichmuller_bar z hz1
  refine ⟨algebraMap (PadicAlgCl p) ℂ_[p] ζ, root_mem_kurC φ hm (by rw [← map_pow, hζ, map_one]), ?_⟩
  have e : x - algebraMap (PadicAlgCl p) ℂ_[p] ζ =
      (x - algebraMap (PadicAlgCl p) ℂ_[p] z) + algebraMap (PadicAlgCl p) ℂ_[p] (z - ζ) := by
    rw [map_sub]; ring
  rw [e]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hz (by rwa [norm_algebraMap']))

theorem kurC_value_residue : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (φ : F →+* ℂ_[p]),
    (∀ x ∈ kurC φ, ∃ a : F, ‖x‖ = ‖φ a‖) ∧ ∀ x : ℂ_[p], ‖x‖ ≤ 1 → ∃ y ∈ kurC φ, ‖x - y‖ < 1 :=
  fun _ _ _ _ _ φ => ⟨fun _ hx => exists_norm_eq φ hx, fun _ hx => exists_near φ hx⟩

end GlobalTheory.KurValue

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRayFieldEmbedding
section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RayUp

theorem containsRayField_up {K L L' : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field L'] [NumberField L']
    (φ : K →+* L) (τ : L →+* L') (n : ℕ) (h : GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField φ n) :
    GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (τ.comp φ) n := by
  intro P hP
  letI : Algebra L L' := τ.toAlgebra
  let Q : HeightOneSpectrum (𝓞 L) := P.under (𝓞 L)
  have hQ : Q.asIdeal = P.asIdeal.comap (RingOfIntegers.mapRingHom τ) := rfl
  haveI hPo : P.asIdeal.LiesOver Q.asIdeal := ⟨rfl⟩
  have hn : ((n : ℕ) : 𝓞 L) ∉ Q.asIdeal := fun h' => hP (by
    rw [hQ, Ideal.mem_comap, map_natCast] at h'
    exact h')
  obtain ⟨f, α, h1, h2, h3⟩ := h Q hn
  have hf := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver P.asIdeal Q.asIdeal Q.isPrime Q.ne_bot
  have hcm : P.asIdeal.comap (RingOfIntegers.mapRingHom (τ.comp φ)) =
      Q.asIdeal.comap (RingOfIntegers.mapRingHom φ) := by
    ext x
    rfl
  rw [hcm]
  refine ⟨f * Q.asIdeal.inertiaDeg' P.asIdeal, α ^ Q.asIdeal.inertiaDeg' P.asIdeal, ?_, ?_, ?_⟩
  · rw [hf, h1, ← pow_mul]
  · rw [pow_mul, h2, Ideal.span_singleton_pow]
  · have := sub_dvd_pow_sub_pow α 1 (Q.asIdeal.inertiaDeg' P.asIdeal)
    rw [one_pow] at this
    exact dvd_trans h3 this

end GlobalTheory.RayUp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTrivOutsideLoc
section
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.TypeRec GlobalTheory.TypeVec
attribute [local instance] GlobalTheory.TypeRec.factG Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitSec

theorem exists_trivOutside_loc : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (u : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))), ∃ x : GAf L n, TrivOutside {s.v} (x : GA L n) ∧ s.loc n x = u := by
  intro L _ _ _ n s u
  exact GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s u

end GlobalTheory.SplitSec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedByUnitaryIntegralPointsOfLevelFixedStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixed_by_unitaryIntegralPoints_of_level_fixed : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (U : Submodule ℂ (UA L n → ℂ)), IsAutRepU U → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ U0 : Subgroup (GAf L n), (∀ κ, TrivOutside {v} κ → (κ ∈ U0 ↔ κ ∈ Umax L n)) → ∀ (σ : w.adicCompletion L →+* w.adicCompletion L) (b : GL (Fin n) (w.adicCompletion L)), b ∈ GlobalTheory.LFun.KGL w (n := n) → ∀ p : locU n w →* Formalism.UG.GU σ n, (∀ x, (p x).val = b⁻¹ * cLoc w x.val * b) → ∀ φ ∈ U, (∀ g, ∀ κ ∈ U0, φ (F.j (g * κ)) = φ (F.j g)) → ∀ x : locU n w, p x ∈ Formalism.UG.KU σ n → RU L n x.val φ = φ := by
  first | exact @GlobalTheory.UnramDict.fixed_of_mem_KU | exact GlobalTheory.UnramDict.fixed_of_mem_KU | (intros; apply GlobalTheory.UnramDict.fixed_of_mem_KU <;> assumption)
end

