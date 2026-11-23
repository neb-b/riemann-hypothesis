module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0359
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0152
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0075
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0220
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBoundedUnitary
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1350
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.IntegralFderivApplyEqZero

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperspecialFixesVacuaGoodInertPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
namespace GlobalTheory.FixAllGood
open GlobalTheory.Hk3 (UnrPl VacFix)

theorem unrPl_mul {D : D7} {P : Pl D.host.E} {χ χ' : (AE D)ˣ →* Circle} (h : UnrPl P χ) (h' : UnrPl P χ') :
    UnrPl P (χ * χ') := fun e f hP x a b c => by
  rw [MonoidHom.mul_apply, h e f hP x a b c, h' e f hP x a b c, mul_one]

theorem unrPl_inv {D : D7} {P : Pl D.host.E} {χ : (AE D)ˣ →* Circle} (h : UnrPl P χ) :
    UnrPl P χ⁻¹ := fun e f hP x a b c => by
  rw [MonoidHom.inv_apply, h e f hP x a b c, inv_one]

theorem unrPl_chrStep {D : D7} {P : Pl D.host.E} {μ : ℕ → (AE D)ˣ →* Circle} {η : (AE D)ˣ →* Circle} {j : ℕ}
    (hμ : UnrPl P (μ j)) (hη : UnrPl P η) :
    UnrPl P (Lift.chrStep μ η j).1 ∧ UnrPl P (Lift.chrStep μ η j).2 := by
  unfold Lift.chrStep
  split_ifs
  · exact ⟨unrPl_mul hμ (unrPl_inv hη), hμ⟩
  · exact ⟨hμ, unrPl_mul hμ (unrPl_inv hη)⟩

theorem unrPl_chrTh {D : D7} {P : Pl D.host.E} {μ : ℕ → (AE D)ˣ →* Circle} {η : (AE D)ˣ →* Circle} {j : ℕ}
    (hμ : UnrPl P (μ j)) (hη : UnrPl P η) :
    UnrPl P (Lift.chrTh μ η j).1 ∧ UnrPl P (Lift.chrTh μ η j).2 :=
  ⟨hμ, unrPl_mul hμ (unrPl_inv hη)⟩

theorem fixAll_of_good : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → ∀ t P, Good R.toRealDat t P → Formalism.DivisionValues.conjPl P = P → FixAll R.toRealDat t P := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F h _ t P hP _
  have hu := _root_.GlobalTheory.UnrOffLevels.unrPl_of_good R.toRealDat F.lv2 h.base.lev t P hP
  have hm := D.R.two_le_m
  refine ⟨fun k hk => ?_, ?_, fun i => ?_⟩
  · have hc := unrPl_chrStep (hu.2 (k + 1) (Nat.le_add_left _ _) hk.le) hu.1
    exact GlobalTheory.ConjVacFix.vacFix_of_unrPl _ _ _ _ _ _ P (h.fullY t k hk).datum hc.1 hc.2
  · have hc := unrPl_chrStep (hu.2 D.R.m (by omega) le_rfl) hu.1
    exact GlobalTheory.ConjVacFix.vacFix_of_unrPl _ _ _ _ _ _ P (h.fullX t).datum hc.1 hc.2
  · have hc := unrPl_chrTh (hu.2 ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2) hu.1
    exact GlobalTheory.ConjVacFix.vacFix_of_unrPl _ _ _ _ _ _ P (h.fullP i t).datum hc.1 hc.2

end GlobalTheory.FixAllGood
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntValuationPrimeBack
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal
open IsDedekindDomain

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GalSup

section Prime

variable {K : Type} [Field K] [NumberField K]

abbrev primeBack (s : K ≃+* K) (la : HeightOneSpectrum (𝓞 K)) : HeightOneSpectrum (𝓞 K) :=
  HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv s).symm la

theorem count_equiv {R S : Type} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
    [DecidableEq (Associates (Ideal R))] [∀ p : Associates (Ideal R), Decidable (Irreducible p)]
    [DecidableEq (Associates (Ideal S))] [∀ p : Associates (Ideal S), Decidable (Irreducible p)]
    (e : R ≃+* S) (p : HeightOneSpectrum R) {I : Ideal R} (hI : I ≠ ⊥) :
    (Associates.mk (HeightOneSpectrum.equivOfRingEquiv e p).asIdeal).count (Associates.mk (I.comap e.symm)).factors =
      (Associates.mk p.asIdeal).count (Associates.mk I).factors := by
  have hI' : I.comap e.symm ≠ ⊥ := by
    rw [← Ideal.map_comap_of_equiv]
    exact fun h => hI ((Ideal.map_eq_bot_iff_of_injective e.injective).1 h)
  refine eq_of_forall_le_iff fun k => ?_
  rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.2 hI') (HeightOneSpectrum.associates_irreducible _),
    ← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.2 hI) (HeightOneSpectrum.associates_irreducible _),
    ← Associates.mk_pow, ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd, Associates.mk_le_mk_iff_dvd,
    Ideal.dvd_iff_le, Ideal.dvd_iff_le]
  have : (HeightOneSpectrum.equivOfRingEquiv e p).asIdeal = p.asIdeal.map (e : R →+* S) := by
    rw [Ideal.map_comap_of_equiv]; rfl
  rw [this, ← Ideal.map_pow, Ideal.map_comap_of_equiv]
  exact Ideal.comap_le_comap_iff_of_surjective e.symm e.symm.surjective _ _

theorem intValuation_primeBack (s : K ≃+* K) (la : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) :
    (primeBack s la).intValuation a = la.intValuation (RingOfIntegers.mapRingEquiv s a) := by
  classical
  by_cases ha : a = 0
  · subst ha; simp
  have ha' : RingOfIntegers.mapRingEquiv s a ≠ 0 := by simpa using ha
  rw [HeightOneSpectrum.intValuation_if_neg _ ha, HeightOneSpectrum.intValuation_if_neg _ ha']
  have hc : (Ideal.span {RingOfIntegers.mapRingEquiv s a}).comap (RingOfIntegers.mapRingEquiv s).symm.symm =
      Ideal.span {a} := by
    rw [← Ideal.map_comap_of_equiv, Ideal.map_span, Set.image_singleton]
    simp
  have := count_equiv (RingOfIntegers.mapRingEquiv s).symm la
    (I := Ideal.span {RingOfIntegers.mapRingEquiv s a}) (by simpa using ha')
  rw [hc] at this
  rw [this]

theorem valuation_primeBack (s : K ≃+* K) (la : HeightOneSpectrum (𝓞 K)) (x : K) :
    (primeBack s la).valuation K x = la.valuation K (s x) := by
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have hs : ∀ z : 𝓞 K, s (algebraMap (𝓞 K) K z) = algebraMap (𝓞 K) K (RingOfIntegers.mapRingEquiv s z) :=
    fun _ => rfl
  rw [map_div₀, map_div₀, map_div₀, hs, hs, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, intValuation_primeBack, intValuation_primeBack]

theorem vLa_primeBack (s : K ≃+* K) (la : HeightOneSpectrum (𝓞 K)) (x : K) :
    vLa (primeBack s la) x = vLa la (s x) := by
  simp only [vLa, valuation_primeBack]

end Prime
end GlobalTheory.GalSup

namespace GlobalTheory.GalSup

section Pts

open ReciprocityTheory.ChartRestriction.G

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F)

def changeEmbedding {L : Type} [CommRing L] (ι₀ ι₁ : c'.F →+* L) (κ : c.F →+* L)
    (h₀ : ∀ a, ι₀ (incF c c' hle a) = κ a) (h₁ : ∀ a, ι₁ (incF c c' hle a) = κ a)
    (y : letI := ι₀.toAlgebra; FrPt Xo c' L) : letI := ι₁.toAlgebra; FrPt Xo c' L :=
  letI : Algebra c.F L := κ.toAlgebra
  let y₀ : FrPt Xo c L := (letI : Algebra c'.F L := ι₀.toAlgebra; y.res hle h₀)
  letI : Algebra c'.F L := ι₁.toAlgebra
  y₀.ext hle h₁

theorem evR_rulBC {L : Type} [CommRing L] (ι₀ : c'.F →+* L) (κ : c.F →+* L)
    (h₀ : ∀ a, ι₀ (incF c c' hle a) = κ a) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a n)
    (y : letI := ι₀.toAlgebra; FrPt Xo c' L) :
    (letI := ι₀.toAlgebra; evR Xo c' (rulBC hle f) y) =
      (letI : Algebra c.F L := κ.toAlgebra; letI := ι₀.toAlgebra; evR Xo c f (y.res hle h₀)) := by
  letI : Algebra c.F L := κ.toAlgebra
  letI := ι₀.toAlgebra
  exact ((rulBC_sec_val_linear E H Dw l Xo c c' hle).1 a n f hf).2 L h₀ y

theorem integral_reread {T : CDVR} (ι₀ ι₁ : c'.F →+* T.Fr) (κ : c.F →+* T.Fr)
    (h₀ : ∀ a, ι₀ (incF c c' hle a) = κ a) (h₁ : ∀ a, ι₁ (incF c c' hle a) = κ a)
    (y : letI := ι₀.toAlgebra; FrPt Xo c' T.Fr) (hy : Integral T ι₀ y) :
    Integral T ι₁ (changeEmbedding hle ι₀ ι₁ κ h₀ h₁ y) := by
  have key : ∀ (τ : E →+* ℂ) (b : 𝓞 E), ι₁ (embK c' τ b) = ι₀ (embK c' τ b) := fun τ b => by
    rw [← embK_incF hle τ b, h₀, h₁]
  have eig : ∀ (G : SAB H (Sp T.V)) τ (w : epsOver T.V T.V ⟶ G.G),
      IsEigV c' ι₁ G τ w ↔ IsEigV c' ι₀ G τ w := fun G τ w => by
    unfold IsEigV
    simp only [key]
  obtain ⟨G, t', m1, m2, ⟨ub, h1, h2, h3, h4⟩, rest⟩ := hy
  exact ⟨G, t', m1, m2, ⟨ub, h1, fun τ i => (eig G τ _).2 (h2 τ i),
    fun τ w ht he => h3 τ w ht ((eig G τ w).1 he), h4⟩, rest⟩

end Pts
end GlobalTheory.GalSup

namespace GlobalTheory.GalSup

open ReciprocityTheory.ChartRestriction.G

theorem evI_sum {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr} (y : IntFr Xo c T io) {m : ℕ}
    (b : Fin m → c.F) (g : Fin m → Rul Xo c) :
    evI y (∑ i, b i • g i) = ∑ i, io (b i) * evI y (g i) := by
  have h := map_sum (AddMonoidHom.mk' (evI y) (evI_add y)) (fun i => b i • g i) Finset.univ
  simp only [AddMonoidHom.mk'_apply] at h
  rw [h]
  simp only [evI_smul]

theorem intAt_galois : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (s : c'.F ≃+* c'.F), (∀ x : c.F, s (incF c c' hle x) = incF c c' hle x) → ∀ (m : ℕ) (as : Fin m → c'.F) (fs : Fin m → Rul Xo c), (∀ i, fs i ∈ sec Xo c a n) → IntAt Xo c' (∑ i, as i • rulBC hle (fs i)) → IntAt Xo c' (∑ i, s (as i) • rulBC hle (fs i)) := by
  intro E _ _ _ H Dw l Xo c c' hle a n s hs m as fs hfs hint la v hv
  obtain ⟨⟨q, T, ι, e, ho, y, hy, eta, heta, hq⟩, rfl⟩ := hv
  subst hq
  show 0 ≤ nval T.V e (evI y _)
  let κ : c.F →+* T.Fr := ι.comp (incF c c' hle)
  let ι₁ : c'.F →+* T.Fr := ι.comp (s : c'.F →+* c'.F)
  have h₀ : ∀ x, ι (incF c c' hle x) = κ x := fun _ => rfl
  have h₁ : ∀ x, ι₁ (incF c c' hle x) = κ x := fun x => by
    show ι (s (incF c c' hle x)) = ι (incF c c' hle x)
    rw [hs x]
  let y₁ : IntFr Xo c' T ι₁ := ⟨changeEmbedding hle ι ι₁ κ h₀ h₁ y.1,
    (letI := ι₁.toAlgebra; GlobalTheory.FlagTan.fromTest_of_isLocalRing _), integral_reread hle ι ι₁ κ h₀ h₁ y.1 y.2.2⟩
  have ho₁ : OverLa (primeBack s la) T.V ι₁ e := ⟨ho.1, fun x => by
    rw [vLa_primeBack]; exact ho.2 (s x)⟩
  have key : 0 ≤ nval T.V e (evI y₁ (∑ i, as i • rulBC hle (fs i))) :=
    hint (primeBack s la) _ ⟨PtV.mk (primeBack s la) ho₁ y₁ hy () trivial, rfl⟩
  have e1 : evI y (∑ i, s (as i) • rulBC hle (fs i)) = evI y₁ (∑ i, as i • rulBC hle (fs i)) := by
    rw [evI_sum, evI_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    unfold evI
    rw [evR_rulBC hle ι κ h₀ (hfs i), evR_rulBC hle ι₁ κ h₁ (hfs i)]
    rfl
  rw [e1]
  exact key

end GlobalTheory.GalSup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOfMem
section
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SchwartzAInt

open GlobalTheory.RegSch.IkSchwartz GlobalTheory.PartialIntegral


set_option maxHeartbeats 800000 in
theorem integrable_pure {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (μ : Measure (Mx D m n))
    [μ.IsAddHaarMeasure] (f : SchwartzMap (D.what₂.Tau → Fin m → Fin n → ℂ) ℂ) (g : (Fin m → Fin n → AEf D) → ℂ)
    (hg : g ∈ WeilM.SB (Fin m → Fin n → AEf D)) :
    Integrable (fun x => f (fun τ i j => compAt θ τ x i j) * g (fun i j => finPart D (x i j))) μ := by
  haveI : IsModuleTopology (Af D.host.F) (AEf D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AEf D) := IsModuleTopology.isTopologicalRing (Af D.host.F) _
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele D.host.F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele D.host.F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField D.host.F
  obtain ⟨e0⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (Af D.host.F)
  haveI : LocallyCompactSpace (AEf D) := e0.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AEf D) := e0.secondCountableTopology
  haveI : T2Space (AEf D) := e0.isEmbedding.t2Space
  letI : MeasurableSpace (Fin m → Fin n → AEf D) := borel _
  haveI : BorelSpace (Fin m → Fin n → AEf D) := ⟨rfl⟩
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  haveI := (lattice_Mx D m n).1
  obtain ⟨e, he⟩ := exists_split hθ m n
  let μr : Measure (D.what₂.Tau → Fin m → Fin n → ℂ) := Measure.addHaar
  let ν : Measure (Fin m → Fin n → AEf D) := Measure.addHaar
  obtain ⟨c, hc⟩ := exists_integral_split e μ μr ν
  have hf : Integrable (fun x => f x) μr := f.integrable
  have hg' : Integrable g ν := hg.1.continuous.integrable_of_hasCompactSupport hg.2
  have := (hc _ _ hf hg').1
  convert this using 2 with x
  rw [he]

theorem integrable_of_mem : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ) (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)),
    IsCovolOne (ratMx D m n) μ 𝓕 → ∀ Φ ∈ schwartzA θ m n, Integrable Φ μ := by
  intro D θ hθ m n μ 𝓕 hμ Φ hΦ
  haveI := hμ.1
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    exact integrable_pure hθ μ f g hg
  | zero => exact integrable_zero _ _ _
  | add Φ Ψ _ _ h1 h2 => exact h1.add h2
  | smul c Φ _ h => exact h.smul c

end GlobalTheory.SchwartzAInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAdaptedTriangularBounded
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit

namespace GlobalTheory.AnisoCocompact

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

abbrev finP : AF F ⊗[F] E →+* Af F ⊗[F] E := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom

abbrev infP : AF F ⊗[F] E →+* Ainf F ⊗[F] E := (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom

abbrev ratQ (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J

abbrev matA {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (g : HA (AF F) σ J) :
    Matrix (Fin M) (Fin M) (AF F ⊗[F] E) := (HA.mat (AF F) σ J g).1

theorem exists_finite_part (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) : ∃ C : Set (Af F ⊗[F] E), IsCompact C ∧
    ∀ g : HA (AF F) σ J, ∃ γ ∈ ratQ σ J, ∀ B : Matrix (Fin M) (Fin M) E, (∀ a b, IsIntegral ℤ (B a b)) →
      ∀ a b, finP ((matA (g * γ) * B.map (inclR (F := F) (AF F))) a b) ∈ C := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Af F) _
  obtain ⟨π, hπ, -⟩ := GlobalTheory.Mass.existsUnique_isFinProj σ J
  obtain ⟨S, hS⟩ := GlobalTheory.Mem.ClassFinite.exists_finset_classes F E σ hcm M J hJ _ (GlobalTheory.Mass.isOpen_stdLevel σ J)
  obtain ⟨C, hC, hCe⟩ := (GlobalTheory.Mass.intTens_open_compact F E).2
  obtain ⟨C₁, hC₁, hCe₁⟩ := GlobalTheory.Mem.AnisoQuotient.exists_compact_mul hC
    (S.finite_toSet.image fun s => (HA.mat (Af F) σ J s⁻¹).1)
  refine ⟨C₁, hC₁, fun g => ?_⟩
  obtain ⟨γ₀, s, hs, k, hk, e⟩ := hS (π g⁻¹)
  obtain ⟨γ, hγ, hγe⟩ : (γ₀.1 : HA (Af F) σ J) ∈ (GlobalTheory.Mass.ratIn (AF F) σ J).map π := by
    rw [hπ.map_ratIn]; exact γ₀.2
  refine ⟨γ, hγ, fun B hBi a b => ?_⟩
  have e' : π (g * γ) = k⁻¹ * s⁻¹ := by
    have e1 : π g⁻¹ = π γ * (s * k) := by rw [hγe]; exact e
    rw [map_mul, ← inv_inv g, map_inv, e1]; group
  generalize g * γ = x at e'
  have e3 : (matA x).map finP = (HA.mat (Af F) σ J k⁻¹).1 * (HA.mat (Af F) σ J s⁻¹).1 := by
    have := congrArg Units.val (hπ x)
    rw [e'] at this
    exact this.symm
  have e4 : finP ((matA x * B.map (inclR (F := F) (AF F))) a b) =
      ((matA x).map finP * (B.map (inclR (F := F) (AF F))).map finP) a b :=
    congrFun (congrFun (Matrix.map_mul (L := matA x) (M := B.map (inclR (F := F) (AF F))) (f := finP)) a) b
  rw [e4, e3]
  refine hCe₁ _ ⟨s, hs, rfl⟩ _ _ (fun a b => hCe _ ((GlobalTheory.Mass.mem_stdLevel _ _ _).1 (inv_mem hk) a b).1)
    (fun a b => hCe _ ?_) a b
  exact Subring.subset_closure (Or.inl ⟨⟨B a b, ⟨_, hBi a b⟩, rfl⟩, rfl⟩)

theorem exists_real_part (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : J.det ≠ 0) (han : ∀ x, x ≠ 0 → Formalism.UG.hform (σ : E →+* E) J x x ≠ 0)
    {I : Type} [Fintype I] {τ : I → (E →+* ℂ)} (hτ : GlobalTheory.Mem.Vol.IsCMFam τ)
    {θ : I → (Ainf F ⊗[F] E →+* ℂ)} (hθ : ∀ ρ, Formalism.MainNotions.StandardLattice.IsInfEmb (τ ρ) (θ ρ)) :
    ∃ (R : ℝ) (𝓒 : Set (Matrix (Fin M) (Fin M) E)), 𝓒.Finite ∧ ∀ x : HA (AF F) σ J,
      ∃ u ∈ ratQ σ J, ∃ B : Matrix (Fin M) (Fin M) E, ∃ N ∈ 𝓒,
        matA u = (B * N).map (inclR (F := F) (AF F)) ∧ (∀ a b, IsIntegral ℤ (B a b)) ∧
        ∀ a b ρ, ‖θ ρ (infP ((matA x * B.map (inclR (F := F) (AF F))) a b))‖ ≤ R := by
  haveI := hcm.2.1
  obtain ⟨R, 𝓒, h𝓒, H⟩ := GlobalTheory.Mem.AnisoQuotient.exists_bounded_unitary (σ := (σ : E →+* E)) hτ
    (fun ρ x => hcm.2.2.2 _ x) hJ han
  refine ⟨R, 𝓒, h𝓒, fun x => ?_⟩
  let p : AF F ⊗[F] E →+* (I → ℂ) := Pi.ringHom fun ρ => (θ ρ).comp infP
  have hp : ∀ N : Matrix (Fin M) (Fin M) E, (N.map (inclR (F := F) (AF F))).map p = N.map (Pi.ringHom τ) :=
    fun N => by ext i j ρ; exact (hθ ρ).1 _
  have hev : ∀ (ρ : I) (X : Matrix (Fin M) (Fin M) (I → ℂ)), X.map (Pi.evalRingHom (fun _ => ℂ) ρ) = X.map (fun z => z ρ) :=
    fun _ _ => rfl
  obtain ⟨u, hu, B, N, hN, hum, hBi, hBR⟩ := H ((matA x).map p) (by
    ext i j ρ
    have h1 := congrFun (congrFun (GlobalTheory.Mem.VolExists.infMat_unitary J hcm (hθ ρ) x) i) j
    have h2 : ((Formalism.UG.cT (starRingEnd (I → ℂ)) ((matA x).map p) * J.map (Pi.ringHom τ) * (matA x).map p).map
        (Pi.evalRingHom (fun _ => ℂ) ρ)) = (Formalism.MainNotions.StandardLattice.infMat σ J (θ ρ) x).conjTranspose * J.map (τ ρ) *
        Formalism.MainNotions.StandardLattice.infMat σ J (θ ρ) x := by
      have e1 : ((matA x).map p).map (Pi.evalRingHom (fun _ => ℂ) ρ) = Formalism.MainNotions.StandardLattice.infMat σ J (θ ρ) x := by
        ext a b; rfl
      have e2 : (Formalism.UG.cT (starRingEnd (I → ℂ)) ((matA x).map p)).map (Pi.evalRingHom (fun _ => ℂ) ρ) =
          (Formalism.MainNotions.StandardLattice.infMat σ J (θ ρ) x).conjTranspose := by
        rw [← e1]; ext a b; rfl
      have e3 : (J.map (Pi.ringHom τ)).map (Pi.evalRingHom (fun _ => ℂ) ρ) = J.map (τ ρ) := by
        ext a b; rfl
      rw [Matrix.map_mul, Matrix.map_mul, e1, e2, e3]
    have h3 := congrFun (congrFun h2 i) j
    simp only [Matrix.map_apply, Pi.evalRingHom_apply] at h3
    rw [h3, h1]
    rfl)
  refine ⟨⟨_, GlobalTheory.Mem.ClassFinite.baseChange_mem (AF F) σ J u hu⟩, ⟨u, hu, rfl⟩, B, N, hN,
    congrArg (fun X => X.map (inclR (F := F) (AF F))) hum, hBi, fun a b ρ => ?_⟩
  have := hBR a b
  rw [← hp, ← Matrix.map_mul] at this
  exact (norm_le_pi_norm (p ((matA x * B.map (inclR (F := F) (AF F))) a b)) ρ).trans this

theorem exists_compact (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) (han : ∀ x, x ≠ 0 → Formalism.UG.hform (σ : E →+* E) J x x ≠ 0) :
    ∃ K : Set (HA (AF F) σ J), IsCompact K ∧ ∀ g, ∃ γ ∈ ratQ σ J, ∃ k ∈ K, g = γ * k := by
  haveI := hcm.1
  let τ : InfinitePlace E → (E →+* ℂ) := fun w => w.embedding
  have hτ : GlobalTheory.Mem.Vol.IsCMFam τ := by
    have : (fun w => InfinitePlace.mk (τ w)) = id := funext fun w => InfinitePlace.mk_embedding w
    unfold GlobalTheory.Mem.Vol.IsCMFam; rw [this]; exact Function.bijective_id
  choose θ hθ1 hθ2 using fun ρ => GlobalTheory.InfAdeleCM.exists_hom (F := F) (τ ρ)
  have hθ : ∀ ρ, Formalism.MainNotions.StandardLattice.IsInfEmb (τ ρ) (θ ρ) := fun ρ => ⟨hθ1 ρ, hθ2 ρ⟩
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsTopologicalGroup (HA (AF F) σ J) := inferInstanceAs (IsTopologicalGroup (HR (AF F) σ J))
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨C₁, hC₁, H₁⟩ := exists_finite_part σ hcm J hJ
  obtain ⟨R, 𝓒, h𝓒, H₂⟩ := exists_real_part σ hcm J hJ.2 han hτ hθ
  obtain ⟨C₂, hC₂, hCe₂⟩ := GlobalTheory.Mem.VolExists.exists_compact_adele hcm hτ hθ R C₁ hC₁
  obtain ⟨C₃, hC₃, hCe₃⟩ := GlobalTheory.Mem.AnisoQuotient.exists_compact_mul ((hC₂.insert 0).insert 1)
    (h𝓒.image fun N => N.map (inclR (F := F) (AF F)))
  obtain ⟨K, hK, hKe⟩ := GlobalTheory.StabCompact.exists_compact_of_entries (AF F) σ J hJ.2 C₃ hC₃
  refine ⟨Inv.inv '' K, hK.image continuous_inv, fun g => ?_⟩
  obtain ⟨γ, hγ, h₁⟩ := H₁ g⁻¹
  obtain ⟨u, hu, B, N, hN, hum, hBi, hBR⟩ := H₂ (g⁻¹ * γ)
  refine ⟨γ * u, mul_mem hγ hu, (g⁻¹ * γ * u)⁻¹, ⟨_, hKe _ fun a b => ?_, rfl⟩, by group⟩
  have e : matA (g⁻¹ * γ * u) = matA (g⁻¹ * γ) * B.map (inclR (F := F) (AF F)) *
      N.map (inclR (F := F) (AF F)) * 1 := by
    rw [show matA (g⁻¹ * γ * u) = matA (g⁻¹ * γ) * matA u from rfl, hum, Matrix.map_mul, Matrix.mul_one,
      Matrix.mul_assoc]
  change matA (g⁻¹ * γ * u) a b ∈ C₃
  rw [e]
  refine hCe₃ _ ⟨N, hN, rfl⟩ _ _ (fun a b => Or.inr (Or.inr (hCe₂ _ (h₁ B hBi a b) (hBR a b)))) (fun a b => ?_) a b
  rw [Matrix.one_apply]
  split_ifs
  exacts [Or.inl rfl, Or.inr (Or.inl rfl)]

end GlobalTheory.AnisoCocompact
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralReTopDegreeDensityDbarEqZero
section
set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame
open GlobalTheory.GoodMetric (coordVec)

namespace GlobalTheory.CxForm

theorem integrable_dbar_integral_eq_zero {n : ℕ} {G : V n → ℂ} (hG : ContDiff ℝ 1 G)
    (hc : HasCompactSupport G) (u : V n) :
    Integrable (fun v => dbar G v u) ∧ ∫ v, dbar G v u = 0 := by
  have hint : ∀ w : V n, Integrable (fun y => fderiv ℝ G y w) := fun w =>
    ((hG.continuous_fderiv (by norm_num)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) w)
  refine ⟨?_, ?_⟩
  · simp only [dbar_apply, smul_eq_mul]
    exact ((hint _).add ((hint _).const_mul _)).const_mul _
  · simp only [dbar_apply, smul_eq_mul]
    rw [integral_const_mul, integral_add (hint _) ((hint _).const_mul _), integral_const_mul,
      ReciprocityTheory.L2DbarEstimates.integral_fderiv_apply_eq_zero n G hG hc,
      ReciprocityTheory.L2DbarEstimates.integral_fderiv_apply_eq_zero n G hG hc]
    simp

theorem dens_dbarAt_eq_sum {n : ℕ} (F : V n → Alt n) (v : V n) :
    dens (dbarAt F v) = ∑ a, ∑ S, dbar (fun x => (bas n).repr (F x) S) v (coordVec a) * dens (dzb a * bas n S) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dens, dbarAt, coefwise, Finset.mul_sum, mul_smul_comm, map_sum, map_smul, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, smul_eq_mul, Finset.sum_div, mul_div_assoc]

theorem integral_re_dens_dbarAt_eq_zero {n : ℕ} (F : V n → Alt n)
    (hF : ∀ S, ContDiff ℝ 1 (fun v => (bas n).repr (F v) S)) (hc : HasCompactSupport F) :
    ∫ v, (dens (dbarAt F v)).re = 0 := by
  have h (a : Fin n) (S : Finset (Fin (n + n))) :=
    integrable_dbar_integral_eq_zero (hF S)
      (hc.comp_left (g := fun α : Alt n => (bas n).repr α S) (by simp)) (coordVec a)
  have hi (a : Fin n) (S : Finset (Fin (n + n))) :
      Integrable fun v => dbar (fun x => (bas n).repr (F x) S) v (coordVec a) * dens (dzb a * bas n S) :=
    (h a S).1.mul_const _
  have hD : Integrable fun v => dens (dbarAt F v) := by
    simp only [dens_dbarAt_eq_sum]
    exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun S _ => hi a S
  have h0 : ∫ v, dens (dbarAt F v) = 0 := by
    simp only [dens_dbarAt_eq_sum]
    rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun S _ => hi a S]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [integral_finsetSum _ fun S _ => hi a S]
    refine Finset.sum_eq_zero fun S _ => ?_
    rw [integral_mul_const, (h a S).2, zero_mul]
  have := Complex.reCLM.integral_comp_comm hD
  simp only [Complex.reCLM_apply] at this
  rw [this, h0, Complex.zero_re]

end GlobalTheory.CxForm
end
end

