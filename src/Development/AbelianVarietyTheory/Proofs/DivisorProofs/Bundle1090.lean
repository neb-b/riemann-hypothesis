module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
public import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCB
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.WithZeroEqOfLeExpIff
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalOperatorsRowsNormalEigenspaces
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0942
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1035
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
public import Formalism.PieriBlockIdeals.PieriColumnMinors.HeckeLFunctionIdealEulerProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0821
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeCharCMLocKNonsplitEqNegOnePow
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.InertChar

open ValuativeRel

variable {F : Type} [Field F] [NumberField F]

theorem valued_eq_exp_ordL (v : HeightOneSpectrum (𝓞 F)) (x : (v.adicCompletion F)ˣ) :
    Valued.v (x : v.adicCompletion F) = WithZero.exp (-Formalism.UG.ordL (x : v.adicCompletion F)) := by
  have h0 : Valued.v (x : v.adicCompletion F) ≠ 0 := (_root_.map_ne_zero _).2 x.ne_zero
  rw [← WithZero.exp_log h0]
  congr 1
  unfold Formalism.UG.ordL
  rw [dite_eq_right h0, neg_neg]
  have key : ∀ (z : WithZero (Multiplicative ℤ)) (h : z ≠ 0), WithZero.log z = Multiplicative.toAdd (WithZero.unzero h) := by
    intro z h
    cases z with
    | zero => exact absurd rfl h
    | coe a => rfl
  exact key _ h0

theorem ord_eq_ordL (v : HeightOneSpectrum (𝓞 F)) (x : (v.adicCompletion F)ˣ) :
    GlobalTheory.SmGL.ord (v.adicCompletion F) x = Formalism.UG.ordL (x : v.adicCompletion F) := by
  haveI : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have hE := ValuativeRel.isEquiv (valuation (v.adicCompletion F))
    (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))
  obtain ⟨p, hp⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp (-1 : ℤ))
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [map_zero] at hp
    exact WithZero.exp_ne_zero hp.symm
  obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective (uniformizer (v.adicCompletion F))
  have hpu : valuation (v.adicCompletion F) p = uniformizer (v.adicCompletion F) := by
    refine le_antisymm (le_uniformizer_iff.2 (hE.lt_one_iff_lt_one.2 ?_)) ?_
    · rw [hp, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
    · have h1 : Valued.v y < 1 := hE.lt_one_iff_lt_one.1 (hy ▸ uniformizer_lt_one)
      rw [← hy, hE.le_iff_le, hp]
      rcases eq_or_ne (Valued.v y) 0 with h0 | h0
      · rw [h0]; exact zero_le
      · rw [← WithZero.exp_log h0] at h1 ⊢
        rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
        rw [WithZero.exp_le_exp]; omega
  set P : (v.adicCompletion F)ˣ := Units.mk0 p hp0
  have hP1 : GlobalTheory.SmGL.ord (v.adicCompletion F) P = 1 := GlobalTheory.SmGL.ord_eq_one hpu
  set m := Formalism.UG.ordL (x : v.adicCompletion F)
  set U : (v.adicCompletion F)ˣ := x * P ^ (-m)
  have hU : Valued.v (U : v.adicCompletion F) = 1 := by
    simp only [U, Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, P, Units.val_mk0, hp]
    rw [valued_eq_exp_ordL v x, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp [m]
  have hU' : valuation (v.adicCompletion F) (U : v.adicCompletion F) = 1 := by
    apply le_antisymm
    · rw [← map_one (valuation (v.adicCompletion F)), hE.le_iff_le, hU, map_one]
    · rw [← map_one (valuation (v.adicCompletion F)), hE.le_iff_le, hU, map_one]
  have hU0 : GlobalTheory.SmGL.ord (v.adicCompletion F) U = 0 := GlobalTheory.SmGL.ord_eq_zero hU'
  let o : (v.adicCompletion F)ˣ →* Multiplicative ℤ :=
    MonoidHom.mk' (fun z => .ofAdd (GlobalTheory.SmGL.ord (v.adicCompletion F) z)) fun a b => by
      rw [GlobalTheory.SmGL.ord_mul, ofAdd_add]
  have hx : x = U * P ^ m := by simp [U]
  have : o x = o U * o P ^ m := by rw [hx, map_mul, map_zpow]
  have e2 : GlobalTheory.SmGL.ord (v.adicCompletion F) x = GlobalTheory.SmGL.ord (v.adicCompletion F) U +
      m * GlobalTheory.SmGL.ord (v.adicCompletion F) P := by
    have := congrArg Multiplicative.toAdd this
    simpa [o, mul_comm] using this
  rw [e2, hU0, hP1]; ring

end GlobalTheory.BCT.InertChar

open GlobalTheory.BCT.InertChar in
theorem GlobalTheory.BCT.inertChar_muLocK : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e → ∀ w : Pl E, ¬ IsSplitAt w → ∀ k : Eˣ, ((μ.locK w k : ℂˣ) : ℂ) = (-1) ^ ordL (algebraMap E (w.adicCompletion E) (k : E)) := by
  intro E _ _ _ μ e hμ w hw k
  have h := hμ.2.2.1 w hw
  show ((μ.loc w (atFin w k) : ℂˣ) : ℂ) = _
  rw [h, GlobalTheory.SmGL.unrChar_apply, ord_eq_ordL]
  push_cast
  rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryRealPointsFixFiniteAdelicHoms
section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

noncomputable section
namespace GlobalTheory.RealWeilFinFix

theorem actOF_fin : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (nS nT : ℕ)
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (g : GAF σ JS) (h : GAF σ JT),
      g ∈ GlobalTheory.WeilPartsF.GinfCF σ JS → h ∈ GlobalTheory.WeilPartsF.GinfCF σ JT → ∀ u : WOF F E nS nT, u.map (infPartF F E) = 0 →
        actOF σ JS JT g h u = u := by
  intro F E _ _ _ _ _ σ nS nT JS JT g h hg hh u hu
  have h1 : (mtF σ JT h).map (finPartF F E) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hh)
  have h2 : (mtF σ JS g⁻¹).map (finPartF F E) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 (inv_mem hg))
  have h3 : (actOF σ JS JT g h u).map (finPartF F E) = u.map (finPartF F E) := by
    unfold actOF
    rw [Matrix.map_mul, Matrix.map_mul, h1, h2, Matrix.one_mul, Matrix.mul_one]
  have h4 : (actOF σ JS JT g h u).map (infPartF F E) = u.map (infPartF F E) := by
    unfold actOF
    rw [Matrix.map_mul, Matrix.map_mul, hu, Matrix.mul_zero, Matrix.zero_mul]
  ext i j
  have k3 : finPartF F E (actOF σ JS JT g h u i j) = finPartF F E (u i j) := congrFun (congrFun h3 i) j
  have k4 : infPartF F E (actOF σ JS JT g h u i j) = infPartF F E (u i j) := congrFun (congrFun h4 i) j
  rw [← Formalism.L2.Fam.ThC.pairE_eta (actOF σ JS JT g h u i j), ← Formalism.L2.Fam.ThC.pairE_eta (u i j)]
  exact congrArg₂ Formalism.L2.Fam.ThC.pairE k4 k3

end GlobalTheory.RealWeilFinFix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversallyClosedOpenContainingFibreContainsNear
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory

theorem spMap_base_mem_basicOpen {R T : Type} [CommRing R] [CommRing T] (χ : R →+* T) (a : R)
    (ha : IsUnit (χ a)) (t : Sp T) : (spMap χ).base t ∈ (PrimeSpectrum.basicOpen a : (Sp R).Opens) := by
  change a ∉ (PrimeSpectrum.comap χ t).asIdeal
  intro h
  exact t.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h ha)

theorem tube_of_universallyClosed : ∀ (R k : Type) [CommRing R] [Field k] (φ : R →+* k) (X X' : Scheme.{0})
    (f : X ⟶ Sp R) (f' : X' ⟶ Sp k) (π : X' ⟶ X) [UniversallyClosed f] (W : X.Opens),
    IsPullback π f' f (spMap φ) → π ⁻¹ᵁ W = ⊤ → ∃ a : R, φ a ≠ 0 ∧ ∀ (T : Type) [CommRing T] (χ : R →+* T),
    IsUnit (χ a) → ∀ (Z : Scheme.{0}) (g : Z ⟶ Sp T) (ρ : Z ⟶ X), IsPullback ρ g f (spMap χ) → ρ ⁻¹ᵁ W = ⊤ := by
  intro R k _ _ φ X X' f f' π _ W H hW
  have hc : IsClosed (f.base '' (W : Set X)ᶜ) := f.isClosedMap _ W.isOpen.isClosed_compl
  let t : Sp k := ⟨⊥, Ideal.isPrime_bot⟩
  have hx : (spMap φ).base t ∈ (f.base '' (W : Set X)ᶜ)ᶜ := by
    rintro ⟨x, hx, e⟩
    obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback H x t e
    exact hx (hW.ge (Set.mem_univ z))
  obtain ⟨_, ⟨a, rfl⟩, ha, hle⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hx hc.isOpen_compl
  refine ⟨a, ?_, ?_⟩
  · intro h0
    apply ha
    change φ a ∈ (⊥ : Ideal k)
    exact h0
  · intro T _ χ hχ Z g ρ H'
    refine top_le_iff.1 fun z _ => ?_
    by_contra hz
    have hm := spMap_base_mem_basicOpen χ a hχ (g.base z)
    have e : f.base (ρ.base z) = (spMap χ).base (g.base z) := by
      have := congrArg (fun h : Z ⟶ Sp R => h.base z) H'.w
      simpa using this
    exact hle (e ▸ hm : f.base (ρ.base z) ∈ _) ⟨ρ.base z, hz, rfl⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationEqOrConjOfUnderMaximalRealSubfieldEq
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.BCT

theorem valuation_eq_or_eq_conj_of_under_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w u : Pl E), u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → (∀ y : E, w.valuation E y = u.valuation E y) ∨ (∀ y : E, w.valuation E y = u.valuation E (IsCMField.complexConj E y)) := by
  intro E _ _ _ w u h
  set σ : E ≃+* E := (IsCMField.complexConj E).toRingEquiv with hσ
  set e : 𝓞 E ≃+* 𝓞 E := RingOfIntegers.mapRingEquiv σ with he
  have hc : ∀ x : 𝓞 E, ((e x : 𝓞 E) : E) = IsCMField.complexConj E (x : E) := fun x => rfl
  have hmem : ∀ x ∈ w.asIdeal, x ∈ u.asIdeal ∨ e x ∈ u.asIdeal := by
    intro x hx
    have hfix : IsCMField.complexConj E (((x * e x : 𝓞 E)) : E) = ((x * e x : 𝓞 E) : E) := by
      have h1 : ((x * e x : 𝓞 E) : E) = (x : E) * IsCMField.complexConj E (x : E) := by
        rw [← hc]; rfl
      rw [h1, map_mul, IsCMField.complexConj_apply_apply, mul_comm]
    have hF : ((x * e x : 𝓞 E) : E) ∈ maximalRealSubfield E :=
      (IsCMField.complexConj_eq_self_iff E _).1 hfix
    have hint : IsIntegral ℤ (⟨_, hF⟩ : maximalRealSubfield E) := by
      have := (x * e x).isIntegral_coe
      exact (isIntegral_algebraMap_iff ).1 this
    have hz : algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) ⟨_, hint⟩ = x * e x :=
      RingOfIntegers.ext rfl
    have h1 : (⟨_, hint⟩ : 𝓞 (maximalRealSubfield E)) ∈ (w.under (𝓞 (maximalRealSubfield E))).asIdeal := by
      change algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) _ ∈ w.asIdeal
      rw [hz]
      exact Ideal.mul_mem_right _ _ hx
    rw [← h] at h1
    change algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) _ ∈ u.asIdeal at h1
    rw [hz] at h1
    exact u.isPrime.mem_or_mem h1
  have hsub : (w.asIdeal : Set (𝓞 E)) ⊆ (u.asIdeal : Set (𝓞 E)) ∪
      (u.comap (e : 𝓞 E →+* 𝓞 E) e.surjective).asIdeal := fun x hx => hmem x hx
  rcases Ideal.subset_union.1 hsub with h2 | h2
  · left
    have : w = u := HeightOneSpectrum.ext (w.isMaximal.eq_of_le u.isPrime.ne_top h2)
    subst this
    intro y; rfl
  · right
    intro y
    exact GlobalTheory.QNorm.valuation_of_eq_comap σ u w
      (w.isMaximal.eq_of_le (u.comap (e : 𝓞 E →+* 𝓞 E) e.surjective).isPrime.ne_top h2) y

end GlobalTheory.BCT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WFormsPartsOfDistinctTypesOrthogonal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram evC dualC)
namespace GlobalTheory.OrthW

theorem evC_single {D : D7} {V : HSp D} {P : Pl D.host.E} {a : List ℤ → ℂ} {d : List ℤ} (hd : IsLab V P d) :
    evC V P a (Finsupp.single d 1) = a d := by
  unfold evC
  rw [Finsupp.sum_single_index] <;> simp [hd]

theorem dualC_single (d : List ℤ) :
    dualC (Finsupp.mapRange star (star_zero ℂ) (Finsupp.single d (1 : ℂ))) = Finsupp.single (dualLab d) 1 := by
  simp [dualC, Finsupp.mapRange_single, Finsupp.mapDomain_single]

theorem inner_eq_zero_of_eig {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (T S : H →ₗ[ℂ] H) (hadj : LinearMap.adjoint T = S) {a b b' : ℂ} {x y : H} (hx : T x = a • x) (hy : T y = b • y)
    (hy' : S y = b' • y) (hne : a ≠ b) : ⟪x, y⟫_ℂ = 0 := by
  have hxy : ⟪T x, y⟫_ℂ = ⟪x, S y⟫_ℂ := by rw [← hadj, LinearMap.adjoint_inner_right]
  have hyy : ⟪T y, y⟫_ℂ = ⟪y, S y⟫_ℂ := by rw [← hadj, LinearMap.adjoint_inner_right]
  rw [hx, hy'] at hxy
  rw [hy, hy'] at hyy
  rw [inner_smul_left, inner_smul_right] at hxy hyy
  by_cases hy0 : y = 0
  · simp [hy0]
  have hyy0 : ⟪y, y⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hy0
  have hconj : (starRingEnd ℂ) b = b' := mul_right_cancel₀ hyy0 hyy
  rw [← hconj] at hxy
  have hne' : (starRingEnd ℂ) a ≠ (starRingEnd ℂ) b := fun h => hne ((starRingEnd ℂ).injective h)
  have := sub_eq_zero.mpr hxy
  rw [← sub_mul] at this
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne')

theorem inner_wp3_eq_zero_of_ne : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → ∀ i p q, p ≠ q → ∀ w ∈ R.Wp3 i p, ∀ w' ∈ R.Wp3 i q, ⟪w, w'⟫_ℂ = 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hW hEx hSch hOkH hPos hB i p q hpq
  obtain ⟨hCore, hSF, hE, hWc⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hW hEx
  have hX : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hOk.ok2.irr
  obtain ⟨hE', hOpsE, hNE, -, hEig, hMem⟩ := _root_.GlobalTheory.Hk3.OpsRows.exists_opsE R.toRealDat F.lv2 hCore hSch R.SF hSF
  obtain ⟨hw, -, hNW, -, -, -, hWEig, -⟩ := _root_.GlobalTheory.SphOpsModel.sphericalOperators_forms_on_rank_space_normal_alt R.toRealDat F.lv2 hCore hSch hX R.SF hSF i
  have hLab := fun P d hP => _root_.GlobalTheory.LabEq.isLab_W_iff (s := s) R.toRealDat F.lv2 hCore i P d hP
  have horthE := _root_.GlobalTheory.Div.inner_EEp3_eq_zero_of_ne R F hOk hW hOkH hPos hB p q hpq
  have key : ∀ c c', R.Carries p c → R.Carries q c' → ∀ x ∈ R.Wc' i c, ∀ y ∈ R.Wc' i c', ⟪x, y⟫_ℂ = 0 := by
    intro c c' hc hc' x hx y hy
    rw [hWc] at hx hy
    rcases Classical.em (∃ P d, Good R.toRealDat A3.A.μ0 P ∧ IsLab (Wc D i) P d ∧ c P d ≠ c' P d) with hdiff | hdiff
    · obtain ⟨P, d, hP, hd, hne⟩ := hdiff
      have hd' : IsLab (Wc D i) P (dualLab d) := (hLab P (dualLab d) hP).2.mpr ((hLab P d hP).1.mp hd)
      have hadj := hNW.2 P hP (Finsupp.single d 1)
      rw [dualC_single] at hadj
      have ex := hWEig c P hP (Finsupp.single d 1) x hx
      have ey := hWEig c' P hP (Finsupp.single d 1) y hy
      have ey' := hWEig c' P hP (Finsupp.single (dualLab d) 1) y hy
      rw [evC_single hd] at ex ey
      rw [evC_single hd'] at ey'
      exact inner_eq_zero_of_eig _ _ hadj ex ey ey' hne
    · have hagree : ∀ P d, Good R.toRealDat A3.A.μ0 P → IsLab (Wc D i) P d → c P d = c' P d :=
        fun P d hP hd => Classical.byContradiction fun h => hdiff ⟨P, d, hP, hd, h⟩
      exfalso
      have hle : EEc R.toRealDat R.SF c ≤ EEc R.toRealDat R.SF c' := by
        intro e he
        apply hMem c' e
        intro P d hP hd
        rw [hEig c P hP _ e he, evC_single hd]
        congr 1
        apply hagree P (dualLab d) hP
        exact (hLab P (dualLab d) hP).2.mpr ((hLab P d hP).1.mp ((hLab P d hP).2.mpr hd))
      obtain ⟨e, he, he0⟩ := (Submodule.ne_bot_iff _).mp hc.1
      have hep : e ∈ R.EEp3 p := (le_iSup₂ (f := fun c (_ : R.Carries p c) => R.EEc c) c hc) he
      have he' : e ∈ R.EEc c' := by
        rw [hE] at he ⊢
        exact hle he
      have heq : e ∈ R.EEp3 q := (le_iSup₂ (f := fun c (_ : R.Carries q c) => R.EEc c) c' hc') he'
      exact he0 (inner_self_eq_zero.mp (horthE e hep e heq))
  have hort : R.Wp3 i p ⟂ R.Wp3 i q := by
    unfold RealDat3.Wp3
    refine Submodule.isOrtho_iSup_left.mpr fun c => Submodule.isOrtho_iSup_left.mpr fun hc => ?_
    refine Submodule.isOrtho_iSup_right.mpr fun c' => Submodule.isOrtho_iSup_right.mpr fun hc' => ?_
    exact Submodule.isOrtho_iff_inner_eq.mpr (key c c' hc hc')
  intro w hw' w' hw''
  exact Submodule.isOrtho_iff_inner_eq.mp hort w hw' w' hw''

end GlobalTheory.OrthW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WachModuleMapMatrixCompMul
section
open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WachPlace

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {f : ℕ}

theorem wachMap_comp_coeff (W : LocWach PD LL O v f) {T T' T'' : LocLat G Qp LL O} {n n' n'' : ℕ}
    (b : Module.Basis (Fin n) (LetA O f) ↥(W.N T)) (b' : Module.Basis (Fin n') (LetA O f) ↥(W.N T'))
    (b'' : Module.Basis (Fin n'') (LetA O f) ↥(W.N T''))
    (g : LatHom T.L T'.L) (g' : LatHom T'.L T''.L) (g'' : LatHom T.L T''.L)
    (a : Fin n → Fin n' → LetA O f) (a' : Fin n' → Fin n'' → LetA O f) (a'' : Fin n → Fin n'' → LetA O f)
    (h1 : ∀ k, W.map g (b k : W.DD T) = ∑ m, a k m • (b' m : W.DD T'))
    (h2 : ∀ k, W.map g' (b' k : W.DD T') = ∑ m, a' k m • (b'' m : W.DD T''))
    (h3 : ∀ k, W.map g'' (b k : W.DD T) = ∑ m, a'' k m • (b'' m : W.DD T''))
    (hc : ∀ x, g''.f x = g'.f (g.f x)) (k : Fin n) (p : Fin n'') :
    a'' k p = ∑ m, a k m * a' m p := by
  have hg : g'' = latComp g' g := by
    cases g''
    simp only [latComp]
    congr 1
    exact LinearMap.ext hc
  have hsm : ∀ {S S' : LocLat G Qp LL O} (u : LatHom S.L S'.L) (c : LetA O f) (x : W.DD S),
      W.map u (c • x) = c • W.map u x := fun u c x => (W.map u).map_smul_of_tower c x
  have key : W.map g'' (b k : W.DD T) = ∑ q, (∑ m, a k m * a' m q) • (b'' q : W.DD T'') := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hg, W.map_comp, h1 k, map_sum]
    simp_rw [hsm, h2, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul]
  have e : ∑ q, a'' k q • b'' q = ∑ q, (∑ m, a k m * a' m q) • b'' q := by
    apply (W.N T'').subtype_injective
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sum] using (h3 k).symm.trans key
  have := congrArg (fun x => b''.repr x p) e
  set_option synthInstance.maxHeartbeats 100000 in
    simpa [Finset.sum_apply, map_sum, Finsupp.smul_apply, b''.repr_self, Finsupp.single_apply] using this

end Gen


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem isMapMat_comp_mul : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (K LL : FinExt l) (hA : CaseA K LL) (T T' T'' : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (n n' n'' : ℕ) (b : Module.Basis (Fin n) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥((H.W K 1 LL hA.2.2).N T)) (b' : Module.Basis (Fin n') (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥((H.W K 1 LL hA.2.2).N T')) (b'' : Module.Basis (Fin n'') (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥((H.W K 1 LL hA.2.2).N T'')) (g : LatHom T.L T'.L) (g' : LatHom T'.L T''.L) (g'' : LatHom T.L T''.L) (A : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Mx (PowerSeries ↥(OL LL)) n' n) (A' : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Mx (PowerSeries ↥(OL LL)) n'' n') (A'' : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Mx (PowerSeries ↥(OL LL)) n'' n), IsMapMat (H.W K 1 LL hA.2.2) g b b' A → IsMapMat (H.W K 1 LL hA.2.2) g' b' b'' A' → IsMapMat (H.W K 1 LL hA.2.2) g'' b b'' A'' → (∀ x, g''.f x = g'.f (g.f x)) → ∀ i, A'' i = A' i * A i := by
  intro l _ P H K LL hA T T' T'' n n' n'' b b' b'' g g' g'' A A' A'' h1 h2 h3 hc i
  obtain ⟨hadd, hmul, hC, -, -, -, -, hinj⟩ := Formalism.CohomologicalDescent.FrobeniusPeriodChange.pi0Subst_laws_hold l ↥(OL LL)
  let incR : (↥(OL LL))⟦X⟧ →+* (↥(OL LL))⟦X⟧ :=
    { toFun := inc l ↥(OL LL)
      map_one' := by simpa using hC 1
      map_mul' := hmul
      map_zero' := by simpa using hC 0
      map_add' := hadd }
  refine Matrix.ext fun p k => hinj hA.2.1 ?_
  have e := congrFun (wachMap_comp_coeff (H.W K 1 LL hA.2.2) b b' b'' g g' g''
    (fun k m i => inc l ↥(OL LL) (A i m k)) (fun k m i => inc l ↥(OL LL) (A' i m k))
    (fun k m i => inc l ↥(OL LL) (A'' i m k)) h1 h2 h3 hc k p) i
  rw [Finset.sum_apply] at e
  rw [Matrix.mul_apply]
  refine e.trans (Eq.trans ?_ (map_sum incR _ _).symm)
  exact Finset.sum_congr rfl fun m _ => (mul_comm _ _).trans (hmul _ _).symm

end GlobalTheory.WachPlace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerBumpFiniteFactorProperties
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff

namespace GlobalTheory.WhitBump.FinBump

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ}

theorem psiFin_add (a b : Af E) : psiFin (a + b) = psiFin a * psiFin b := by
  simp only [psiFin, map_add (f := _), AddChar.map_add_eq_mul, Circle.coe_mul]

theorem bumpFin_eq (hK : ∀ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n),
      u ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n → psiFin (GlobalTheory.Whittaker.superDiag u) = 1)
    {g u : GL (Fin n) (Af E)} (hu : u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n))
    (hg : u⁻¹ * g ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n) :
    bumpFin g = psiFin (GlobalTheory.Whittaker.superDiag u) := by
  have h : ∃ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n), u⁻¹ * g ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n :=
    ⟨u, hu, hg⟩
  unfold bumpFin
  rw [dite_eq_left h]
  obtain ⟨hu', hg'⟩ := h.choose_spec
  set u' := h.choose
  have hw : u⁻¹ * u' ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n) := mul_mem (inv_mem hu) hu'
  have hwK : u⁻¹ * u' ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n := by
    have : u⁻¹ * u' = (u⁻¹ * g) * (u'⁻¹ * g)⁻¹ := by group
    rw [this]; exact mul_mem hg (inv_mem hg')
  have hsplit : u' = u * (u⁻¹ * u') := by group
  rw [hsplit, GlobalTheory.GamMul.UnipPlaced.superDiag_mul_unip hu hw, psiFin_add, hK _ hw hwK, mul_one]

end GlobalTheory.WhitBump.FinBump

namespace GlobalTheory.WhitBump.FinBump

theorem bumpFin_zero_of_not {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ}
    {g : GL (Fin n) (Af E)}
    (h : ¬ ∃ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n), u⁻¹ * g ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n) :
    bumpFin g = 0 := by
  unfold bumpFin; rw [dite_eq_right h]

theorem bumpFin_props : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ),
    (∀ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n), u ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n →
      psiFin (GlobalTheory.Whittaker.superDiag u) = 1) →
    bumpFin (E := E) (n := n) 1 = 1 ∧
    (∀ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n), ∀ g, bumpFin (u * g) = psiFin (GlobalTheory.Whittaker.superDiag u) * bumpFin g) ∧
    (∀ k ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n, ∀ g, bumpFin (g * k) = bumpFin g) ∧
    ∀ g, bumpFin g ≠ 0 → ∃ u ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n),
      u⁻¹ * g ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n := by
  intro E _ _ _ n hK
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [bumpFin_eq hK (one_mem _) (by simpa using one_mem _), hK 1 (one_mem _) (one_mem _)]
  · intro u hu g
    by_cases h : ∃ v ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n), v⁻¹ * g ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n
    · obtain ⟨v, hv, hvg⟩ := h
      have e : (u * v)⁻¹ * (u * g) = v⁻¹ * g := by group
      rw [bumpFin_eq hK (mul_mem hu hv) (by rw [e]; exact hvg), bumpFin_eq hK hv hvg,
        GlobalTheory.GamMul.UnipPlaced.superDiag_mul_unip hu hv, psiFin_add]
    · rw [bumpFin_zero_of_not h, mul_zero]
      refine bumpFin_zero_of_not fun ⟨v, hv, hvg⟩ => h ⟨u⁻¹ * v, mul_mem (inv_mem hu) hv, ?_⟩
      have e : (u⁻¹ * v)⁻¹ * g = v⁻¹ * (u * g) := by group
      rw [e]; exact hvg
  · intro k hk g
    by_cases h : ∃ v ∈ GlobalTheory.SmGL.unipB (Af E) (Fin n), v⁻¹ * g ∈ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E n
    · obtain ⟨v, hv, hvg⟩ := h
      have e : v⁻¹ * (g * k) = (v⁻¹ * g) * k := by group
      rw [bumpFin_eq hK hv (by rw [e]; exact mul_mem hvg hk), bumpFin_eq hK hv hvg]
    · rw [bumpFin_zero_of_not h]
      refine bumpFin_zero_of_not fun ⟨v, hv, hvg⟩ => h ⟨v, hv, ?_⟩
      have e : v⁻¹ * g = (v⁻¹ * (g * k)) * k⁻¹ := by group
      rw [e]; exact mul_mem hvg (inv_mem hk)
  · intro g hg
    by_contra h
    exact hg (bumpFin_zero_of_not h)

end GlobalTheory.WhitBump.FinBump
end

