module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OmPinsTr
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WeakCharInertPartRealAdelicDataTransport
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0469
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0460
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0465
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0462
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0472
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0473
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0024
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegralQuotientDominatingValuationSubring
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.DomValInt

theorem isIntegral_of_forall_valuationSubring (W : Type) [CommRing W] (F : Type) [Field F]
    [Algebra W F] (y : F)
    (hy : ∀ V : ValuationSubring F, (∀ w : W, algebraMap W F w ∈ V) → y ∈ V) :
    IsIntegral W y := by
  have hcl : IsIntegrallyClosedIn (integralClosure W F).toSubring F :=
    inferInstanceAs (IsIntegrallyClosedIn (integralClosure W F) F)
  by_contra hn
  have hsn : y ∉ (integralClosure W F).toSubring := hn
  obtain ⟨V, hV, hyV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hsn
  exact hyV (hy V fun w => hV (Subalgebra.algebraMap_mem _ w))

theorem split_rel {F : Type} [Field F] (c : ℕ → F) (x : F) (n j : ℕ) (hjn : j ≤ n)
    (hrel : ∑ i ∈ Finset.range (n + 1), c i * x ^ i = 0) :
    (∑ i ∈ Finset.range j, c i * x ^ i) +
      x ^ j * ∑ k ∈ Finset.range (n + 1 - j), c (j + k) * x ^ k = 0 := by
  rw [← hrel, show n + 1 = j + (n + 1 - j) by omega, Finset.sum_range_add, Finset.mul_sum,
    show j + (n + 1 - j) - j = n + 1 - j by omega]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pow_add]; ring

theorem tail_mem {F' : Type} [Field F'] (V : ValuationSubring F') (c : ℕ → F') (hc : ∀ i, c i ∈ V) (x : F')
    (n j : ℕ) (hjn : j ≤ n) (hrel : ∑ i ∈ Finset.range (n + 1), c i * x ^ i = 0) :
    (∑ k ∈ Finset.range (n + 1 - j), c (j + k) * x ^ k) ∈ V ∧
      (∑ k ∈ Finset.range (n + 1 - j), c (j + k) * x ^ k) * x ∈ V := by
  have hsplit := split_rel c x n j hjn hrel
  set s := ∑ k ∈ Finset.range (n + 1 - j), c (j + k) * x ^ k with hs
  by_cases hxV : x ∈ V
  · have : s ∈ V := by
      rw [hs]
      exact sum_mem fun k _ => mul_mem (hc _) (pow_mem hxV k)
    exact ⟨this, mul_mem this hxV⟩
  have hx0 : x ≠ 0 := fun h => hxV (h ▸ V.zero_mem)
  have hxi : x⁻¹ ∈ V := (V.mem_or_inv_mem x).resolve_left hxV
  rcases j with _ | j'
  · simp at hsplit
    rw [hsplit]; simp
  · set A' := ∑ i ∈ Finset.range (j' + 1), c i * x⁻¹ ^ (j' - i) with hA'
    have hA'V : A' ∈ V := sum_mem fun i _ => mul_mem (hc _) (pow_mem hxi _)
    have hA'x : A' * x ^ j' = ∑ i ∈ Finset.range (j' + 1), c i * x ^ i := by
      rw [hA', Finset.sum_mul]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ j' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [show x ^ j' = x ^ (j' - i) * x ^ i by rw [← pow_add]; congr 1; omega, inv_pow]
      field_simp
    have hsx : s * x = -A' := by
      have hpow : x ^ j' ≠ 0 := pow_ne_zero _ hx0
      apply mul_right_cancel₀ hpow
      rw [neg_mul, hA'x, _root_.mul_assoc, ← pow_succ']
      linear_combination hsplit
    have htV : s * x ∈ V := by rw [hsx]; exact neg_mem hA'V
    refine ⟨?_, htV⟩
    have : s = (s * x) * x⁻¹ := by field_simp
    rw [this]; exact mul_mem htV hxi

end GlobalTheory.DomValInt

namespace GlobalTheory.DomValInt

theorem exists_integral_quotient :
    ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (F : Type) [Field F]
    [Algebra (FractionRing W) F] [Algebra.IsAlgebraic (FractionRing W) F] [Algebra W F]
    [IsScalarTower W (FractionRing W) F] (O : ValuationSubring F),
    (∀ w : W, algebraMap W F w ∈ O) → (∀ w ∈ maximalIdeal W, algebraMap W F w ∈ O.nonunits) →
    ∀ x ∈ O, ∃ s t : F, IsIntegral W s ∧ IsIntegral W t ∧ O.valuation s = 1 ∧ s * x = t := by
  intro W _ _ _ F _ _ _ _ _ O hW hmax x hxO

  have hK : ∀ a : FractionRing W, algebraMap (FractionRing W) F a ∈ O →
      ∃ w : W, algebraMap W F w = algebraMap (FractionRing W) F a := by
    intro a ha
    rcases ValuationRing.isInteger_or_isInteger W a with ⟨w, hw⟩ | ⟨w, hw⟩
    · exact ⟨w, by rw [IsScalarTower.algebraMap_apply W (FractionRing W) F, hw]⟩
    · by_cases ha0 : a = 0
      · exact ⟨0, by simp [ha0]⟩
      by_cases hu : IsUnit w
      · refine ⟨↑hu.unit⁻¹, ?_⟩
        have h1 : a⁻¹ * algebraMap W (FractionRing W) ↑hu.unit⁻¹ = 1 := by
          rw [← hw, ← map_mul, IsUnit.mul_val_inv, map_one]
        have h2 := (inv_mul_eq_one₀ ha0).mp h1
        rw [IsScalarTower.algebraMap_apply W (FractionRing W) F, ← h2]
      · have hwm : w ∈ maximalIdeal W := (mem_maximalIdeal _).mpr hu
        have h2 := (O.mem_nonunits_iff).mp (hmax w hwm)
        have h3 := (O.valuation_le_one_iff _).mpr ha
        have h4 : algebraMap (FractionRing W) F a * algebraMap W F w = 1 := by
          rw [IsScalarTower.algebraMap_apply W (FractionRing W) F, hw, ← map_mul,
            mul_inv_cancel₀ ha0, map_one]
        have h5 : O.valuation (algebraMap (FractionRing W) F a * algebraMap W F w) < 1 := by
          rw [map_mul]
          exact lt_of_le_of_lt (mul_le_of_le_one_left' h3) h2
        rw [h4, map_one] at h5
        exact absurd h5 (lt_irrefl _)

  obtain ⟨p, hp0, hpx⟩ := Algebra.IsAlgebraic.isAlgebraic (R := FractionRing W) x
  set n := p.natDegree with hn
  set b : ℕ → F := fun i => algebraMap (FractionRing W) F (p.coeff i) with hb
  set v := O.valuation with hv
  obtain ⟨i0, hi0, hi0max⟩ := Finset.exists_max_image (Finset.range (n + 1))
    (fun i => v (b i)) ⟨0, by simp⟩
  set M := v (b i0) with hM
  set S := (Finset.range (n + 1)).filter (fun i => v (b i) = M) with hS
  obtain ⟨j, hjS, hjmax⟩ := Finset.exists_max_image S id
    ⟨i0, Finset.mem_filter.mpr ⟨hi0, rfl⟩⟩
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hjS).1)
  have hjM : v (b j) = M := (Finset.mem_filter.mp hjS).2
  have hcoeff0 : ∀ i, n < i → b i = 0 := fun i hi => by
    simp [b, Polynomial.coeff_eq_zero_of_natDegree_lt (show p.natDegree < i by omega)]
  have hle : ∀ i, v (b i) ≤ M := fun i => by
    by_cases hi : i ≤ n
    · exact hi0max i (Finset.mem_range.mpr (by omega))
    · rw [hcoeff0 i (by omega), map_zero]; exact zero_le'
  have hM0 : M ≠ 0 := by
    intro h
    have h1 : v (b n) = 0 := le_antisymm (h ▸ hle n) zero_le'
    rw [Valuation.zero_iff] at h1
    have h2 : p.leadingCoeff = 0 := (algebraMap (FractionRing W) F).injective (by rw [map_zero]; exact h1)
    exact hp0 (Polynomial.leadingCoeff_eq_zero.mp h2)
  have hlt : ∀ i, j < i → v (b i) < M := by
    intro i hi
    rcases lt_or_eq_of_le (hle i) with h | h
    · exact h
    exfalso
    by_cases hin : i ≤ n
    · have hiS : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), h⟩
      have := hjmax i hiS
      simp only [id] at this
      omega
    · rw [hcoeff0 i (by omega), map_zero] at h
      exact hM0 h.symm
  have hbj : b j ≠ 0 := fun h => hM0 (by rw [← hjM, h, map_zero])
  have hMpos : 0 < M := zero_lt_iff.mpr hM0
  set c : ℕ → F := fun i => b i / b j with hc
  have hcle : ∀ i, v (c i) ≤ 1 := fun i => by
    simp only [c, map_div₀, hjM]
    exact (div_le_one₀ hMpos).mpr (hle i)
  have hclt : ∀ i, j < i → v (c i) < 1 := fun i hi => by
    simp only [c, map_div₀, hjM]
    exact (div_lt_one₀ hMpos).mpr (hlt i hi)
  have hcW : ∀ i, ∃ w : W, algebraMap W F w = c i := fun i => by
    have hci : c i = algebraMap (FractionRing W) F (p.coeff i / p.coeff j) := by
      simp [c, b, map_div₀]
    rw [hci]
    exact hK _ (by rw [← hci]; exact (O.valuation_le_one_iff _).mp (hcle i))
  have hcj : c j = 1 := div_self hbj
  have hrel : ∑ i ∈ Finset.range (n + 1), c i * x ^ i = 0 := by
    have h := hpx
    rw [Polynomial.aeval_eq_sum_range] at h
    simp only [c, div_mul_eq_mul_div, ← Finset.sum_div]
    rw [div_eq_zero_iff]
    left
    simpa [Algebra.smul_def, b] using h
  set s := ∑ k ∈ Finset.range (n + 1 - j), c (j + k) * x ^ k with hs
  have hmemV : ∀ V : ValuationSubring F, (∀ w : W, algebraMap W F w ∈ V) → s ∈ V ∧ s * x ∈ V :=
    fun V hV => tail_mem V c (fun i => by obtain ⟨w, hw⟩ := hcW i; rw [← hw]; exact hV w)
      x n j hjn hrel
  refine ⟨s, s * x, isIntegral_of_forall_valuationSubring W F s fun V hV => (hmemV V hV).1,
    isIntegral_of_forall_valuationSubring W F _ fun V hV => (hmemV V hV).2, ?_, rfl⟩
  have hxle : v x ≤ 1 := (O.valuation_le_one_iff x).mpr hxO
  rw [hs, show n + 1 - j = (n - j) + 1 by omega, Finset.sum_range_succ', Nat.add_zero, pow_zero,
    _root_.mul_one, hcj, Valuation.map_add_eq_of_lt_right, map_one]
  rw [map_one]
  apply Valuation.map_sum_lt _ one_ne_zero
  intro k _
  rw [map_mul, map_pow]
  exact lt_of_le_of_lt (mul_le_of_le_one_right' (pow_le_one' hxle _)) (hclt _ (by omega))

end GlobalTheory.DomValInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovedRowLiftDataToFittingStages
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw.Mv

variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C) {px : PreX B.toPre} {I : ColIn B px} {hX : B.fields.Ok}
  {T : TwDat B} {Wt : Set B.places.Pl}

def sameGrp {f : Fr B.toPre} (h : GrpTrue a.N f) (h' : GrpTrue b.N f) : SameGrp a b where
  e k := (by with_unfolding_all exact ((plEquiv a.N.naut b.N.naut k) :))
  pl k v := (by with_unfolding_all exact ((TypesTrue.plGw_plEquiv h h' k v) :))
  e0 g := (by with_unfolding_all exact ((h.typeIdempotent_coeff_across_layers h' g) :))

def cpR (z : Dat a.st I hX T Wt) :
    @RealDat3 b.st.toD7 _ _ _ _ _ _ (famR b.st I hX (usedOf I T Wt) z.Xg z.tr) (coreJ b z.core).Q.c.F _ _ ((by with_unfolding_all exact ((alg b z.alg) :))) :=
  (by with_unfolding_all exact ((real3 b (iK := z.alg) z.R) :))

theorem levOf_tr {U : Set I.ι} {L : Links.LevCh a.D (TupU I U)} (h : LevOf a.st I U L) : LevOf b.st I U (levCh b L) := by
  constructor
  case is => exact (by with_unfolding_all exact ((levIs_tr b h.is) :))
  case C => exact (by with_unfolding_all exact ((congrArg (chFr b) h.C) :))
  case xiH => exact (by with_unfolding_all exact (h.xiH :))
  case Pg => exact (by with_unfolding_all exact (h.Pg :))
  case Q => exact (by with_unfolding_all exact (h.Q :))
  case beta => exact (by with_unfolding_all exact (h.beta :))

theorem goodSet_tr (s : SameGrp a b) {eR : Gc B px ≃* G0g a.D.nd} {Xg : Finset (Gc B px → B.LL)}
    (h : GoodSet a.st (px := px) eR Xg) : GoodSet b.st (px := px) (eR.trans s.iso) Xg := by
  have e : (fun g => a.D.ntypes.e0.coeff (eR g)) = fun g => b.D.ntypes.e0.coeff ((eR.trans s.iso) g) :=
    funext fun g => (s.e0 (eR g)).symm
  refine (goodSet_iff b.st (px := px) _ Xg).2 ?_
  exact (congrArg (fun c : Gc B px → ℂ => (∀ χ : Gc B px → B.LL, χ ∈ Xg ↔ IsAbsIrrChar χ ∧
    ∑ g : Gc B px, c g * B.embLL (χ g) = B.embLL (χ 1)) ∧ ∀ g, B.embLL ((idemOf Xg).coeff g) = c g) e).mp
    ((goodSet_iff a.st (px := px) eR Xg).1 h)

def cpDat (s : SameGrp a b) (z : Dat a.st I hX T Wt) : Dat b.st I hX T Wt :=
  @Dat.mk b.st px I hX T Wt
    (Xg := z.Xg)
    (tr := z.tr)
    (core := coreJ b z.core)
    (alg := (by with_unfolding_all exact ((alg b z.alg) :)))
    (alg_eq := (by with_unfolding_all exact (z.alg_eq :)))
    (R := cpR b z)
    (cG := (by with_unfolding_all exact ((z.cG.trans s.iso) :)))
    (geo := (by with_unfolding_all exact ((geoHalf b (iK := z.alg) z.geo) :)))
    (pins := (by with_unfolding_all exact ((pins_tr b (iK := z.alg) s z.pins) :)))
    (lev := (by with_unfolding_all exact ((levOf_tr b z.lev) :)))
    (idG := (by with_unfolding_all exact (z.idG :)))
    (good := (by with_unfolding_all exact ((goodSet_tr b s z.good) :)))
    (mu := (by with_unfolding_all exact (z.mu :)))
    (fieldValues_mem_fixedField := (by with_unfolding_all exact (z.fieldValues_mem_fixedField :)))
    (Ks_le := (by with_unfolding_all exact (z.Ks_le :)))

theorem lawsCore_tr {K : Formalism.L2.Pj.Core a.D} (h : Formalism.L2.Pj.LawsCore K) : Formalism.L2.Pj.LawsCore (core b K) := by
  constructor
  case toLawsM => exact (by with_unfolding_all exact ((lawsM_tr b h.toLawsM) :))
  case cuspMul => exact (by with_unfolding_all exact (h.cuspMul :))
  case latZ => exact (by with_unfolding_all exact (h.latZ :))
  case cuNe => exact (by with_unfolding_all exact (h.cuNe :))
  case expo => exact (by with_unfolding_all exact (h.expo :))

variable (s : SameGrp a b) (z : Dat a.st I hX T Wt)

theorem cp_holds (h : Holds z.R z.F) : Holds (cpDat b s z).R (cpDat b s z).F := (by with_unfolding_all exact ((holds_tr b (iK := z.alg) h) :))

theorem cp_exAt (h : z.R.toRealDat.ExAt) : (cpDat b s z).R.toRealDat.ExAt := (by with_unfolding_all exact ((exAt_tr b (iK := z.alg) h) :))

theorem cp_inGeo (h : GlobalTheory.RealGeo.InGeo z.geo) : GlobalTheory.RealGeo.InGeo (cpDat b s z).geo := (by with_unfolding_all exact ((inGeo_tr b (iK := z.alg) h) :))

theorem cp_canon (h : z.core.Q.Canon) : (cpDat b s z).core.Q.Canon := (by with_unfolding_all exact (h :))

theorem forcedContentPlaces_eq_transport_sameFiniteGroup (F0) : (cpDat b s z).W1 F0 = z.W1 ((F0)) :=
  (by with_unfolding_all exact ((congrArg (fun X : Cx.CxData (famR a.st I hX (usedOf I T Wt) z.Xg z.tr).fam3.amb3 =>
    {w : B.places.Pl | ∃ j, ∃ w' ∈ ({a.D.plEq w, Formalism.DivisionValues.conjPl (a.D.plEq w)} : Set (HeightOneSpectrum (𝓞 a.D.what₂.LL))),
    (X.data z.F.cr false).Iw j (famR a.st I hX (usedOf I T Wt) z.Xg z.tr).A.μ0 w' ≠ 0 ∨
    Formalism.DivisionValues.jw (((famR a.st I hX (usedOf I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 X.zs).HT j
              (famR a.st I hX (usedOf I T Wt) z.Xg z.tr).A.μ0) w'
      (((famR a.st I hX (usedOf I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 X.zs).Tl j
        (famR a.st I hX (usedOf I T Wt) z.Xg z.tr).A.μ0) ≠ 0 ∨ ((F0) : HeightOneSpectrum (𝓞 a.D.what₂.LL) → Fin a.D.R.m → ℝ) w' j ≠ 0})
    (toCx3_eq b (iK := z.alg) z.R z.F).symm) : _))

section Read

variable {G : Type} [Group G] [Fintype G] {Pl0 I0 T₀ : Type} {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]

def fixTup {A : FamIn a.D.what₂.LL G Pl0 T₀ a.D.R.m} {R : RealDat a.D A Ks} (y : Hd R) (y' : HdB b R) : HdB b R :=
  letI := alg b iK
  { y' with tup := (by with_unfolding_all exact (y.tup :)), tupT := (by with_unfolding_all exact (y.tupT :)), tupT_tup := (by with_unfolding_all exact (y.tupT_tup :)), tup0 := (by with_unfolding_all exact (y.tup0 :)) }

theorem fixTup_same {A : FamIn a.D.what₂.LL G Pl0 T₀ a.D.R.m} {R : RealDat a.D A Ks} {y : Hd R} {y' : HdB b R} (h : Same b y y') :
    Same b y (fixTup b y y') :=
  ⟨(by with_unfolding_all exact ((HEq.refl y.tup) :)), (by with_unfolding_all exact ((HEq.refl y.tupT) :)), (by with_unfolding_all exact (h.PY :)), (by with_unfolding_all exact (h.PW :))⟩

variable {A3 : FamIn3 a.D.what₂.LL G Pl0 I0 (List ℕ) T₀ a.D.R.m} {R : RealDat3 a.D A3 Ks} (F : Face3 a.D A3) (y : Hd R.toRealDat)
  (y' : HdB b R.toRealDat)

def hd3 : letI := alg b iK; Hd (real3 b R).toRealDat := (by with_unfolding_all exact ((fixTup b y y') :))

def mCp (mA : Bool → a.D.what₂.Tup → Mat1 a.D.what₂.LL G) : Bool → b.D.what₂.Tup → Mat1 b.D.what₂.LL G := (by with_unfolding_all exact (mA :))

def pCp (p : PkD a.D G) : PkD b.D G := (by with_unfolding_all exact (p :))

theorem dall_tr {n : ℕ} (h : n = Module.finrank ℂ (Mult.Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true)))
    (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true))))) : letI := alg b iK
    n = Module.finrank ℂ (Mult.Mult (real3 b R).θ ((real3 b R).MY 0)
      (levS _ ((real3 b R).βY 0) ((real3 b R).dat0 ((real3 b R).toRealDat.levR (face3 b F).lv2 true)))
      (levChi _ ((real3 b R).βY 0) ((real3 b R).dat0 ((real3 b R).toRealDat.levR (face3 b F).lv2 true)))) := by
  exact (congrArg (fun m : type_of% (@Mult.Mult a.D) => n = Module.finrank ℂ (m R.θ (R.MY 0)
    (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true))) (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 true)))))
    (mult_eq b a)).mp h


set_option maxHeartbeats 1000000 in
theorem pkT_tr (hs : Same b y y') {mA : Bool → a.D.what₂.Tup → Mat1 a.D.what₂.LL G} {p : PkD a.D G} (t : PkT F y mA p) :
    letI := alg b iK
    ∃ t' : PkT (R := real3 b R) (face3 b F) (hd3 b y y') (mCp b mA) (pCp b p),
      HEq t'.tA t.tA ∧ HEq t'.rep t.rep ∧ (∀ c, HEq (t'.ch c).jE (t.ch c).jE) ∧ (∀ c, HEq (t'.ch c).jM (t.ch c).jM) ∧
        (∀ c, HEq (t'.ch c).jX (t.ch c).jX) ∧ HEq t'.lf.eW t.lf.eW ∧ HEq t'.lf.jMt t.lf.jMt := by
  letI := alg b iK
  have hs' := fixTup_same b hs
  have h1 := (_root_.GlobalTheory.Mem.R3.Tr.reps_parts_tr B C a b G Pl0 T₀ Ks A3.A R.toRealDat F.lv2 y _ hs').1 p.Φ t.rep t.reps
  have h2 := fun c => GlobalTheory.T.chainComparison_transfer_otherLaterStages B C a b G Pl0 T₀ Ks A3.A R.toRealDat F.lv2 y _ hs' c p.Φ t.rep
    ((by with_unfolding_all exact ((fun μ => (p.sA c μ).A) :))) ((by with_unfolding_all exact ((p.ch c) :))) ((by with_unfolding_all exact ((fun u x => ((t.tA c (y.tup u)).cast (t.hA c u)).j x) :))) ((by with_unfolding_all exact ((t.ch c) :)))
    ((by with_unfolding_all exact ((fun u x => ((t.tA c (y.tup u)).cast (t.hA c u)).j x) :)))
    ((by with_unfolding_all exact ((HEq.refl (fun u x => ((t.tA c (y.tup u)).cast (t.hA c u)).j x)) :)))
  obtain ⟨l, hl1, hl2⟩ := GlobalTheory.T.liftsCompatible_otherLaterStages_of_sameChoices B C a b G Pl0 T₀ Ks A3.A R.toRealDat F.lv2 y _ hs' p.Φ t.rep
    ((by with_unfolding_all exact ((fun μ j => (p.sL μ j).A) :))) ((by with_unfolding_all exact (p.lf :)))
    ((by with_unfolding_all exact ((fun (i : Fin a.D.R.m) u x => ((p.tL (y.tup u) ((i : ℕ) + 1)).cast (t.hL i u)).j x) :))) ((by with_unfolding_all exact (t.lf :)))
    ((by with_unfolding_all exact ((fun (i : Fin a.D.R.m) u x => ((p.tL (y.tup u) ((i : ℕ) + 1)).cast (t.hL i u)).j x) :)))
    ((by with_unfolding_all exact ((HEq.refl (fun (i : Fin a.D.R.m) u x => ((p.tL (y.tup u) ((i : ℕ) + 1)).cast (t.hL i u)).j x)) :)))
  have h4 := (GlobalTheory.T.rowBasis_congruenceLengths_other_later_stages B C a b G Pl0 I0 T₀ Ks A3 R F).2 y (hd3 b y y') true (p.ch true).EE (t.ch true).jE
    ((by with_unfolding_all exact ((h2 true).choose.jE :))) p.nR p.cR p.Xo ((by with_unfolding_all exact ((h2 true).choose_spec.1 :))) t.rr
  refine ⟨{ rep := (by with_unfolding_all exact (t.rep :))
            reps := (by with_unfolding_all exact (h1 :))
            tA := (by with_unfolding_all exact (t.tA :))
            lawsA := (by with_unfolding_all exact (t.lawsA :))
            lawsL := (by with_unfolding_all exact (t.lawsL :))
            hA := (by with_unfolding_all exact (t.hA :))
            hL := (by with_unfolding_all exact (t.hL :))
            ch := fun c => (by with_unfolding_all exact ((h2 c).choose :))
            lf := (by with_unfolding_all exact (l :))
            dall := (by with_unfolding_all exact ((dall_tr b F t.dall) :))
            rr := (by with_unfolding_all exact (h4 :)) }, ?_, ?_, fun c => ?_, fun c => ?_, fun c => ?_, ?_, ?_⟩
  · exact (by with_unfolding_all exact ((HEq.refl t.tA) :))
  · exact (by with_unfolding_all exact ((HEq.refl t.rep) :))
  · exact (by with_unfolding_all exact ((h2 c).choose_spec.1 :))
  · exact (by with_unfolding_all exact ((h2 c).choose_spec.2.1 :))
  · exact (by with_unfolding_all exact ((h2 c).choose_spec.2.2 :))
  · exact (by with_unfolding_all exact (hl1 :))
  · exact (by with_unfolding_all exact (hl2 :))

end Read


set_option maxHeartbeats 1000000 in
theorem exists_moved : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z₀ : w.Lt) (hX : B.fields.Ok)
    (Wt : Set B.places.Pl) (z₀ : Dat (w.st Z₀) w.I hX T Wt), ∀ (q : RowPk w z₀) (o : q.Over), Holds z₀.R z₀.F →
    z₀.R.toRealDat.ExAt → GlobalTheory.RealGeo.InGeo z₀.geo → GrpTrue Z₀.N f → o.Fits → ∃ m : Moved o, m.Copy ∧ m.Coh := by
  intro B f T w Z₀ hX Wt z₀ q o h1 h2 h3 h4 h5
  have s : SameGrp (B := B) (C := w.C) Z₀ o.Z := sameGrp o.Z h4 h5.grp
  obtain ⟨y', hy⟩ := @GlobalTheory.Mem.R3.Rw.hd_tr B w.C Z₀ o.Z _ _ _ _ _ _ _ _ z₀.alg _ z₀.R.toRealDat q.y
  obtain ⟨t, a1, a2, a3, a4, a5, a6, a7⟩ := pkT_tr (a := Z₀) o.Z (iK := z₀.alg) z₀.F q.y y' hy q.t
  have he := (@GlobalTheory.T.rowBasis_congruenceLengths_other_later_stages B w.C Z₀ o.Z _ _ _ _ _ _ _ _ _ z₀.alg _ z₀.R z₀.F).1
  letI : Algebra z₀.core.Q.c.F (Late.D o.Z).what₂.LL := alg (a := Z₀) o.Z z₀.alg
  have hA : ((by with_unfolding_all exact (t.tA :)) : type_of% q.t.tA) = q.t.tA := eq_of_heq ((by with_unfolding_all exact (a1 :)))
  have hs := fixTup_same (a := Z₀) o.Z (iK := z₀.alg) hy
  refine ⟨{ z := cpDat (a := Z₀) o.Z s z₀
            intersectionNumber_baseChange := cp_holds (a := Z₀) o.Z s z₀ h1
            exAt := cp_exAt (a := Z₀) o.Z s z₀ h2
            inGeo := cp_inGeo (a := Z₀) o.Z s z₀ h3
            Xg := rfl
            tr := rfl
            core := fun h => ⟨(by with_unfolding_all exact ((lawsCore_tr (a := Z₀) o.Z h.1) :)), cp_canon (a := Z₀) o.Z s z₀ h.2.1, (by with_unfolding_all exact (h.2.2.1 :)), (by with_unfolding_all exact (h.2.2.2 :))⟩
            eta := (by with_unfolding_all exact (he :))
            W1 := (by with_unfolding_all exact ((forcedContentPlaces_eq_transport_sameFiniteGroup (a := Z₀) o.Z s z₀) :))
            y := (by with_unfolding_all exact ((hd3 (a := Z₀) o.Z (iK := z₀.alg) q.y y') :))
            tup := (by with_unfolding_all exact (q.tup :))
            t := (by with_unfolding_all exact (t :))
            tA := fun c u => (by with_unfolding_all exact ((heq_of_eq (congrArg (fun r : type_of% q.t.tA => (r c ((u))).j) hA)) : _)) }, ⟨?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact (by with_unfolding_all exact ((HEq.refl (coreJ (a := Z₀) o.Z z₀.core)) :))
  · exact (by with_unfolding_all exact ((HEq.refl (real3 (a := Z₀) o.Z (iK := z₀.alg) z₀.R)) :))
  · exact (by with_unfolding_all exact ((HEq.refl q.y.tupT) :))
  · exact (by with_unfolding_all exact (hy.PY :))
  · exact (by with_unfolding_all exact (hy.PW :))
  · exact (by with_unfolding_all exact (a2 :))
  · exact (by with_unfolding_all exact (a3 :))
  · exact (by with_unfolding_all exact (a4 :))
  · exact (by with_unfolding_all exact (a5 :))
  · exact (by with_unfolding_all exact (a6 :))
  · exact (by with_unfolding_all exact (a7 :))

end GlobalTheory.Mem.R3.Rw.Mv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendSplitTorusHomOverDvr
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.TorusPart

theorem extend_torus_hom_dvr : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G],
    IsSemiAbelian G → ∀ (G₁ : Over (Sp (FractionRing V))) [GrpObj G₁] (φ₁ : G₁.left ⟶ G.left),
    IsGrpPullback G₁ G (spMap (algebraMap V (FractionRing V))) φ₁ → Nonempty (TorusExtension G₁) →
    ∀ (Ω : Type) [Field Ω] (α : FractionRing V →+* Ω) (G' : Over (Sp Ω)) [GrpObj G'] (φ : G'.left ⟶ G.left)
      (h : IsGrpPullback G' G (spMap (α.comp (algebraMap V (FractionRing V)))) φ)
      (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp Ω) X ⟶ G'), IsMonHom i →
      ∃ j : splitTorus (Sp V) X ⟶ G, IsMonHom j ∧ GlobalTheory.TorusPart.pullTorus h j = i := by
  intro V _ _ _ G _ _ hG G₁ _ φ₁ h₁ hT Ω _ α G' _ φ h X _ _ _ i hi
  obtain ⟨T⟩ := hT
  letI := T.addCommGroup; letI := T.grpB
  haveI := T.free; haveI := T.finite
  have := T.i_hom; have := T.q_hom; have := T.isAbelian.proper
  set a := algebraMap V (FractionRing V)
  have ef : spMap (α.comp a) = spMap α ≫ spMap a := by
    rw [← Spec.map_comp]; rfl

  let ψ : G'.left ⟶ G₁.left := h₁.1.lift φ (G'.hom ≫ spMap α) (by
    rw [Category.assoc, ← ef]; exact h.1.w)
  have hψ : ψ ≫ φ₁ = φ := h₁.1.lift_fst _ _ _
  have h₂ : IsGrpPullback G' G₁ (spMap α) ψ :=
    h₁.cancel (h.congr ef hψ.symm) (h₁.1.lift_snd _ _ _)

  obtain ⟨q', hq', hk⟩ := exists_isKernel_pullTorus h₂ T.i T.q T.isKernel
  have : IsProper ((Over.pullback (spMap α)).obj T.B).hom :=
    inferInstanceAs (IsProper (pullback.snd _ _))
  have hiq : i ≫ q' = toUnit _ ≫ η[(Over.pullback (spMap α)).obj T.B] :=
    splitTorus_hom_proper_trivial_local Ω X _ (i ≫ q') inferInstance
  have : Mono (pullTorus h₂ T.i) := ⟨fun x y e => hk.hom_ext e (toUnit_unique _ _)⟩
  let u' := hk.lift i (toUnit _) hiq
  have hu' : u' ≫ pullTorus h₂ T.i = i := hk.lift_fst _ _ _
  have : IsMonHom u' := Serre.isMonHom_of_mul_comp u' fun S x y => by
    rw [← cancel_mono (pullTorus h₂ T.i), MonObj.mul_comp (x ≫ u'), Category.assoc, Category.assoc,
      Category.assoc, hu', MonObj.mul_comp]
  haveI : ConnectedSpace (Sp Ω) := SplitTorus.connectedSpace_of_isLocalRing Ω
  obtain ⟨u, hu⟩ := SplitTorus.exists_eq_torusMap u'

  obtain ⟨e, he, heφ⟩ := grpPullback_iso h₁ (isGrpPullback_pullback G (spMap a))
  let j₁ : splitTorus (Sp (FractionRing V)) X ⟶ G₁ := SplitTorus.torusMap _ u ≫ T.i
  have : IsMonHom j₁ := inferInstance
  let f := (SplitTorus.bcIso (spMap a) X).inv ≫ j₁ ≫ e.hom
  have : IsMonHom f := inferInstance
  obtain ⟨F, ⟨hF, hF'⟩, -⟩ := homExtension_semiAbelian_dvr V (FractionRing V) (splitTorus (Sp V) X) G
    inferInstance hG f inferInstance
  refine ⟨F, hF, ?_⟩
  have hj₁ : pullTorus h₁ F = j₁ := by
    rw [eq_comm, eq_pullTorus_iff]
    have k : f.left ≫ pullback.fst G.hom (spMap a) =
        pullback.fst (splitTorus (Sp V) X).hom (spMap a) ≫ F.left := by
      rw [← hF']; exact pullback.lift_fst _ _ _
    have k2 := congrArg ((SplitTorus.bcIso (spMap a) X).hom.left ≫ ·) k
    simp only [f, Over.comp_left, Category.assoc, heφ] at k2
    rw [← Category.assoc, ← Over.comp_left, Iso.hom_inv_id, Over.id_left, Category.id_comp,
      SplitTorus.bcIso_hom_fst_assoc] at k2
    exact k2
  rw [← pullTorus_pullTorus h₂ h₁ h ef hψ.symm, hj₁, pullTorus_torusMap_comp, ← hu, hu']

end GlobalTheory.TorusPart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaSeriesRationalOnGoodCoversOfUntwistedStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeriesRationalOnGoodCovers_of_untwisted : GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.UntwRatS → GlobalTheory.SerStd.SeriesRatS := by
  first | exact @GlobalTheory.SerStdTwist.seriesRatS_of_untwRatS | exact GlobalTheory.SerStdTwist.seriesRatS_of_untwRatS | (intros; apply GlobalTheory.SerStdTwist.seriesRatS_of_untwRatS <;> assumption)
end

