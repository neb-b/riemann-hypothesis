module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCosetOfIsTensor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoefficientBound
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0604
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0425
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0501
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowEqSpan
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0059
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2786
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2787
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierMultipleGlobalSectionsChartEqSpan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2163
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2159
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2374
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2234
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2694
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2788
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2586
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2805
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2774
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecBaseChangeOfPerf
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FinrankOfIsSecBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedTensorFactorCoeffValuationLossLeAwayPrime
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

noncomputable section

namespace GlobalTheory.MovedTwist

open Formalism.L2.Host GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing GlobalTheory.ChiUnit

theorem unitOff_loc {L : Type} [Field L] [NumberField L] (χ : HChar L) {I : Type} [Fintype I] {φ : I → L →+* ℂ} {n : I → ℤ}
    (hinf : χ.HasInf φ n) (v : HeightOneSpectrum (𝓞 L)) {q : ℕ} (hq : (q : 𝓞 L) ∈ v.asIdeal) (x : (v.adicCompletion L)ˣ) :
    UnitOff q ((χ.loc v x : ℂˣ) : ℂ) := by
  obtain ⟨N, hN, hu⟩ := GlobalTheory.Corev.UnrPow.exists_pow_unrAt L χ
  have hinf' : (χ ^ N).HasInf φ fun i => n i * N := fun k => by
    have e : (χ ^ N).inf k = χ.inf k ^ N := rfl
    rw [e, Units.val_pow_eq_pow_val, hinf k, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [zpow_mul, zpow_natCast]
  have hv := GlobalTheory.ValUnit.unitOff_val L (χ ^ N) I φ _ v q hinf' (by simp [hu]) (fun w x hx _ => hu w x hx) (hu v) hq
  refine unitOff_of_pow hN ?_
  have e : ((χ.loc v x : ℂˣ) : ℂ) ^ N = (((χ ^ N).loc v x : ℂˣ) : ℂ) := by
    rw [← Units.val_pow_eq_pow_val]; rfl
  rw [e]
  set u : (v.adicCompletion L)ˣ := atFin v (unif v) with hudef
  have h0 : Valued.v (x : v.adicCompletion L) ≠ 0 := by simp
  have hu1 : Valued.v (u : v.adicCompletion L) = WithZero.exp (-1 : ℤ) := unif_spec v
  have hx : Valued.v (x : v.adicCompletion L) = WithZero.exp (WithZero.log (Valued.v (x : v.adicCompletion L))) :=
    (WithZero.exp_log h0).symm
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v (((x * u ^ m : (v.adicCompletion L)ˣ)) : v.adicCompletion L) = 1 := by
    refine ⟨WithZero.log (Valued.v (x : v.adicCompletion L)), ?_⟩
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hx, hu1, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp
  have hx' : x = (x * u ^ m) * u ^ (-m) := by
    rw [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
  rw [hx', map_mul, hu v _ hm, one_mul, map_zpow, Units.val_zpow_eq_zpow_val]
  exact unitOff_zpow hv _

theorem unitOff_sqrt_absNorm {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)) {q : ℕ} (hq0 : q ≠ 0)
    (hq : (q : 𝓞 L) ∈ v.asIdeal) : UnitOff q ((Real.sqrt (Ideal.absNorm v.asIdeal) : ℝ) : ℂ) := by
  refine unitOff_of_pow two_pos ?_
  rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
  have h := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hq)
  rw [Ideal.absNorm_span_natCast] at h
  obtain ⟨b, hb⟩ := h
  have hi : ∀ a : ℕ, IsIntegral ℤ (a : ℂ) := fun a => by
    simpa using isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (a : ℤ))
  refine unitOff_of_mul_eq (m := Module.finrank ℤ (𝓞 L)) (hi _) (hi b) ?_ hq0
  rw [← Nat.cast_mul, ← hb, Nat.cast_pow]

variable {D : D7}

theorem unitOff_apow_half {P : Pl D.host.E} {q : ℕ} (hq0 : q ≠ 0) (hq : (q : 𝓞 D.host.E) ∈ P.asIdeal) (x : (Kw P)ˣ) (z : ℤ) :
    UnitOff q (apow x ((z : ℂ) / 2)) := by
  obtain ⟨n, hn⟩ := GlobalTheory.MovedField.exists_zpow_unit P x
  have h1 : valuation (Kw P) (((x * unifAt P ^ n : (Kw P)ˣ)) : Kw P) = 1 := (Good.isEquiv_Kw P).eq_one_iff_eq_one.2 hn
  have hx : x = (x * unifAt P ^ n) * unifAt P ^ (-n) := by
    rw [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
  rw [hx, apow_mul, apow_of_valuation_eq_one h1, one_mul, apow_zpow, (isUnif_unifAt P).apow_eq,
    GlobalTheory.LFun.SatBoundGL.resCard_completion]
  have e1 : -(((-n : ℤ) : ℂ) * ((z : ℂ) / 2)) = ((((n * z : ℤ) : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [e1, GlobalTheory.MovedField.natCast_cpow_half]
  exact unitOff_zpow (unitOff_sqrt_absNorm P hq0 hq) _

theorem lossLe_unit_mul {w : PlL D} {q : ℕ} (hw : (q : 𝓞 D.what₂.LL) ∉ w.asIdeal) {u z : ℂ} {c : ℝ}
    (hu : u ∈ D.what₂.embLL.fieldRange) (hq : UnitOff q u) (hz : LossLe w z c) : LossLe w (u * z) c := by
  obtain ⟨y, rfl⟩ := hu
  obtain ⟨y', rfl, h'⟩ := hz
  refine ⟨y * y', map_mul _ _ _, ?_⟩
  by_cases h0 : y' = 0
  · exact Or.inl (by rw [h0, mul_zero])
  have h' := h'.resolve_left h0
  obtain ⟨hy, k, hk, -⟩ := hq
  have hy0 : y ≠ 0 := fun e => hy (by rw [e, map_zero])
  have hq0 : (q : D.what₂.LL) ≠ 0 := by
    have : q ≠ 0 := fun e => hw (by rw [e, Nat.cast_zero]; exact zero_mem _)
    exact_mod_cast this
  have hint : IsIntegral ℤ ((q : D.what₂.LL) ^ k * y) := by
    rw [← isIntegral_algHom_iff D.what₂.embLL.toIntAlgHom D.what₂.embLL.injective]
    simpa using hk
  have hqk : ((q ^ k : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal := fun h => hw (w.isPrime.mem_of_pow_mem k (by simpa using h))
  have h1 : vw w ((q ^ k : ℕ) : D.what₂.LL) = 0 := by
    have h0 : ((q ^ k : ℕ) : 𝓞 D.what₂.LL) ≠ 0 := fun e => hqk (e ▸ zero_mem _)
    have h1 := Formalism.EigenvalueLevelCeiling.intValuation_eq_exp' w _ h0
    rw [(w.intValuation_eq_one_iff).2 hqk, ← WithZero.exp_zero] at h1
    have h2 := WithZero.exp_injective h1
    have h3 : (((q ^ k : ℕ) : 𝓞 D.what₂.LL) : D.what₂.LL) = ((q ^ k : ℕ) : D.what₂.LL) := by simp
    rw [h3] at h2
    omega
  have h2 : 0 ≤ vw w ((q : D.what₂.LL) ^ k * y) := Formalism.DivisionValues.ValuationRepresentative.vw_int_nonneg w (⟨_, hint⟩ : 𝓞 D.what₂.LL)
  rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ (pow_ne_zero _ hq0) hy0, ← Nat.cast_pow, h1, zero_add] at h2
  refine Or.inr ?_
  rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ hy0 h0, Int.cast_add]
  have h3 : (0 : ℝ) ≤ (vw w y : ℝ) := by exact_mod_cast h2
  linarith

def UnitIn (K : Subfield ℂ) (q : ℕ) (u : ℂ) : Prop := u ∈ K ∧ UnitOff q u

theorem UnitIn.mul {K : Subfield ℂ} {q : ℕ} {u v : ℂ} (h : UnitIn K q u) (h' : UnitIn K q v) : UnitIn K q (u * v) :=
  ⟨mul_mem h.1 h'.1, unitOff_mul h.2 h'.2⟩

theorem UnitIn.inv {K : Subfield ℂ} {q : ℕ} {u : ℂ} (h : UnitIn K q u) : UnitIn K q u⁻¹ := ⟨inv_mem h.1, unitOff_inv h.2⟩

theorem UnitIn.pow {K : Subfield ℂ} {q : ℕ} {u : ℂ} (h : UnitIn K q u) (n : ℕ) : UnitIn K q (u ^ n) :=
  ⟨pow_mem h.1 n, unitOff_pow h.2 n⟩

theorem unitIn_one (K : Subfield ℂ) (q : ℕ) : UnitIn K q 1 := ⟨one_mem K, unitOff_one q⟩

theorem unitIn_prod {α : Type*} {K : Subfield ℂ} {q : ℕ} (f : α → ℂ) :
    ∀ l : List α, (∀ a ∈ l, UnitIn K q (f a)) → UnitIn K q (l.map f).prod
  | [], _ => by simpa using unitIn_one K q
  | a :: l, h => by
    rw [List.map_cons, List.prod_cons]
    exact (h a List.mem_cons_self).mul (unitIn_prod f l fun b hb => h b (List.mem_cons_of_mem _ hb))

end GlobalTheory.MovedTwist


open GlobalTheory.MovedTwist GlobalTheory.MovedField Formalism.L2.Host GlobalTheory.ChiUnit in
theorem GlobalTheory.MovedTwist.moved_lossLe : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A) (CF b : ℝ),
    HidaSetting large₂ R F → ch.Is → ch.AtScale CF b → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ∀ β ∈ ch.S.supp t Φ, ∀ (P : locPl ch.G t),
    (P : Pl D.host.E) ∉ ch.G.pl.W0 → ∀ (w : PlL D), ((Formalism.EigenvalueLevelCeiling.plc (P : Pl D.host.E) : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal →
    ∀ (c : ℝ), 0 ≤ c → (∀ z, LossLe w (Tflip ch.W ch.S.B t Φ P z) c) →
    ∀ z, LossLe w (moved (locGrid ch.G t P) (keepAt ch.G P) ((repsAt ch.G t P).elt (β P)) (Tflip ch.W ch.S.B t Φ P) z) c := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F CF b hS _ _ hF t Φ β _ P hP w hw c _ hT z
  set K : Subfield ℂ := D.what₂.embLL.fieldRange with hKdef
  set q : ℕ := Formalism.EigenvalueLevelCeiling.plc (P : Pl D.host.E) with hqdef
  have hq0 : q ≠ 0 := (Formalism.EigenvalueLevelCeiling.plc_prime _).ne_zero
  have hq : (q : 𝓞 D.host.E) ∈ (P : Pl D.host.E).asIdeal := Formalism.EigenvalueLevelCeiling.plc_mem _
  have hK : ∀ y : ℂ, y ∈ Set.range D.what₂.embLL ↔ y ∈ K := fun y => by
    rw [Set.mem_range, hKdef, RingHom.mem_fieldRange]
  have hsq : ((Real.sqrt (Ideal.absNorm (P : Pl D.host.E).asIdeal) : ℝ) : ℂ) ∈ K :=
    (hK _).1 (hF.sqrt P.1 (.inr ⟨t, P.2⟩))
  have hmu : ∀ j (x : (Kw P.1)ˣ), UnitIn K q (((locGrid ch.G t P).mu j x : ℂˣ) : ℂ) := fun j x => by
    show UnitIn K q ((((GlobalTheory.FunObj.muBase _ j * _).loc _) x : ℂˣ) : ℂ)
    change UnitIn K q (((GlobalTheory.FunObj.muBase R.toLevCh j).loc P.1 x * (R.xiH t).loc P.1 x : ℂˣ) : ℂ)
    rw [Units.val_mul]
    refine UnitIn.mul ?_ ⟨(hK _).1 (hF.chars.xi t _ x), ?_⟩
    · rcases j with _ | j
      · simpa [GlobalTheory.FunObj.muBase, HChar.loc] using unitIn_one K q
      · rw [GlobalTheory.FunObj.muBase]
        split_ifs with hj
        · obtain ⟨n, -, hn⟩ := (R.toLevCh.C.isMu0 ⟨j, hj⟩).inf
          exact ⟨(hK _).1 (hF.chars.mu0 ⟨j, hj⟩ _ x), unitOff_loc _ hn _ hq x⟩
        · simpa [HChar.loc] using unitIn_one K q
    · obtain ⟨n, hn, ho⟩ := hS.core.lev.xi_fin t
      refine unitOff_of_pow_eq_one q hn ?_
      have : ((R.toLevCh.xiH t) ^ n).loc P.1 x = 1 := by rw [show (R.toLevCh.xiH t) ^ n = 1 from ho]; rfl
      rw [← Units.val_pow_eq_pow_val]
      exact congrArg Units.val this
  have hchi : ∀ i, 1 ≤ i → i ≤ D.R.m → ∀ x : (Kw P.1)ˣ, UnitIn K q (((locGrid ch.G t P).chi i x : ℂˣ) : ℂ) :=
    fun i h1 h2 x => ⟨(hK _).1 (hF.chars.chi i h1 h2 _ x), unitOff_loc _ (ch.G.ch.inf i h1 h2) _ hq x⟩
  have heta : ∀ x : (Kw P.1)ˣ, UnitIn K q (((locGrid ch.G t P).eta x : ℂˣ) : ℂ) := fun x => by
    have hu := R.toLevCh.C.isEta.unr P.1
    obtain ⟨y, hy⟩ := hF.chars.eta P.1 hu
    exact ⟨loc_mem_of_unrAt hu (hy ▸ (hK _).1 ⟨y, rfl⟩) hsq x, unitOff_loc _ R.toLevCh.C.isEta.inf _ hq x⟩
  have hkap : ∀ e ∈ oppositePath D.R.m, ∀ X (x : (Kw P.1)ˣ), UnitIn K q (((locGrid ch.G t P).kappa e X x : ℂˣ) : ℂ) := by
    intro e he X x
    rw [Grid.kappa, MonoidHom.div_apply, MonoidHom.pow_apply, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val, div_eq_mul_inv]
    refine UnitIn.mul ?_ ((heta x).pow _).inv
    rcases GlobalTheory.FunObj.mem_oppositePath.1 he with ⟨i, hi, rfl⟩ | ⟨j, -, rfl⟩
    · exact hchi _ (by show 1 ≤ D.R.m - i; omega) (by show D.R.m - i ≤ D.R.m; omega) x
    · exact hmu _ x
  have hap : ∀ (x : (Kw P.1)ˣ) (n : ℕ), UnitIn K q (apow x ((n : ℂ) / 2)) ∧ UnitIn K q (apow x (-(n : ℂ) / 2)) := fun x n =>
    ⟨⟨by simpa using apow_half_mem hsq x n, by simpa using unitOff_apow_half hq0 hq x n⟩,
      by simpa using apow_half_mem hsq x (-n), by simpa using unitOff_apow_half hq0 hq x (-n)⟩
  have hedge : ∀ g, ∀ e ∈ oppositePath D.R.m, UnitIn K q ((locGrid ch.G t P).edgeFactor .one g e) := by
    intro g e he
    rw [Grid.edgeFactor, Units.val_inv_eq_inv_val]
    exact (((hkap e he _ _).mul (hkap e he _ _).inv).mul (hap _ _).1).mul (hap _ _).2
  have hk : keepAt ch.G (P : Pl D.host.E) = true := by
    classical
    simp [keepAt, hP]
  have hg := unitIn_prod _ _ (hedge ((repsAt ch.G t P).elt (β P)))
  simp only [moved, Grid.pathAct, hk, if_true, one_mul]
  exact lossLe_unit_mul hw hg.1 hg.2 (hT _)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyDescentSeparatedEmbedding
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.EmbeddingLemmas

theorem spMap_cst {X : Scheme.{0}} [IsIntegral X] {R : Type} [CommRing R] (p : X ⟶ Sp R) :
    spMap (Desc.cst p) = gp X ≫ p := by
  have h : spMap (Desc.cst p) = Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appTop ≫
      X.presheaf.germ ⊤ (genericPoint X) trivial) := rfl
  rw [h, Spec.map_comp, Spec.map_comp, ← Scheme.fromSpecStalk_toSpecΓ, Category.assoc, Category.assoc,
    ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  rfl

theorem spMap_comp' {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (a : R →+* R') (b : R' →+* R'') :
    spMap (b.comp a) = spMap b ≫ spMap a := by
  rw [← Spec.map_comp]; rfl

theorem cst_comp {X : Scheme.{0}} [IsIntegral X] {R R' : Type} [CommRing R] [CommRing R'] (q : X ⟶ Sp R') (ρ : R →+* R') :
    Desc.cst (q ≫ spMap ρ) = (Desc.cst q).comp ρ := by
  have e : spMap (Desc.cst (q ≫ spMap ρ)) = spMap ((Desc.cst q).comp ρ) := by
    rw [spMap_comp', spMap_cst, spMap_cst, Category.assoc]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)

theorem cst_inj {X : Scheme.{0}} [IsIntegral X] {R : Type} [CommRing R] [IsDomain R] (p : X ⟶ Sp R) [Flat p] :
    Function.Injective (Desc.cst p) := by
  have h1 : Flat (gp X) := GlobalTheory.LocalRingGeneralisation.flat_fromSpecStalk X _
  have h2 : Flat (spMap (Desc.cst p)) := by rw [spMap_cst]; infer_instance
  have h3 : (Desc.cst p).Flat := (HasRingHomProperty.Spec_iff (P := @Flat)).1 h2
  algebraize [Desc.cst p]
  exact FaithfulSMul.algebraMap_injective R X.functionField

theorem baseIndexConstant_injective (σ : Setup) : Function.Injective σ.c₀ := by
  haveI := σ.ab.smooth
  exact cst_inj _

theorem abelianSchemeDescent_chart_baseConstants_comp (σ : Setup) (x : Sp σ.R) : (σ.θ x).comp σ.c₀ = (Desc.cst (σ.C x).G.hom).comp (σ.ρ x) := by
  obtain ⟨l, hl, hl'⟩ := σ.hθ x
  have e : spMap ((σ.θ x).comp σ.c₀) = spMap ((Desc.cst (σ.C x).G.hom).comp (σ.ρ x)) := by
    rw [spMap_comp', spMap_comp', Setup.c₀, spMap_cst, spMap_cst, ← Category.assoc, ← hl', ← hl, Category.assoc,
      (σ.cart x).w]
    simp only [Category.assoc]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)

theorem linDisj_A (σ : Setup) : LinDisj σ.c₀ (Desc.cst σ.A.hom) (RingHom.id _) := by
  haveI := σ.ab.proper
  have hfl : (algebraMap σ.R (Localization.Away σ.f)).Flat := by
    rw [RingHom.flat_algebraMap_iff]; infer_instance
  refine (_root_.GlobalTheory.SecFlatBC.sections_linDisj_flatBaseChange σ.R _ _ hfl σ.A.left σ.A.left σ.A.left (σ.A.hom ≫ awayMap σ.f) σ.A.hom (𝟙 _) (𝟙 _)
    (RingHom.id _) inferInstance inferInstance ?_ ⟨gp _, by simp, ?_⟩ σ.D σ.D ?_).1
  · rw [Category.id_comp]
    exact IsPullback.of_horiz_isIso_mono ⟨by simp⟩
  · have : spMap (RingHom.id σ.A.left.functionField) = 𝟙 _ := Spec.map_id _
    rw [this]; simp
  · intro v g h
    exact h

theorem linDisj_C (σ : Setup) (x : Sp σ.R) : LinDisj σ.c₀ (Desc.cst (σ.C x).G.hom) (σ.θ x) := by
  haveI := σ.ab.proper
  exact (_root_.GlobalTheory.SecFlatBC.sections_linDisj_flatBaseChange σ.R _ _ (σ.flat x) σ.A.left (σ.C x).G.left (σ.V x).toScheme (σ.A.hom ≫ awayMap σ.f) (σ.C x).G.hom
    (σ.V x).ι (σ.φ x) (σ.θ x) inferInstance inferInstance (σ.cart x) (σ.hθ x) σ.D (σ.D₁ x) (σ.pull x)).1

theorem compact_A (σ : Setup) : CompactSpace σ.A.left := by
  haveI := σ.ab.proper
  exact QuasiCompact.compactSpace_of_compactSpace σ.A.hom

theorem qsep_A (σ : Setup) : QuasiSeparatedSpace σ.A.left := by
  haveI := σ.ab.proper
  exact quasiSeparatedSpace_of_quasiSeparated σ.A.hom

theorem compact_C (σ : Setup) (x : Sp σ.R) : CompactSpace (σ.C x).G.left := by
  haveI := (σ.C x).semi.quasiCompact
  exact QuasiCompact.compactSpace_of_compactSpace (σ.C x).G.hom

theorem qsep_C (σ : Setup) (x : Sp σ.R) : QuasiSeparatedSpace (σ.C x).G.left := by
  haveI := (σ.C x).semi.separated
  exact quasiSeparatedSpace_of_quasiSeparated (σ.C x).G.hom

theorem cartA_of_openIn (σ : Setup) (P : Scheme.{0}) [IsIntegral P] (p : P ⟶ Sp σ.R) (hp : IsSeparated p)
    (i : σ.A.left ⟶ P) (h : OpenIn i σ.A.hom p (awayMap σ.f)) : IsPullback i σ.A.hom p (awayMap σ.f) := by
  obtain ⟨w, ho⟩ := h
  haveI := σ.ab.proper
  set g := pullback.lift i σ.A.hom w with hg
  have hsnd : g ≫ pullback.snd p (awayMap σ.f) = σ.A.hom := pullback.lift_snd _ _ _
  haveI : IsProper (g ≫ pullback.snd p (awayMap σ.f)) := by rw [hsnd]; infer_instance
  haveI : IsProper g := IsProper.of_comp g (pullback.snd p (awayMap σ.f))
  haveI : Nonempty (pullback p (awayMap σ.f) : Scheme.{0}) := ⟨g (genericPoint σ.A.left)⟩
  haveI : IsIntegral (pullback p (awayMap σ.f)) := isIntegral_of_isOpenImmersion (pullback.fst p (awayMap σ.f))
  have hclo : IsClopen (Set.range g) := ⟨g.isClosedMap.isClosed_range, g.isOpenEmbedding.isOpen_range⟩
  have hs : Surjective g := ⟨Set.range_eq_univ.1 (hclo.eq_univ (Set.range_nonempty _))⟩
  haveI : IsIso g := (isIso_iff_isOpenImmersion_and_surjective g).2 ⟨ho, hs⟩
  exact IsPullback.of_iso_pullback ⟨w⟩ (asIso g) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

theorem onV_of (σ : Setup) (x : Sp σ.R) (P : Scheme.{0}) [IsIntegral P] (p : P ⟶ Sp σ.R) (hp : IsSeparated p)
    (ψ : P.functionField →+* σ.A.left.functionField) (i : σ.A.left ⟶ P) (hi : i ≫ p = σ.A.hom ≫ awayMap σ.f)
    (hfA : PFF (𝟙 _) i ψ) (e : (σ.C x).G.left ⟶ P) (he : e ≫ p = (σ.C x).G.hom ≫ spMap (σ.ρ x))
    (hf : PFF (𝟙 _) e ((σ.θ x).comp ψ)) : σ.φ x ≫ i = (σ.V x).ι ≫ e := by
  obtain ⟨l, hl, hl'⟩ := σ.hθ x
  obtain ⟨a, ha, ha'⟩ := hfA
  obtain ⟨b, hb, hb'⟩ := hf
  rw [Category.comp_id] at ha hb
  subst ha hb
  haveI : IsDominant (l ≫ (σ.V x).ι) := by
    rw [hl]
    refine ⟨?_⟩
    have hm : genericPoint (σ.C x).G.left ∈ Set.range (gp (σ.C x).G.left) :=
      ⟨closedPoint _, Scheme.fromSpecStalk_closedPoint⟩
    have hd : Dense {genericPoint (σ.C x).G.left} := by
      rw [dense_iff_closure_eq]; exact (genericPoint_spec _).def.trans rfl
    exact hd.mono (Set.singleton_subset_iff.2 hm)
  haveI : IsDominant l := IsDominant.of_comp_of_isOpenImmersion l (σ.V x).ι
  refine ext_of_isDominant_of_isSeparated p ?_ l ?_
  · rw [Category.assoc, Category.assoc, hi, he, (σ.cart x).w, Category.assoc]
  · rw [← Category.assoc, hl', ← Category.assoc, hl, hb', Category.assoc, ha', spMap_comp', Category.assoc]

end GlobalTheory.Desc.EmbeddingLemmas

namespace GlobalTheory.Desc


open GlobalTheory.Desc.EmbeddingLemmas in
theorem nonempty_emb : ∀ σ : Setup, σ.Common → Nonempty (Emb σ) := by
  intro σ _
  obtain ⟨hG, k₀, hk₀, b₀, hb₀, hb₀0⟩ := _root_.GlobalTheory.DescGraded.gradedFam_and_ne_zero σ
  obtain ⟨P, hPi, p, ψ, Dp, hM⟩ := _root_.GlobalTheory.Desc.exists_model σ.R _ σ.c₀ σ.N hG ⟨k₀, hk₀, b₀, hb₀, hb₀0⟩
  have hinj := baseIndexConstant_injective σ

  haveI : IsDomain (Localization.Away σ.f) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors σ.hf)
  have hcA : (RingHom.id _).comp σ.c₀ = (cst σ.A.hom).comp (algebraMap σ.R (Localization.Away σ.f)) := by
    rw [RingHom.id_comp]; exact cst_comp σ.A.hom _
  have hspA : ∀ k, Sec σ.D k = spanBy (cst σ.A.hom) ((RingHom.id _) '' σ.N k) := by
    intro k; rw [RingHom.coe_id, Set.image_id]; exact _root_.GlobalTheory.Desc.sec_eq_spanBy_N σ k
  have hsecA : ∀ k, ∀ a ∈ σ.N k, (RingHom.id _) a ∈ Sec σ.D k := fun k a ha => ha.1
  have hcovA := _root_.GlobalTheory.Desc.exists_locus_of_span _ _ σ.A.left σ.A.hom (RingHom.id _) σ.N σ.D σ.amp hspA
  obtain ⟨m, hm, hmf, hml⟩ := _root_.GlobalTheory.Desc.ToModel.exists_map_to_model σ.R _ σ.c₀ σ.N hG P p ψ Dp hM (Localization.Away σ.f)
    (algebraMap σ.R (Localization.Away σ.f)) σ.A.left σ.A.hom (RingHom.id _) σ.D hcA hsecA hcovA
  haveI := compact_A σ
  haveI := qsep_A σ
  have hflA : (algebraMap σ.R (Localization.Away σ.f)).Flat := by
    rw [RingHom.flat_algebraMap_iff]; infer_instance
  have hoA := _root_.GlobalTheory.Desc.openIn_model σ.R _ σ.c₀ σ.N hG P p ψ Dp hM (Localization.Away σ.f)
    (algebraMap σ.R (Localization.Away σ.f)) hflA hinj σ.A.left σ.A.hom (RingHom.id _) σ.D hcA (linDisj_A σ) σ.amp hspA
    m hm hmf hml
  have hcart := cartA_of_openIn σ P p hM.sep m hoA

  have hC : ∀ x, ∃ e : (σ.C x).G.left ⟶ P, e ≫ p = (σ.C x).G.hom ≫ spMap (σ.ρ x) ∧ PFF (𝟙 _) e ((σ.θ x).comp ψ) ∧
      OpenIn e (σ.C x).G.hom p (spMap (σ.ρ x)) := by
    intro x
    have hsp := _root_.GlobalTheory.Desc.ChartSpan.sec_eq_spanBy σ x
    have hsec : ∀ k, ∀ a ∈ σ.N k, σ.θ x a ∈ Sec (σ.D₁ x) k := fun k a ha => by
      rw [hsp k]; exact subset_spanBy _ _ (Set.mem_image_of_mem _ ha)
    have hcov := _root_.GlobalTheory.Desc.exists_locus_of_span _ _ (σ.C x).G.left (σ.C x).G.hom (σ.θ x) σ.N (σ.D₁ x) (σ.amp₁ x) hsp
    obtain ⟨e, he, hef, hel⟩ := _root_.GlobalTheory.Desc.ToModel.exists_map_to_model σ.R _ σ.c₀ σ.N hG P p ψ Dp hM (σ.C x).R (σ.ρ x) (σ.C x).G.left
      (σ.C x).G.hom (σ.θ x) (σ.D₁ x) (abelianSchemeDescent_chart_baseConstants_comp σ x) hsec hcov
    haveI := compact_C σ x
    haveI := qsep_C σ x
    exact ⟨e, he, hef, _root_.GlobalTheory.Desc.openIn_model σ.R _ σ.c₀ σ.N hG P p ψ Dp hM (σ.C x).R (σ.ρ x) (σ.flat x) hinj (σ.C x).G.left
      (σ.C x).G.hom (σ.θ x) (σ.D₁ x) (abelianSchemeDescent_chart_baseConstants_comp σ x) (linDisj_C σ x) (σ.amp₁ x) hsp e he hef hel⟩
  choose e he hef heo using hC
  have hm' : m ≫ p = σ.A.hom ≫ awayMap σ.f := hm
  have hmf' : PFF (𝟙 _) m ψ := by simpa using hmf
  exact ⟨{
    P := P
    p := p
    sep := hM.sep
    ψ := ψ
    ιA := m
    cartA := hcart
    ffA := hmf'
    emb := e
    openIn := heo
    ff := hef
    onV := fun x => onV_of σ x P p hM.sep ψ m hm' hmf' (e x) (he x) (hef x) }⟩

end GlobalTheory.Desc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveHodgeToPdivisibleOmegaSurjective
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem surjective_of_isCan_field :
    GlobalTheory.Published.AbelianHodgeDeRham →
    ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K], (p : K) = 0 →
    ∀ (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom →
    ∀ (G : PDivGroup p K) (t : PDivGroup.TorsionTower G A)
      (ψ : PrimitiveSubmodule A →ₗ[K] G.omega),
      (∀ c : PrimitiveSubmodule A, PtExt.IsCan t c.1 (G.rigOfOmega (ψ c))) →
      Function.Surjective ψ := by
  intro hH p _ K _ hp A _ g hA hg G t ψ hψ
  have hL : LieExact A :=
    _root_.GlobalTheory.LieHodge.lieExact_of_crystallineLift_hodgeDeRham
      GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations hH K A g hA hg
  have hx := _root_.GlobalTheory.PDivGroup.eq_zero_of_forall_apply_psi_eq_zero p K 1 (by rw [pow_one]; exact hp) A hA hL G t ψ hψ
  rw [← LinearMap.dualMap_injective_iff, injective_iff_map_eq_zero]
  intro x hx0
  exact hx x fun c ↦ by simpa using LinearMap.congr_fun hx0 c

end GlobalTheory.PtExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedLineBundleTrivialOfTorsionGeometricFibStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rigidified_lineBundle_trivial_of_torsion_geometricFibres : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB → (∃ t : (M.pull (1 : 𝟙_ (Over S) ⟶ A).left).Gen, t.IsGen) → ∀ k : ℕ, IsUnit ((k : Γ(S, ⊤))) → (∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow M k).Gen, t.IsGen) → (∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ S), ∃ t : (M.pull (pullback.fst A.hom y)).Gen, t.IsGen) → ∃ t : M.Gen, t.IsGen := by
  first | (exact @GlobalTheory.RigTorsTriv.triv_of_geometricFibres) | (exact GlobalTheory.RigTorsTriv.triv_of_geometricFibres) | (intros; apply GlobalTheory.RigTorsTriv.triv_of_geometricFibres <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionBasesTransferTotalSpaceIsoStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionBases_transfer_totalSpaceIso : ∀ {S S' : Scheme.{0}} (A : Over S) [GrpObj A] (Ag : Over S') [GrpObj Ag] (φ : Ag.left ⟶ A.left) (L : LB A.left), L.IsLB → ∀ (k : ℤ) (R : Type) [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S') (y : Spec (CommRingCat.of R) ⟶ S) (h : (Over.mk x ⊗ Ag).left ⟶ (Over.mk y ⊗ A).left) (hc : ∀ _ : Fin 1, (snd (Over.mk x) Ag).left ≫ φ = h ≫ (snd (Over.mk y) A).left), IsIso h → h ≫ (fst (Over.mk y) A).left = (fst (Over.mk x) Ag).left → ∀ (m : ℕ) (b : Fin m → LB.Sec (LPow A L k (Over.mk y))) (b' : Fin m → LB.Sec (LPow Ag (L.pull φ) k (Over.mk x))), (∀ i, b' i = GlobalTheory.SecTwist.pullSec (chartPullLinComb L φ (fun _ : Fin 1 => (snd (Over.mk x) Ag).left) (fun _ : Fin 1 => (snd (Over.mk y) A).left) (fun _ => k) h hc) (b i)) → LinearIndependent Γ((Over.mk y).left, ⊤) (fun i => (SecM.ofSec A (b i) : SecM A L k (Over.mk y))) → Submodule.span Γ((Over.mk y).left, ⊤) (Set.range fun i => (SecM.ofSec A (b i) : SecM A L k (Over.mk y))) = ⊤ → LinearIndependent Γ((Over.mk x).left, ⊤) (fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) k (Over.mk x))) ∧ Submodule.span Γ((Over.mk x).left, ⊤) (Set.range fun i => (SecM.ofSec Ag (b' i) : SecM Ag (L.pull φ) k (Over.mk x))) = ⊤ := by
  first | (exact @GlobalTheory.SecBasisTransfer.bases_transfer) | (exact GlobalTheory.SecBasisTransfer.bases_transfer) | (intros; apply GlobalTheory.SecBasisTransfer.bases_transfer  <;> assumption)
end

