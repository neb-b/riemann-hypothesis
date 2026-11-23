module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1579
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0879
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0374
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierInversionZeroCompactQuotientSummable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AeZeroOfSmall
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0353
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0487
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0365
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0779
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0490
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovedTensorFactorMemCoeffField
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.MovedField

open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.FunObj Formalism.L2.Host ValuativeRel

variable {D : D7}

theorem exists_zpow_unit (w : Pl D.host.E) (x : (Kw w)ˣ) :
    ∃ n : ℤ, Valued.v (((x * unifAt w ^ n : (Kw w)ˣ)) : Kw w) = 1 := by
  have h0 : Valued.v (x : Kw w) ≠ 0 := by simp
  have hu : Valued.v (unifAt w : Kw w) = WithZero.exp (-1 : ℤ) := unif_spec w
  have hx : Valued.v (x : Kw w) = WithZero.exp (WithZero.log (Valued.v (x : Kw w))) := (WithZero.exp_log h0).symm
  refine ⟨WithZero.log (Valued.v (x : Kw w)), ?_⟩
  rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hx, hu, ← WithZero.exp_zsmul, ← WithZero.exp_add]
  simp

theorem natCast_cpow_half (N : ℕ) (m : ℤ) :
    (N : ℂ) ^ ((((m : ℝ) / 2 : ℝ)) : ℂ) = ((Real.sqrt N : ℝ) : ℂ) ^ m := by
  rw [show (N : ℂ) = ((N : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_cpow (Nat.cast_nonneg _), ← Complex.ofReal_zpow]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1
  ring

theorem sqrt_absNorm_ne_zero (w : Pl D.host.E) : ((Real.sqrt (Ideal.absNorm w.asIdeal) : ℝ) : ℂ) ≠ 0 := by
  have h : (Ideal.absNorm w.asIdeal : ℝ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 w.ne_bot)
  exact_mod_cast (Real.sqrt_ne_zero'.2 (lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm h)))

theorem apow_half_mem {w : Pl D.host.E} {K : Subfield ℂ}
    (hs : ((Real.sqrt (Ideal.absNorm w.asIdeal) : ℝ) : ℂ) ∈ K) (x : (Kw w)ˣ) (z : ℤ) : apow x ((z : ℂ) / 2) ∈ K := by
  obtain ⟨n, hn⟩ := exists_zpow_unit w x
  have h1 : valuation (Kw w) (((x * unifAt w ^ n : (Kw w)ˣ)) : Kw w) = 1 := (Good.isEquiv_Kw w).eq_one_iff_eq_one.2 hn
  have hx : x = (x * unifAt w ^ n) * unifAt w ^ (-n) := by
    rw [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
  rw [hx, apow_mul, apow_of_valuation_eq_one h1, one_mul, apow_zpow, (isUnif_unifAt w).apow_eq,
    GlobalTheory.LFun.SatBoundGL.resCard_completion]
  have e1 : -(((-n : ℤ) : ℂ) * ((z : ℂ) / 2)) = ((((n * z : ℤ) : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [e1, natCast_cpow_half]
  exact zpow_mem hs _

theorem loc_mem_of_unrAt {w : Pl D.host.E} {K : Subfield ℂ} {χ : HChar D.host.E} (hu : χ.UnrAt w)
    (hv : χ.valTw (1 / 2) w ∈ K) (hs : ((Real.sqrt (Ideal.absNorm w.asIdeal) : ℝ) : ℂ) ∈ K) (x : (Kw w)ˣ) :
    ((χ.loc w x : ℂˣ) : ℂ) ∈ K := by
  obtain ⟨n, hn⟩ := exists_zpow_unit w x
  have hx : x = (x * unifAt w ^ n) * unifAt w ^ (-n) := by
    rw [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
  rw [hx, map_mul, hu _ hn, one_mul, map_zpow, Units.val_zpow_eq_zpow_val]
  refine zpow_mem ?_ _
  have e1 : -(((1 / 2 : ℝ)) : ℂ) = ((((-1 : ℤ) : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
  have hval : χ.valTw (1 / 2) w = ((χ.loc w (unifAt w) : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm w.asIdeal) : ℝ) : ℂ)⁻¹ := by
    rw [HChar.valTw, e1, natCast_cpow_half, zpow_neg_one]
    rfl
  have : ((χ.loc w (unifAt w) : ℂˣ) : ℂ) = χ.valTw (1 / 2) w * ((Real.sqrt (Ideal.absNorm w.asIdeal) : ℝ) : ℂ) := by
    rw [hval, inv_mul_cancel_right₀ (sqrt_absNorm_ne_zero w)]
  rw [this]
  exact mul_mem hv hs

theorem units_prod_mem {α : Type*} (K : Subfield ℂ) (f : α → ℂˣ) :
    ∀ l : List α, (∀ a ∈ l, ((f a : ℂˣ) : ℂ) ∈ K) → (((l.map f).prod : ℂˣ) : ℂ) ∈ K
  | [], _ => by simp [one_mem]
  | a :: l, h => by
    rw [List.map_cons, List.prod_cons, Units.val_mul]
    exact mul_mem (h a List.mem_cons_self) (units_prod_mem K f l fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem list_prod_mem' {α : Type*} (K : Subfield ℂ) (f : α → ℂ) :
    ∀ l : List α, (∀ a ∈ l, f a ∈ K) → (l.map f).prod ∈ K
  | [], _ => by simp [one_mem]
  | a :: l, h => by
    rw [List.map_cons, List.prod_cons]
    exact mul_mem (h a List.mem_cons_self) (list_prod_mem' K f l fun b hb => h b (List.mem_cons_of_mem _ hb))

end GlobalTheory.MovedField


open GlobalTheory.MovedField GlobalTheory.SplitFlip GlobalTheory.SplitWeil Formalism.L2.Host in
theorem GlobalTheory.MovedField.moved_mem : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : GlobalTheory.RowTest.Choice R) (large₂ : SizeData₂ D) (F : Face D A) (CF b : ℝ), HidaSetting large₂ R F → ch.Is → ch.AtScale CF b → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ch.S.SumOK t Φ → ∀ β ∈ ch.S.supp t Φ, ∀ (w : locPl ch.G t) (S : (locGrid ch.G t w).Args → ℂ), (∀ z, S z ∈ Set.range D.what₂.embLL) → ∀ z, moved (locGrid ch.G t w) (keepAt ch.G w) ((repsAt ch.G t w).elt (β w)) S z ∈ Set.range D.what₂.embLL := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F CF b _ _ _ hF t Φ _ β _ w S hS z
  set K : Subfield ℂ := D.what₂.embLL.fieldRange with hKdef
  have hK : ∀ y : ℂ, y ∈ Set.range D.what₂.embLL ↔ y ∈ K := fun y => by
    rw [Set.mem_range, hKdef, RingHom.mem_fieldRange]
  have hsq : ((Real.sqrt (Ideal.absNorm (w : Pl D.host.E).asIdeal) : ℝ) : ℂ) ∈ K :=
    (hK _).1 (hF.sqrt w.1 (.inr ⟨t, w.2⟩))

  have hmu : ∀ j (x : (Kw w.1)ˣ), (((locGrid ch.G t w).mu j x : ℂˣ) : ℂ) ∈ K := fun j x => by
    change ((GlobalTheory.FunObj.muBase R.toLevCh j).loc w.1 x : ℂ) *
      ((R.xiH t).loc w.1 x : ℂ) ∈ K
    refine mul_mem ?_ ((hK _).1 (hF.chars.xi t _ x))
    rcases j with _ | j
    · exact one_mem K
    · rw [GlobalTheory.FunObj.muBase]
      split_ifs with hj
      · exact (hK _).1 (hF.chars.mu0 ⟨j, hj⟩ _ x)
      · exact one_mem K
  have hchi : ∀ i, 1 ≤ i → i ≤ D.R.m → ∀ x : (Kw w.1)ˣ, (((locGrid ch.G t w).chi i x : ℂˣ) : ℂ) ∈ K :=
    fun i h1 h2 x => (hK _).1 (hF.chars.chi i h1 h2 _ x)
  have heta : ∀ x : (Kw w.1)ˣ, (((locGrid ch.G t w).eta x : ℂˣ) : ℂ) ∈ K := fun x => by
    have hu := R.toLevCh.C.isEta.unr w.1
    obtain ⟨y, hy⟩ := hF.chars.eta w.1 hu
    exact loc_mem_of_unrAt hu (hy ▸ (hK _).1 ⟨y, rfl⟩) hsq x

  have hkap : ∀ e ∈ oppositePath D.R.m, ∀ X (x : (Kw w.1)ˣ), (((locGrid ch.G t w).kappa e X x : ℂˣ) : ℂ) ∈ K := by
    intro e he X x
    rw [Grid.kappa, MonoidHom.div_apply, MonoidHom.pow_apply, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val]
    refine div_mem ?_ (pow_mem (heta x) _)
    rcases GlobalTheory.FunObj.mem_oppositePath.1 he with ⟨i, hi, rfl⟩ | ⟨j, -, rfl⟩
    · exact hchi _ (by show 1 ≤ D.R.m - i; omega) (by show D.R.m - i ≤ D.R.m; omega) x
    · exact hmu _ x
  have hap : ∀ (x : (Kw w.1)ˣ) (n : ℕ), apow x ((n : ℂ) / 2) ∈ K ∧ apow x (-(n : ℂ) / 2) ∈ K := fun x n =>
    ⟨by simpa using apow_half_mem hsq x n, by simpa using apow_half_mem hsq x (-n)⟩
  have hedge : ∀ g, ∀ e ∈ oppositePath D.R.m, (locGrid ch.G t w).edgeFactor .one g e ∈ K := by
    intro g e he
    rw [Grid.edgeFactor, Units.val_inv_eq_inv_val]
    exact mul_mem (mul_mem (mul_mem (hkap e he _ _) (inv_mem (hkap e he _ _))) (hap _ _).1) (hap _ _).2
  have hchar : ∀ g, ((((charFactor (locGrid ch.G t w) g)⁻¹ : ℂˣ)) : ℂ) ∈ K := by
    intro g
    rw [Units.val_inv_eq_inv_val]
    refine inv_mem (units_prod_mem K _ _ fun e he => ?_)
    rw [Units.val_mul, Units.val_inv_eq_inv_val]
    exact mul_mem (hkap e he _ _) (inv_mem (hkap e he _ _))
  rw [hK]
  simp only [moved, Grid.pathAct]
  refine mul_mem ?_ (mul_mem (list_prod_mem' K _ _ (hedge _)) ((hK _).1 (hS _)))
  split
  · exact one_mem K
  · exact hchar _
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MoyalOrthogonalityHeisenbergThetaFunctions
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.MoyalTheta

theorem orthogonality : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (v : VolM D T.rank S.rank) f f₀, IsThetaFunO ψ S T f → IsThetaFunO ψ S T f₀ → Integrable (fun w => thPair v.μ v.𝓕 f (heisO ψ S T w f₀)) v.μ ∧ ∀ x, ∫ w, thPair v.μ v.𝓕 f (heisO ψ S T w f₀) * heisO ψ S T w f₀ x ∂v.μ = thPair v.μ v.𝓕 f₀ f₀ * f x := by
  intro D ψ hψ S T v f f₀ hf hf₀
  have hv : IsCovolOne (ratL T S) v.μ v.𝓕 := v.covol
  obtain ⟨hμ, h𝓕, h1⟩ := hv
  obtain ⟨i1, i2, i3, i4, i5, -, -, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : IsTopologicalAddGroup (WO S T) := i1
  haveI : LocallyCompactSpace (WO S T) := i2
  haveI : SecondCountableTopology (WO S T) := i3
  haveI : T2Space (WO S T) := i4
  haveI : DiscreteTopology (ratL T S) := i5
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : Countable (ratL T S) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI := hμ
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨-, -, -, -, hcont, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D S T
  have hcc := _root_.GlobalTheory.MatCoefCont.continuous_thPair_heisO D ψ hψ S T v.μ v.𝓕 v.covol f f₀ hf hf₀
  obtain ⟨C, hC⟩ := _root_.GlobalTheory.LatticeTranslateSum.sum_translates_bounded D ψ hψ θ hθ S T _ (_root_.GlobalTheory.MatCoefLevel.matCoef_level D ψ hψ S T v.μ v.𝓕 v.covol f f₀ hf hf₀)
    (_root_.GlobalTheory.RealDecay.realDecay D ψ hψ θ hθ S T v.μ v.𝓕 v.covol f f₀ hf hf₀)
  have hint : Integrable (fun w => thPair v.μ v.𝓕 f (heisO ψ S T w f₀)) v.μ :=
    GlobalTheory.T.integrable_of_tsum_norm_translate_le (WO S T) (ratL T S) v.μ inferInstance v.𝓕 h𝓕 (by rw [h1]; exact ENNReal.one_lt_top) _ hcc C hC
  refine ⟨hint, fun x => ?_⟩
  have hψn : ∀ a, ‖ψ a‖ = 1 := hψ.1.2.1
  have hgc : Continuous fun w => heisO ψ S T w f₀ x := by
    unfold heisO
    exact (hψ.1.1.comp (hcont.comp (continuous_const.prodMk continuous_id))).mul
      (hf₀.cont.comp (continuous_const.add continuous_id))
  obtain ⟨-, ⟨B, hB⟩, -⟩ := GlobalTheory.ThetaSquare.squareIntegrable hψ f₀ hf₀
  have hgb : ∃ B : ℝ, ∀ w, ‖heisO ψ S T w f₀ x‖ ≤ B :=
    ⟨B, fun w => by rw [GlobalTheory.ThetaSquare.norm_heisO hψ]; exact hB _⟩
  rw [_root_.GlobalTheory.unfold_integral_fundamentalDomain (WO S T) (ratL T S) v.μ inferInstance v.𝓕 h𝓕 _ _ hint hgc hgb]
  simp_rw [GlobalTheory.T.fourierInversion_thetaMatrixCoeff_rationalTranslates D ψ hψ S T v.μ v.𝓕 v.covol f f₀ hf hf₀ _ x (hC _).1]
  have e : ∀ w, f x * star (heisO ψ S T w f₀ x) * heisO ψ S T w f₀ x = f x * (f₀ (w + x) * star (f₀ (w + x))) := by
    intro w
    have hu : star (ψ (symplOH S T x w)) * ψ (symplOH S T x w) = 1 := by
      rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hψn]; norm_num
    unfold heisO
    rw [star_mul, add_comm x w]
    linear_combination (f x * f₀ (w + x) * star (f₀ (w + x))) * hu
  simp_rw [e]
  rw [integral_const_mul]
  have hper : ∀ γ ∈ ratL T S, ∀ w : WO S T, f₀ (γ + w) * star (f₀ (γ + w)) = f₀ w * star (f₀ w) := by
    rintro _ ⟨γ, rfl⟩ w
    have hq := hf₀.quasi γ w
    have hu : ψ (-(symplOH S T (ratW T S γ) w)) * star (ψ (-(symplOH S T (ratW T S γ) w))) = 1 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hψn]; norm_num
    change f₀ (ratW T S γ + w) * star (f₀ (ratW T S γ + w)) = _
    rw [hq, star_mul]
    linear_combination (f₀ w * star (f₀ w)) * hu
  rw [GlobalTheory.CompactQuotientFourier.setIntegral_translate (ratL T S) v.μ v.𝓕 h𝓕 (fun w => f₀ w * star (f₀ w)) hper x]
  unfold thPair
  ring

end GlobalTheory.MoyalTheta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NsmulMemLiftPointsOfCompletedHomLatticeHalf
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.LiftMul

variable {D : D7}

theorem exists_den_AA (D : D7) :
    ∃ d : ℕ, 0 < d ∧ ∀ a ∈ D.host.AA, ∃ o : 𝓞 D.host.E, (d : D.host.E) * a = (o : D.host.E) := by
  obtain ⟨b, hb, hbI⟩ := D.host.AA.isFractional
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  refine ⟨Ideal.absNorm (Ideal.span {b}), Nat.pos_of_ne_zero ?_, fun a ha => ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hb0
  · obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {b}))
    obtain ⟨o, ho⟩ := hbI a ha
    refine ⟨c * o, ?_⟩
    show _ = algebraMap (𝓞 D.host.E) D.host.E (c * o)
    rw [map_mul, ho, Algebra.smul_def, ← mul_assoc, ← map_mul, hc, map_natCast]

def fA (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) :
    WO S T →+ Matrix (Fin S.rank) (Fin T.rank) (EAf D) :=
  AddMonoidHom.mk' (frMapAdj S T βS βT) (GlobalTheory.PlaceVec.frMapAdj_add S T βS βT)

theorem gen_int (S T : HSp D) (ΛT : Lt D.host.E T.rank) (hsd : IsSelfDualC T ΛT)
    (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (hβS : Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank)) (hβT : Formalism.L2.DIV.IsFrame βT ΛT)
    {d : ℕ} {α : Af D.host.F} (hα : ((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    {a : D.host.E} (ha : ∃ o : 𝓞 D.host.E, (d : D.host.E) * a = (o : D.host.E))
    {s : Fin S.rank → D.host.E} (hs : s ∈ stdL D.host.E S.rank) {t : Fin T.rank → D.host.E} (ht : t ∈ ΛT) :
    IsIntM (frMapAdj S T βS βT (incA D (d : D.host.E) • GlobalTheory.LatVac.finTens α (GlobalTheory.LatVac.genMap S T a s t))) := by
  obtain ⟨o, ho⟩ := ha
  have hc : toEAf D (incA D (d : D.host.E) * incA D a) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [← map_mul, ho]
    exact GlobalTheory.IdemIntegral.eToEAf_int D o
  rw [GlobalTheory.PlaceVec.frMapAdj_eq, GlobalTheory.ConjHalfInt.map_gen, GlobalTheory.ConjHalfInt.adj_shape, Matrix.mul_smul, Matrix.smul_mul]
  refine GlobalTheory.ConjHalfInt.isIntM_smul (GlobalTheory.PlaceVec.cF_mem_int (mul_mem hc hα)) ?_
  have hA : (S.gram⁻¹).map (eToEAf D) *
      ((Matrix.of fun (_ : Fin 1) j => eToEAf D (∑ k, star (s k) * S.gram k j)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ =
      Matrix.of fun m (_ : Fin 1) => eToEAf D (s m) := by
    ext m z
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply,
      GlobalTheory.ConjHalfInt.cF_eToEAf, ← map_mul, ← map_sum]
    rw [GlobalTheory.ConjHalfInt.gram_inv_star]
  have hB : ((Matrix.of fun i (_ : Fin 1) => eToEAf D (t i)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ * T.gram.map (eToEAf D) =
      Matrix.of fun (_ : Fin 1) m => eToEAf D (∑ l, star (t l) * T.gram l m) := by
    ext z m
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.of_apply,
      GlobalTheory.ConjHalfInt.cF_eToEAf, ← map_mul, ← map_sum]
  have e : (βS⁻¹).val * (S.gram⁻¹).map (eToEAf D) *
      (((Matrix.of fun (_ : Fin 1) j => eToEAf D (∑ k, star (s k) * S.gram k j)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ *
        ((Matrix.of fun i (_ : Fin 1) => eToEAf D (t i)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ) *
      (T.gram.map (eToEAf D) * βT.val) =
      ((βS⁻¹).val * ((S.gram⁻¹).map (eToEAf D) *
        ((Matrix.of fun (_ : Fin 1) j => eToEAf D (∑ k, star (s k) * S.gram k j)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ)) *
      ((((Matrix.of fun i (_ : Fin 1) => eToEAf D (t i)).map (GlobalTheory.AdelicLatMove.cF D))ᵀ * T.gram.map (eToEAf D)) *
        βT.val) := by
    simp only [Matrix.mul_assoc]
  rw [e, hA, hB]
  exact GlobalTheory.ConjHalfInt.isIntM_mul (GlobalTheory.ConjHalfInt.frame_col_int hβS hs)
    (GlobalTheory.ConjHalfInt.pair_row_int hsd hβT ht)

theorem lat_int (S T : HSp D) (ΛT : Lt D.host.E T.rank) (hsd : IsSelfDualC T ΛT)
    (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (hβS : Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank)) (hβT : Formalism.L2.DIV.IsFrame βT ΛT)
    {d : ℕ} (hd : ∀ a ∈ D.host.AA, ∃ o : 𝓞 D.host.E, (d : D.host.E) * a = (o : D.host.E))
    {x : WO S T}
    (hx : x ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
      fun _ => True) :
    IsIntM (frMapAdj S T βS βT (incA D (d : D.host.E) • x)) := by
  refine GlobalTheory.LatVac.latO_induction (p := fun u => IsIntM (frMapAdj S T βS βT (incA D (d : D.host.E) • u)))
    ?_ ?_ ?_ ?_ hx
  · intro α hα M hM
    have hα' : ((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
      Subring.subset_closure (Or.inr ⟨⟨α, hα⟩, rfl⟩)
    induction hM using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, ha, s, hs, t, ht, rfl⟩ := hw
      exact gen_int S T ΛT hsd βS βT hβS hβT hα' (hd a ha) hs ht
    | zero =>
      rw [GlobalTheory.LatVac.finTens_zero, smul_zero, GlobalTheory.ConjHalfInt.frMapAdj_zero]
      exact fun _ _ => zero_mem _
    | add M N _ _ hM hN =>
      rw [GlobalTheory.LatVac.finTens_add, smul_add, GlobalTheory.PlaceVec.frMapAdj_add]
      exact fun i j => add_mem (hM i j) (hN i j)
    | neg M _ hM =>
      rw [GlobalTheory.LatVac.finTens_neg, smul_neg, GlobalTheory.ConjHalfInt.frMapAdj_neg]
      exact fun i j => neg_mem (hM i j)
  · rw [smul_zero, GlobalTheory.ConjHalfInt.frMapAdj_zero]
    exact fun _ _ => zero_mem _
  · intro u v hu hv
    rw [smul_add, GlobalTheory.PlaceVec.frMapAdj_add]
    exact fun i j => add_mem (hu i j) (hv i j)
  · intro u hu
    rw [smul_neg, GlobalTheory.ConjHalfInt.frMapAdj_neg]
    exact fun i j => neg_mem (hu i j)

theorem red_nsmul {b a : ℕ} (PP : Formalism.L2.DIV.Pl D.host.E) {N : Matrix (Fin b) (Fin a) (EAf D)} (hN : IsIntM N)
    {m : ℕ} (hm : (m : 𝓞 D.host.E) ∈ PP.asIdeal) : IsIntM (m • N) ∧ redM PP (m • N) = 0 := by
  have hI : IsIntM (m • N) := fun i j => by
    rw [Matrix.smul_apply, nsmul_eq_mul]; exact mul_mem (natCast_mem _ m) (hN i j)
  refine ⟨hI, ?_⟩
  ext i j
  simp only [redM, dif_pos (hI i j), Matrix.zero_apply]
  have e : (⟨(m • N) i j, hI i j⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) =
      (m : Formalism.L2.Herm.intAf D.host.F D.host.E) * ⟨N i j, hN i j⟩ := by
    apply Subtype.ext; simp [Matrix.smul_apply, nsmul_eq_mul]
  rw [e, map_mul, map_natCast]
  have h0 : (m : Formalism.L2.DIV.kP PP) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal) m]; exact Ideal.Quotient.eq_zero_iff_mem.2 hm
  rw [h0, zero_mul]

theorem nsmul_mem_liftL : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∃ m : ℕ, 0 < m ∧ ∀ x ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True, IsHalf (cA D e) x → m • x ∈ GlobalTheory.LiftLevel.liftL S T βS βT Pg Q e := by
  intro D S T C hn ΛT hsd hAA βS βT hβS hβT Pg Q ξ hne h2 e hidem
  obtain ⟨d, hd0, hd⟩ := exists_den_AA D
  set m2 : ℕ := ∏ PP ∈ Pg ∪ Q, Ideal.absNorm PP.asIdeal with hm2
  have hm2pos : 0 < m2 := Finset.prod_pos fun PP _ =>
    Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact PP.ne_bot)
  have hm2mem : ∀ PP ∈ Pg ∪ Q, (m2 : 𝓞 D.host.E) ∈ PP.asIdeal := fun PP hPP => by
    rw [hm2, Nat.cast_prod]
    exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ hPP) (Ideal.absNorm_mem _)
  refine ⟨d * m2, Nat.mul_pos hd0 hm2pos, fun x hx hh => ?_⟩
  have hint := lat_int S T ΛT hsd βS βT hβS hβT hd hx
  have heq : frMapAdj S T βS βT ((d * m2) • x) = m2 • frMapAdj S T βS βT (incA D (d : D.host.E) • x) := by
    have hdx : d • x = incA D (d : D.host.E) • x := by rw [map_natCast, Nat.cast_smul_eq_nsmul]
    rw [mul_comm d m2, ← smul_smul, hdx]
    exact (fA S T βS βT).map_nsmul _ _
  show IsHalf (cA D e) ((d * m2) • x) ∧ IsIntM (frMapAdj S T βS βT ((d * m2) • x)) ∧
    ∀ PP ∈ Pg ∪ Q, redM PP (frMapAdj S T βS βT ((d * m2) • x)) = 0
  refine ⟨fun i j => ?_, ?_, fun PP hPP => ?_⟩
  · rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hh i j]
  · obtain ⟨PP, hPP⟩ := hne
    rw [heq]; exact (red_nsmul PP hint (hm2mem PP (Finset.mem_union_left _ hPP))).1
  · rw [heq]; exact (red_nsmul PP hint (hm2mem PP hPP)).2

end GlobalTheory.LiftMul

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OrthogonalProjectionPreservesDepthLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.ProjCore

variable {D : D7}

theorem rat_entry' {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E) (i : Fin m) (j : Fin n) :
    (rat A : Mx D m n) i j = (1 : AF D.host.F) ⊗ₜ[D.host.F] A i j := rfl

theorem rat_mul_mem_hatMx {m n : ℕ} {ΛS : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} (M : Matrix (Fin m) (Fin m) D.host.E)
    (hM : ∀ y ∈ ΛT, M *ᵥ y ∈ ΛT) (I : Ideal (𝓞 D.host.E)) {z : Mx D m n} (hz : z ∈ hatMx (I • homLat ΛS ΛT)) :
    (rat M : Mx D m m) ⬝ z ∈ hatMx (I • homLat ΛS ΛT) := by
  have key : ∀ X ∈ I • homLat ΛS ΛT, M * X ∈ I • homLat ΛS ΛT := by
    intro X hX
    refine Submodule.smul_induction_on hX (fun r hr Y hY => ?_) (fun a b ha hb => ?_)
    · rw [Matrix.mul_smul]
      refine Submodule.smul_mem_smul hr ?_
      intro y hy
      rw [← Matrix.mulVec_mulVec]
      exact hM _ (hY _ hy)
    · rw [Matrix.mul_add]; exact add_mem ha hb
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, X, hX, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨α, hα, M * X, key X hX, ?_⟩
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, TensorProduct.tmul_sum, rat_entry',
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [Matrix.mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mul_neg]; exact neg_mem hx

theorem proj_mem_latCore : OnStd fun {D} _ _ _ {G} _ F => ∀ u ∈ latCore G 0, F.oz.jA ⬝ (F.oz.pA ⬝ u) ∈ latCore G 0 := by
  intro D hq T L μ0 hL sc G W M hM F hF u hu
  have hz := hF.zA
  have hqa : F.oz.qA * G.sp.dec0.a = 0 := by
    have hp := G.sp.dec0.perp
    rw [show Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (frameMat (G.sp.P 0).sp (Yc D 0) G.sp.dec0.ι) =
        (frameMat (G.sp.P 0).sp (Yc D 0) G.sp.dec0.ι)ᴴ from Matrix.ext fun _ _ => rfl, ← hz] at hp
    rw [OrthDec.qA, Matrix.mul_assoc, hp, Matrix.mul_zero]
  have hmap : ∀ x ∈ G.Λ (.core 0), (F.oz.iA * F.oz.qA) *ᵥ x ∈ G.Λ (.core 0) := by
    intro x hx
    have hx' : x ∈ G.sp.dec0.lat (L.ΛY 0) (fun _ => 1) := by rw [← G.sp.lat0]; exact hx
    obtain ⟨y, hy, c, hc, rfl⟩ := hx'
    show _ ∈ (G.sp.P 0).lat
    rw [G.sp.lat0]
    refine ⟨y, hy, 0, fun _ => Submodule.zero_mem _, ?_⟩
    rw [Matrix.mulVec_add, Matrix.mulVec_zero, add_zero, ← hz, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_assoc, F.oz.qA_iA, Matrix.mul_one, Matrix.mul_assoc, hqa, Matrix.mul_zero, Matrix.zero_mulVec, add_zero]
  have he : F.oz.jA ⬝ (F.oz.pA ⬝ u) = (rat (F.oz.iA * F.oz.qA) : Mx D _ _) ⬝ u := by
    rw [rat_mul, ← Matrix.mul_assoc]; rfl
  rw [he]
  refine ⟨?_, fun e he' => ?_⟩
  · exact GlobalTheory.OverTgt.mul_mem_latO (LT := G.Λ (.core 0)) (LT' := G.Λ (.core 0)) _
      (fun y hy => GlobalTheory.OrthSumLat.rat_mulVec_mem_latV _ hmap hy) hu.1
  · rw [← Matrix.mul_smul]
    exact rat_mul_mem_hatMx _ hmap _ (hu.2 e he')

end GlobalTheory.ProjCore
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryLatticeCongruenceMemConjugateIdealInfStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryLatticeCongruence_mem_conjugateIdeal_inf : ∀ {D : D7} (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSelfDualC V Λ → ∀ (𝔪 : Ideal (𝓞 D.host.E)) (g : GL (Fin V.rank) (Lev.EAf D)), g ∈ congLev D.sp.cm V.gram Λ 𝔪 → g ∈ congLev D.sp.cm V.gram Λ (𝔪 ⊓ D.host.conj • 𝔪) := by
  first | exact @GlobalTheory.CongSelfDual.congLev_conj | exact GlobalTheory.CongSelfDual.congLev_conj | (intros; apply GlobalTheory.CongSelfDual.congLev_conj <;> assumption)
end

