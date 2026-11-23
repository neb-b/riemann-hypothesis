module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0019
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0021
public import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsPosConstLagrangeCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
public import Formalism.SharpRestriction.LevelLetterCocycles.MixedPositionHypothesis
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInvariantPreimageAverage
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0006
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.LevelLetterCocycles.PlaceLabelTeichmuller

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.BaseChangeOfCoefficientJump
section
noncomputable section

open Classical TensorProduct

namespace Formalism.MainNotions.UnusedSlot80.BCF

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.UnusedSlot80.BCW

variable {l : ℕ} [Fact l.Prime]


set_option maxHeartbeats 1600000 in
theorem bcAt_fin (hJ : Formalism.MainNotions.N.GlobalTheory.CoefJumpGen) (Th : LocTheory) (K LL LL' : FinExt l)
    (hLL : LL.1 ≤ LL'.1) :
    Formalism.MainNotions.WachCoordinates.BCAt ((Th l).PD K) (LL := ↥LL.1) (O := ↥(OL LL)) (O' := ↥(OL LL'))
      (IntermediateField.inclusion hLL) := by
  letI iA : Algebra ↥LL.1 ↥LL'.1 := (IntermediateField.inclusion hLL).toRingHom.toAlgebra
  haveI tA : IsScalarTower ℚ_[l] ↥LL.1 ↥LL'.1 :=
    IsScalarTower.of_algebraMap_eq fun x => ((IntermediateField.inclusion hLL).commutes x).symm
  letI iO : Algebra ↥(OL LL) ↥(OL LL') := (jO hLL).toAlgebra
  letI sO : SMul ↥(OL LL) ↥(OL LL') := iO.toSMul
  haveI t1 : IsScalarTower ↥(OL LL) ↥(OL LL') ↥LL'.1 := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI := isFrac_OL LL
  have hc : Continuous (algebraMap ↥LL.1 ↥LL'.1) := by
    refine continuous_induced_rng.2 ?_
    exact continuous_subtype_val
  have hO' : Function.Injective (algebraMap ↥(OL LL') ↥LL'.1) := Subtype.val_injective
  have hjO : Function.Injective (algebraMap ↥(OL LL) ↥(OL LL')) := by
    intro a b h
    have h1 := congrArg (fun x : ↥(OL LL') => ((x : ↥LL'.1) : Om l)) h
    exact Subtype.ext (Subtype.ext h1)

  haveI tZ : IsScalarTower ℤ_[l] ↥(OL LL) ↥(OL LL') := IsScalarTower.of_algebraMap_eq fun z => by
    apply Subtype.ext; apply Subtype.ext
    show ((algebraMap ℤ_[l] ↥(OL LL') z : ↥LL'.1) : Om l) = ((algebraMap ℤ_[l] ↥(OL LL) z : ↥LL.1) : Om l)
    simp only [SubalgebraClass.coe_algebraMap]
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL'.1, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1]
    rfl
  haveI : Module.Finite ↥(OL LL) ↥(OL LL') := Module.Finite.of_restrictScalars_finite ℤ_[l] _ _
  haveI : FaithfulSMul ↥(OL LL) ↥(OL LL') := (faithfulSMul_iff_algebraMap_injective _ _).2 hjO
  haveI : Module.IsTorsionFree ↥(OL LL) ↥(OL LL') := ⟨fun r hr a b hab => by
    have hr0 : algebraMap ↥(OL LL) ↥(OL LL') r ≠ 0 := fun h => hr.ne_zero (hjO (h.trans (map_zero _).symm))
    simp only [Algebra.smul_def] at hab
    exact mul_left_cancel₀ hr0 hab⟩
  haveI : Module.Free ↥(OL LL) ↥(OL LL') := Module.free_of_finite_type_torsion_free'
  let bO := Module.Free.chooseBasis ↥(OL LL) ↥(OL LL')

  haveI : FiniteDimensional ℚ_[l] ↥LL'.1 := LL'.2
  haveI : IsIntegralClosure ↥(OL LL') ℤ_[l] ↥LL'.1 := integralClosure.isIntegralClosure ℤ_[l] ↥LL'.1
  haveI : IsLocalization (Algebra.algebraMapSubmonoid ↥(OL LL') (nonZeroDivisors ℤ_[l])) ↥LL'.1 :=
    IsIntegralClosure.isLocalization ℤ_[l] ℚ_[l] ↥LL'.1 ↥(OL LL')
  let b : Module.Free.ChooseBasisIndex ↥(OL LL) ↥(OL LL') → ↥LL'.1 :=
    fun i => algebraMap ↥(OL LL') ↥LL'.1 (bO i)
  have hliO : LinearIndependent ↥(OL LL) b :=
    bO.linearIndependent.map' (IsScalarTower.toAlgHom ↥(OL LL) ↥(OL LL') ↥LL'.1).toLinearMap
      (LinearMap.ker_eq_bot.2 hO')
  have hli : LinearIndependent ↥LL.1 b := linInd_frac (O := ↥(OL LL)) b hliO
  have hy : ∀ a : ↥(OL LL'), algebraMap ↥(OL LL') ↥LL'.1 a ∈ Submodule.span ↥LL.1 (Set.range b) := by
    intro a
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← bO.sum_repr a, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    have e : algebraMap ↥(OL LL') ↥LL'.1 (bO.repr a i • bO i) =
        (algebraMap ↥(OL LL) ↥LL.1 (bO.repr a i)) • b i := by
      rw [Algebra.smul_def, map_mul, Algebra.smul_def, ← IsScalarTower.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hsp : ⊤ ≤ Submodule.span ↥LL.1 (Set.range b) := by
    intro x _
    obtain ⟨⟨a, s⟩, hx⟩ := IsLocalization.surj
      (Algebra.algebraMapSubmonoid ↥(OL LL') (nonZeroDivisors ℤ_[l])) x
    obtain ⟨z, hz, hzs⟩ := s.2
    have e1 : algebraMap ↥(OL LL') ↥LL'.1 (s : ↥(OL LL')) = algebraMap ℚ_[l] ↥LL'.1 (z : ℚ_[l]) := by
      rw [← hzs, ← IsScalarTower.algebraMap_apply ℤ_[l] ↥(OL LL') ↥LL'.1,
        IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL'.1]
      rfl
    have hz0 : (z : ℚ_[l]) ≠ 0 := by
      intro h0
      exact nonZeroDivisors.coe_ne_zero ⟨z, hz⟩ (PadicInt.coe_eq_zero.1 h0)
    have hq : algebraMap ℚ_[l] ↥LL'.1 (z : ℚ_[l]) ≠ 0 := (map_ne_zero _).2 hz0
    have hxe : x = algebraMap ↥LL.1 ↥LL'.1 (algebraMap ℚ_[l] ↥LL.1 (z : ℚ_[l])⁻¹) *
        algebraMap ↥(OL LL') ↥LL'.1 a := by
      rw [← IsScalarTower.algebraMap_apply, map_inv₀, ← hx, e1]
      field_simp
    rw [hxe, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (hy a)
  let bL := Module.Basis.mk hli hsp
  have hb : ∀ i, bL i = algebraMap ↥(OL LL') ↥LL'.1 (bO i) := fun i => Module.Basis.mk_apply hli hsp i
  have hlin : ∀ φ : ↥LL'.1 →ₗ[↥LL.1] ↥LL.1, Continuous φ := fun φ =>
    LinearMap.continuous_of_finiteDimensional (φ.restrictScalars ℚ_[l])
  have hk : lenOl ((Th l).PD K) (O := ↥(OL LL)) ≠ ⊤ := by
    have hp : (((((Th l).PD K).p : ℕ)) : ↥(OL LL)) ≠ 0 := by
      rw [(Th l).PD_p K]
      intro h0
      have h1 := congrArg (algebraMap ↥(OL LL) ↥LL.1) h0
      rw [map_natCast, map_zero] at h1
      exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h1
    obtain ⟨k, hk⟩ := Formalism.MainNotions.RamifiedCoefficientChains.len_quot_nat _ hp
    unfold lenOl
    rw [hk]
    exact ENat.natCast_ne_top k
  have e : IsScalarTower.toAlgHom ℚ_[l] ↥LL.1 ↥LL'.1 = IntermediateField.inclusion hLL :=
    AlgHom.ext fun _ => rfl
  rw [← e]
  exact bcAt_desc ((Th l).PD K) hc hO' hJ bO bL hb hlin hk

theorem base_change_of_coefficient_jump (hJ : Formalism.MainNotions.N.GlobalTheory.CoefJumpGen) (Th : LocTheory) : Formalism.MainNotions.WachCoordinates.admBC Th := by
  intro l _ K LL LL' hLL
  exact bcAt_fin hJ Th K LL LL' hLL

theorem base_change_statement_of_jump (hJ : Formalism.MainNotions.N.GlobalTheory.CoefJumpGen) (D : D7) : Formalism.MainNotions.UnusedSlot80.H1fBaseChangeTheorem D :=
  base_change_of_coefficient_jump hJ D.loc

end Formalism.MainNotions.UnusedSlot80.BCF
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DdRFull
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module

def DdRFull (D : D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l), (∃ s, Good K s LL) →
    ∀ T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL), IsCrys ((D.loc l).PD K) T.ρ → ∀ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1,
      finrank ↥LL.1 ↥(DdRE ((D.loc l).PD K) T.ρ τ) = finrank ↥LL.1 T.V

def DiRank (D : D7) (HW : HWOf D.loc) (_F : FonOf D.loc D.locA HW) (_Cm : CmpOf D.loc D.locA HW _F) :
    Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)),
    IsCrys ((D.loc l).PD K) T.ρ → ∀ c : ZMod (finrank ℚ_[l] ↥(K0 K)),
      finrank ↥LL.1 ↥(Formalism.MainNotions.DeltaInvariantLattices.ιDi ((HW l).W K 1 LL hG) T c) = finrank ↥LL.1 T.V

end Formalism.MainNotions.N.Ln34

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.DerivativeProdSubEval
section
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Polynomial

section LemG2Main

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem derivative_prod_sub_eval {R : Type} [CommRing R] (S₀ : Finset ℤ) (c : ℤ → R) (a : ℤ)
    (ha : a ∈ S₀) :
    (derivative (∏ b ∈ S₀, (X - C (c b)))).eval (c a) = ∏ b ∈ S₀.erase a, (c a - c b) := by
  classical
  have h1 : (∏ b ∈ S₀, (X - C (c b))) = (Multiset.map (fun x => X - C x) (S₀.val.map c)).prod := by
    rw [Finset.prod_eq_multiset_prod, Multiset.map_map]
    rfl
  rw [h1, eval_multiset_prod_X_sub_C_derivative (Multiset.mem_map_of_mem c ha),
    ← Multiset.map_erase_of_mem c S₀.val ha, Multiset.map_map, Finset.prod_eq_multiset_prod, Finset.erase_val]
  rfl

theorem addValuation_prod (w : AddValuation LL (WithTop ℚ)) {ι : Type} (S₀ : Finset ι) (f : ι → LL) :
    w (∏ b ∈ S₀, f b) = ∑ b ∈ S₀, w (f b) := by
  classical
  induction S₀ using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, AddValuation.map_mul, ih]

theorem algebraMap_cc_eq (W : LocWach PD LL O v n) (cc : ℤ → O)
    (hcc : ∀ x : ℤ, (-((PD.p : ℕ) : O)) * cc x = (((W.χΓ W.gam) ^ (-x) : Oˣ) : O) - 1) (j : ℤ) :
    algebraMap O LL (cc j) = Formalism.MainNotions.CrystallineLiftingInputs.cR W j := by
  have hp0 : (PD.p : LL) ≠ 0 := by
    intro h
    have := W.v_l
    rw [h, AddValuation.map_zero] at this
    exact WithTop.top_ne_one this
  unfold Formalism.MainNotions.CrystallineLiftingInputs.cR
  rw [eq_div_iff (neg_ne_zero.2 hp0)]
  have h1 := congrArg (algebraMap O LL) (hcc j)
  rw [map_mul, map_neg, map_natCast, map_sub, map_one] at h1
  rw [← h1]
  ring

theorem valuation_cc_sub (W : LocWach PD LL O v n) (hRN : Formalism.MainNotions.CrystallineLiftingInputs.RToolNum W) (cc : ℤ → O)
    (hcc : ∀ x : ℤ, (-((PD.p : ℕ) : O)) * cc x = (((W.χΓ W.gam) ^ (-x) : Oˣ) : O) - 1)
    (a b : ℤ) (hab : a ≠ b) :
    v (algebraMap O LL (cc a - cc b)) = ((padicValInt PD.p (a - b) : ℕ) : WithTop ℚ) := by
  rw [map_sub, algebraMap_cc_eq W cc hcc, algebraMap_cc_eq W cc hcc, hRN.2 a b hab, WithTop.coe_natCast]

theorem lemGB_of [NeZero n] (W : LocWach PD LL O v n) (hQ : Formalism.MainNotions.CrystallineLiftingInputs.QTool W)
    (hRN : Formalism.MainNotions.LiftingTheory.CaseA W → Formalism.MainNotions.CrystallineLiftingInputs.RToolNum W) (hC4 : Formalism.MainNotions.N.LetterConditionLocal W)
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hL : Formalism.MainNotions.LiftingTheory.coreL W)
    (hcc : Formalism.MainNotions.LiftingTheory.CaseA W → ∃ cc : ℤ → O,
      ∀ x : ℤ, (-((PD.p : ℕ) : O)) * cc x = (((W.χΓ W.gam) ^ (-x) : Oˣ) : O) - 1)
    (hΔ : Formalism.MainNotions.LiftingTheory.CaseA W → IsUnit ((PD.p - 1 : ℕ) : O)) (h56 : WachGammaDerivation W) : LemGB W := by
  intro d T₁ T₂ F b S η m hS i hi
  have hA : Formalism.MainNotions.LiftingTheory.CaseA W := hS.1
  have hl : 11 ≤ PD.p := hS.2.1
  have hsur : Formalism.MainNotions.LiftingTheory.Sur W F := hS.2.2.2.2.2.1
  have hjump := hS.2.2.2.2.2.2.1
  have hbR := hS.2.2.2.2.2.2.2.2.1 i
  have : Fact PD.p.Prime := ⟨PD.hp⟩
  have hRN := hRN hA
  obtain ⟨cc, hcc⟩ := hcc hA
  obtain ⟨hπ, hπΔ, hmod₁, hcard⟩ := uniformizer_unit_and_delta_card W h9 hA hsur.1
  have hΔ : IsUnit ((W.DelF.card : ℕ) : O) := by rw [hcard]; exact hΔ hA
  have hq := isUnit_q_of_uniformizer_unit W hπ
  obtain ⟨dop₁, hd₁⟩ := exists_derivation_gamma_sub W T₁ hπ
  obtain ⟨dop₂, hd₂⟩ := exists_derivation_gamma_sub W T₂ hπ
  have hl2 : 2 ≤ PD.p := by omega
  have hpR : (11 : ℝ) ≤ PD.p := by exact_mod_cast hl
  have haR0 : 0 ≤ aR PD.p (hpar n b S + η) := aR_nonneg PD.p _ hl2
  have haR3 : (3 : ℝ) ≤ aR PD.p (hpar n b S + η) := by
    have h1 := one_le_lam PD.p (hpar n b S + η) hl2
    have h2 : 0 ≤ (((hpar n b S + η : ℕ) : ℝ)) * (2 * (PD.p : ℝ) - 1) / ((PD.p : ℝ) - 1) ^ 2 :=
      div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) (sq_nonneg _)
    unfold aR
    linarith
  obtain ⟨a, ha⟩ : ∃ a, a = ⌈aR PD.p (hpar n b S + η)⌉₊ := ⟨_, rfl⟩
  have halt : (a : ℝ) < aR PD.p (hpar n b S + η) + 1 := ha ▸ Nat.ceil_lt_add_one haR0
  have hale : aR PD.p (hpar n b S + η) ≤ a := ha ▸ Nat.le_ceil _
  have ha1 : 1 ≤ a := by
    have : (1 : ℝ) ≤ a := by linarith
    exact_mod_cast this
  have hab : 2 * a + η ≤ b i := by
    have : ((2 * a + η : ℕ) : ℝ) < ((b i + 1 : ℕ) : ℝ) := by push_cast; linarith
    have := Nat.cast_lt.1 this
    omega
  have hbh : b i ≤ hpar n b S := by
    unfold hpar
    have := Finset.le_sup (f := b) (Finset.mem_univ i)
    omega

  obtain ⟨Bd, hBd⟩ : ∃ Bd : ℝ, Bd = (3 * (a : ℝ) + S + 2 * η - 1) / ((PD.p : ℝ) - 1) +
      Real.logb PD.p ((hpar n b S + η : ℕ) : ℝ) := ⟨_, rfl⟩
  have hpos : (0 : ℝ) < (PD.p : ℝ) - 1 := by linarith
  have hH1 : (1 : ℝ) ≤ ((hpar n b S + η : ℕ) : ℝ) := by
    have : 1 ≤ hpar n b S + η := by omega
    exact_mod_cast this
  have hp1 : (1 : ℝ) < PD.p := by linarith
  have hB0 : 0 ≤ Bd := by
    rw [hBd]
    have : (1 : ℝ) ≤ a := by exact_mod_cast ha1
    have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg _
    have hη0 : (0 : ℝ) ≤ η := Nat.cast_nonneg _
    have h1 : 0 ≤ (3 * (a : ℝ) + S + 2 * η - 1) / ((PD.p : ℝ) - 1) :=
      div_nonneg (by linarith) hpos.le
    have h2 := Real.logb_nonneg hp1 hH1
    linarith
  refine ⟨⌊Bd⌋₊, ?_, ?_⟩
  · have hfl : (⌊Bd⌋₊ : ℝ) ≤ Bd := Nat.floor_le hB0
    have h1 : (3 * (a : ℝ) + S + 2 * η - 1) / ((PD.p : ℝ) - 1) ≤
        (3 * aR PD.p (hpar n b S + η) + S + 2 * η) / ((PD.p : ℝ) - 1) + 1 := by
      rw [div_le_iff₀ hpos, add_mul, div_mul_cancel₀ _ hpos.ne', one_mul]
      linarith
    have h2 : Real.logb PD.p ((hpar n b S + η : ℕ) : ℝ) ≤ lam PD.p (hpar n b S + η) - 1 := by
      unfold lam
      have := Real.logb_le_logb_of_le hp1 (by linarith : (0 : ℝ) < ((hpar n b S + η : ℕ) : ℝ))
        (by linarith : ((hpar n b S + η : ℕ) : ℝ) ≤ 2 * ((hpar n b S + η : ℕ) : ℝ))
      linarith
    calc (⌊Bd⌋₊ : ℝ) ≤ Bd := hfl
      _ = (3 * (a : ℝ) + S + 2 * η - 1) / ((PD.p : ℝ) - 1) +
          Real.logb PD.p ((hpar n b S + η : ℕ) : ℝ) := hBd
      _ ≤ _ := by linarith
  intro x la hP
  have hxN : x ∈ W.N T₂ := hP.1
  have hxe : (letE i : LetA O n) • x = x := hP.2.1.1
  have hxΔ : ∀ δ ∈ W.DelF, W.γD T₂ δ x = x := hP.2.1.2
  have hxl : x ∈ W.Nl T₂ i := mem_letter_of_idempotent_smul W hxN hxe

  have hJL : Formalism.MainNotions.LiftingTheory.JumpsLet W T₁ (fun _ => hpar n b S + η) (fun _ => hpar n b S + η) := by
    intro j τ hτ u hu
    have h1 := hjump j τ hτ u hu
    have hbj : b j + S ≤ hpar n b S := by
      unfold hpar
      have := Finset.le_sup (f := b) (Finset.mem_univ j)
      omega
    unfold JumpWinS at h1
    split_ifs at h1 <;> simp only [Set.mem_union, Set.mem_Icc] at h1 ⊢ <;> omega
  have hK := ((hQ d T₁ T₂ F b S η m _ _ hS hJL).1 i).2.2
  rw [← ha] at hK

  obtain ⟨y₀, hy₀, hy₀F⟩ := Submodule.mem_map.1 (hK x hxl)
  have htx : ∀ δ ∈ W.DelF, W.γD T₂ δ (Formalism.MainNotions.LiftingTheory.qp W ^ a • x) = Formalism.MainNotions.LiftingTheory.qp W ^ a • x := by
    intro δ hδ
    rw [gammaD_smul_letA, map_pow, gammaA_q_of_mem_delta W hπΔ δ hδ, hxΔ δ hδ]
  obtain ⟨y₂, hy₂N, hy₂F⟩ := exists_invariant_preimage_average W hΔ F i hy₀ htx hy₀F
  let qi : W.EE := ((hq.unit⁻¹ : W.EEˣ) : W.EE)
  have hqz : Formalism.MainNotions.LiftingTheory.qp W ^ a • (qi ^ a • y₂) = y₂ := by
    rw [← algebraMap_smul W.EE (Formalism.MainNotions.LiftingTheory.qp W ^ a), smul_smul, map_pow, ← mul_pow,
      hq.mul_val_inv, one_pow, one_smul]
  have hFz : W.map F (qi ^ a • y₂) = x := by
    have hqa : IsUnit (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W ^ a)) := by
      rw [map_pow]; exact hq.pow a
    refine (hqa.smul_left_cancel).1 ?_
    rw [algebraMap_smul, algebraMap_smul, ← map_letA_smul_comm, hqz, hy₂F]
  have hX : ∀ (τ : K →ₐ[Qp] LL) (u : ℤ) (j : ℕ), Formalism.MainNotions.LiftingTheory.Over W τ i → IsJumpV PD T₁.ρ τ u →
      1 ≤ j → j ≤ a → u + (j : ℤ) ∈ Finset.Icc ((b i : ℤ) + 1) ((b i : ℤ) + S + a) ∪
        Finset.Icc (1 - (η : ℤ)) ((η : ℤ) + a) := by
    intro τ u j hτ hu hj1 hj2
    have h1 := hjump i τ hτ u hu
    unfold JumpWinS at h1
    rw [if_neg (by omega)] at h1
    simp only [Set.mem_union, Set.mem_Icc, Finset.mem_union, Finset.mem_Icc] at h1 ⊢
    omega
  have hC := hC4 hA T₁ hsur.1 i a ha1 dop₁ hd₁ cc hcc _ hX (qi ^ a • y₂) (by
    change Formalism.MainNotions.LiftingTheory.InNΔi W T₁ i (Formalism.MainNotions.LiftingTheory.qp W ^ a • (qi ^ a • y₂))
    rw [hqz]
    exact hy₂N)

  obtain ⟨w, ⟨⟨-, hwΔ⟩, hwl⟩, hP1⟩ := h56 d T₁ T₂ F b S η m hS i hi dop₂ hd₂ cc hcc x la hP
  rw [← ha] at hP1
  obtain ⟨y₁', hy₁', hy₁F'⟩ := Submodule.mem_map.1 (hK w hwl)
  have htw : ∀ δ ∈ W.DelF, W.γD T₂ δ (Formalism.MainNotions.LiftingTheory.qp W ^ a • w) = Formalism.MainNotions.LiftingTheory.qp W ^ a • w := by
    intro δ hδ
    rw [gammaD_smul_letA, map_pow, gammaA_q_of_mem_delta W hπΔ δ hδ, hwΔ δ hδ]
  obtain ⟨y₁, hy₁N, hy₁F⟩ := exists_invariant_preimage_average W hΔ F i hy₁' htw hy₁F'

  have hdis : Disjoint (Finset.Icc ((b i : ℤ) - a + 1) (b i : ℤ))
      (Finset.Icc ((b i : ℤ) + 1) ((b i : ℤ) + S + a) ∪ Finset.Icc (1 - (η : ℤ)) ((η : ℤ) + a)) := by
    rw [Finset.disjoint_left]
    intro u hu hu'
    simp only [Finset.mem_union, Finset.mem_Icc] at hu hu'
    omega
  have hval : ∀ a' ∈ Finset.Icc ((b i : ℤ) - a + 1) (b i : ℤ) ∪
      (Finset.Icc ((b i : ℤ) + 1) ((b i : ℤ) + S + a) ∪ Finset.Icc (1 - (η : ℤ)) ((η : ℤ) + a)),
      ∀ b' ∈ Finset.Icc ((b i : ℤ) - a + 1) (b i : ℤ) ∪
      (Finset.Icc ((b i : ℤ) + 1) ((b i : ℤ) + S + a) ∪ Finset.Icc (1 - (η : ℤ)) ((η : ℤ) + a)),
      a' ≠ b' → v (algebraMap O LL (cc a' - cc b')) =
        ((0 + padicValInt PD.p (a' - b') : ℕ) : WithTop ℚ) := by
    intro a' _ b' _ h
    rw [zero_add]
    exact valuation_cc_sub W hRN cc hcc a' b' h
  have hE : ∀ j₀ ∈ Finset.Icc ((b i : ℤ) - a + 1) (b i : ℤ),
      v (algebraMap O LL ((∏ b' ∈ Finset.Icc ((b i : ℤ) + 1) ((b i : ℤ) + S + a) ∪
          Finset.Icc (1 - (η : ℤ)) ((η : ℤ) + a), (X - C (cc b'))).eval (cc j₀))) +
        v (algebraMap O LL ((derivative (∏ b' ∈ Finset.Icc ((b i : ℤ) - a + 1) (b i : ℤ),
          (X - C (cc b')))).eval (cc j₀))) ≤ ((⌊Bd⌋₊ : ℕ) : WithTop ℚ) := by
    intro j₀ hj₀
    have hj₀' := Finset.disjoint_left.1 hdis hj₀
    rw [derivative_prod_sub_eval _ cc j₀ hj₀, eval_prod]
    simp only [eval_sub, eval_X, eval_C]
    rw [map_prod (algebraMap O LL), map_prod (algebraMap O LL), addValuation_prod v, addValuation_prod v]
    have e2 : ∀ b' ∈ Finset.Icc ((b i : ℤ) + 1) ((b i : ℤ) + S + a) ∪
        Finset.Icc (1 - (η : ℤ)) ((η : ℤ) + a),
        v (algebraMap O LL (cc j₀ - cc b')) = ((padicValInt PD.p (j₀ - b') : ℕ) : WithTop ℚ) :=
      fun b' hb' => valuation_cc_sub W hRN cc hcc j₀ b' (fun h => hj₀' (h ▸ hb'))
    have e1 : ∀ b' ∈ (Finset.Icc ((b i : ℤ) - a + 1) (b i : ℤ)).erase j₀,
        v (algebraMap O LL (cc j₀ - cc b')) = ((padicValInt PD.p (j₀ - b') : ℕ) : WithTop ℚ) :=
      fun b' hb' => valuation_cc_sub W hRN cc hcc j₀ b' (Finset.ne_of_mem_erase hb').symm
    rw [Finset.sum_congr rfl e2, Finset.sum_congr rfl e1, ← Nat.cast_sum, ← Nat.cast_sum,
      ← Nat.cast_add, ← WithTop.coe_natCast, ← WithTop.coe_natCast, WithTop.coe_le_coe, Nat.cast_le]
    apply Nat.le_floor
    have h11 := FactorialSumBounds.sum_erase_add_sum_le PD.p a (b i) S η (hpar n b S) hab hbh _ subset_rfl j₀ hj₀
    rw [hBd]
    push_cast at h11 ⊢
    linarith
  have hlag := hL _ _ 0 cc hdis hval ⌊Bd⌋₊ hE
  let fO : W.DD T₁ →ₗ[O] W.DD T₂ := ((W.map F).restrictScalars (LetA O n)).restrictScalars O
  have hf : ∀ y, fO (dop₁ y) = dop₂ (fO y) := fun y => map_comm_derivation W F hπ dop₁ hd₁ dop₂ hd₂ y
  have h2' : fO (aeval dop₁ (∏ x ∈ Finset.Icc ((b i : ℤ) + 1) ((b i : ℤ) + S + a) ∪
      Finset.Icc (1 - (η : ℤ)) ((η : ℤ) + a), (X - C (cc x))) (qi ^ a • y₂)) =
      aeval dop₂ (∏ x ∈ Finset.Icc ((b i : ℤ) + 1) ((b i : ℤ) + S + a) ∪
        Finset.Icc (1 - (η : ℤ)) ((η : ℤ) + a), (X - C (cc x))) x := by
    rw [FactorialSumBounds.linearMap_aeval_apply_comm_of_intertwine fO dop₁ dop₂ hf]
    exact congrArg _ hFz
  obtain ⟨y, hyN, hyF⟩ := FactorialSumBounds.exists_mem_map_eq_smul fO dop₁ dop₂ hf (invariantLetter W T₁ i)
    (derivation_preserves_invariants W i hπ hmod₁ dop₁ hd₁) _ _ _ hlag x ⟨y₁, hy₁N, hy₁F.trans hP1.symm⟩
    ⟨_, hC, h2'⟩
  obtain ⟨⟨hyN1, hyΔ⟩, hyl⟩ := hyN
  exact ⟨y, hyN1, ⟨idempotent_smul_of_mem_letter W hyl, hyΔ⟩, hyF⟩

end LemG2Main

end Formalism.MainNotions.RamifiedCoefficientChains.S9
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.FamilyStatementsLocal
section
noncomputable section

namespace Formalism.MainNotions.FamilyNumericLemmas

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders Filter Topology

theorem cyl_univ (D : D7) (k : Fin 2) : cyl D k Set.univ = Set.univ := by
  ext t; simp [cyl]

end Formalism.MainNotions.FamilyNumericLemmas
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.NormAHolds
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

theorem normA_holds {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) : normA P K LL := by
  intro T₁ T₂ F r S η m h up b hA hJ
  unfold Formalism.MainNotions.ElementDenominator.HypA at hA
  obtain ⟨hc1, hc2, hon, _, hj1, hηb, hsum, hjh, hposition⟩ := hA
  have hT1 : ∀ τ, JumpsInV (P.PD K) T₁.ρ τ
      (deep (up τ) (min (b τ) (h + 1)) S ∪ Set.Icc (-((min η h : ℕ) : ℤ)) (min η h : ℕ)) := by
    intro τ a ha
    have ha1 := hj1 τ a ha
    have hah := hjh τ a ha
    simp only [Set.mem_Icc] at hah
    rcases ha1 with h1 | h1
    · left
      unfold deep at h1 ⊢
      split_ifs at h1 ⊢ <;> simp only [Set.mem_Icc] at h1 ⊢ <;> push_cast <;> omega
    · right
      simp only [Set.mem_Icc] at h1 ⊢
      push_cast
      omega
  have hj2h : ∀ τ, JumpsInV (P.PD K) T₂.ρ τ (Set.Icc (-(h : ℤ)) h) := fun τ => hJ τ _ (hjh τ)
  refine ⟨min η h, h + S + 1, fun τ => min (b τ) (h + 1), min_le_left _ _, le_rfl, ?_⟩
  refine ⟨hc1, hc2, hon, hT1, fun τ => hJ τ _ (hT1 τ), fun τ => ?_, fun τ => ?_, by omega,
    fun τ => ?_, hposition⟩
  · have := hηb τ
    show min η h < min (b τ) (h + 1)
    omega
  · show min (b τ) (h + 1) + S ≤ h + S + 1
    omega
  · refine le_of_eq_of_le ?_ (hsum τ)
    apply Finset.sum_subset
    · intro x hx
      simp only [Finset.mem_Icc] at hx ⊢
      push_cast at hx
      omega
    · intro x hx hx'
      simp only [Finset.mem_Icc] at hx hx'
      push_cast at hx'
      have hnj : ¬ IsJumpV (P.PD K) T₂.ρ τ x := by
        intro hj
        have h2 := hj2h τ x hj
        simp only [Set.mem_Icc] at h2
        omega
      unfold IsJumpV at hnj
      push_neg at hnj
      unfold multV
      rw [hnj, sub_self]

theorem normR_holds (D : D7) : normR D := by
  intro l _ _ K LL _
  exact normA_holds (D.loc l) K LL

end Formalism.MainNotions.N.Ln34

end
end

