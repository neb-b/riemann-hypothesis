module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOfMemSB
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockTriangularOneAddMat
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantModulus
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0040
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralCompBlocks
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetIntegral
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp ValuativeRel Matrix MeasureTheory
open GlobalTheory.IwahoriInj (Deep)

namespace GlobalTheory.MellinPoly

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem absPow_eq_zpow (s : ℂ) (x : kˣ) :
    (absPow k s x : ℂ) = ((resCard k : ℂ) ^ (-s)) ^ (SmGL.ord k x : ℤ) := by
  have hq : (0 : ℝ) < (resCard k : ℝ) := by
    unfold resCard
    exact_mod_cast Nat.card_pos
  have hq0 : (resCard k : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hz : (resCard k : ℝ) ^ (-SmGL.ord k x) ≠ 0 := (zpow_pos hq _).ne'
  unfold absPow
  simp only [MonoidHom.coe_toHomUnits, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [GlobalTheory.LGrp.nabs_eq_zpow, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 hz),
    Complex.cpow_def_of_ne_zero hq0, ← Complex.exp_int_mul, ← Complex.ofReal_log (zpow_pos hq _).le,
    Real.log_zpow, ← Complex.ofReal_natCast, ← Complex.ofReal_log hq.le]
  push_cast
  congr 1
  ring

end GlobalTheory.MellinPoly
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiUnipotentEqProdRootExchange
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

namespace GlobalTheory.RootEx.FJUnipotent
open GlobalTheory.RootEx.Radical

section
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

def midLev (ρ : ℕ) : n ⊕ Fin c → ℕ :=
  Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1))

def midGroup (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) :
    Subgroup (GL (n ⊕ Fin c) k) where
  carrier := {g | Uni (midLev ρ) g.val}
  one_mem' := fun _ _ _ => rfl
  mul_mem' := fun hx hy => Uni.mul hx hy
  inv_mem' := fun hx => Uni.inv hx

theorem NFJ_le_midGroup (ρ : ℕ) : NFJ k n c ρ ≤ midGroup k n c ρ := by
  have key : ∀ p, p = ρ ∨ p = ρ + 1 → N k n c p ≤ midGroup k n c ρ := by
    rintro p hp g hg
    have hg' := (mem_N_iff g).1 hg
    show Uni (midLev ρ) g.val
    intro r s hrs
    apply hg' r s
    rcases r with r | i <;> rcases s with s | j <;>
      simp only [lev, midLev, Sum.elim_inl, Sum.elim_inr] at hrs ⊢ <;> omega
  exact sup_le (key ρ (Or.inl rfl)) (key (ρ + 1) (Or.inr rfl))

theorem exists_col (P : Fin c) {g : GL (n ⊕ Fin c) k} (hg : g ∈ midGroup k n c P.val) :
    ∃ u ∈ N k n c (P.val + 1), ∃ β : n → k, g = u * colE c (P.val + 1) β := by
  have hg' : ∀ r s, midLev (n := n) (c := c) P.val s ≤ midLev P.val r →
      g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s := hg
  refine ⟨g * colE c (P.val + 1) (-fun r => g.val (Sum.inl r) (Sum.inr P)), ?_,
    fun r => g.val (Sum.inl r) (Sum.inr P), ?_⟩
  · rw [mem_N_iff]
    intro r s hrs
    rw [Units.val_mul]
    rcases s with s | j
    · rw [GlobalTheory.RootEx.Exchange.mul_colE_inl]
      apply hg'
      rcases r with r | i <;>
        simp only [lev, midLev, Sum.elim_inl, Sum.elim_inr] at hrs ⊢ <;> omega
    · rw [GlobalTheory.RootEx.Exchange.mul_colE_inr]
      by_cases hj : j = P
      · have hc : j.val + 1 = P.val + 1 := by rw [hj]
        rw [if_pos hc, hj]
        rcases r with r | i
        · have hX : ∀ t, g.val (Sum.inl r) (Sum.inl t) = if r = t then 1 else 0 := by
            intro t
            rw [hg' _ _ (by simp only [midLev, Sum.elim_inl]; omega)]
            simp [Matrix.one_apply]
          simp [hX]
        · have hi : P.val ≤ i.val := by
            rw [hj] at hrs
            simp only [lev, Sum.elim_inr] at hrs
            omega
          have h1 := hg' (Sum.inr i) (Sum.inr P) (by simp only [midLev, Sum.elim_inr]; omega)
          have h2 : ∀ t, g.val (Sum.inr i) (Sum.inl t) = 0 := fun t => by
            rw [hg' _ _ (by simp only [midLev, Sum.elim_inl, Sum.elim_inr]; omega)]
            simp
          simp [h1, h2]
      · have hj' : j.val ≠ P.val := fun h => hj (Fin.ext h)
        have hc : ¬ (j.val + 1 = P.val + 1) := fun h => hj' (by omega)
        rw [if_neg hc, add_zero]
        apply hg'
        rcases r with r | i <;>
          simp only [lev, midLev, Sum.elim_inl, Sum.elim_inr] at hrs ⊢ <;> omega
  · rw [mul_assoc, GlobalTheory.RootEx.Exchange.colE_neg_mul, mul_one]

end

theorem fj_unipotent : ∀ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (_ : 1 ≤ ρ) (_ : ρ < c), (∀ g, g ∈ NFJ k n c ρ ↔ ∃ x ∈ N k n c ρ, ∃ y ∈ N k n c (ρ + 1), g = x * y) ∧ (∀ g : GL (n ⊕ Fin c) k, g ∈ NFJ k n c ρ ↔ ∀ r s : n ⊕ Fin c, Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) s ≤ Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) r → g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s) ∧ ∀ g ∈ NFJ k n c ρ, ∃ u ∈ N k n c (ρ + 1), ∃ β : n → k, g = u * colE c (ρ + 1) β := by
  intro k _ n _ _ c ρ _ hρc
  have hle := NFJ_le_midGroup (k := k) (n := n) (c := c) ρ
  have hcol : ∀ g ∈ NFJ k n c ρ, ∃ u ∈ N k n c (ρ + 1), ∃ β : n → k,
      g = u * colE c (ρ + 1) β :=
    fun g hg => exists_col ⟨ρ, hρc⟩ (hle hg)
  have hcolN : ∀ β : n → k, colE c (ρ + 1) β ∈ N k n c ρ :=
    fun β => colE_mem β (Nat.lt_succ_self ρ)
  have hmid : ∀ g : GL (n ⊕ Fin c) k, g ∈ midGroup k n c ρ → g ∈ NFJ k n c ρ := by
    intro g hg
    obtain ⟨u, hu, β, rfl⟩ := exists_col (k := k) ⟨ρ, hρc⟩ hg
    exact (NFJ k n c ρ).mul_mem (le_sup_right (a := N k n c ρ) hu)
      (le_sup_left (b := N k n c (ρ + 1)) (hcolN β))
  refine ⟨fun g => ⟨fun hg => ?_, ?_⟩, fun g => ⟨fun hg => hle hg, fun hg => hmid g hg⟩, hcol⟩
  · obtain ⟨u, hu, β, hg'⟩ := hcol g⁻¹ ((NFJ k n c ρ).inv_mem hg)
    refine ⟨(colE c (ρ + 1) β)⁻¹, (N k n c ρ).inv_mem (hcolN β), u⁻¹,
      (N k n c (ρ + 1)).inv_mem hu, ?_⟩
    rw [← _root_.mul_inv_rev, ← hg', inv_inv]
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact (NFJ k n c ρ).mul_mem (le_sup_left (b := N k n c (ρ + 1)) hx)
      (le_sup_right (a := N k n c ρ) hy)

end GlobalTheory.RootEx.FJUnipotent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasFiniteRankTraceOfOfRangeLeFiniteDimensional
section
namespace GlobalTheory.IndefiniteRowSideFullHecke.RangeTrace

theorem hasFinTrace_of_range_le (X : Type) [AddCommGroup X] [Module ℂ X] (T : X →ₗ[ℂ] X)
    (Z : Submodule ℂ X) [FiniteDimensional ℂ Z] (hT : LinearMap.range T ≤ Z) :
    GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasFinTrace T (LinearMap.trace ℂ Z (T.restrict (p := Z) (q := Z)
      fun x _ => hT (LinearMap.mem_range_self T x))) := by
  haveI : FiniteDimensional ℂ (LinearMap.range T) := Submodule.finiteDimensional_of_le hT
  refine ⟨inferInstance, ?_⟩
  have hmem : ∀ x : Z, (T.restrict (p := Z) (q := Z)
      fun x _ => hT (LinearMap.mem_range_self T x)) x ∈ (LinearMap.range T).comap Z.subtype :=
    fun x => LinearMap.mem_range_self T (x : X)
  rw [← LinearMap.trace_restrict_eq_of_forall_mem _ _ hmem,
    ← LinearMap.trace_conj' _ (Submodule.comapSubtypeEquivOfLe hT)]
  congr 1

end GlobalTheory.IndefiniteRowSideFullHecke.RangeTrace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralIntegralGLMulRightComplexProductSigma
section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Topology
open scoped ENNReal

namespace GlobalTheory.SmGL.IndDual

section Real

open GlobalTheory.SplitFlip

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)
  [MeasurableSpace k] [BorelSpace k]

theorem integral_KO_mul_right_real (μ : Measure (GL n k)) [μ.IsHaarMeasure] {f : GL n k → ℝ}
    (hf : Continuous f) (hlaw : ∀ (p : parab k e) x, f (p * x) = modulus k m (leviProj k e p) * f x)
    (g : GL n k) :
    ∫ x in (KO k n : Set (GL n k)), f (x * g) ∂μ = ∫ x in (KO k n : Set (GL n k)), f x ∂μ := by
  have h1 : IntegrableOn (fun x => f (x * g)) (KO k n : Set (GL n k)) μ :=
    (hf.comp (continuous_mul_const g)).continuousOn.integrableOn_compact isCompact_KO
  have h2 : IntegrableOn f (KO k n : Set (GL n k)) μ := hf.continuousOn.integrableOn_compact isCompact_KO
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part h1,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part h2,
    UnitInd.lintegral_KO_mul_right e μ (φ := fun x => ENNReal.ofReal (f x)) hf.measurable.ennreal_ofReal
      (fun p x => by rw [hlaw, ENNReal.ofReal_mul (modulus_pos k _).le]) g,
    UnitInd.lintegral_KO_mul_right e μ (φ := fun x => ENNReal.ofReal (-f x)) hf.neg.measurable.ennreal_ofReal
      (fun p x => by rw [hlaw, ← mul_neg, ENNReal.ofReal_mul (modulus_pos k _).le]) g]

theorem integral_integralGL_mul_right_complex_productSigma (μ : Measure (GL n k)) [μ.IsHaarMeasure] {F : GL n k → ℂ}
    (hF : Continuous F) (hlaw : ∀ (p : parab k e) x, F (p * x) = (modulus k m (leviProj k e p) : ℂ) * F x)
    (g : GL n k) :
    ∫ x in (KO k n : Set (GL n k)), F (x * g) ∂μ = ∫ x in (KO k n : Set (GL n k)), F x ∂μ := by
  have h1 : IntegrableOn (fun x => F (x * g)) (KO k n : Set (GL n k)) μ :=
    (hF.comp (continuous_mul_const g)).continuousOn.integrableOn_compact isCompact_KO
  have h2 : IntegrableOn F (KO k n : Set (GL n k)) μ := hF.continuousOn.integrableOn_compact isCompact_KO
  have hre := integral_KO_mul_right_real e μ (Complex.continuous_re.comp hF)
    (fun p x => by simp [hlaw]) g
  have him := integral_KO_mul_right_real e μ (Complex.continuous_im.comp hF)
    (fun p x => by simp [hlaw]) g
  refine Complex.ext ?_ ?_
  · exact ((integral_re h1).symm.trans hre).trans (integral_re h2)
  · exact ((integral_im h1).symm.trans him).trans (integral_im h2)

end Real

theorem integral_KO_mul_right : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) [MeasurableSpace (GL n k)] [BorelSpace (GL n k)] (μ : Measure (GL n k)) [μ.IsHaarMeasure] (F : GL n k → ℂ), Continuous F → (∀ (p : parab k e) (g : GL n k), F (p * g) = (modulus k m (leviProj k e p) : ℂ) * F g) → ∀ g : GL n k, ∫ x in (KO k n : Set (GL n k)), F (x * g) ∂μ = ∫ x in (KO k n : Set (GL n k)), F x ∂μ := by
  intro k _ _ _ _ α n m _ _ _ _ _ _ e M hM μ _ F hF hlaw g
  borelize k
  obtain rfl : M = Units.instMeasurableSpace :=
    hM.measurable_eq.trans (SplitFlip.borel_GL (k := k) (n := n)).measurable_eq.symm
  exact integral_integralGL_mul_right_complex_productSigma e μ hF hlaw g

end GlobalTheory.SmGL.IndDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviIntegralFacts
section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Topology
open scoped ENNReal

namespace GlobalTheory.SmGL.LeviInt


open MeasureTheory Topology in
open scoped ENNReal in
open ValuativeRel Matrix in
theorem _root_.GlobalTheory.SmGL.LeviInt.nabs_det_eq_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n] {g : GL n k}
    (hg : g ∈ _root_.GlobalTheory.SplitWeil.KO k n) :
    _root_.GlobalTheory.SplitWeil.nabs k (GeneralLinearGroup.det g) = 1 := by
  obtain ⟨h1, h2⟩ := (_root_.GlobalTheory.SplitFlip.mem_KO_iff g).1 hg
  have hdet : ∀ M : Matrix n n k, (∀ i j, M i j ∈ (valuation k).integer) →
      M.det ∈ (valuation k).integer := by
    intro M hM
    rw [Matrix.det_apply]
    refine sum_mem fun σ _ => ?_
    rw [Units.smul_def]
    exact zsmul_mem (prod_mem fun i _ => hM _ _) _
  apply _root_.GlobalTheory.SmGL.nabs_eq_one
  have hd1 : valuation k ((GeneralLinearGroup.det g : kˣ) : k) ≤ 1 := by
    rw [← Valuation.mem_integer_iff, Matrix.GeneralLinearGroup.val_det_apply]
    exact hdet _ h1
  have hd2 : valuation k (((GeneralLinearGroup.det g)⁻¹ : kˣ) : k) ≤ 1 := by
    rw [← map_inv, ← Valuation.mem_integer_iff, Matrix.GeneralLinearGroup.val_det_apply]
    exact hdet _ h2
  have hprod : valuation k ((GeneralLinearGroup.det g : kˣ) : k) *
      valuation k (((GeneralLinearGroup.det g)⁻¹ : kˣ) : k) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  exact le_antisymm hd1 (hprod ▸ mul_le_of_le_one_right' hd2)


open MeasureTheory Topology in
open scoped ENNReal in
theorem _root_.GlobalTheory.SmGL.LeviInt.levi_integral_facts : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n), (∀ (g : _root_.GlobalTheory.SmGL.Levi k m) (u : GL n k), u ∈ _root_.GlobalTheory.SmGL.unipRad k e → (_root_.GlobalTheory.SmGL.leviEmb k e g * u ∈ _root_.GlobalTheory.SplitWeil.KO k n ↔ (∀ a, g a ∈ _root_.GlobalTheory.SplitWeil.KO k (m a)) ∧ u ∈ _root_.GlobalTheory.SplitWeil.KO k n)) ∧ (∀ p : _root_.GlobalTheory.SmGL.parab k e, (p : GL n k) ∈ _root_.GlobalTheory.SplitWeil.KO k n → ∀ a, _root_.GlobalTheory.SmGL.leviProj k e p a ∈ _root_.GlobalTheory.SplitWeil.KO k (m a)) ∧ (∀ g : _root_.GlobalTheory.SmGL.Levi k m, (∀ a, g a ∈ _root_.GlobalTheory.SplitWeil.KO k (m a)) → _root_.GlobalTheory.SmGL.modulus k m g = 1) ∧ (∀ g h : _root_.GlobalTheory.SmGL.Levi k m, _root_.GlobalTheory.SmGL.modulus k m (g * h) = _root_.GlobalTheory.SmGL.modulus k m g * _root_.GlobalTheory.SmGL.modulus k m h) ∧ Continuous (_root_.GlobalTheory.SmGL.modulus k m) ∧ Continuous (_root_.GlobalTheory.SmGL.leviProj k e) ∧ IsClosed (_root_.GlobalTheory.SmGL.parab k e : Set (GL n k)) ∧ IsClosed (_root_.GlobalTheory.SmGL.unipRad k e : Set (GL n k)) ∧ ∀ g : GL n k, ∃ p ∈ _root_.GlobalTheory.SmGL.parab k e, ∃ x ∈ _root_.GlobalTheory.SplitWeil.KO k n, g = p * x := by
  intro k _ _ _ _ α n m _ _ _ _ _ _ e
  have hT2 : T2Space k := (_root_.GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)).2
  have hlevi : ∀ (g : _root_.GlobalTheory.SmGL.Levi k m) (u : GL n k), u ∈ _root_.GlobalTheory.SmGL.unipRad k e →
      (_root_.GlobalTheory.SmGL.leviEmb k e g * u ∈ _root_.GlobalTheory.SplitWeil.KO k n ↔
        (∀ a, g a ∈ _root_.GlobalTheory.SplitWeil.KO k (m a)) ∧
          u ∈ _root_.GlobalTheory.SplitWeil.KO k n) := by
    intro g u hu
    rw [← Subgroup.inv_mem_iff, mul_inv_rev, ← map_inv]
    refine (_root_.GlobalTheory.SmGL.UnitInd.unip_mul_levi_mem_KO e ⟨u⁻¹, inv_mem hu⟩ g⁻¹).trans ?_
    have hinv : ∀ a, (g⁻¹) a = (g a)⁻¹ := fun a => rfl
    simp only [hinv, Subgroup.inv_mem_iff]
    exact and_comm
  have hemb : ∀ g : _root_.GlobalTheory.SmGL.Levi k m,
      _root_.GlobalTheory.SmGL.leviEmb k e g ∈ _root_.GlobalTheory.SmGL.parab k e := by
    intro g
    apply _root_.GlobalTheory.SmGL.mem_parab_iff.2
    intro a b i j hab
    classical
    simp [_root_.GlobalTheory.SmGL.leviEmb, Matrix.blockDiagonal'_apply, hab.ne']
  have hdec : ∀ p : _root_.GlobalTheory.SmGL.parab k e,
      ∃ u ∈ _root_.GlobalTheory.SmGL.unipRad k e,
        (p : GL n k) = _root_.GlobalTheory.SmGL.leviEmb k e (_root_.GlobalTheory.SmGL.leviProj k e p) * u := by
    intro p
    let L : _root_.GlobalTheory.SmGL.parab k e :=
      ⟨_root_.GlobalTheory.SmGL.leviEmb k e (_root_.GlobalTheory.SmGL.leviProj k e p), hemb _⟩
    have hL : _root_.GlobalTheory.SmGL.leviProj k e L = _root_.GlobalTheory.SmGL.leviProj k e p := by
      funext a
      ext i j
      simp [_root_.GlobalTheory.SmGL.leviProj_apply, L, _root_.GlobalTheory.SmGL.leviEmb, Matrix.blockDiagonal'_apply_eq]
    refine ⟨((L⁻¹ * p : _root_.GlobalTheory.SmGL.parab k e) : GL n k), ?_, ?_⟩
    · unfold _root_.GlobalTheory.SmGL.unipRad
      refine Subgroup.mem_map.mpr ⟨L⁻¹ * p, ?_, rfl⟩
      change _root_.GlobalTheory.SmGL.leviProj k e (L⁻¹ * p) = 1
      rw [map_mul, map_inv, hL, inv_mul_cancel]
    · rw [Subgroup.coe_mul, Subgroup.coe_inv]
      exact (mul_inv_cancel_left _ _).symm
  have hproj : ∀ p : _root_.GlobalTheory.SmGL.parab k e,
      (p : GL n k) ∈ _root_.GlobalTheory.SplitWeil.KO k n →
        ∀ a, _root_.GlobalTheory.SmGL.leviProj k e p a ∈ _root_.GlobalTheory.SplitWeil.KO k (m a) := by
    intro p hp a
    obtain ⟨u, hu, hpu⟩ := hdec p
    rw [hpu] at hp
    exact ((hlevi _ u hu).1 hp).1 a
  have hmod : ∀ g : _root_.GlobalTheory.SmGL.Levi k m,
      (∀ a, g a ∈ _root_.GlobalTheory.SplitWeil.KO k (m a)) → _root_.GlobalTheory.SmGL.modulus k m g = 1 := by
    intro g hg
    unfold _root_.GlobalTheory.SmGL.modulus
    exact Finset.prod_eq_one fun a _ => by
      rw [_root_.GlobalTheory.SmGL.LeviInt.nabs_det_eq_one (hg a), one_zpow]
  have hmul : ∀ g h : _root_.GlobalTheory.SmGL.Levi k m,
      _root_.GlobalTheory.SmGL.modulus k m (g * h) = _root_.GlobalTheory.SmGL.modulus k m g * _root_.GlobalTheory.SmGL.modulus k m h := by
    intro g h
    unfold _root_.GlobalTheory.SmGL.modulus
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [← mul_zpow, ← _root_.GlobalTheory.SmGL.nabs_mul', ← map_mul]
    rfl
  have hcont : Continuous (_root_.GlobalTheory.SmGL.leviProj k e) := by
    refine continuous_pi fun a => Units.continuous_iff.2 ⟨?_, ?_⟩
    · refine continuous_pi fun i => continuous_pi fun j => ?_
      simp only [Function.comp_apply, _root_.GlobalTheory.SmGL.leviProj_apply]
      exact (Units.continuous_val.comp continuous_subtype_val).matrix_elem _ _
    · have hinv : ∀ p : _root_.GlobalTheory.SmGL.parab k e,
          (_root_.GlobalTheory.SmGL.leviProj k e p a)⁻¹ = _root_.GlobalTheory.SmGL.leviProj k e p⁻¹ a := by
        intro p
        rw [map_inv]
        rfl
      refine continuous_pi fun i => continuous_pi fun j => ?_
      simp only [hinv, _root_.GlobalTheory.SmGL.leviProj_apply, Subgroup.coe_inv]
      exact (Units.continuous_coe_inv.comp continuous_subtype_val).matrix_elem _ _
  have hP : IsClosed (_root_.GlobalTheory.SmGL.parab k e : Set (GL n k)) := by
    have hset : (_root_.GlobalTheory.SmGL.parab k e : Set (GL n k)) =
        ⋂ (a) (b) (i : m a) (j : m b) (_ : b < a),
          {g : GL n k | (g : Matrix n n k) (e ⟨a, i⟩) (e ⟨b, j⟩) = 0} := by
      ext g
      rw [SetLike.mem_coe, _root_.GlobalTheory.SmGL.mem_parab_iff]
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
    rw [hset]
    exact isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun i =>
      isClosed_iInter fun j => isClosed_iInter fun _ =>
        isClosed_eq (Units.continuous_val.matrix_elem _ _) continuous_const
  have hN : IsClosed (_root_.GlobalTheory.SmGL.unipRad k e : Set (GL n k)) := by
    have hset : (_root_.GlobalTheory.SmGL.unipRad k e : Set (GL n k)) =
        (_root_.GlobalTheory.SmGL.parab k e : Set (GL n k)) ∩
          ⋂ (a) (i : m a) (j : m a), {g : GL n k |
            (g : Matrix n n k) (e ⟨a, i⟩) (e ⟨a, j⟩) = (1 : Matrix (m a) (m a) k) i j} := by
      ext g
      rw [SetLike.mem_coe, _root_.GlobalTheory.SmGL.mem_unipRad]
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, SetLike.mem_coe]
    rw [hset]
    exact hP.inter (isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_eq (Units.continuous_val.matrix_elem _ _) continuous_const)
  refine ⟨hlevi, hproj, hmod, hmul, _root_.GlobalTheory.SmGL.UnitInd.isLocallyConstant_modulus.continuous, hcont,
    hP, hN, fun g => ?_⟩
  obtain ⟨u, h, w, hw, rfl⟩ := _root_.GlobalTheory.SmGL.UnitInd.exists_iwasawa e g
  exact ⟨_, mul_mem (_root_.GlobalTheory.SmGL.unipRad_le_parab k e u.2)
    (hemb h), w, hw, rfl⟩

end GlobalTheory.SmGL.LeviInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemGridPathInnerVerticesFlipGridPathAtSquareStatement
section
open GlobalTheory.SplitFlip
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_gridPathInnerVertices_flipGridPathAtSquare : ∀ {γ : List Edge} {i j : ℕ}, IsPath γ → PassesThrough i j γ → ∀ X ∈ innerVertices (flipPath i j γ), X ≠ (i, j) ∧ (X ≠ (i + 1, j + 1) → X ∈ innerVertices γ) := by
  first | exact @GlobalTheory.SplitFlip.mem_innerVertices_flipPath | exact GlobalTheory.SplitFlip.mem_innerVertices_flipPath | (intros; apply GlobalTheory.SplitFlip.mem_innerVertices_flipPath <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NabsDetEqOfActEq
section
open MeasureTheory ValuativeRel Matrix
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.HalfPowerSpherical GlobalTheory.LatPair GlobalTheory.StepData
open scoped Pointwise

noncomputable section
namespace GlobalTheory.IdealChain

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]






section Act
variable {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']






end Act

section Half

end Half

end GlobalTheory.IdealChain
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoUnramTwistOfNoInert
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.InertSupp ValuativeRel Matrix MeasureTheory

namespace GlobalTheory.InertSupp.Unram

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


open ValuativeRel Matrix MeasureTheory in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem _root_.GlobalTheory.InertSupp.Unram.valuation_det_KO {m : Type} [Fintype m] [DecidableEq m] {g : GL m k}
    (hg : g ∈ _root_.GlobalTheory.SplitWeil.KO k m) :
    valuation k (GeneralLinearGroup.det g : k) = 1 := by
  unfold _root_.GlobalTheory.SplitWeil.KO at hg
  obtain ⟨h, rfl⟩ := hg
  have hdet : (GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap (𝒪[k]) k) h) : k)
      = algebraMap (𝒪[k]) k (GeneralLinearGroup.det h : 𝒪[k]) := by
    simp [GeneralLinearGroup.val_det_apply, RingHom.map_det]
  rw [hdet]
  exact (Valuation.integer.integers (valuation k)).one_of_isUnit (Units.isUnit _)

end GlobalTheory.InertSupp.Unram
end
end

