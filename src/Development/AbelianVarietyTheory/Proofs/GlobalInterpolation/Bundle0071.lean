module

public import Mathlib
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0058
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsPrincipalIdealRingSemiLoc
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0061

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogfSqLeRS
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem logf_sq_le_rS : ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks), x0 ≤ s.x → RankVal s R →
    Real.log R.f ^ 2 ≤ (R.rS : ℝ) := by
  obtain ⟨x1, h1⟩ := GlobalTheory.log_add_rpow_mul_log_pow_le_rpow 0 (1 / 4) 0 36 (1 / 2) 2 le_rfl (by norm_num) (by norm_num)
  refine ⟨max x1 (Real.exp 1), fun s R hx hR => ?_⟩
  have hn := hR.n_le'
  obtain ⟨-, ⟨hm, -⟩, -, -⟩ := hR
  have hx1 := h1 s.x (le_trans (le_max_left _ _) hx)
  have hxe : Real.exp 1 ≤ s.x := le_trans (le_max_right _ _) hx
  have h1x := s.one_lt_alt
  have hx0 : 0 < s.x := by linarith
  have he := s.eps_lt
  have he0 := s.eps_pos
  have hl : 1 ≤ Real.log s.x := by
    rw [Real.le_log_iff_exp_le hx0]; exact hxe
  rw [Real.rpow_zero] at hx1
  have hm' : s.x ^ (1 / 4 : ℝ) ≤ (R.m : ℝ) := by
    refine le_trans ?_ hm
    apply Real.le_sqrt_of_sq_le
    unfold Scale.delta1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    have : s.x * s.x ^ (-(s.eps / 8)) = s.x ^ (1 + -(s.eps / 8)) := by
      rw [Real.rpow_add hx0, Real.rpow_one]
    rw [this]
    apply Real.rpow_le_rpow_of_exponent_le h1x.le
    push_cast
    linarith
  have hf1 : 1 ≤ R.f := by
    have : 0 < R.ord := R.ord_pos
    unfold Ranks.f Ranks.n; omega
  have hf1' : (1 : ℝ) ≤ R.f := by exact_mod_cast hf1
  have hf : (R.f : ℝ) ≤ 4 * s.x ^ (3 : ℝ) := by
    have : s.x ^ ((9 : ℝ) / 4) ≤ s.x ^ (3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h1x.le (by norm_num)
    unfold Ranks.f
    push_cast
    linarith
  have hlf : Real.log R.f ≤ 6 * Real.log s.x := by
    have h2 := Real.log_le_log (by linarith) hf
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hx0] at h2
    have h4 : Real.log 4 ≤ 4 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  have hlf0 : 0 ≤ Real.log R.f := Real.log_nonneg hf1'
  have hsq : Real.log R.f ^ 2 ≤ (6 * Real.log s.x) ^ 2 := pow_le_pow_left₀ hlf0 hlf 2
  have hr : R.m ≤ 2 * R.rS + 3 := by unfold Ranks.rS; omega
  have hr' : (R.m : ℝ) ≤ 2 * R.rS + 3 := by exact_mod_cast hr
  nlinarith

theorem szRow_logf : SzRow (fun C D L => (Real.log D.R.f ≤ Real.sqrt D.R.rS) ∧
    (Real.log D.R.f ^ 2 ≤ (D.R.m : ℝ) ^ 2 * L.sc.L) ∧
    (Real.log (Real.log L.sc.b) ≤ C.P.cLL * D.R.r * D.R.f * Real.log D.R.r) ∧
    ((4 * (D.R.f : ℝ) + 10) * D.R.r ≤ nW L C.P.CnW)) := by
  intro eps _ _ C hC
  obtain ⟨x1, h1⟩ := logf_sq_le_rS
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨max x1 C.P.cLL⁻¹, fun D L _ hx hV => ?_⟩⟩⟩
  have hsq := h1 L.sc D.R (le_trans (le_max_left _ _) hx) hV.ranks
  have hxc : C.P.cLL⁻¹ ≤ L.sc.x := le_trans (le_max_right _ _) hx
  have hc1 : 1 ≤ C.P.cLL⁻¹ := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 _ (by simp [FC.cLast])
  have hc0 : 0 < C.P.cLL := inv_pos.mp (by linarith)
  have hW : C.P.CnW = 10 := hC.1.2.2.2.2.2.2.2.1
  obtain ⟨-, -, ⟨hk, -⟩, -⟩ := hV.ranks
  have h1x := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have he := L.sc.eps_lt
  have he0 := L.sc.eps_pos
  have hm2 := D.R.two_le_m
  have hmk := D.R.m_add_three_le_k
  have hf2 : 2 ≤ D.R.f := by
    have : 0 < D.R.ord := D.R.ord_pos
    unfold Ranks.f Ranks.n; omega
  have hf2' : (2 : ℝ) ≤ D.R.f := by exact_mod_cast hf2
  have hL : 1 ≤ L.sc.L := Real.one_le_rpow h1x.le he0.le
  have hm2' : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm2
  refine ⟨Real.le_sqrt_of_sq_le hsq, ?_, ?_, ?_⟩
  · have hr : D.R.rS ≤ D.R.m := by unfold Ranks.rS; omega
    have hr' : (D.R.rS : ℝ) ≤ D.R.m := by exact_mod_cast hr
    have h2 : (D.R.m : ℝ) ≤ (D.R.m : ℝ) ^ 2 := by nlinarith
    have h3 : (D.R.m : ℝ) ^ 2 ≤ (D.R.m : ℝ) ^ 2 * L.sc.L := le_mul_of_one_le_right (by positivity) hL
    linarith
  · have hkr : D.R.k ≤ D.R.r := by unfold Ranks.r; omega
    have hkr' : (D.R.k : ℝ) ≤ D.R.r := by exact_mod_cast hkr
    have hxk : L.sc.x ≤ L.sc.x ^ (9 / 2 + 10 * L.sc.eps) := by
      conv_lhs => rw [← Real.rpow_one L.sc.x]
      exact Real.rpow_le_rpow_of_exponent_le h1x.le (by linarith)
    have hxr : L.sc.x ≤ D.R.r := by linarith
    have hl0 : 0 ≤ Real.log L.sc.x := Real.log_nonneg h1x.le
    have hlr : Real.log L.sc.x ≤ Real.log D.R.r := Real.log_le_log hx0 hxr
    have hb : Real.log (Real.log L.sc.b) = L.sc.eps * Real.log L.sc.x := by
      unfold Scale.b Scale.L
      rw [Real.log_exp, Real.log_rpow hx0]
    have hcr : 1 ≤ C.P.cLL * D.R.r := by
      have := mul_le_mul_of_nonneg_left (le_trans hxc hxr) hc0.le
      rwa [mul_inv_cancel₀ hc0.ne'] at this
    have hcrf : 1 ≤ C.P.cLL * D.R.r * D.R.f := by nlinarith
    have h3 : Real.log D.R.r ≤ C.P.cLL * D.R.r * D.R.f * Real.log D.R.r :=
      le_mul_of_one_le_left (by linarith) hcrf
    rw [hb]
    nlinarith
  · unfold nW
    rw [hW]
    have hk1 : (1 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 1 ≤ D.R.k)
    have hk0 : (0 : ℝ) ≤ (D.R.k : ℝ) - 1 := by linarith
    have h2 : 0 ≤ (D.R.f : ℝ) ^ 2 * ((D.R.k : ℝ) - 1) ^ 3 * L.sc.L ^ 2 / D.R.m := by positivity
    have hr0 : (0 : ℝ) ≤ D.R.r := by positivity
    nlinarith [mul_nonneg hr0 h2, mul_nonneg hr0 (sub_nonneg.mpr hf2')]

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MPowFiveMulFMulLLe
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem m_pow_five_mul_f_mul_L_le (s : Scale) (R : Ranks) (h : RankVal s R) :
    (R.m : ℝ) ^ 5 * R.f * s.L ≤ 128 * s.x ^ (9 / 2 + 9 * s.eps) := by
  have hn := h.n_le
  obtain ⟨-, ⟨-, hm⟩, -, -⟩ := h
  have hx1 := s.one_lt_alt
  have hx0 : 0 < s.x := by linarith
  have he := s.eps_pos
  have hm2 : (R.m : ℝ) ≤ 2 * s.x ^ (1 / 2 - s.eps / 16) := by
    refine hm.trans (le_of_eq ?_)
    have hd : s.delta1 = s.x ^ (-(s.eps / 8)) := rfl
    rw [hd, Real.sqrt_eq_rpow, ← Real.rpow_one_add' hx0.le (by linarith [s.eps_lt]), ← Real.rpow_mul hx0.le]
    congr 2; ring
  have hm5 : (R.m : ℝ) ^ 5 ≤ 32 * s.x ^ (5 / 2 - 5 * s.eps / 16) := by
    calc (R.m : ℝ) ^ 5 ≤ (2 * s.x ^ (1 / 2 - s.eps / 16)) ^ 5 := by gcongr
      _ = 32 * s.x ^ (5 / 2 - 5 * s.eps / 16) := by
        rw [mul_pow, ← Real.rpow_natCast (s.x ^ (1 / 2 - s.eps / 16)), ← Real.rpow_mul hx0.le]
        congr 1
        · norm_num
        · congr 1; push_cast; ring
  have hf : (R.f : ℝ) ≤ 4 * s.x ^ (2 + 8 * s.eps + s.eps / 100) := by
    simp only [Ranks.f]; push_cast; linarith
  have hL : s.L = s.x ^ s.eps := rfl
  have hL0 : 0 ≤ s.x ^ s.eps := by positivity
  calc (R.m : ℝ) ^ 5 * R.f * s.L
      ≤ (32 * s.x ^ (5 / 2 - 5 * s.eps / 16)) * (4 * s.x ^ (2 + 8 * s.eps + s.eps / 100)) * s.x ^ s.eps := by
        rw [hL]; gcongr
    _ = 128 * (s.x ^ (5 / 2 - 5 * s.eps / 16) * s.x ^ (2 + 8 * s.eps + s.eps / 100) * s.x ^ s.eps) := by ring
    _ ≤ 128 * s.x ^ (9 / 2 + 9 * s.eps) := by
        rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)) (by norm_num)

theorem exists_injective_words : ∀ eps CG CF : ℝ, 0 < eps → eps < 1 / 52 → 0 ≤ CG → 0 ≤ CF → ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks), s.eps = eps → x0 ≤ s.x → RankVal s R → ∃ c : Fin ⌈3 * Real.exp (CG * (R.m : ℝ) ^ 5 * R.f * s.L) ^ 2 * s.x ^ CF⌉₊ → (Fin (R.k - 2) → Bool), Function.Injective c ∧ 0 < ⌈3 * Real.exp (CG * (R.m : ℝ) ^ 5 * R.f * s.L) ^ 2 * s.x ^ CF⌉₊ := by
  intro eps CG CF he _ hG hF
  set K : ℝ := 2 * (2 + 256 * CG + CF) + 2 with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨K ^ (1 / eps), fun s R hs hx hR => ?_⟩
  have hx1 := s.one_lt_alt
  have hx0 : 0 < s.x := by linarith
  have hb := m_pow_five_mul_f_mul_L_le s R hR
  have hk := hR.2.2.1.1
  rw [hs] at hb hk
  have hKx : K ≤ s.x ^ eps := by
    calc K = (K ^ (1 / eps)) ^ eps := by
          rw [← Real.rpow_mul hK0, one_div_mul_cancel he.ne', Real.rpow_one]
      _ ≤ s.x ^ eps := by gcongr
  set X : ℝ := s.x ^ (9 / 2 + 9 * eps) with hX
  have hxX : s.x ≤ X := by
    calc s.x = s.x ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ X := Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
  have hX1 : 1 ≤ X := by linarith
  have hkX : K * X ≤ R.k := by
    refine le_trans ?_ hk
    have : s.x ^ (9 / 2 + 10 * eps) = s.x ^ eps * X := by
      rw [hX, ← Real.rpow_add hx0]; congr 1; ring
    rw [this]; gcongr
  have hk2 : 2 ≤ R.k := by have := R.m_add_three_le_k; omega
  have hlog : Real.log s.x ≤ X := by
    have := Real.log_le_sub_one_of_pos hx0; linarith
  have h3 : (3 : ℝ) ≤ Real.exp 2 := by have := Real.add_one_le_exp (2 : ℝ); linarith
  have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hA : CG * (R.m : ℝ) ^ 5 * R.f * s.L ≤ 128 * CG * X := by
    calc CG * (R.m : ℝ) ^ 5 * R.f * s.L = CG * ((R.m : ℝ) ^ 5 * R.f * s.L) := by ring
      _ ≤ CG * (128 * X) := by gcongr
      _ = _ := by ring
  have hFX : Real.log s.x * CF ≤ X * CF := by gcongr
  have hkc : ((R.k - 2 : ℕ) : ℝ) = (R.k : ℝ) - 2 := by rw [Nat.cast_sub hk2]; norm_num
  have hmain : 3 * Real.exp (CG * (R.m : ℝ) ^ 5 * R.f * s.L) ^ 2 * s.x ^ CF ≤ ((2 ^ (R.k - 2) : ℕ) : ℝ) := by
    calc 3 * Real.exp (CG * (R.m : ℝ) ^ 5 * R.f * s.L) ^ 2 * s.x ^ CF
        ≤ Real.exp 2 * Real.exp (128 * CG * X) ^ 2 * Real.exp (X * CF) := by
          rw [Real.rpow_def_of_pos hx0]; gcongr
      _ = Real.exp (2 + 256 * CG * X + X * CF) := by
          rw [sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (((R.k - 2 : ℕ) : ℝ) * Real.log 2) := by
          apply Real.exp_le_exp.2
          have h1 : 2 + 256 * CG * X + X * CF ≤ ((R.k - 2 : ℕ) : ℝ) * (1 / 2) := by
            rw [hkc]; rw [hK] at hkX; nlinarith
          refine h1.trans ?_
          gcongr
      _ = ((2 ^ (R.k - 2) : ℕ) : ℝ) := by
          rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]; push_cast; rfl
  have hle := Nat.ceil_le.2 hmain
  have hcard : Fintype.card (Fin ⌈3 * Real.exp (CG * (R.m : ℝ) ^ 5 * R.f * s.L) ^ 2 * s.x ^ CF⌉₊) ≤
      Fintype.card (Fin (R.k - 2) → Bool) := by
    simpa using hle
  obtain ⟨c⟩ := Function.Embedding.nonempty_of_card_le hcard
  exact ⟨c, c.injective, Nat.ceil_pos.2 (by positivity)⟩

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemDualSetOfMemSpan
section
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
open scoped TensorProduct

namespace GlobalTheory.DualFrame

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
theorem _root_.GlobalTheory.DualFrame.hform_eq_dot {A n : Type} [CommRing A] [Fintype n] (σ : A →+* A) (J : Matrix n n A)
    (x y : n → A) : _root_.Formalism.UG.hform σ J x y = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ y) := by
  simp [_root_.Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]


open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
theorem _root_.GlobalTheory.DualFrame.hform_mulVec {A n : Type} [CommRing A] [Fintype n] (σ : A →+* A) (J B : Matrix n n A)
    (u y : n → A) : _root_.Formalism.UG.hform σ J (B *ᵥ u) y = (fun i => σ (u i)) ⬝ᵥ ((_root_.Formalism.UG.cT σ B * J) *ᵥ y) := by
  rw [_root_.GlobalTheory.DualFrame.hform_eq_dot, ← mulVec_mulVec, _root_.Formalism.UG.cT,
    dotProduct_mulVec (fun i => σ (u i)) (B.map σ)ᵀ, vecMul_transpose]
  congr 1
  funext i
  rw [RingHom.map_mulVec]
  rfl


open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
theorem _root_.GlobalTheory.DualFrame.mem_dualSet_of_mem_span {E n : Type} [Field E] [NumberField E] [Fintype n] (σ : E →+* E)
    (J : Matrix n n E) (L : Submodule (𝓞 E) (n → E)) {y : n → E}
    (hy : y ∈ Submodule.span (𝓞 E) (_root_.Formalism.BasicNotions.dualSet σ J L)) : y ∈ _root_.Formalism.BasicNotions.dualSet σ J L := by
  induction hy using Submodule.span_induction with
  | mem z hz => exact hz
  | zero =>
    intro x _
    rw [_root_.GlobalTheory.DualFrame.hform_eq_dot, mulVec_zero, dotProduct_zero]
    exact zero_mem _
  | add a b _ _ ha hb =>
    intro x hx
    rw [_root_.GlobalTheory.DualFrame.hform_eq_dot, mulVec_add, dotProduct_add,
      ← _root_.GlobalTheory.DualFrame.hform_eq_dot, ← _root_.GlobalTheory.DualFrame.hform_eq_dot]
    exact add_mem (ha x hx) (hb x hx)
  | smul a z _ hz =>
    intro x hx
    have hsm : a • z = algebraMap (𝓞 E) E a • z := (algebraMap_smul E a z).symm
    rw [hsm, _root_.GlobalTheory.DualFrame.hform_eq_dot, mulVec_smul, dotProduct_smul,
      ← _root_.GlobalTheory.DualFrame.hform_eq_dot, smul_eq_mul]
    exact mul_mem ⟨a, rfl⟩ (hz x hx)

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
private theorem mulVec_mem_latticeCompletion_iff {F E : Type} [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) {k : ℕ}
    (L : Submodule (𝓞 E) (Fin k → E)) (P : GL (Fin k) E) (c : 𝓞 F) (hc : c ∉ v.asIdeal)
    (hint : ∀ x ∈ L, ∀ i, algebraMap F E c * (((P⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) *ᵥ x) i ∈
      (algebraMap (𝓞 E) E).range)
    (hcol : ∀ j, (fun i => algebraMap F E c * (P : Matrix (Fin k) (Fin k) E) i j) ∈ L)
    (y : Fin k → E ⊗[F] v.adicCompletion F) :
    (P : Matrix (Fin k) (Fin k) E).map (_root_.Formalism.UG.inclE (F := F) (v.adicCompletion F)) *ᵥ y ∈
        _root_.GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat v L ↔ ∀ i, y i ∈ _root_.Formalism.BasicNotions.intV E v := by
  obtain ⟨u, hu, huc⟩ := _root_.GlobalTheory.OverCompare.exists_intV_mul_inclE_eq_one (E := E) v c hc
  have hgen : ∀ x ∈ L, (fun i => _root_.Formalism.UG.inclE (F := F) (v.adicCompletion F) (x i)) ∈
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat v L := by
    intro x hx
    unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat _root_.Formalism.UG.latS
    exact Submodule.subset_span ⟨x, hx, rfl⟩
  have hsmul : ∀ s ∈ _root_.Formalism.BasicNotions.intV E v, ∀ z ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat v L,
      (fun i => s * z i) ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat v L :=
    fun s hs z hz => Submodule.smul_mem _ (⟨s, hs⟩ : _root_.Formalism.BasicNotions.intV E v) hz
  constructor
  · intro h
    have key : ∀ z ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat v L, ∀ i,
        (((P⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E).map
          (_root_.Formalism.UG.inclE (F := F) (v.adicCompletion F)) *ᵥ z) i ∈ _root_.Formalism.BasicNotions.intV E v := by
      intro z hz
      unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat _root_.Formalism.UG.latS at hz
      induction hz using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨x, hx, rfl⟩ := hw
        intro i
        obtain ⟨a, ha⟩ := hint x hx i
        have hmap := RingHom.map_mulVec (_root_.Formalism.UG.inclE (F := F) (E := E) (v.adicCompletion F))
          ((P⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) x i
        simp only [Function.comp_def] at hmap
        rw [← hmap]
        have : _root_.Formalism.UG.inclE (F := F) (v.adicCompletion F)
            ((((P⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) *ᵥ x) i) =
            u * _root_.Formalism.UG.inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E a) := by
          rw [ha, map_mul]
          linear_combination (-(_root_.Formalism.UG.inclE (F := F) (v.adicCompletion F)
            ((((P⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) *ᵥ x) i))) * huc
        rw [this]
        refine mul_mem hu ?_
        unfold _root_.Formalism.UG.inclE
        rw [Algebra.TensorProduct.includeLeftRingHom_apply]
        exact _root_.GlobalTheory.OverCompare.tmul_mem_intV a
      | zero =>
        intro i
        rw [mulVec_zero]
        exact zero_mem _
      | add a b _ _ ha hb =>
        intro i
        rw [mulVec_add]
        exact add_mem (ha i) (hb i)
      | smul s z _ hz =>
        intro i
        rw [mulVec_smul]
        exact mul_mem s.2 (hz i)
    intro i
    have hy : y = ((P⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E).map
        (_root_.Formalism.UG.inclE (F := F) (v.adicCompletion F)) *ᵥ
        ((P : Matrix (Fin k) (Fin k) E).map (_root_.Formalism.UG.inclE (F := F) (v.adicCompletion F)) *ᵥ y) := by
      rw [mulVec_mulVec, ← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _),
        one_mulVec]
    rw [hy]
    exact key _ h i
  · intro hy
    have hsum : (P : Matrix (Fin k) (Fin k) E).map (_root_.Formalism.UG.inclE (F := F) (v.adicCompletion F)) *ᵥ y =
        ∑ j, fun i => (y j * u) * _root_.Formalism.UG.inclE (F := F) (v.adicCompletion F)
          (algebraMap F E c * (P : Matrix (Fin k) (Fin k) E) i j) := by
      funext i
      simp only [mulVec, dotProduct, Matrix.map_apply, Finset.sum_apply, map_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      linear_combination (-(y j * _root_.Formalism.UG.inclE (F := F) (v.adicCompletion F)
        ((P : Matrix (Fin k) (Fin k) E) i j))) * huc
    rw [hsum]
    refine Submodule.sum_mem _ fun j _ => ?_
    exact hsmul _ (mul_mem (hy j) hu) _ (hgen _ (hcol j))


open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
theorem _root_.GlobalTheory.DualFrame.exists_dual_frames (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (k : ℕ) (J : Matrix (Fin k) (Fin k) E) (hJ : IsUnit J.det)
    (Λ : Submodule (𝓞 E) (Fin k → E)) (hfin : Module.Finite (𝓞 E) Λ)
    (hsp : Submodule.span E (Λ : Set (Fin k → E)) = ⊤) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ B C : GL (Fin k) (E ⊗[F] v.adicCompletion F),
      _root_.Formalism.UG.cT (_root_.Formalism.UG.sigR σ (v.adicCompletion F)) (B : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) *
        J.map (_root_.Formalism.UG.inclE (F := F) (v.adicCompletion F)) *
        (C : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) = 1 ∧
      (∀ y : Fin k → E ⊗[F] v.adicCompletion F,
        (B : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) *ᵥ y ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat v Λ ↔
          ∀ i, y i ∈ _root_.Formalism.BasicNotions.intV E v) ∧
      ∀ y : Fin k → E ⊗[F] v.adicCompletion F,
        (C : Matrix (Fin k) (Fin k) (E ⊗[F] v.adicCompletion F)) *ᵥ y ∈
          _root_.GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.locLat v (Submodule.span (𝓞 E) (_root_.Formalism.BasicNotions.dualSet (σ : E →+* E) J Λ)) ↔ ∀ i, y i ∈ _root_.Formalism.BasicNotions.intV E v := by
  obtain ⟨B₀, c, hc, hint, hcol⟩ := _root_.GlobalTheory.SemiLocalFrame.exists_frame_denominator F E k Λ hfin hsp v
  set σ' : E →+* E := (σ : E →+* E) with hσ'
  have hσc : σ' (algebraMap F E c) = algebraMap F E c := σ.commutes _
  have hdet : (_root_.Formalism.UG.cT σ' (B₀ : Matrix (Fin k) (Fin k) E) * J).det ≠ 0 := by
    rw [det_mul, _root_.Formalism.UG.cT, det_transpose,
      show ((B₀ : Matrix (Fin k) (Fin k) E).map σ').det = σ' (B₀ : Matrix (Fin k) (Fin k) E).det from
        (RingHom.map_det σ' _).symm]
    exact mul_ne_zero ((map_ne_zero σ').mpr (B₀.isUnit.map Matrix.detMonoidHom).ne_zero) hJ.ne_zero
  set M : GL (Fin k) E := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet with hM
  have hMcoe : (M : Matrix (Fin k) (Fin k) E) = _root_.Formalism.UG.cT σ' (B₀ : Matrix (Fin k) (Fin k) E) * J := rfl
  have hconj : ∀ e : E, _root_.Formalism.UG.sigR σ (v.adicCompletion F) (_root_.Formalism.UG.inclE (F := F) (v.adicCompletion F) e) =
      _root_.Formalism.UG.inclE (F := F) (v.adicCompletion F) (σ' e) := by
    intro e
    simp [_root_.Formalism.UG.sigR, _root_.Formalism.UG.inclE, hσ']
  refine ⟨Matrix.GeneralLinearGroup.map (_root_.Formalism.UG.inclE (F := F) (v.adicCompletion F)) B₀,
    Matrix.GeneralLinearGroup.map (_root_.Formalism.UG.inclE (F := F) (v.adicCompletion F)) M⁻¹, ?_, ?_, ?_⟩
  · change _root_.Formalism.UG.cT (_root_.Formalism.UG.sigR σ (v.adicCompletion F))
        ((B₀ : Matrix (Fin k) (Fin k) E).map (_root_.Formalism.UG.inclE (F := F) (v.adicCompletion F))) *
        J.map (_root_.Formalism.UG.inclE (F := F) (v.adicCompletion F)) *
        (((M⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E)).map (_root_.Formalism.UG.inclE (F := F) (v.adicCompletion F)) = 1
    have hT : _root_.Formalism.UG.cT (_root_.Formalism.UG.sigR σ (v.adicCompletion F))
        ((B₀ : Matrix (Fin k) (Fin k) E).map (_root_.Formalism.UG.inclE (F := F) (v.adicCompletion F))) =
        (_root_.Formalism.UG.cT σ' (B₀ : Matrix (Fin k) (Fin k) E)).map (_root_.Formalism.UG.inclE (F := F) (v.adicCompletion F)) := by
      simp only [_root_.Formalism.UG.cT, transpose_map, Matrix.map_map]
      congr 2
    rw [hT, ← Matrix.map_mul, ← Matrix.map_mul, ← hMcoe, Units.mul_inv,
      Matrix.map_one _ (map_zero _) (map_one _)]
  · exact mulVec_mem_latticeCompletion_iff v Λ B₀ c hc hint hcol
  · refine mulVec_mem_latticeCompletion_iff v _ M⁻¹ c hc ?_ ?_
    · intro y hy i
      have hyd := _root_.GlobalTheory.DualFrame.mem_dualSet_of_mem_span σ' J Λ hy
      have hx : (fun l => algebraMap F E c * (B₀ : Matrix (Fin k) (Fin k) E) l i) =
          (B₀ : Matrix (Fin k) (Fin k) E) *ᵥ Pi.single i (algebraMap F E c) := by
        funext l
        simp [mulVec_single, mul_comm]
      have hval := hyd _ (hcol i)
      rw [hx, _root_.GlobalTheory.DualFrame.hform_mulVec] at hval
      have hfun : (fun l => σ' ((Pi.single i (algebraMap F E c) : Fin k → E) l)) =
          (Pi.single i (algebraMap F E c) : Fin k → E) := by
        funext l
        by_cases hl : l = i
        · subst hl
          simp [hσc]
        · simp [hl]
      rw [hfun, single_dotProduct, ← hMcoe] at hval
      rwa [inv_inv]
    · intro j
      refine Submodule.subset_span ?_
      intro x hx
      set u := ((B₀⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) *ᵥ x with hu
      have hxu : x = (B₀ : Matrix (Fin k) (Fin k) E) *ᵥ u := by
        rw [hu, mulVec_mulVec, Units.mul_inv, one_mulVec]
      have hw : (fun i => algebraMap F E c * ((M⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) i j) =
          ((M⁻¹ : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) *ᵥ Pi.single j (algebraMap F E c) := by
        funext l
        simp [mulVec_single, mul_comm]
      obtain ⟨a, ha⟩ := hint x hx j
      rw [hxu, hw, _root_.GlobalTheory.DualFrame.hform_mulVec, ← hMcoe, mulVec_mulVec, Units.mul_inv, one_mulVec,
        dotProduct_single, ← hσc, ← map_mul, mul_comm, ← ha]
      exact ⟨⟨σ' a, (RingOfIntegers.isIntegral_coe a).map σ'.toIntAlgHom⟩, rfl⟩

end GlobalTheory.DualFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowAndImp
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem SzRow.and {P Q : FC → ∀ D : D7, SizeData₂ D → Prop} (hP : SzRow P) (hQ : SzRow Q) :
    SzRow (fun C D L => P C D L ∧ Q C D L) := by
  intro eps h0 h1 C hC
  obtain ⟨a1, ha1⟩ := hP eps h0 h1 C hC
  obtain ⟨b1, hb1⟩ := hQ eps h0 h1 C hC
  refine ⟨max a1 b1, fun cD hcD => ?_⟩
  obtain ⟨a2, ha2⟩ := ha1 cD (le_trans (le_max_left _ _) hcD)
  obtain ⟨b2, hb2⟩ := hb1 cD (le_trans (le_max_right _ _) hcD)
  refine ⟨max a2 b2, fun ch hch => ?_⟩
  obtain ⟨a3, ha3⟩ := ha2 ch (le_trans (le_max_left _ _) hch)
  obtain ⟨b3, hb3⟩ := hb2 ch (le_trans (le_max_right _ _) hch)
  refine ⟨max a3 b3, fun D L he hx hV => ⟨?_, ?_⟩⟩
  · exact ha3 D L he (le_trans (le_max_left _ _) hx) hV
  · exact hb3 D L he (le_trans (le_max_right _ _) hx) hV

theorem SzRow.imp {P Q : FC → ∀ D : D7, SizeData₂ D → Prop} (hP : SzRow P)
    (h : ∀ C cD ch D L, Std C → Val C cD ch L → P C D L → Q C D L) : SzRow Q := by
  intro eps h0 h1 C hC
  obtain ⟨a1, ha1⟩ := hP eps h0 h1 C hC
  refine ⟨a1, fun cD hcD => ?_⟩
  obtain ⟨a2, ha2⟩ := ha1 cD hcD
  refine ⟨a2, fun ch hch => ?_⟩
  obtain ⟨a3, ha3⟩ := ha2 ch hch
  exact ⟨a3, fun D L he hx hV => h C cD ch D L hC hV (ha3 D L he hx hV)⟩

theorem szRow_and_imp :
    (∀ P Q : FC → ∀ D : D7, SizeData₂ D → Prop, SzRow P → SzRow Q → SzRow (fun C D L => P C D L ∧ Q C D L)) ∧
    (∀ P Q : FC → ∀ D : D7, SizeData₂ D → Prop, SzRow P →
      (∀ C cD ch D L, Std C → Val C cD ch L → P C D L → Q C D L) → SzRow Q) :=
  ⟨fun _ _ hP hQ => hP.and hQ, fun _ _ hP h => hP.imp h⟩

end GlobalTheory.EX
end

