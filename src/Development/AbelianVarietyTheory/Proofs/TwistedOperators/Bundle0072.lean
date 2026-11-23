module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumSpherical
section
noncomputable section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {ϖ : L} {q N : ℕ}

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem det_mat_ne_zero {n : ℕ} (g : GU σ n) : (mat g).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp (g : GL (Fin n) L).isUnit).ne_zero

theorem constTerm (hF : FracExists) (hP : Pointwise) (hC : Count) (hS : SmallCorner) (hG : GenFun)
    (hU : IsUnramInv ϖ σ q) {a : ℤ} {g₀ : GU σ N} {m : GU σ (N + 2)} (hm : IsLeviElt ϖ a g₀ m) (X : ℂ)
    (hX : ‖(q : ℂ) ^ (N + 1) * X‖ < 1) :
    HasSum (fun c : RadQuot σ N => X ^ len (mat (m * (c.out : radQ σ N).1)))
      ((q : ℂ) ^ (2 * len (mat g₀) + (2 * N + 2) * a.toNat) * X ^ (a.natAbs + len (mat g₀)) * jFac q N X) := by
  have hv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
  have hq : 1 ≤ q := le_trans (by norm_num) hU.2.2.2.2.2.1
  obtain ⟨U, V, C, hfr, hdet⟩ := hF L ϖ N hv (mat g₀) (det_mat_ne_zero g₀)
  have hPt := hP L ϖ σ q N hU a g₀ m hm U V C (len (mat g₀)) hfr hdet
  have hcard : ∀ j : ℕ, Nat.card {c : RadQuot σ N //
      len (mat (m * (c.out : radQ σ N).1)) ≤ a.natAbs + len (mat g₀) + j} =
      q ^ (2 * len (mat g₀) + (2 * N + 2) * a.toNat) * q ^ (2 * N * (j / 2) + j) := by
    intro j
    have hiff : ∀ c : RadQuot σ N, len (mat (m * (c.out : radQ σ N).1)) ≤ a.natAbs + len (mat g₀) + j ↔
        Small ϖ (a.toNat + j / 2) (2 * a.toNat + j) C (C * V * mat g₀) (c.out : radQ σ N).1 :=
      fun c => (hPt _ (c.out : radQ σ N).2).2 j
    rw [Nat.card_congr (Equiv.subtypeEquivRight hiff)]
    rw [hC L ϖ σ q N hU C (C * V * mat g₀) (len (mat g₀)) (a.toNat + j / 2) (2 * a.toNat + j) hfr.2.2.1 hdet
      (fun r hr => hS L ϖ σ q N hU g₀ U V C hfr _ _ r (by omega) hr) ?_]
    · rw [← pow_add]; congr 1; generalize j / 2 = t; ring
    · intro u hu k hk hkK hsm
      have hlen : len (mat (m * (u * k))) = len (mat (m * u)) := by
        have h := len_mat_mul (KU σ (N + 2)).one_mem hkK (m * u)
        rwa [one_mul, mul_assoc] at h
      refine ((hPt _ (mul_mem hu hk)).2 j).mp ?_
      rw [hlen]
      exact ((hPt u hu).2 j).mpr hsm
  have key := hG (RadQuot σ N) (fun c => len (mat (m * (c.out : radQ σ N).1))) (a.natAbs + len (mat g₀))
    (q ^ (2 * len (mat g₀) + (2 * N + 2) * a.toNat)) q N X (Nat.one_le_pow _ _ hq) hq
    (fun c => (hPt _ (c.out : radQ σ N).2).1) hcard hX
  push_cast at key
  exact key

theorem bijective_cells (hS : CosetSurj) (hI : CosetInj) (hU : IsUnramInv ϖ σ q)
    (m : ℤ → GU σ N ⧸ KU σ N → GU σ (N + 2)) (hm : ∀ a y, IsLeviElt ϖ a y.out (m a y)) :
    Function.Bijective fun p : (ℤ × (GU σ N ⧸ KU σ N)) × RadQuot σ N =>
      (QuotientGroup.mk (m p.1.1 p.1.2 * (p.2.out : radQ σ N).1) : GU σ (N + 2) ⧸ KU σ (N + 2)) := by
  constructor
  · rintro ⟨⟨a, y⟩, c⟩ ⟨⟨a', y'⟩, c'⟩ h
    have h' := QuotientGroup.eq.mp h
    obtain ⟨rfl, hy⟩ := hI L ϖ σ q N hU a a' y.out y'.out (m a y) (m a' y') (hm a y) (hm a' y')
      _ (c.out : radQ σ N).2 _ (c'.out : radQ σ N).2 h'
    have hyy : y = y' := by
      rw [← QuotientGroup.out_eq' y, ← QuotientGroup.out_eq' y']
      exact QuotientGroup.eq.mpr hy
    subst hyy
    have hc : c = c' := by
      rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c']
      apply QuotientGroup.eq.mpr
      rw [Subgroup.mem_subgroupOf]
      simpa [mul_assoc] using h'
    rw [hc]
  · intro z
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨a, y, hay⟩ := hS L ϖ σ q N hU g
    obtain ⟨u, hu, k, hk, rfl⟩ := hay (m a y) (hm a y)
    refine ⟨((a, y), (QuotientGroup.mk ⟨u, hu⟩ : RadQuot σ N)), ?_⟩
    dsimp only
    apply QuotientGroup.eq.mpr
    have h1 := QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk ⟨u, hu⟩ : RadQuot σ N))
    rw [Subgroup.mem_subgroupOf] at h1
    have e : (m a y * ((QuotientGroup.mk ⟨u, hu⟩ : RadQuot σ N).out : radQ σ N).1)⁻¹ * (m a y * u * k) =
        (((QuotientGroup.mk ⟨u, hu⟩ : RadQuot σ N).out)⁻¹ * ⟨u, hu⟩ : radQ σ N).1 * k := by
      simp [mul_assoc]
    rw [e]
    exact mul_mem h1 hk

theorem zVal_succ (q N : ℕ) (X y : ℂ) {r : ℕ} (α : Fin (r + 1) → ℂ) :
    zVal q (N + 2) X y α = (1 - X) * (1 + q * X) * ((1 - y * α 0)⁻¹ * (1 - y / α 0)⁻¹) *
      zVal q N ((q : ℂ) ^ 2 * X) y (Fin.tail α) := by
  have hp : ∏ j ∈ Finset.range (N + 2), (1 - (-(q : ℂ)) ^ j * X) =
      (1 - X) * (1 + q * X) * ∏ j ∈ Finset.range N, (1 - (-(q : ℂ)) ^ j * ((q : ℂ) ^ 2 * X)) := by
    rw [Finset.prod_range_succ', Finset.prod_range_succ']
    have h : ∀ j ∈ Finset.range N,
        (1 - (-(q : ℂ)) ^ (j + 1 + 1) * X) = (1 - (-(q : ℂ)) ^ j * ((q : ℂ) ^ 2 * X)) := by
      intro j _; ring
    rw [Finset.prod_congr rfl h]; ring
  have ho : Odd (N + 2) ↔ Odd N := by rw [Nat.odd_add]; simp
  unfold zVal
  rw [hp, Fin.prod_univ_succ, if_congr ho rfl rfl]
  simp only [Fin.tail]
  ring

theorem hasSum_small (hR : SmallRank) (hU : IsUnramInv ϖ σ q) {n : ℕ} (hn : n ≤ 1) (F : GU σ n → ℂ)
    (hF : ∀ k ∈ KU σ n, F k = 1) : HasSum (fun x : GU σ n ⧸ KU σ n => F x.out) 1 := by
  have hK : ∀ g : GU σ n, g ∈ KU σ n := fun g => hR L ϖ σ q n hU hn g
  have h1 : (fun x : GU σ n ⧸ KU σ n => F x.out) = fun _ => 1 := funext fun x => hF _ (hK _)
  rw [h1]
  refine hasSum_single (f := fun _ : GU σ n ⧸ KU σ n => (1 : ℂ)) (QuotientGroup.mk 1) fun b hb => ?_
  exfalso; apply hb
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective b
  exact QuotientGroup.eq.mpr (hK _)

theorem len_of_mem {n : ℕ} {k : GU σ n} (hk : k ∈ KU σ n) : len (mat k) = 0 := by
  apply HasLen.len_eq
  apply hasLen_of_isInt
  intro i j
  rw [KU, Subgroup.mem_subgroupOf] at hk
  unfold intPts at hk
  obtain ⟨A, hA⟩ := (Subgroup.mem_inf.mp hk).2
  show (((k : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ intL L
  rw [← hA]
  exact ((A : Matrix (Fin n) (Fin n) (intL L)) i j).2

private lemma ordL_one_twisted_operators : ordL (1 : L) = 0 := by
  have h : Valued.v (1 : L) ≠ 0 := by simp
  have hu : WithZero.unzero h = 1 := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, map_one, WithZero.coe_one]
  unfold ordL
  rw [dite_eq_right h, hu]
  simp

private lemma chiDeltaU_one' {n m : ℕ} (α : Fin m → ℂ) : chiDeltaU (σ := σ) (n := n) q α 1 = 1 := by
  unfold chiDeltaU
  refine Finset.prod_eq_one fun i _ => ?_
  split_ifs
  · simp [ordL_one_twisted_operators]
  · rfl

private lemma isBorelU_one' {n : ℕ} : IsBorelU (1 : GU σ n) := by
  intro i j h
  simp [Matrix.one_apply_ne h.ne']

private lemma isSphericalU_apply_mul_of_mem_KU {n m : ℕ} {α : Fin m → ℂ} {φ : GU σ n → ℂ} (hφ : IsSphericalU q α φ) (g k : GU σ n)
    (hk : k ∈ KU σ n) : φ (g * k) = φ g := by
  have h := hφ 1 g k isBorelU_one' hk
  rwa [one_mul, chiDeltaU_one', one_mul] at h

private lemma exists_mem_KU_out_mk_eq_mul {n : ℕ} (g : GU σ n) :
    ∃ k ∈ KU σ n, (QuotientGroup.mk g : GU σ n ⧸ KU σ n).out = g * k := by
  refine ⟨g⁻¹ * (QuotientGroup.mk g : GU σ n ⧸ KU σ n).out, ?_, (mul_inv_cancel_left _ _).symm⟩
  have h := QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk g : GU σ n ⧸ KU σ n))
  simpa [_root_.mul_inv_rev] using inv_mem h

theorem hasSum_spherical [CompleteSpace L] (hF : FracExists) (hP : Pointwise) (hC : Count) (hS : SmallCorner)
    (hG : GenFun) (hSu : CosetSurj) (hI : CosetInj) (hL : LeviExists) (hT : SphTrans) (hR : SmallRank) (hSt : Step)
    (hU : IsUnramInv ϖ σ q) (r : ℕ) : ∀ (n : ℕ), 2 * r ≤ n → n ≤ 2 * r + 1 → ∀ (α : Fin r → ℂ) (X y : ℂ)
      (φ : GU σ n → ℂ), (∀ i, α i ≠ 0) → y * q = X * (q : ℂ) ^ n → ‖y‖ < 1 →
      (∀ i, ‖y‖ * ‖α i‖ < 1 ∧ ‖y‖ * ‖α i‖⁻¹ < 1) → IsSphericalU q α φ → φ 1 = 1 →
      HasSum (fun x : GU σ n ⧸ KU σ n => X ^ len (mat x.out) * φ x.out) (zVal q n X y α) := by
  have hq2 : 2 ≤ q := hU.2.2.2.2.2.1
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  induction r with
  | zero =>
    intro n hn0 hn1 α X y φ _ hyX hy _ hφ h1
    have hn : n ≤ 1 := by omega
    have hK : ∀ g : GU σ n, g ∈ KU σ n := fun g => hR L ϖ σ q n hU hn g
    have hφk : ∀ g : GU σ n, φ g = 1 := by
      intro g
      have h := isSphericalU_apply_mul_of_mem_KU hφ 1 g (hK g)
      rwa [one_mul, h1] at h
    have hsum := hasSum_small hR hU hn (fun g => X ^ len (mat g) * φ g)
      (fun k hk => by rw [len_of_mem hk, hφk, pow_zero, one_mul])
    convert hsum using 1
    interval_cases n
    · simp [zVal]
    · have hyx : y = X := by
        apply mul_right_cancel₀ hq0
        rw [hyX]; ring
      subst hyx
      have hy1 : (1 : ℂ) - y ≠ 0 := by
        intro h
        have h' : y = 1 := by linear_combination -h
        rw [h'] at hy; simp at hy
      simp [zVal, hy1]
  | succ r ih =>
    intro n hn0 hn1 α X y φ hα hyX hy hαy hφ h1
    obtain ⟨N, rfl⟩ : ∃ N, n = N + 2 := ⟨n - 2, by omega⟩
    obtain ⟨φ₀, hφ₀, hφ₀1, -⟩ := Formalism.UG.Final.SphericalExistsU L ϖ σ q N r hU (by omega) (by omega)
      (Fin.tail α) (fun i => hα _)
    have hZ := ih N (by omega) (by omega) (Fin.tail α) ((q : ℂ) ^ 2 * X) y φ₀ (fun i => hα _)
      (by rw [hyX]; ring) hy (fun i => hαy _) hφ₀ hφ₀1
    have hy' : y = (q : ℂ) ^ (N + 1) * X := by
      apply mul_right_cancel₀ hq0
      rw [hyX]; ring
    choose m hm using fun (a : ℤ) (b : GU σ N ⧸ KU σ N) => hL L ϖ σ q N hU a b.out
    have hstep := hSt (GU σ N ⧸ KU σ N) (RadQuot σ N) q N
      (fun a b c => len (mat (m a b * (c.out : radQ σ N).1))) (fun b => len (mat b.out)) (fun b => φ₀ b.out)
      (α 0) X y (zVal q N ((q : ℂ) ^ 2 * X) y (Fin.tail α))
      (by omega) (hα 0) hy' hy (hαy 0).1 (hαy 0).2
      (fun X' hX' a b => constTerm hF hP hC hS hG hU (hm a b) X' hX') hZ
    rw [zVal_succ, ← (Equiv.ofBijective _ (bijective_cells hSu hI hU m hm)).hasSum_iff]
    convert hstep using 1
    funext p
    obtain ⟨⟨a, b⟩, c⟩ := p
    simp only [Function.comp_apply, Equiv.ofBijective_apply]
    obtain ⟨k, hk, hout⟩ := exists_mem_KU_out_mk_eq_mul (m a b * (c.out : radQ σ N).1)
    have hlen := len_mat_mul (KU σ (N + 2)).one_mem hk (m a b * (c.out : radQ σ N).1)
    rw [one_mul] at hlen
    rw [hout, isSphericalU_apply_mul_of_mem_KU hφ _ _ hk, hlen,
      hT L ϖ σ q N r hU (by omega) α φ φ₀ hα hφ h1 hφ₀ hφ₀1 a b.out (m a b) (hm a b) _ (c.out : radQ σ N).2]

end GlobalTheory.InertZeta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralRightInvariantEqSumOpenSubgroupCosets
section
open GlobalTheory.InertZeta

open MeasureTheory Pointwise

namespace GlobalTheory.InertZeta

theorem cosetIntegral_holds : CosetIntegral := by
  intro G _ _ _ _ _ μ _ K hK hμK F Z hF hZ
  classical
  set f : G ⧸ K → ℂ := fun x => F x.out with hf
  let A : G ⧸ K → Set G := fun x => QuotientGroup.mk ⁻¹' {x}
  have hA : ∀ x, A x = x.out • (K : Set G) := by
    intro x; ext g
    simp only [A, Set.mem_preimage, Set.mem_singleton_iff, mem_leftCoset_iff]
    conv_lhs => rw [← QuotientGroup.out_eq' x]
    rw [eq_comm, QuotientGroup.eq]
    rfl
  have hAm : ∀ x, MeasurableSet (A x) := fun x => by
    rw [hA]; exact (hK.smul x.out).measurableSet
  have hAμ : ∀ x, μ (A x) = 1 := fun x => by rw [hA, measure_smul]; exact hμK
  have hconst : ∀ x, ∀ g ∈ A x, F g = f x := by
    intro x g hg
    rw [hA, mem_leftCoset_iff] at hg
    have := hF x.out _ hg
    rwa [mul_inv_cancel_left] at this
  have hself : ∀ g : G, g ∈ A (QuotientGroup.mk g) := fun g => rfl
  have hdisj : Pairwise (Function.onFun Disjoint A) := by
    intro x y hxy
    exact (Set.disjoint_singleton.mpr hxy).preimage _
  set S := Function.support f with hSdef
  have hS : S.Countable := hZ.summable.countable_support
  haveI : Countable S := hS.to_subtype
  let B : S → Set G := fun i => A i.1
  have hBint : ∀ i : S, ∫ g in B i, F g ∂μ = f i.1 := by
    intro i
    rw [setIntegral_congr_fun (hAm i.1) (fun g hg => hconst i.1 g hg), setIntegral_const]
    simp [Measure.real, hAμ]
  have hBnorm : ∀ i : S, ∫ g in B i, ‖F g‖ ∂μ = ‖f i.1‖ := by
    intro i
    rw [setIntegral_congr_fun (g := fun _ => ‖f i.1‖) (hAm i.1) (fun g hg => by simp only [hconst i.1 g hg]), setIntegral_const]
    simp [Measure.real, hAμ]
  have hBon : ∀ i : S, IntegrableOn F (B i) μ := by
    intro i
    have h1 : IntegrableOn (fun _ : G => f i.1) (B i) μ :=
      integrableOn_const (by simp [B, hAμ]) (by simp)
    exact h1.congr_fun (fun g hg => (hconst i.1 g hg).symm) (hAm i.1)
  have hsumm : Summable fun i : S => ∫ g in B i, ‖F g‖ ∂μ := by
    simp only [hBnorm]
    exact (summable_norm_iff.mpr hZ.summable).subtype (fun x => x ∈ S)
  have hU : IntegrableOn F (Set.iUnion B) μ :=
    integrableOn_iUnion_of_summable_integral_norm hBon hsumm
  have hzero : ∀ g ∉ Set.iUnion B, F g = 0 := by
    intro g hg
    have hnot : (QuotientGroup.mk g : G ⧸ K) ∉ S := by
      intro hm
      exact hg (Set.mem_iUnion.mpr ⟨⟨_, hm⟩, hself g⟩)
    rw [hconst _ g (hself g)]
    simpa [hSdef] using hnot
  have hInt : Integrable F μ := hU.integrable_of_forall_notMem_eq_zero hzero
  refine ⟨hInt, ?_⟩
  have h1 := hasSum_integral_iUnion (fun i : S => hAm i.1) (fun i j hij => hdisj (fun h => hij (Subtype.ext h))) hU
  have hfun : (fun i : S => ∫ g in B i, F g ∂μ) = fun i => f i.1 := funext hBint
  rw [hfun] at h1
  have h2 : HasSum (fun i : S => f i.1) Z :=
    (hasSum_subtype_iff_of_support_subset (s := S) subset_rfl).mpr hZ
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  exact h1.unique h2

end GlobalTheory.InertZeta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeAddVectorDetValuation
section
noncomputable section

open Matrix

namespace GlobalTheory.InertZeta

theorem smul_mem_integral_submodule_of_valuation_le_one {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
    {P : Submodule (Formalism.UG.intL L) (Fin n → L)} {x : L} (hx : Valued.v x ≤ 1) {w : Fin n → L} (hw : w ∈ P) :
    x • w ∈ P :=
  P.smul_mem (⟨x, hx⟩ : Formalism.UG.intL L) hw

theorem addVec : AddVec := by
  intro L _ _ n M k ρ e hM hρ he
  rcases he with rfl | ⟨i₀, hi₀⟩
  · refine ⟨M, by simpa using hM, ?_⟩
    refine sup_eq_left.2 ((Submodule.span_singleton_le_iff_mem _ _).2 (mem_rowLat.2 ⟨ρ, fun i => ?_, rfl⟩))
    exact (by simpa using hρ i : Valued.v (ρ i) ≤ 1)
  · have h0 : ρ i₀ ≠ 0 := fun h => by rw [h, map_zero] at hi₀; exact WithZero.exp_ne_zero hi₀.symm
    refine ⟨M.updateRow i₀ (ρ ᵥ* M), ?_, ?_⟩
    · rw [Matrix.vecMul_eq_sum, Matrix.det_updateRow_sum, smul_eq_mul, map_mul, hi₀, hM, ← WithZero.exp_add, add_comm]
    · apply le_antisymm
      · refine sup_le (rowLat_le.2 fun i => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 ?_)
        · by_cases hi : i = i₀
          · subst hi
            have hs : ρ ᵥ* M = ρ i • M i + ∑ j ∈ Finset.univ.erase i, ρ j • M j := by
              rw [Matrix.vecMul_eq_sum]; exact (Finset.add_sum_erase _ (fun j => ρ j • M j) (Finset.mem_univ _)).symm
            have : M i = (ρ i)⁻¹ • (M.updateRow i (ρ ᵥ* M)) i -
                ∑ j ∈ Finset.univ.erase i, ((ρ i)⁻¹ * ρ j) • (M.updateRow i (ρ ᵥ* M)) j := by
              rw [Matrix.updateRow_self, hs, smul_add, smul_smul, inv_mul_cancel₀ h0, one_smul, Finset.smul_sum]
              rw [add_sub_assoc, ← Finset.sum_sub_distrib]
              rw [Finset.sum_eq_zero, add_zero]
              intro j hj
              rw [Matrix.updateRow_ne (Finset.ne_of_mem_erase hj), smul_smul, sub_self]
            rw [this]
            have hv : Valued.v (ρ i)⁻¹ = WithZero.exp (-(e : ℤ)) := by rw [map_inv₀, hi₀, WithZero.exp_neg]
            refine Submodule.sub_mem _ (smul_mem_integral_submodule_of_valuation_le_one ?_ (row_mem_rowLat _ _)) (Submodule.sum_mem _ fun j _ => smul_mem_integral_submodule_of_valuation_le_one ?_ (row_mem_rowLat _ _))
            · rw [hv, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega
            · rw [map_mul, hv]
              calc WithZero.exp (-(e : ℤ)) * Valued.v (ρ j) ≤ WithZero.exp (-(e : ℤ)) * WithZero.exp (e : ℤ) :=
                    mul_le_mul' le_rfl (hρ j)
                _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
          · have := row_mem_rowLat (M.updateRow i₀ (ρ ᵥ* M)) i
            rwa [Matrix.updateRow_ne hi] at this
        · have := row_mem_rowLat (M.updateRow i₀ (ρ ᵥ* M)) i₀
          rwa [Matrix.updateRow_self] at this
      · refine rowLat_le.2 fun i => ?_
        by_cases hi : i = i₀
        · subst hi
          rw [Matrix.updateRow_self]
          exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
        · rw [Matrix.updateRow_ne hi]
          exact Submodule.mem_sup_left (row_mem_rowLat _ _)

end GlobalTheory.InertZeta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LengthCountGeneratingSeriesFormula
section
open GlobalTheory.InertZeta

noncomputable section

namespace GlobalTheory.InertZeta

theorem genFun_counts_hasSum {𝕜 : Type} [NormedField 𝕜] [CompleteSpace 𝕜] (c q N : ℕ) (x : 𝕜)
    (hx : ‖(q : 𝕜) ^ (N + 1) * x‖ < 1) :
    HasSum (fun j : ℕ => ((c * q ^ (2 * N * (j / 2) + j) : ℕ) : 𝕜) * x ^ j)
      (c * (1 + q * x) / (1 - ((q : 𝕜) ^ (N + 1) * x) ^ 2)) := by
  set y := (q : 𝕜) ^ (N + 1) * x with hy
  have hy2 : ‖y ^ 2‖ < 1 := by
    rw [norm_pow]; nlinarith [norm_nonneg y]
  have hg := hasSum_geometric_of_norm_lt_one hy2
  have fe : (fun k : ℕ => ((c * q ^ (2 * N * ((2 * k) / 2) + 2 * k) : ℕ) : 𝕜) * x ^ (2 * k)) =
      fun k => (c : 𝕜) * (y ^ 2) ^ k := by
    funext k
    rw [Nat.mul_div_cancel_left k (by norm_num : 0 < 2)]
    push_cast
    rw [hy]; ring
  have fo : (fun k : ℕ => ((c * q ^ (2 * N * ((2 * k + 1) / 2) + (2 * k + 1)) : ℕ) : 𝕜) * x ^ (2 * k + 1)) =
      fun k => ((c : 𝕜) * q * x) * (y ^ 2) ^ k := by
    funext k
    rw [show (2 * k + 1) / 2 = k by omega]
    push_cast
    rw [hy]; ring
  have he := hg.mul_left (c : 𝕜)
  have ho := hg.mul_left ((c : 𝕜) * q * x)
  rw [← fe] at he
  rw [← fo] at ho
  have := HasSum.even_add_odd (f := fun j : ℕ => ((c * q ^ (2 * N * (j / 2) + j) : ℕ) : 𝕜) * x ^ j) he ho
  rw [show (c : 𝕜) * (1 + q * x) / (1 - y ^ 2) = c * (1 - y ^ 2)⁻¹ + c * q * x * (1 - y ^ 2)⁻¹ by
    rw [div_eq_mul_inv]; ring]
  exact this

theorem genFun_diff_hasSum {𝕜 : Type} [NormedField 𝕜] (C d : ℕ → ℕ) (x S : 𝕜)
    (h0 : d 0 = C 0) (hs : ∀ j, C (j + 1) = C j + d (j + 1))
    (hA : HasSum (fun j => (C j : 𝕜) * x ^ j) S) :
    HasSum (fun j => (d j : 𝕜) * x ^ j) ((1 - x) * S) := by
  let h : ℕ → 𝕜 := fun j => if j = 0 then 0 else (C (j - 1) : 𝕜) * x ^ j
  have hsh : (fun n => h (n + 1)) = fun n => x * ((C n : 𝕜) * x ^ n) := by
    funext n
    simp only [h, Nat.add_sub_cancel, if_neg (Nat.succ_ne_zero n)]
    ring
  have h1 : HasSum (fun n => h (n + 1)) (x * S) := by rw [hsh]; exact hA.mul_left x
  have hh : HasSum h (x * S) := by
    have := (hasSum_nat_add_iff (f := h) 1).1 h1
    simpa [h] using this
  have hd : (fun j => (d j : 𝕜) * x ^ j) = fun j => (C j : 𝕜) * x ^ j - h j := by
    funext j
    rcases j with _ | j
    · simp [h, h0]
    · simp only [h, if_neg (Nat.succ_ne_zero j), Nat.add_sub_cancel, hs j]
      push_cast; ring
  rw [hd, show (1 - x) * S = S - x * S by ring]
  exact hA.sub hh

theorem genFun_fibre_hasSum {ι 𝕜 : Type} [NormedField 𝕜] (f : ι → ℕ) (l j : ℕ) (x : 𝕜)
    (hfin : Set.Finite {i | f i - l = j}) (hl : ∀ i, l ≤ f i) :
    HasSum (fun y : {i // f i - l = j} => x ^ f y.1) ((Set.ncard {i | f i - l = j} : 𝕜) * x ^ (l + j)) := by
  haveI : Finite {i // f i - l = j} := hfin.to_subtype
  haveI : Fintype {i // f i - l = j} := Fintype.ofFinite _
  have hc : ∀ y : {i // f i - l = j}, x ^ f y.1 = x ^ (l + j) := fun y => by
    have := hl y.1; have := y.2
    rw [show f y.1 = l + j by omega]
  have e : Nat.card {i // f i - l = j} = Set.ncard {i | f i - l = j} := Nat.card_coe_set_eq {i : ι | f i - l = j}
  have h := hasSum_fintype (fun y : {i // f i - l = j} => x ^ f y.1)
  rw [Finset.sum_congr rfl (fun y _ => hc y), Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card, e] at h
  exact h

theorem genFun_holds : GenFun := by
  intro ι f l c q N X hc hq hl hcard hX
  let C : ℕ → ℕ := fun j => c * q ^ (2 * N * (j / 2) + j)
  let g : ι → ℕ := fun i => f i - l
  have hCpos : ∀ j, C j ≠ 0 := fun j =>
    Nat.mul_ne_zero (by omega) (pow_ne_zero _ (by omega))
  have hle : ∀ j, {i | g i ≤ j} = {i | f i ≤ l + j} := fun j => by
    ext i; simp only [Set.mem_setOf_eq, g]; have := hl i; omega
  have hcum : ∀ j, Set.ncard {i | g i ≤ j} = C j := fun j => by
    rw [hle, ← Nat.card_coe_set_eq]; exact hcard j
  have hfin : ∀ j, Set.Finite {i | g i ≤ j} := fun j => by
    apply Set.finite_of_ncard_ne_zero; rw [hcum]; exact hCpos j
  have hfin' : ∀ j, Set.Finite {i | f i - l = j} := fun j =>
    (hfin j).subset fun i hi => by simp only [Set.mem_setOf_eq, g] at hi ⊢; omega
  let d : ℕ → ℕ := fun j => Set.ncard {i | f i - l = j}
  have h0 : d 0 = C 0 := by
    rw [← hcum 0]
    show Set.ncard {i | f i - l = 0} = _
    congr 1; ext i; simp only [Set.mem_setOf_eq, g]; omega
  have hs : ∀ j, C (j + 1) = C j + d (j + 1) := fun j => by
    have hdis : Disjoint {i | g i ≤ j} {i | f i - l = j + 1} :=
      Set.disjoint_left.2 fun i h1 h2 => by simp only [Set.mem_setOf_eq, g] at h1 h2; omega
    have hun : {i | g i ≤ j + 1} = {i | g i ≤ j} ∪ {i | f i - l = j + 1} := by
      ext i; simp only [Set.mem_setOf_eq, Set.mem_union, g]; omega
    rw [← hcum, ← hcum, hun, Set.ncard_union_eq hdis (hfin j) (hfin' (j + 1))]
  let e := Equiv.sigmaFiberEquiv g
  have hr : ‖(q : ℝ) ^ (N + 1) * ‖X‖‖ < 1 := by
    rw [norm_mul, norm_pow, Real.norm_natCast, norm_norm]
    rwa [norm_mul, norm_pow, Complex.norm_natCast] at hX
  have hRB := (genFun_diff_hasSum C d ‖X‖ _ h0 hs (genFun_counts_hasSum c q N ‖X‖ hr)).mul_left (‖X‖ ^ l)
  have hsumR : Summable (fun i => ‖X‖ ^ f i) := by
    rw [← e.summable_iff]
    refine (summable_sigma_of_nonneg (f := (fun i => ‖X‖ ^ f i) ∘ e) (fun _ => pow_nonneg (norm_nonneg _) _)).2 ⟨fun j => (genFun_fibre_hasSum f l j ‖X‖ (hfin' j) hl).summable, ?_⟩
    refine hRB.summable.congr fun j => ?_
    have ht : ∑' (y : {x // g x = j}), ((fun i => ‖X‖ ^ f i) ∘ e) ⟨j, y⟩ = (d j : ℝ) * ‖X‖ ^ (l + j) :=
      (genFun_fibre_hasSum f l j ‖X‖ (hfin' j) hl).tsum_eq
    rw [ht, pow_add]
    ring
  have hsumC : Summable (fun i => X ^ f i) := Summable.of_norm (by simpa [norm_pow] using hsumR)
  have hB := (genFun_diff_hasSum C d X _ h0 hs (genFun_counts_hasSum c q N X hX)).mul_left (X ^ l)
  have hBC : HasSum (fun j => (d j : ℂ) * X ^ (l + j)) (c * X ^ l * jFac q N X) := by
    have e1 : (fun j => (d j : ℂ) * X ^ (l + j)) = fun j => X ^ l * ((d j : ℂ) * X ^ j) := by
      funext j; rw [pow_add]; ring
    rw [e1, show (c : ℂ) * X ^ l * jFac q N X =
      X ^ l * ((1 - X) * (c * (1 + q * X) / (1 - ((q : ℂ) ^ (N + 1) * X) ^ 2))) by unfold jFac; ring]
    exact hB
  have hsig := HasSum.sigma_of_hasSum (f := (fun i => X ^ f i) ∘ e) hBC
    (fun j => genFun_fibre_hasSum f l j X (hfin' j) hl) (e.summable_iff.2 hsumC)
  exact e.hasSum_iff.1 hsig

end GlobalTheory.InertZeta
end
end

