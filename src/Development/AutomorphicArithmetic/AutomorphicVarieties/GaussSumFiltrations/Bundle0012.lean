module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.DualLatticeIndexEqDiscrPowMulDetPow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.GaussSumBound

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsIsHolAdelicLiftOfEvenWeightSystem
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

theorem lift_isHol : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ), Even k →
    ∀ (Ψ : GL (Fin 2) (Af F) → Hn F → ℂ), Sys k Ψ → ∃ φ : TR.Sm F 2, IsLift k Ψ φ.1 ∧ IsHol k (fun _ => 0) 1 φ := by
  intro F _ _ _ k hk Ψ hΨ
  obtain ⟨φ₀, hL, hR, hZ⟩ := GlobalTheory.T.exists_adelic_lift_of_hilbert_system F k hk Ψ hΨ
  obtain ⟨hsm, hlie⟩ := GlobalTheory.T.adelic_lift_mem_smooth_killed_by_lowering F k Ψ φ₀ hΨ.hol hL
  let φ : TR.Sm F 2 := ⟨φ₀, hsm⟩
  have hfix : ∀ u ∈ KLev F 2 1, TR.finRep F 2 u φ = φ := fun u hu =>
    Subtype.ext (funext fun g => hR u hu g)
  have hlev : IsOpen {u | TR.finRep F 2 u φ = φ} := by
    let H : Subgroup (GL (Fin 2) (Af F)) :=
      { carrier := {u | TR.finRep F 2 u φ = φ}
        one_mem' := by simp
        mul_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq] at ha hb ⊢
          rw [map_mul, Module.End.mul_apply, hb, ha]
        inv_mem' := fun {a} ha => by
          simp only [Set.mem_setOf_eq] at ha ⊢
          conv_lhs => rw [← ha]
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
    exact Subgroup.isOpen_mono (H₁ := KLev F 2 1) (H₂ := H) hfix (isOpen_KLev (F := F) (n := 2) (M := 1) le_rfl)
  have hcen : ∀ (z : Ideles F) (g : GA F 2),
      φ.1 (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = (((1 : HChar F).1 z : ℂˣ) : ℂ) * φ.1 g := by
    intro z g
    simp only [OneMemClass.coe_one, MonoidHom.one_apply, Units.val_one, one_mul]
    exact hZ z g
  have haut : TR.IsAutForm φ :=
    ⟨hL.1, hlev, GlobalTheory.T.adelic_lift_kFinite_of_isLift F k Ψ φ hL,
      UpperTheory.V.Af.Nf.zFin F k 1 IsOfFinOrder.one φ hcen (fun v => (hlie v).1) (fun v => (hlie v).2),
      GlobalTheory.T.adelic_lift_has_moderate_growth F k Ψ φ₀ hΨ.gr hL⟩
  refine ⟨φ, hL, haut, fun w u hu => hfix _ ((GlobalTheory.T.maximalCompactGL2_finiteAdele_characterization F).2.2.1 w u hu), hcen, fun v => (hlie v).1,
    fun v => (hlie v).2⟩

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isHol_adelic_lift_of_even_weight_system : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ), Even k → ∀ (Ψ : GL (Fin 2) (Af F) → Hn F → ℂ), Sys k Ψ → ∃ φ : TR.Sm F 2, IsLift k Ψ φ.1 ∧ IsHol k (fun _ => 0) 1 φ := by
  first | exact @GlobalTheory.HilbertThetaSeries.lift_isHol | exact GlobalTheory.HilbertThetaSeries.lift_isHol | (intros; apply GlobalTheory.HilbertThetaSeries.lift_isHol <;> assumption)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertQExpPadicBoundAlgebraProperties
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

theorem small_filtration : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (r s : ℝ) (f g : Hn F → ℂ) (c : ℂ), Small ι r f → Small ι s g → Small ι (max r s) (f + g) ∧ Small ι (r * s) (f * g) ∧ Small ι (‖ι.symm c‖ * r) (c • f) ∧ (r ≤ s → Small ι s f) ∧ 0 ≤ r ∧ Small ι ‖ι.symm c‖ (fun _ : Hn F => c) := by
  intro F _ _ _ p _ ι r s f g c hf hg
  obtain ⟨a, ha, har⟩ := hf
  obtain ⟨b, hb, hbs⟩ := hg
  have hr : 0 ≤ r := (norm_nonneg _).trans (har 0)
  have hs : 0 ≤ s := (norm_nonneg _).trans (hbs 0)
  obtain ⟨h1, h2, -, h4⟩ := GlobalTheory.T.qExpansion_linear_combination F f g a b c ha hb
  refine ⟨⟨a + b, h1, fun ξ => ?_⟩, ?_, ⟨c • a, h2, fun ξ => ?_⟩, fun hrs => ⟨a, ha, fun ξ => (har ξ).trans hrs⟩, hr,
    ⟨_, h4, fun ξ => ?_⟩⟩
  · rw [Pi.add_apply, map_add (f := _)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max (har ξ) (hbs ξ))
  · obtain ⟨d, hd, hds⟩ := GlobalTheory.T.qExpansion_mul_finite_convolution F f g a b ha hb
    refine ⟨d, hd, fun ξ => ?_⟩
    obtain ⟨t, ht⟩ := hds ξ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [ht, map_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hr hs) fun η _ => ?_
    rw [map_mul, norm_mul]
    exact mul_le_mul (har η) (hbs _) (norm_nonneg _) hr
  · rw [Pi.smul_apply, smul_eq_mul, map_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (har ξ) (norm_nonneg _)
  · split_ifs
    · exact le_rfl
    · rw [map_zero, norm_zero]; exact norm_nonneg _

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertQExp_padicBound_algebra_properties : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (r s : ℝ) (f g : Hn F → ℂ) (c : ℂ), Small ι r f → Small ι s g → Small ι (max r s) (f + g) ∧ Small ι (r * s) (f * g) ∧ Small ι (‖ι.symm c‖ * r) (c • f) ∧ (r ≤ s → Small ι s f) ∧ 0 ≤ r ∧ Small ι ‖ι.symm c‖ (fun _ : Hn F => c) := by
  first | exact @GlobalTheory.HilbertThetaSeries.small_filtration | exact GlobalTheory.HilbertThetaSeries.small_filtration | (intros; apply GlobalTheory.HilbertThetaSeries.small_filtration <;> assumption)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.LatticeGaussSumTwistDualEqIndicator
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

theorem sum_isReps_add_shift {V : Type} [AddCommGroup V] (A B : AddSubgroup V) (T : Finset V)
    (hT : IsReps A B T) (f : V → ℂ) (hf : ∀ x ∈ B, ∀ m ∈ A, f (x + m) = f x) (s : V) (hs : s ∈ B) :
    ∑ x ∈ T, f (x + s) = ∑ x ∈ T, f x := by
  classical
  obtain ⟨hTB, huniq⟩ := hT
  have key : ∀ x ∈ B, ∃ y ∈ T, x - y ∈ A := fun x hx => by
    obtain ⟨y, ⟨hy, hxy⟩, _⟩ := huniq x hx
    exact ⟨y, hy, hxy⟩
  choose! g hgT hgA using key
  have hfx : ∀ x ∈ T, f (x + s) = f (g (x + s)) := by
    intro x hx
    have hxs : x + s ∈ B := B.add_mem (hTB x hx) hs
    have h := hf (g (x + s)) (hTB _ (hgT _ hxs)) _ (hgA _ hxs)
    rw [← h]
    congr 1
    abel
  rw [Finset.sum_congr rfl hfx]
  apply Finset.sum_nbij (fun x => g (x + s))
  · intro x hx
    exact hgT _ (B.add_mem (hTB x hx) hs)
  · intro x hx x' hx' h
    simp only [Finset.mem_coe] at hx hx'
    have h1 := hgA _ (B.add_mem (hTB x hx) hs)
    have h2 := hgA _ (B.add_mem (hTB x' hx') hs)
    simp only at h
    rw [h] at h1
    have hd : x - x' ∈ A := by
      have h3 := A.sub_mem h1 h2
      convert h3 using 1
      abel
    obtain ⟨y, _, hy⟩ := huniq x (hTB x hx)
    have e1 := hy x ⟨hx, by rw [sub_self]; exact A.zero_mem⟩
    have e2 := hy x' ⟨hx', hd⟩
    rw [e1, e2]
  · intro y hy
    simp only [Finset.mem_coe] at hy
    have hys : y - s ∈ B := B.sub_mem (hTB y hy) hs
    refine ⟨g (y - s), hgT _ hys, ?_⟩
    have hxs : g (y - s) + s ∈ B := B.add_mem (hTB _ (hgT _ hys)) hs
    apply (huniq _ hxs).unique ⟨hgT _ hxs, hgA _ hxs⟩ ⟨hy, ?_⟩
    have h4 := A.neg_mem (hgA _ hys)
    convert h4 using 1
    abel
  · intro x hx
    rfl

theorem gaussSum_dual_shift : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → ∀ (N : ℕ) (a b c d : F) (T : Finset (κ → F)), 0 < N → (∀ y ∈ dualL F G, (N : F) • y ∈ LL F κ ∧ IsIntegral ℤ ((N : F) * QF G y)) → IsIntegral ℤ a → IsIntegral ℤ b → IsIntegral ℤ (c / N) → IsIntegral ℤ d → a * d - b * c = 1 → c ≠ 0 → IsReps (aL κ c) (aL κ (1 : F)) T → ∀ y ∈ dualL F G, (∑ x ∈ T, et (a / c * QF G x) * et (BF G y x / c)) * et (d / c * QF G y) = oneL y * ∑ x ∈ T, et (a / c * QF G x) := by
  intro F _ _ κ _ _ G hG N a b c d T hN hNy ha hb hcN hd hdet hc hT y hy
  obtain ⟨hBsymm, hsmul, hBadd, hint, hLLiff, haL, het, hLLdual⟩ := GlobalTheory.T.evenPos_gramForm_integral_lattice_properties F κ G hG
  obtain ⟨-, -, hdd, -, -⟩ := GlobalTheory.T.dualLattice_index_eq_discr_pow_mul_det_pow F κ G hG
  have etadd : ∀ u v : F, et (u + v) = et u * et v := fun u v => (het u v).1
  have etint : ∀ u : F, IsIntegral ℤ u → et u = 1 := fun u hu => (het u 0).2.2.2 hu
  have etiff : ∀ u : F, et u = 1 ↔ ∃ n : ℤ, Algebra.trace ℚ F u = n := fun u => (het u 0).2.2.1
  have hLLsmul : ∀ r : F, IsIntegral ℤ r → ∀ x ∈ LL F κ, r • x ∈ LL F κ := by
    intro r hr x hx
    rw [hLLiff] at hx ⊢
    intro i
    simpa [Pi.smul_apply, smul_eq_mul] using hr.mul (hx i)
  have hB1 : ∀ x, x ∈ aL κ (1 : F) ↔ x ∈ LL F κ := by
    intro x
    rw [haL]
    constructor
    · rintro ⟨l, hl, rfl⟩
      simpa using hl
    · intro hx
      exact ⟨x, hx, by simp⟩
  have hdualet : ∀ w ∈ dualL F G, ∀ l ∈ LL F κ, et (BF G w l) = 1 := by
    intro w hw l hl
    exact (etiff _).2 (hw l hl)
  have hexp : ∀ (x : κ → F) (r : F) (z : κ → F),
      QF G (x + r • z) = QF G x + r * BF G x z + r ^ 2 * QF G z := by
    intro x r z
    rw [(hBsymm x (r • z)).2, (hBsymm x (r • z)).1, (hsmul r z x).1, (hsmul r z x).2.1,
      (hBsymm z x).1]
  have hBlin : ∀ (y x : κ → F) (r : F) (z : κ → F),
      BF G y (x + r • z) = BF G y x + r * BF G y z := by
    intro y x r z
    rw [(hBsymm y (x + r • z)).1, hBadd, (hsmul r z y).1, (hBsymm x y).1, (hBsymm z y).1]
  have hNF : (N : F) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hcw : ∀ w ∈ dualL F G, c • w ∈ LL F κ := by
    intro w hw
    have e : c • w = (c / N) • ((N : F) • w) := by
      rw [smul_smul]
      congr 1
      field_simp
    rw [e]
    exact hLLsmul _ hcN _ (hNy w hw).1
  have hcQ : ∀ w ∈ dualL F G, IsIntegral ℤ (a * c * QF G w) := by
    intro w hw
    have e : a * c * QF G w = a * (c / N) * ((N : F) * QF G w) := by
      field_simp
    rw [e]
    exact (ha.mul hcN).mul (hNy w hw).2
  have haB : ∀ x ∈ LL F κ, ∀ w ∈ dualL F G, et (a * BF G x w) = 1 := by
    intro x hx w hw
    rw [← (hsmul a x w).1, (hBsymm _ w).1]
    exact hdualet w hw _ (hLLsmul a ha x hx)
  have hg : ∀ x ∈ aL κ (1 : F), ∀ m ∈ aL κ c,
      et (a / c * QF G (x + m)) = et (a / c * QF G x) := by
    intro x hx m hm
    rw [hB1] at hx
    obtain ⟨l, hl, rfl⟩ := (haL c m).1 hm
    rw [hexp]
    have e : a / c * (QF G x + c * BF G x l + c ^ 2 * QF G l)
        = a / c * QF G x + (a * BF G x l + a * c * QF G l) := by
      field_simp
      ring
    rw [e, etadd, etint _ ((ha.mul ((hint x hx).2 l hl)).add (hcQ l (hLLdual hl))), mul_one]
  by_cases hyL : y ∈ LL F κ
  · have h1 : oneL y = 1 := by simp [oneL, hyL]
    rw [h1, one_mul, Finset.sum_mul]
    have hs : d • y ∈ aL κ (1 : F) := (hB1 _).2 (hLLsmul d hd y hyL)
    refine Eq.trans ?_ (sum_isReps_add_shift (aL κ c) (aL κ 1) T hT
      (fun x => et (a / c * QF G x)) hg (d • y) hs)
    apply Finset.sum_congr rfl
    intro x hxT
    have hx : x ∈ LL F κ := (hB1 x).1 (hT.1 x hxT)
    rw [hexp]
    have key : a / c * (QF G x + d * BF G x y + d ^ 2 * QF G y)
        = a / c * QF G x + BF G y x / c + d / c * QF G y
          + (b * BF G x y + b * d * QF G y) := by
      rw [(hBsymm x y).1]
      field_simp
      linear_combination (BF G y x + d * QF G y) * hdet
    rw [key, etadd, etint _ ((hb.mul ((hint x hx).2 y hyL)).add ((hb.mul hd).mul (hint y hyL).1)),
      mul_one, etadd, etadd]
  · have h0 : oneL y = 0 := by simp [oneL, hyL]
    rw [h0, zero_mul]
    obtain ⟨w, hw, hnot⟩ : ∃ w ∈ dualL F G, et (BF G y w) ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      exact hyL (hdd y (fun ν hν => (etiff _).1 (hcon ν hν)))
    have hs : c • w ∈ aL κ (1 : F) := (hB1 _).2 (hcw w hw)
    have hf : ∀ x ∈ aL κ (1 : F), ∀ m ∈ aL κ c,
        et (a / c * QF G (x + m)) * et (BF G y (x + m) / c)
          = et (a / c * QF G x) * et (BF G y x / c) := by
      intro x hx m hm
      rw [hg x hx m hm]
      congr 1
      obtain ⟨l, hl, rfl⟩ := (haL c m).1 hm
      rw [hBlin y x c l]
      have e : (BF G y x + c * BF G y l) / c = BF G y x / c + BF G y l := by
        field_simp
      rw [e, etadd, hdualet y hy l hl, mul_one]
    have h := sum_isReps_add_shift (aL κ c) (aL κ 1) T hT
      (fun x => et (a / c * QF G x) * et (BF G y x / c)) hf (c • w) hs
    have hmul : ∑ x ∈ T, et (a / c * QF G (x + c • w)) * et (BF G y (x + c • w) / c)
        = et (BF G y w) * ∑ x ∈ T, et (a / c * QF G x) * et (BF G y x / c) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hxT
      have hx : x ∈ LL F κ := (hB1 x).1 (hT.1 x hxT)
      rw [hexp, hBlin]
      have e1 : a / c * (QF G x + c * BF G x w + c ^ 2 * QF G w)
          = a / c * QF G x + (a * BF G x w + a * c * QF G w) := by
        field_simp
        ring
      have e2 : (BF G y x + c * BF G y w) / c = BF G y x / c + BF G y w := by
        field_simp
      rw [e1, e2, etadd, etadd, etadd, haB x hx w hw, etint _ (hcQ w hw)]
      ring
    have hsum : ∑ x ∈ T, et (a / c * QF G x) * et (BF G y x / c) = 0 := by
      rw [hmul] at h
      have h5 : (et (BF G y w) - 1) * ∑ x ∈ T, et (a / c * QF G x) * et (BF G y x / c) = 0 := by
        rw [sub_mul, h, one_mul, sub_self]
      exact (mul_eq_zero.1 h5).resolve_left (sub_ne_zero.2 hnot)
    rw [hsum, zero_mul]

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_gaussSum_twist_dual_eq_indicator : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → ∀ (N : ℕ) (a b c d : F) (T : Finset (κ → F)), 0 < N → (∀ y ∈ dualL F G, (N : F) • y ∈ LL F κ ∧ IsIntegral ℤ ((N : F) * QF G y)) → IsIntegral ℤ a → IsIntegral ℤ b → IsIntegral ℤ (c / N) → IsIntegral ℤ d → a * d - b * c = 1 → c ≠ 0 → IsReps (aL κ c) (aL κ (1 : F)) T → ∀ y ∈ dualL F G, (∑ x ∈ T, et (a / c * QF G x) * et (BF G y x / c)) * et (d / c * QF G y) = oneL y * ∑ x ∈ T, et (a / c * QF G x) := by
  first | exact @GlobalTheory.HilbertThetaSeries.gaussSum_dual_shift | exact GlobalTheory.HilbertThetaSeries.gaussSum_dual_shift | (intros; apply GlobalTheory.HilbertThetaSeries.gaussSum_dual_shift <;> assumption)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ThetaSeriesHolomorphicQExpansionOfBoundedCoeff
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

theorem GlobalTheory.HilbertThetaSeries.th_expansion : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → ∀ (a : F) (Φ : (κ → F) → ℂ) (B : ℝ), (∀ x, Φ x ≠ 0 → x ∈ aL κ a) → (∀ x, ‖Φ x‖ ≤ B) → (∀ z, Summable fun x => Φ x * ez (QF G x) z) ∧ Hol (th G Φ) ∧ Gr (th G Φ) ∧ HasQ (th G Φ) (fun ξ => ∑ᶠ x ∈ {x : κ → F | x ∈ aL κ a ∧ QF G x = ξ}, Φ x) := by
  intro F _ _ _ κ _ _ G hG a Φ B hsupp hB
  obtain ⟨C, A, hCA⟩ := GlobalTheory.HilbertThetaSeries.GaussSum.gauss_sum_bound F κ G hG a
  obtain ⟨hTP, -, hfin⟩ := GlobalTheory.HilbertThetaSeries.qf_totPos_proper F κ G hG
  obtain ⟨-, hsc, -, hint, -, haL, -⟩ := GlobalTheory.HilbertThetaSeries.formLatticeProps F κ G hG
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hle : ∀ z (x : κ → F), ‖Φ x * ez (QF G x) z‖ ≤ B * ‖ez (QF G x) z‖ := fun z x => by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
  have hsub : ∀ z, Summable fun x : aL κ a => ‖Φ x * ez (QF G (x : κ → F)) z‖ := fun z =>
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun x => hle z x) (((hCA z).1).mul_left B)
  have hzero : ∀ x, x ∉ aL κ a → Φ x = 0 := fun x hx => by
    by_contra h; exact hx (hsupp x h)
  have hsumN : ∀ z, Summable fun x : κ → F => ‖Φ x * ez (QF G x) z‖ := by
    intro z
    refine (Function.Injective.summable_iff (f := fun x : κ → F => ‖Φ x * ez (QF G x) z‖)
      (g := ((↑) : aL κ a → κ → F)) Subtype.val_injective ?_).1 (hsub z)
    intro x hx
    have : x ∉ aL κ a := fun h => hx ⟨⟨x, h⟩, rfl⟩
    simp [hzero x this]
  have hsum : ∀ z, Summable fun x => Φ x * ez (QF G x) z := fun z => (hsumN z).of_norm
  have hgr : Gr (th G Φ) := by
    refine ⟨B * C, A, fun z => ?_⟩
    have e1 : ‖th G Φ z‖ ≤ ∑' x, ‖Φ x * ez (QF G x) z‖ := norm_tsum_le_tsum_norm (hsumN z)
    have e2 : ∑' x, ‖Φ x * ez (QF G x) z‖ = ∑' x : aL κ a, ‖Φ x * ez (QF G (x : κ → F)) z‖ := by
      refine (tsum_subtype_eq_of_support_subset (s := (aL κ a : Set (κ → F))) ?_).symm
      intro x hx
      by_contra h
      exact hx (by simp [hzero x h])
    have e3 : ∑' x : aL κ a, ‖Φ x * ez (QF G (x : κ → F)) z‖ ≤ ∑' x : aL κ a, B * ‖ez (QF G (x : κ → F)) z‖ :=
      Summable.tsum_le_tsum (fun x => hle z x) (hsub z) (((hCA z).1).mul_left B)
    rw [tsum_mul_left] at e3
    calc ‖th G Φ z‖ ≤ _ := e1
      _ = _ := e2
      _ ≤ _ := e3
      _ ≤ B * (C * (∏ v, (1 + ‖(z v : ℂ)‖ ^ 2) / (z v).im) ^ A) := mul_le_mul_of_nonneg_left (hCA z).2 hB0
      _ = _ := by ring
  have hQ : HasQ (th G Φ) (fun ξ => ∑ᶠ x ∈ {x : κ → F | x ∈ aL κ a ∧ QF G x = ξ}, Φ x) := by
    refine ⟨?_, fun z => ?_⟩
    · obtain ⟨y, hy0, hy⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (.of_finite ℚ (a ^ 2))).exists_integral_multiple
      have hya : IsIntegral ℤ ((y.natAbs : F) * a ^ 2) := by
        have hy' : IsIntegral ℤ ((y : F) * a ^ 2) := by rwa [zsmul_eq_mul] at hy
        have hc : ((y.natAbs : ℕ) : F) = (((y.natAbs : ℕ) : ℤ) : F) := (Int.cast_natCast _).symm
        rw [hc]
        rcases Int.natAbs_eq y with h | h
        · rw [← h]; exact hy'
        · have h' : ((y.natAbs : ℕ) : ℤ) = -y := by omega
          rw [h', Int.cast_neg, neg_mul]; exact hy'.neg
      refine ⟨y.natAbs, Int.natAbs_pos.2 hy0, fun ξ hξ => ?_⟩
      obtain ⟨x, ⟨hxa, hxξ⟩, -⟩ : ∃ x ∈ {x : κ → F | x ∈ aL κ a ∧ QF G x = ξ}, Φ x ≠ 0 := by
        by_contra h
        push_neg at h
        apply hξ
        beta_reduce
        rw [finsum_mem_eq_finite_toFinset_sum _ (hfin a ξ)]
        exact Finset.sum_eq_zero fun x hx => h x ((hfin a ξ).mem_toFinset.1 hx)
      obtain ⟨l, hl, rfl⟩ := (haL a x).1 hxa
      subst hxξ
      constructor
      · by_cases hx : a • l = 0
        · left; rw [hx]; simp [QF, BF]
        · right; exact hTP _ hx
      · rw [(hsc a l l).2.1, ← mul_assoc]
        exact hya.mul (hint l hl).1
    · have hfib : ∀ ξ, HasSum (fun c : {x // QF G x = ξ} => Φ c * ez (QF G c) z)
          ((∑ᶠ x ∈ {x : κ → F | x ∈ aL κ a ∧ QF G x = ξ}, Φ x) * ez ξ z) := by
        intro ξ
        have e : (fun c : {x // QF G x = ξ} => Φ c * ez (QF G c) z) = fun c : {x // QF G x = ξ} => Φ c * ez ξ z := by
          funext c; rw [c.2]
        rw [e]
        refine HasSum.mul_right _ ?_
        rw [finsum_mem_eq_finite_toFinset_sum _ (hfin a ξ)]
        have h2 : HasSum (({x | QF G x = ξ} : Set (κ → F)).indicator Φ) (∑ x ∈ (hfin a ξ).toFinset, Φ x) := by
          have h3 : ∑ x ∈ (hfin a ξ).toFinset, Φ x = ∑ x ∈ (hfin a ξ).toFinset, ({x | QF G x = ξ} : Set (κ → F)).indicator Φ x :=
            Finset.sum_congr rfl fun x hx => (Set.indicator_of_mem (show x ∈ ({x | QF G x = ξ} : Set (κ → F)) from ((hfin a ξ).mem_toFinset.1 hx).2) _).symm
          rw [h3]
          refine hasSum_sum_of_ne_finset_zero fun x hx => ?_
          by_cases hq : QF G x = ξ
          · rw [Set.indicator_of_mem (show x ∈ ({x | QF G x = ξ} : Set (κ → F)) from hq)]
            refine hzero x fun hxa => hx ?_
            exact (hfin a ξ).mem_toFinset.2 ⟨hxa, hq⟩
          · exact Set.indicator_of_notMem (show x ∉ ({x | QF G x = ξ} : Set (κ → F)) from hq) _
        exact (hasSum_subtype_iff_indicator (f := Φ) (s := {x | QF G x = ξ})).2 h2
      have hall : HasSum (fun x => Φ x * ez (QF G x) z) (th G Φ z) := (hsum z).hasSum
      rw [← (Equiv.sigmaFiberEquiv (QF G)).hasSum_iff] at hall
      exact hall.sigma hfib
  exact ⟨hsum, GlobalTheory.HilbertThetaSeries.QHol.hol F (th G Φ) _ hQ, hgr, hQ⟩

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeries_holomorphic_qExpansion_of_bounded_coeff : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → ∀ (a : F) (Φ : (κ → F) → ℂ) (B : ℝ), (∀ x, Φ x ≠ 0 → x ∈ aL κ a) → (∀ x, ‖Φ x‖ ≤ B) → (∀ z, Summable fun x => Φ x * ez (QF G x) z) ∧ Hol (th G Φ) ∧ Gr (th G Φ) ∧ HasQ (th G Φ) (fun ξ => ∑ᶠ x ∈ {x : κ → F | x ∈ aL κ a ∧ QF G x = ξ}, Φ x) := by
  first | exact @GlobalTheory.HilbertThetaSeries.th_expansion | exact GlobalTheory.HilbertThetaSeries.th_expansion | (intros; apply GlobalTheory.HilbertThetaSeries.th_expansion <;> assumption)
end

