module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0260
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedPhiGammaModelCharacterEqStandard
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0193
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0067
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceMirabolicDetCharacterAverageVectorIndep
section
open GlobalTheory.GLq GlobalTheory.MirAvg Polynomial

noncomputable section

namespace GlobalTheory.MirAvg

open Matrix

variable {g : ℕ} [Fact g.Prime]

theorem exists_gl_mulVec_single_eq {r : ℕ} (i : Fin r) {a : Fin r → ZMod g} (ha : a ≠ 0) :
    ∃ y : Gn g r, (y : Mt g r) *ᵥ Pi.single i 1 = a := by
  have he : (Pi.single i (1 : ZMod g) : Fin r → ZMod g) ≠ 0 := by
    intro h; have := congrFun h i; simp at this
  let f := (LinearEquiv.toSpanNonzeroSingleton (ZMod g) (Fin r → ZMod g) _ he).symm.trans
    (LinearEquiv.toSpanNonzeroSingleton (ZMod g) (Fin r → ZMod g) a ha)
  obtain ⟨e, hef⟩ := Submodule.exists_linearEquiv_restrict_eq f
  have h1 : e (Pi.single i 1) = a := by
    have := hef ⟨_, Submodule.mem_span_singleton_self _⟩
    rw [← this]
    simp only [f, LinearEquiv.trans_apply]
    rw [← LinearEquiv.toSpanNonzeroSingleton_one (ZMod g) (Fin r → ZMod g) _ he, LinearEquiv.symm_apply_apply,
      LinearEquiv.toSpanNonzeroSingleton_one]
  refine ⟨⟨LinearMap.toMatrix' e.toLinearMap, LinearMap.toMatrix' e.symm.toLinearMap, ?_, ?_⟩, ?_⟩
  · rw [← LinearMap.toMatrix'_comp]; simp
  · rw [← LinearMap.toMatrix'_comp]; simp
  · show LinearMap.toMatrix' e.toLinearMap *ᵥ _ = a
    rw [LinearMap.toMatrix'_mulVec]; exact h1

theorem mirSet_true_conj {r : ℕ} (a : Fin r → ZMod g) (y z : Gn g r) :
    mirSet a true (y * z * y⁻¹) ↔ mirSet ((↑y⁻¹ : Mt g r) *ᵥ a) true z := by
  have hAB : (y : Mt g r) * (↑y⁻¹ : Mt g r) = 1 := y.mul_inv
  have hBA : (↑y⁻¹ : Mt g r) * (y : Mt g r) = 1 := y.inv_mul
  simp only [mirSet, if_true, Units.val_mul]
  constructor
  · intro h x
    obtain ⟨c, hc⟩ := h ((y : Mt g r) *ᵥ x)
    refine ⟨c, ?_⟩
    have := congrArg (fun v => (↑y⁻¹ : Mt g r) *ᵥ v) hc
    simp only [mulVec_sub, mulVec_smul, mulVec_mulVec, ← Matrix.mul_assoc, hBA, Matrix.one_mul] at this
    rw [Matrix.mul_assoc, hBA, Matrix.mul_one, one_mulVec] at this
    exact this
  · intro h x
    obtain ⟨c, hc⟩ := h ((↑y⁻¹ : Mt g r) *ᵥ x)
    refine ⟨c, ?_⟩
    have := congrArg (fun v => (y : Mt g r) *ᵥ v) hc
    simp only [mulVec_sub, mulVec_smul, mulVec_mulVec, ← Matrix.mul_assoc, hAB, Matrix.one_mul, one_mulVec] at this
    rw [← this]

theorem mirSet_false_conj {r : ℕ} (a : Fin r → ZMod g) (y z : Gn g r) :
    mirSet a false (y * z * y⁻¹) ↔ mirSet (a ᵥ* (y : Mt g r)) false z := by
  have hAB : (y : Mt g r) * (↑y⁻¹ : Mt g r) = 1 := y.mul_inv
  have hBA : (↑y⁻¹ : Mt g r) * (y : Mt g r) = 1 := y.inv_mul
  simp only [mirSet, Bool.false_eq_true, if_false, Units.val_mul]
  constructor
  · intro h x hx
    rw [← dotProduct_mulVec] at hx
    have := h _ hx
    have := congrArg (fun v => (↑y⁻¹ : Mt g r) *ᵥ v) this
    simp only [mulVec_mulVec, ← Matrix.mul_assoc, hBA, Matrix.one_mul] at this
    rw [Matrix.mul_assoc, hBA, Matrix.mul_one, one_mulVec] at this
    exact this
  · intro h x hx
    have h2 : (a ᵥ* (y : Mt g r)) ⬝ᵥ ((↑y⁻¹ : Mt g r) *ᵥ x) = 0 := by
      rw [← dotProduct_mulVec, mulVec_mulVec, hAB, one_mulVec]; exact hx
    have := h _ h2
    have := congrArg (fun v => (y : Mt g r) *ᵥ v) this
    simp only [mulVec_mulVec, hAB, one_mulVec] at this
    rw [Matrix.mul_assoc]; exact this

open Classical in
theorem mirEl_coeff {r : ℕ} (θ : (ZMod g)ˣ →* ℂˣ) (a : Fin r → ZMod g) (b : Bool) (x : Gn g r) :
    (mirEl θ a b).coeff x = if mirSet a b x then ((θ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) else 0 := by
  unfold mirEl
  rw [MonoidAlgebra.coeff_sum, Finset.sum_apply', Finset.sum_eq_single x]
  · simp [MonoidAlgebra.coeff_single]
  · intro h _ hne; simp [MonoidAlgebra.coeff_single, Finsupp.single_apply, hne]
  · intro h; exact absurd (Finset.mem_univ x) h

theorem tr_mirEl_conj {r : ℕ} (ψ : Gn g r → ℂ) (hψ : IsClass ψ) (θ : (ZMod g)ˣ →* ℂˣ)
    (a a' : Fin r → ZMod g) (b : Bool) (y : Gn g r) (H : ∀ z, mirSet a b (y * z * y⁻¹) ↔ mirSet a' b z) :
    tr (mirEl θ a b) ψ = tr (mirEl θ a' b) ψ := by
  classical
  unfold tr
  simp only [mirEl_coeff]
  rw [← Equiv.sum_comp (MulAut.conj y).toEquiv]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
  have hd : Matrix.GeneralLinearGroup.det (y * z * y⁻¹) = Matrix.GeneralLinearGroup.det z := by
    rw [map_mul, map_mul, map_inv, mul_comm (Matrix.GeneralLinearGroup.det y), mul_inv_cancel_right]
  rw [hd, hψ z y]
  simp only [H z]

end GlobalTheory.MirAvg


open GlobalTheory.GLq GlobalTheory.MirAvg Matrix in
theorem GlobalTheory.MirAvg.tr_mirEl_indep : ∀ (g : ℕ) [Fact g.Prime] (n : ℕ) (ψ : Gn g (n + 1) → ℂ), IsClass ψ → ∀ (θ : (ZMod g)ˣ →* ℂˣ)
    (a : Fin (n + 1) → ZMod g), a ≠ 0 → ∀ b : Bool,
      tr (mirEl θ a b) ψ = tr (mirEl θ (if b then Pi.single 0 1 else Pi.single (Fin.last n) 1) b) ψ := by
  intro g _ n ψ hψ θ a ha b
  cases b with
  | true =>
    obtain ⟨y, hy⟩ := exists_gl_mulVec_single_eq (0 : Fin (n + 1)) ha
    refine tr_mirEl_conj ψ hψ θ a _ true y fun z => ?_
    rw [mirSet_true_conj, if_pos rfl, ← hy, mulVec_mulVec, y.inv_mul, one_mulVec]
  | false =>
    obtain ⟨P, hP⟩ := exists_gl_mulVec_single_eq (Fin.last n) ha
    let y : Gn g (n + 1) := ⟨(↑P⁻¹ : Mt g (n + 1))ᵀ, (P : Mt g (n + 1))ᵀ,
      by rw [← transpose_mul, P.mul_inv, transpose_one], by rw [← transpose_mul, P.inv_mul, transpose_one]⟩
    refine tr_mirEl_conj ψ hψ θ a _ false y fun z => ?_
    rw [mirSet_false_conj]
    have : a ᵥ* (y : Mt g (n + 1)) = Pi.single (Fin.last n) 1 := by
      show a ᵥ* (↑P⁻¹ : Mt g (n + 1))ᵀ = _
      rw [vecMul_transpose, ← hP, mulVec_mulVec, P.inv_mul, one_mulVec]
    rw [this]; rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrivialLineAdmissibleCocyclesNotIndependent
section
noncomputable section
namespace GlobalTheory.TopSteps.TrivLine
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries

theorem exists_diff_of_sum_eq_zero {k : Type} [Field k] {n : ℕ} [NeZero n] (c : ZMod n → k) (hc : ∑ i, c i = 0) :
    ∃ d : ZMod n → k, ∀ i, c i = d (i - 1) - d i := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  refine ⟨fun i => -∑ j ∈ Finset.range (i.val + 1), c (j : ZMod (n + 1)), fun i => ?_⟩
  have hall : ∑ j ∈ Finset.range (n + 1), c (j : ZMod (n + 1)) = 0 := by
    rw [← hc, Finset.sum_range]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    exact ZMod.natCast_zmod_val (n := n + 1) x
  by_cases hi : i = 0
  · subst hi
    have h1 : ((0 : ZMod (n + 1)) - 1).val = n := by
      rw [zero_sub]; exact ZMod.val_neg_one n
    simp only [h1, ZMod.val_zero, hall]
    simp
  · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (fun h => hi ((ZMod.val_eq_zero i).1 h))
    have hlt := ZMod.val_lt i
    have hi' : i = ((j + 1 : ℕ) : ZMod (n + 1)) := by
      rw [show j + 1 = i.val from hj.symm, ZMod.natCast_zmod_val]
    have h1 : (i - 1).val = j := by
      have : i - 1 = (j : ZMod (n + 1)) := by rw [hi']; push_cast; ring
      rw [this, ZMod.val_natCast_of_lt (by omega)]
    simp only [h1, hj, Nat.succ_eq_add_one]
    rw [Finset.sum_range_succ _ (j + 1), ← hi']
    ring

variable {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l}

theorem mem_of_inZZ (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (h1 : Dt.T1 l) (h2 : Dt.T2 l)
    (h3 : Dt.T3 l) (b g : ZMod n → Vc k 1) (hZ : InZZ (F.D (chr 1)) Dt (M.Nχ 0) b g) (i : ZMod n) :
    b i ∈ M.Nχ 0 i := by
  have hω : M.ω ^ (-(0 : ℤ)) = 1 := by simp
  have ht : (0 : ℤ) < Dt.t := by exact_mod_cast Dt.one_le_letterBlockLength
  have hlat := M.χ_lat 0 (by norm_num) ht i
  rw [hω] at hlat
  obtain ⟨hL, hC, hP, hS⟩ := hlat
  rw [sh_zero_eq] at hP
  obtain ⟨z0, z1, zG, zB⟩ := hZ i
  have hv := vv_ne_zero k
  have hφ : (F.D (chr 1)).φ i (g (i - 1)) ∈ sh 1 (M.Nχ 0 i) := by
    obtain ⟨y, hy, e⟩ := mem_sh_iff_exists.1 (hZ (i - 1)).2.1
    obtain ⟨u, hu⟩ := R.φ_v
    obtain ⟨l', hl'⟩ := Nat.exists_eq_add_of_le (Fact.out : l.Prime).one_le
    have hy' : (F.D (chr 1)).φ i y ∈ M.Nχ 0 i := by
      rw [← hP]; exact Submodule.subset_span ⟨y, hy, rfl⟩
    refine mem_sh_iff_exists.2 ⟨((u : k⟦X⟧) * PowerSeries.X ^ l') • (F.D (chr 1)).φ i y,
      Submodule.smul_mem _ _ hy', ?_⟩
    rw [← e, (F.D (chr 1)).φ_semi i, zpow_one, hu, ← algebraMap_smul k⸨X⸩ ((u : k⟦X⟧) * PowerSeries.X ^ l'),
      smul_smul]
    congr 1
    change _ * (((u : k⟦X⟧) * PowerSeries.X ^ l' : k⟦X⟧) : k⸨X⸩) = _
    rw [map_mul, map_pow, ← vv_eq_coe_X, hl']
    ring
  have hnab : nab ((F.D (chr 1)).γ i) (b i) ∈ M.Nχ 0 i := by
    have := mem_sh_iff_smul_mem.1 (Submodule.sub_mem _ hφ z1)
    rw [← z0, zpow_neg_one] at this
    exact this
  have key : ∀ J : ℤ, 0 ≤ J → J ≤ Dt.η i → b i ∈ sh (-J) (M.Nχ 0 i) → b i ∈ M.Nχ 0 i := by
    intro J hJ hJ' hb
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hJ
    have hl := h1 i
    have := (GlobalTheory.PhiGam.Window.nab_bijective_window R _ ((F.D (chr 1)).γ_semi i) _ hL hC (-(m : ℤ)) m (by
      intro j hj
      rw [hS, resCount, Multiset.card_eq_zero]
      refine (@Multiset.filter_eq_nil _ _ (_) _).2 ?_
      intro a ha e
      rw [Multiset.mem_singleton] at ha
      subst ha
      have e' : ((m - j : ℕ) : k) = 0 := by
        rw [Nat.cast_sub hj.le]
        push_cast at e
        linear_combination e
      have := Nat.le_of_dvd (by omega) ((CharP.cast_eq_zero_iff k l _).1 e')
      omega)).1 (b i) hb (by rw [neg_add_cancel, sh_zero_eq]; exact hnab)
    rwa [neg_add_cancel, sh_zero_eq] at this
  obtain ⟨-, -, wG, wB⟩ := GlobalTheory.WindowArith.windows (k := k) Dt h1 h2 h3 i
  cases hty : Dt.ty i with
  | G =>
    obtain ⟨-, -, a1, a2⟩ := wG hty
    exact key _ (by omega) (by omega) (zG hty)
  | Bd =>
    obtain ⟨-, -, a1, a2⟩ := wB hty
    have := (zB hty).1
    rw [hP] at this
    exact key _ (by omega) a2 this

theorem exists_const_pair (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (h1 : Dt.T1 l)
    (h2 : Dt.T2 l) (h3 : Dt.T3 l) (z : G → Fin 1 → k) (hz : z ∈ M.twistedModelAdmissibleCocycles (chr 1)) :
    ∃ (b g m : ZMod n → Vc k 1) (c : ZMod n → k), Repr F (chr 1) z b g ∧
      ∀ i, b i = (F.D (chr 1)).φ i (m (i - 1)) - m i + c i • F.unit i ∧ g i = (F.D (chr 1)).γ i (m i) - m i := by
  obtain ⟨N, b, g, hN, hR, hZ⟩ := _root_.GlobalTheory.TopSteps.ExtPair.exists_model_repr_inZZ F M h1 h2 h3 (chr 1) z hz
  have hω : M.ω ^ (-(0 : ℤ)) = 1 := by simp
  have ht : (0 : ℤ) < Dt.t := by exact_mod_cast Dt.one_le_letterBlockLength
  have hCH := _root_.GlobalTheory.Models.CharModel.model_chr_eq F M h1 h2 h3 0 le_rfl ht N
  rw [hω] at hCH
  obtain rfl := hCH hN
  have hb : ∀ i, ∃ β : k⟦X⟧, b i = (β : k⸨X⸩) • F.unit i := fun i => by
    have := mem_of_inZZ F M h1 h2 h3 b g hZ i
    rw [M.χ_zero, Submodule.mem_span_singleton] at this
    obtain ⟨β, e⟩ := this
    exact ⟨β, by rw [← e, ← algebraMap_smul k⸨X⸩ β]; rfl⟩
  have hg : ∀ i, ∃ β : k⟦X⟧, PowerSeries.constantCoeff β = 0 ∧ g i = (β : k⸨X⸩) • F.unit i := fun i => by
    obtain ⟨y, hy, e⟩ := mem_sh_iff_exists.1 (hZ i).2.1
    rw [M.χ_zero, Submodule.mem_span_singleton] at hy
    obtain ⟨β, rfl⟩ := hy
    refine ⟨PowerSeries.X * β, by simp, ?_⟩
    rw [← e, ← algebraMap_smul k⸨X⸩ β, zpow_one, smul_smul, map_mul, ← vv_eq_coe_X]; rfl
  choose β hβ using hb
  choose δ hδ0 hδ using hg
  have eφ : ∀ i (a : k⸨X⸩), (F.D (chr 1)).φ i (a • F.unit (i - 1)) = R.φ a • F.unit i := fun i a => by
    rw [(F.D (chr 1)).φ_semi i, F.unit_φ]
  have eγ : ∀ i (a : k⸨X⸩), (F.D (chr 1)).γ i (a • F.unit i) = R.γ a • F.unit i := fun i a => by
    rw [(F.D (chr 1)).γ_semi i, F.unit_γ]
  obtain ⟨m, c, hm⟩ := GlobalTheory.PhiGam.TrivCocycle.main R β δ hδ0 (fun i => by
    have e := (hZ i).1
    rw [hβ i, hδ i, hδ (i - 1), eφ, eγ, ← sub_smul, ← sub_smul] at e
    exact smul_left_injective _ (F.unit_ne i) e)
  refine ⟨b, g, fun i => (m i : k⸨X⸩) • F.unit i, c, hR, fun i => ⟨?_, ?_⟩⟩
  · rw [hβ, (hm i).1, eφ, add_smul, sub_smul]
    congr 1
    apply funext
    intro j
    change (algebraMap k k⸨X⸩) (c i) * F.unit i j = c i • F.unit i j
    rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, HahnSeries.ofPowerSeries_C,
      HahnSeries.C_mul_eq_smul]
    simp
  · rw [hδ, (hm i).2, eγ, sub_smul]

theorem main : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ z : Fin 2 → G → Fin 1 → k, (∀ a, z a ∈ M.twistedModelAdmissibleCocycles (chr 1)) → ¬ LinearIndependent k (fun a => (cob (chr (1 : G →* kˣ))).mkQ (z a)) := by
  intro k G _ _ l n _ _ _ R F r Dt M h1 h2 h3 z hz hli
  choose b g m c hR hm using fun a => exists_const_pair F M h1 h2 h3 (z a) (hz a)
  have key : ∀ (p q : Fin 2) (x : k), x * ∑ i, c p i + ∑ i, c q i = 0 →
      x • (cob (chr (1 : G →* kˣ))).mkQ (z p) + (cob (chr (1 : G →* kˣ))).mkQ (z q) = 0 := by
    intro p q x hx
    obtain ⟨d, hd⟩ := exists_diff_of_sum_eq_zero (fun i => x * c p i + c q i)
      (by rw [Finset.sum_add_distrib, ← Finset.mul_sum, hx])
    have hr := GlobalTheory.T.repr_smul_add F (chr 1) x (z p) (z q) _ _ _ _ (hR p) (hR q)
    have h0 := _root_.GlobalTheory.TopSteps.mem_cob_of_repr_mem_herrB F (chr 1) _ _ _ hr (by
      refine ⟨fun i => x • m p i + m q i + d i • F.unit i, Prod.ext (funext fun i => ?_) (funext fun i => ?_)⟩
      · change (F.D (chr 1)).φ i (x • m p (i - 1) + m q (i - 1) + d (i - 1) • F.unit (i - 1)) -
          (x • m p i + m q i + d i • F.unit i) = x • b p i + b q i
        have e : d (i - 1) = x * c p i + c q i + d i := by rw [hd i]; ring
        rw [map_add (f := _), map_add (f := _), map_smul, map_smul, F.unit_φ, (hm p i).1, (hm q i).1, e]
        module
      · change (F.D (chr 1)).γ i (x • m p i + m q i + d i • F.unit i) -
          (x • m p i + m q i + d i • F.unit i) = x • g p i + g q i
        rw [map_add (f := _), map_add (f := _), map_smul, map_smul, F.unit_γ, (hm p i).2, (hm q i).2]
        module)
    rw [← map_smul, ← map_add (f := _)]
    exact (Submodule.Quotient.mk_eq_zero _).2 h0
  rw [Fintype.linearIndependent_iff] at hli
  by_cases hs : ∑ i, c 0 i = 0
  · have := hli ![1, 0] (by
      rw [Fin.sum_univ_two, add_comm]
      have := key 1 0 0 (by rw [hs]; ring)
      simpa using this) 0
    simp at this
  · have := hli ![-(∑ i, c 1 i) / ∑ i, c 0 i, 1] (by
      rw [Fin.sum_univ_two]
      have := key 0 1 (-(∑ i, c 1 i) / ∑ i, c 0 i) (by field_simp; ring)
      simpa using this) 1
    simp at this

end GlobalTheory.TopSteps.TrivLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistInvOfCharLawsMultOne
section
open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.TypeLeaf


open Polynomial NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.TypeLeaf.lpChar_eq_triv_of_mul_eq_one (D : _root_.Formalism.BasicNotions.D7) (w : _root_.Formalism.BasicNotions.PlE D.host)
    (χ χ' : D.naut.LP w) (c c' : ℂ)
    (hu : D.naut.unr χ) (hu' : D.naut.unr χ') (hd' : D.naut.lpDim χ' = 1)
    (hc : D.naut.frobEig χ = {c}) (hc' : D.naut.frobEig χ' = {c'}) (h : c * c' = 1) :
    D.naut.lpChar χ χ' = D.naut.lpUnr w {1} := by
  have hu2 := D.naut.unr_char χ χ' hd' hu hu'
  rw [D.naut.unr_eq_lpUnr _ hu2, D.naut.frobEig_char χ χ' c' hu hu' hd' hc', hc]
  simp [h]

open Polynomial NumberField IsDedekindDomain in
private lemma exists_frobEig_etaT_inv_etaTinv (D : _root_.Formalism.BasicNotions.D7) (w : _root_.Formalism.BasicNotions.PlE D.host) :
    ∃ c : ℂ, c ≠ 0 ∧ D.naut.frobEig (D.naut.locG D.naut.etaT w) = {c} ∧
      D.naut.frobEig (D.naut.locG D.naut.etaTinv w) = {c⁻¹} := by
  have hu := D.naut.etaT_unr w
  have hcard : (D.naut.frobEig (D.naut.locG D.naut.etaT w)).card = 1 := by
    rw [D.naut.frobEig_card _ hu, D.naut.locG_dim]
  obtain ⟨c, hc⟩ := Multiset.card_eq_one.1 hcard
  have hne := D.naut.frobEig_ne_zero _ hu
  refine ⟨c, fun h0 => hne (by rw [hc, h0]; exact Multiset.mem_singleton_self 0), hc, ?_⟩
  rw [(D.naut.etaTinv_def w).2, hc]
  simp


open Polynomial NumberField IsDedekindDomain in
theorem _root_.GlobalTheory.TypeLeaf.twistInv_of_charLaws_multOne :
    ∀ D : _root_.Formalism.BasicNotions.D7, _root_.GlobalTheory.TypeLeaf.CharLaws D → _root_.GlobalTheory.TypeLeaf.MultOne D →
      _root_.GlobalTheory.TypeLeaf.TwistInv D := by
  intro D hlaw hmult
  have hdim : ∀ w : _root_.Formalism.BasicNotions.PlE D.host, D.naut.lpDim (D.naut.locG D.naut.etaT w) = 1 :=
    fun w => D.naut.locG_dim _ w
  have hdim' : ∀ w : _root_.Formalism.BasicNotions.PlE D.host, D.naut.lpDim (D.naut.locG D.naut.etaTinv w) = 1 :=
    fun w => D.naut.locG_dim _ w
  constructor
  · intro a π ha
    refine hmult a _ _ ha fun w => ?_
    obtain ⟨c, hc0, hc, hc'⟩ := exists_frobEig_etaT_inv_etaTinv D w
    rw [D.naut.locG_tw, D.naut.locG_tw, (hlaw w _ _ _ (hdim w) (hdim' w)).1,
      _root_.GlobalTheory.TypeLeaf.lpChar_eq_triv_of_mul_eq_one D w _ _ c c⁻¹ (D.naut.etaT_unr w)
        (D.naut.etaTinv_def w).1 (hdim' w) hc hc' (mul_inv_cancel₀ hc0),
      (hlaw w _ _ _ (hdim w) (hdim w)).2]
  · intro a π ha
    refine hmult a _ _ ha fun w => ?_
    obtain ⟨c, hc0, hc, hc'⟩ := exists_frobEig_etaT_inv_etaTinv D w
    rw [D.naut.locG_tw, D.naut.locG_tw, (hlaw w _ _ _ (hdim' w) (hdim w)).1,
      _root_.GlobalTheory.TypeLeaf.lpChar_eq_triv_of_mul_eq_one D w _ _ c⁻¹ c (D.naut.etaTinv_def w).1
        (D.naut.etaT_unr w) (hdim w) hc' hc (inv_mul_cancel₀ hc0),
      (hlaw w _ _ _ (hdim w) (hdim w)).2]

end GlobalTheory.TypeLeaf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedDualEvalBidualApply
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.DualSide

section Anti

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [TopologicalSpace G]
  {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
  {M' : Type*} [AddCommGroup M'] [Module R M'] [TopologicalSpace M']
  [IsTopologicalAddGroup M'] [ContinuousConstSMul R M']
  {P : Type*} [AddCommGroup P] [Module R P] [TopologicalSpace P]
  [IsTopologicalAddGroup P] [ContinuousConstSMul R P]

end Anti

section Dual

variable {R : Type*} [CommRing R] {Γ : Type*} [Group Γ] {M : Type*} [AddCommGroup M] [Module R M]

theorem finite_TDual [Finite R] [Finite M] : Finite (TDual R M) :=
  Finite.of_injective _ (DFunLike.coe_injective (F := TDual R M))

variable [TopologicalSpace R] [DiscreteTopology R] [TopologicalSpace M] [DiscreteTopology M]

theorem contAction_twDual [TopologicalSpace Γ] [ContinuousInv Γ] [Finite M] {χ : Γ →* Rˣ}
    {rho : Representation R Γ M} (hχ : ContAction (charRep χ)) (h : ContAction rho) :
    ContAction (twDual χ rho) := by
  have h1 : Continuous fun (p : Γ × TDual R M) (m : M) => twDual χ rho p.1 p.2 m :=
    continuous_pi fun m => hχ.comp (continuous_fst.prodMk
      ((continuous_of_discreteTopology (f := fun q : TDual R M × M => q.1 q.2)).comp
        (continuous_snd.prodMk (h.comp (continuous_fst.inv.prodMk continuous_const)))))
  exact (IsLocallyConstant.desc _ (fun (φ : TDual R M) (m : M) => φ m)
    ((IsLocallyConstant.iff_continuous _).2 h1) DFunLike.coe_injective).continuous

variable {D : Type*} [Group D] [TopologicalSpace D]

end Dual

section Global

open GlobalTheory.Published GlobalTheory.Published.PoitouTate

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime] {r : ℕ} {S : Finset (HeightOneSpectrum (𝓞 F))}
  {Av : S → ValuationSubring Ω}
  {μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ}
  {j : ∀ v : S, H2 ((charRep μ).comp (locFam S Av v)) →ₗ[ZMod (l ^ r)] ZMod (l ^ r)}
  {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
  [DiscreteTopology M]
  {ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M}

omit [TopologicalSpace M] [DiscreteTopology M] in
theorem finite_TDual_pow : Finite (TDual (ZMod (l ^ r)) M) :=
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  finite_TDual

end Global


end GlobalTheory.DualSide
end
end

