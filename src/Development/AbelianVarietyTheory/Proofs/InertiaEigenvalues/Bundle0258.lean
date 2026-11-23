module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0231
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0223
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthEqInfKerAddMap
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.Cut.Peel

theorem length_eq_inf_ker_add_map {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (C : Submodule R M) :
    Module.length R ↥C = Module.length R ↥(C ⊓ LinearMap.ker f) + Module.length R ↥(C.map f) := by
  refine Module.length_eq_add_of_exact (Submodule.inclusion (inf_le_left : C ⊓ LinearMap.ker f ≤ C))
    (f.submoduleMap C) (Submodule.inclusion_injective _) (f.submoduleMap_surjective C) ?_
  intro y
  constructor
  · intro hy
    have hy' : f y = 0 := by
      simpa [LinearMap.submoduleMap_coe_apply] using congrArg Subtype.val hy
    exact ⟨⟨y.1, y.2, hy'⟩, rfl⟩
  · rintro ⟨z, rfl⟩
    ext
    simpa [LinearMap.submoduleMap_coe_apply] using z.2.2

theorem exists_le_map_eq_bot {R M ι : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {N : ι → Type*} [∀ q, AddCommGroup (N q)] [∀ q, Module R (N q)] (f : ∀ q, M →ₗ[R] N q)
    (C : Submodule R M) (Q : Finset ι) :
    ∃ C' : Submodule R M, C' ≤ C ∧ (∀ q ∈ Q, C'.map (f q) = ⊥) ∧
      Module.length R ↥C ≤ Module.length R ↥C' + ∑ q ∈ Q, Module.length R ↥(C.map (f q)) := by
  classical
  induction Q using Finset.induction_on with
  | empty => exact ⟨C, le_rfl, by simp, by simp⟩
  | insert q Q hq ih =>
    obtain ⟨C₀, hC₀, hmap, hlen⟩ := ih
    refine ⟨C₀ ⊓ LinearMap.ker (f q), inf_le_left.trans hC₀, ?_, ?_⟩
    · intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hp
      · rw [eq_bot_iff]
        rintro _ ⟨x, hx, rfl⟩
        exact hx.2
      · rw [eq_bot_iff, ← hmap p hp]
        exact Submodule.map_mono inf_le_left
    · have hsplit := length_eq_inf_ker_add_map (f q) C₀
      have hle : Module.length R ↥(C₀.map (f q)) ≤ Module.length R ↥(C.map (f q)) :=
        Module.length_le_of_injective _ (Submodule.inclusion_injective (Submodule.map_mono hC₀))
      rw [Finset.sum_insert hq]
      calc Module.length R ↥C ≤ Module.length R ↥C₀ + ∑ p ∈ Q, Module.length R ↥(C.map (f p)) := hlen
        _ = Module.length R ↥(C₀ ⊓ LinearMap.ker (f q)) + Module.length R ↥(C₀.map (f q)) +
              ∑ p ∈ Q, Module.length R ↥(C.map (f p)) := by rw [← hsplit]
        _ ≤ Module.length R ↥(C₀ ⊓ LinearMap.ker (f q)) + Module.length R ↥(C.map (f q)) +
              ∑ p ∈ Q, Module.length R ↥(C.map (f p)) := by gcongr
        _ = _ := by rw [add_assoc]

theorem main : ∀ (D : D7) (i : D.nd.Loc) (k : ℕ) (C : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) k)) (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))), ∃ C' : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) k), C' ≤ C ∧ (∀ q ∈ Q, resIne i C' q = ⊥) ∧ Module.length (D.nd.O i) ↥C ≤ Module.length (D.nd.O i) ↥C' + ∑ q ∈ Q, Module.length (D.nd.O i) ↥(resIne i C q) := by
  intro D i k C Q
  exact exists_le_map_eq_bot
    (fun q => LinearMap.funLeft (D.nd.O i) (KOG (D.nd.O i) k)
      (Subtype.val : ↥(Ine (F := D.host.E) (D.nd.plOm.1 q)) → GE D.nd)) C Q

end GlobalTheory.Cut.Peel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocPrimeVNormalised
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.HWL.NormVal

section General

variable {K : Type*} [Field K]

end General

open GlobalTheory.Per.Val

open TensorProduct in
private lemma addValuation_pow_mul_pow_div_pow {F : Type*} [Field F]
    (u : AddValuation F (WithTop ℚ)) {π : F} (hu : u π = 1) {x : F} {t : ℚ} (hx : u x = t)
    (b M N : ℕ) : u (x ^ b * π ^ M / π ^ N) = ((b * t + M - N : ℚ) : WithTop ℚ) := by
  rw [AddValuation.map_div, AddValuation.map_mul, AddValuation.map_pow, AddValuation.map_pow,
    AddValuation.map_pow, hx, hu]
  norm_cast
  simp [nsmul_eq_mul]

open TensorProduct in
private lemma le_of_nonneg_imp_nonneg {F : Type*} [Field F] (v w : AddValuation F (WithTop ℚ)) {π : F}
    (hv : v π = 1) (hw : w π = 1) (h : ∀ y, 0 ≤ v y → 0 ≤ w y) {x : F} {t s : ℚ}
    (hvx : v x = t) (hwx : w x = s) : t ≤ s := by
  have hMN : ((t.num.toNat : ℕ) : ℚ) - ((-t.num).toNat : ℕ) = t.num := by
    exact_mod_cast Int.toNat_sub_toNat_neg t.num
  have hbt : (t.den : ℚ) * t = t.num := by rw [mul_comm]; exact Rat.mul_den_eq_num t
  have hy := h (x ^ t.den * π ^ (-t.num).toNat / π ^ t.num.toNat) (by
    rw [addValuation_pow_mul_pow_div_pow v hv hvx]
    exact_mod_cast (by linarith : (0 : ℚ) ≤ t.den * t + ((-t.num).toNat : ℕ) - (t.num.toNat : ℕ)))
  rw [addValuation_pow_mul_pow_div_pow w hw hwx] at hy
  have hy' : (0 : ℚ) ≤ t.den * s + ((-t.num).toNat : ℕ) - (t.num.toNat : ℕ) := by exact_mod_cast hy
  have hd : (0 : ℚ) < t.den := by exact_mod_cast t.den_pos
  nlinarith

open TensorProduct in
private lemma addValuation_eq_of_nonneg_iff {F : Type*} [Field F] (v w : AddValuation F (WithTop ℚ))
    {π : F} (hv : v π = 1) (hw : w π = 1) (h : ∀ y, 0 ≤ v y ↔ 0 ≤ w y) (x : F) : v x = w x := by
  by_cases hx : x = 0
  · subst hx; simp
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp (mt (AddValuation.top_iff v).mp hx)
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp (mt (AddValuation.top_iff w).mp hx)
  rw [← ht, ← hs]
  have h1 := le_of_nonneg_imp_nonneg v w hv hw (fun y => (h y).mp) ht.symm hs.symm
  have h2 := le_of_nonneg_imp_nonneg w v hw hv (fun y => (h y).mpr) hs.symm ht.symm
  exact congrArg _ (le_antisymm h1 h2)


open TensorProduct in
theorem _root_.GlobalTheory.HWL.NormVal.locPrime_v_normalised : ∀ (l : ℕ) [Fact l.Prime] (P : _root_.Formalism.BasicNotions.LocPrime l) (LL : _root_.Formalism.BasicNotions.Loc.FinExt l), (∀ (x : ↥LL.1) (q : ℚ), P.v LL x = (q : WithTop ℚ) ↔ ‖(x : _root_.Formalism.BasicNotions.Loc.Om l)‖ = (l : ℝ) ^ (-(q : ℝ))) ∧ (∀ (x : ↥LL.1) (q : ℚ), (q : WithTop ℚ) ≤ P.v LL x ↔ ‖(x : _root_.Formalism.BasicNotions.Loc.Om l)‖ ≤ (l : ℝ) ^ (-(q : ℝ))) ∧ ∀ x : ↥LL.1, x ∈ _root_.Formalism.BasicNotions.Loc.OL LL ↔ ‖(x : _root_.Formalism.BasicNotions.Loc.Om l)‖ ≤ 1 := by
  intro l _ P LL
  set w : AddValuation (↥LL.1) (WithTop ℚ) :=
    (_root_.GlobalTheory.Per.Val.vOm l).comap (algebraMap (↥LL.1) (_root_.Formalism.BasicNotions.Loc.Om l)) with hwdef
  have hwx : ∀ x : ↥LL.1, w x = _root_.GlobalTheory.Per.Val.vf (x : _root_.Formalism.BasicNotions.Loc.Om l) := fun x => rfl
  have hw : w (l : ↥LL.1) = 1 := by
    rw [hwx]
    have : ((l : ↥LL.1) : _root_.Formalism.BasicNotions.Loc.Om l) = (l : _root_.Formalism.BasicNotions.Loc.Om l) := by simp
    rw [this]
    exact _root_.GlobalTheory.Per.Val.vf_l
  have hnn : ∀ y : ↥LL.1, 0 ≤ P.v LL y ↔ 0 ≤ w y := by
    intro y
    rw [_root_.Formalism.BasicNotions.LocPrime.v_O, _root_.GlobalTheory.Per.Val.mem_OL_iff, hwx]
    have := _root_.GlobalTheory.Per.Val.le_vf_iff (y : _root_.Formalism.BasicNotions.Loc.Om l) 0
    simp only [Rat.cast_zero, neg_zero, Real.rpow_zero, WithTop.coe_zero] at this
    exact this.symm
  have key : ∀ x : ↥LL.1, P.v LL x = _root_.GlobalTheory.Per.Val.vf (x : _root_.Formalism.BasicNotions.Loc.Om l) := fun x =>
    (addValuation_eq_of_nonneg_iff (P.v LL) w (P.v_l LL) hw hnn x).trans (hwx x)
  refine ⟨fun x q => ?_, fun x q => ?_, fun x => _root_.GlobalTheory.Per.Val.mem_OL_iff LL x⟩
  · rw [key]; exact _root_.GlobalTheory.Per.Val.vf_eq_iff _ q
  · rw [key]; exact _root_.GlobalTheory.Per.Val.le_vf_iff _ q

end GlobalTheory.HWL.NormVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixFrobeniusSubOneBijectiveModSubring
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

namespace GlobalTheory.DecomplMat

variable {R A : Type} [CommRing R] [CommRing A] {ι : A →+* R} {p : ℕ} {t : R}

theorem near_pow_two {x : R} (hx : Near ι p t 2 x) (n : ℕ) : Near ι p t (2 * n) (x ^ n) := by
  induction n with
  | zero => exact ⟨1, 0, by simp⟩
  | succ n ih =>
    have h := ih.mul hx
    rw [← pow_succ] at h
    exact h

theorem near_frob (φ : R →+* R) (hι : ∀ a, ∃ a', φ (ι a) = ι a') (ht : Near ι p t 2 (φ t))
    {n : ℕ} {v : R} (hv : Near ι p t n v) : Near ι p t (2 * n) (φ v) := by
  obtain ⟨a, r, rfl⟩ := hv
  obtain ⟨a', ha'⟩ := hι a
  rw [map_add (f := _), map_mul, map_mul, map_pow, map_natCast, ha', mul_comm _ (ι a')]
  exact ((near_pow_two ht n).mul_ι a').add (Near.of_mul _ _)

theorem near_mul_of_bound {c m : ℕ} {q w : R} (hq : Near ι p t 0 (t ^ c * q))
    (hw : Near ι p t (m + c) w) : Near ι p t m (q * w) := by
  obtain ⟨a, r, rfl⟩ := hw
  obtain ⟨b, s, h⟩ := hq
  refine ⟨b * a, t ^ m * ι a * s + q * r, ?_⟩
  rw [map_mul, pow_add]
  linear_combination (t ^ m * ι a) * h

theorem near_bound_mono {τ : A} (hτ : ι τ = t) {c c' : ℕ} (h : c ≤ c') {q : R}
    (hq : Near ι p t 0 (t ^ c * q)) : Near ι p t 0 (t ^ c' * q) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  have h1 := hq.mul_ι (τ ^ k)
  rw [map_pow, hτ] at h1
  convert h1 using 1
  ring

def nearSub (ι : A →+* R) (p : ℕ) (t : R) (m : ℕ) : AddSubgroup R where
  carrier := {x | Near ι p t m x}
  add_mem' := Near.add
  zero_mem' := Near.zero m
  neg_mem' := Near.neg

def vecs (d : ℕ) (H : AddSubgroup R) : AddSubgroup (Fin d → R) where
  carrier := {v | ∀ i, v i ∈ H}
  add_mem' := fun ha hb i => H.add_mem (ha i) (hb i)
  zero_mem' := fun _ => H.zero_mem
  neg_mem' := fun ha i => H.neg_mem (ha i)

def semi {d : ℕ} (Q : Fin d → Fin d → R) (φ : R →+* R) : (Fin d → R) →+ (Fin d → R) where
  toFun v := fun i => ∑ k, Q i k * φ (v k)
  map_zero' := by ext i; simp
  map_add' v w := by ext i; simp [mul_add, Finset.sum_add_distrib]

theorem semi_apply {d : ℕ} (Q : Fin d → Fin d → R) (φ : R →+* R) (v : Fin d → R) (i : Fin d) :
    semi Q φ v i = ∑ k, Q i k * φ (v k) := rfl

theorem semi_iterate {EE : Type} [CommRing EE] (j : EE →+* R) (φ : R →+* R)
    (hφ : ∀ e, ∃ e', φ (j e) = j e') {d : ℕ} (Pm : Matrix (Fin d) (Fin d) EE) (n : ℕ) :
    ∃ q : Fin d → Fin d → EE, ∀ v i,
      (semi (fun i k => j (Pm i k)) φ)^[n] v i = ∑ k, j (q i k) * φ^[n] (v k) := by
  classical
  choose ψ hψ using hφ
  induction n with
  | zero =>
    refine ⟨fun i k => if i = k then 1 else 0, fun v i => ?_⟩
    simp [apply_ite j]
  | succ n ih =>
    obtain ⟨q, hq⟩ := ih
    refine ⟨fun i l => ∑ k, Pm i k * ψ (q k l), fun v i => ?_⟩
    rw [Function.iterate_succ_apply', semi_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hq, map_sum, map_mul, hψ, Function.iterate_succ_apply', Finset.mul_sum,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [mul_assoc]

theorem iterate_persist {EE : Type} [CommRing EE] (j : EE →+* R) (φ : R →+* R)
    (hφ : ∀ e, ∃ e', φ (j e) = j e') {n n' : ℕ} (h : n ≤ n') {y : R}
    (hy : ∃ e r, φ^[n] y = j e + (p : R) * r) : ∃ e r, φ^[n'] y = j e + (p : R) * r := by
  induction h with
  | refl => exact hy
  | step _ ih =>
    obtain ⟨e, r, h⟩ := ih
    obtain ⟨e', he'⟩ := hφ e
    refine ⟨e', φ r, ?_⟩
    rw [Function.iterate_succ_apply', h, map_add (f := _), map_mul, map_natCast, he']

theorem matrix_frob_sub_one_bijective :
    ∀ (R EE A : Type) [CommRing R] [CommRing EE] [CommRing A] (j : EE →+* R) (ι : A →+* R) (φ : R →+* R) (S : Subring R) (p : ℕ) (t : R) (τ : A), ι τ = t → (∀ e, j e ∈ S) → (∀ x ∈ S, φ x ∈ S) → (∀ e, ∃ e', φ (j e) = j e') → (∀ a, ∃ a', φ (ι a) = ι a') → Near ι p t 2 (φ t) → (∀ e, ∃ c : ℕ, Near ι p t 0 (t ^ c * j e)) → (∀ x, (p : R) * x ∈ S → x ∈ S) → (∀ x e, (p : R) * x = j e → ∃ e', x = j e') → (∀ (k : ℕ) (f : ℕ → R), (∀ i, f i ∈ S) → (∀ i, Near ι p t (i + k) (f i)) → ∃ s ∈ S, ∀ m, Near ι p t (m + k) (s - ∑ i ∈ Finset.range m, f i)) → (∀ x, (∀ m, ∃ e, Near ι p t m (x - j e)) → ∃ e r, x - j e = (p : R) * r) → (∀ y ∈ S, ∀ m, ∃ (n : ℕ) (y0 : R) (e : EE) (r : R), φ^[n] y0 = j e + (p : R) * r ∧ Near ι p t m (y - y0)) → (∀ x : ℕ → R, (∀ i, x i ∈ S) → ∃ s ∈ S, ∀ k, ∃ r, s - ∑ i ∈ Finset.range k, (p : R) ^ i * x i = (p : R) ^ k * r) → (∀ x, (∀ k : ℕ, ∃ e r, x - j e = (p : R) ^ k * r) → ∃ e, x = j e) → ∀ (d : ℕ) (Pm : Matrix (Fin d) (Fin d) EE), (∀ y : Fin d → R, (∀ i, y i ∈ S) → ∃ z : Fin d → R, (∀ i, z i ∈ S) ∧ ∀ i, ∃ e, y i - (∑ k, j (Pm i k) * φ (z k) - z i) = j e) ∧ (∀ z : Fin d → R, (∀ i, z i ∈ S) → (∀ i, ∃ e, ∑ k, j (Pm i k) * φ (z k) - z i = j e) → ∀ i, ∃ e, z i = j e) := by
  intro R EE A _ _ _ j ι φ S p t τ hτ hjS hφS hφj hφι hφt hbd hSs hEs hc hcl hnil hpc hEc d Pm
  classical
  obtain ⟨c, hcP⟩ : ∃ c : ℕ, ∀ i k, Near ι p t 0 (t ^ c * j (Pm i k)) := by
    choose cf hcf using hbd
    exact ⟨Finset.univ.sup (fun x : Fin d × Fin d => cf (Pm x.1 x.2)), fun i k =>
      near_bound_mono hτ (Finset.le_sup (f := fun x : Fin d × Fin d => cf (Pm x.1 x.2))
        (Finset.mem_univ (i, k))) (hcf _)⟩
  set Φ := semi (fun i k => j (Pm i k)) φ with hΦ
  have hF : ∀ m, ∀ x ∈ vecs d (nearSub ι p t (m + (c + 1))),
      Φ x ∈ vecs d (nearSub ι p t (m + 1 + (c + 1))) := by
    intro m x hx i
    change Near ι p t _ (∑ k, j (Pm i k) * φ (x k))
    refine Near.sum _ fun k _ => near_mul_of_bound (hcP i k) ?_
    exact (near_frob φ hφι hφt (hx k)).mono hτ (by omega)
  have hFa : ∀ m, vecs d (nearSub ι p t (m + 1 + (c + 1))) ≤
      vecs d (nearSub ι p t (m + (c + 1))) :=
    fun m x hx i => Near.mono hτ (by omega) (hx i)
  have key := sub_one_bijective_quotient_of_topNilpotent (Fin d → R) p Φ
    (vecs d S.toAddSubgroup) (vecs d j.range.toAddSubgroup)
    (fun m => vecs d (nearSub ι p t (m + (c + 1))))
    (fun x hx i => by obtain ⟨e, he⟩ := hx i; exact he ▸ hjS e)
    (fun x hx i => show ∑ k, j (Pm i k) * φ (x k) ∈ S from S.sum_mem fun k _ => S.mul_mem (hjS _) (hφS _ (hx k)))
    (fun x hx i => show ∑ k, j (Pm i k) * φ (x k) ∈ j.range from
      j.range.sum_mem fun k _ => j.range.mul_mem ⟨_, rfl⟩ (by
      obtain ⟨e, he⟩ := hx k
      obtain ⟨e', he'⟩ := hφj e
      exact ⟨e', by rw [← he', he]⟩))
    hF hFa
    (fun x hx i => hSs _ (by simpa using hx i))
    (fun x hx i => by
      obtain ⟨e, he⟩ := hx i
      obtain ⟨e', he'⟩ := hEs (x i) e (by simpa using he.symm)
      exact ⟨e', he'.symm⟩)
    (fun f hf hf' => by
      choose s hs hs' using fun i => hc (c + 1) (fun n => f n i) (fun n => hf n i)
        (fun n => hf' n i)
      refine ⟨s, hs, fun m i => ?_⟩
      have := hs' i m
      rw [Pi.sub_apply, Finset.sum_apply]
      exact this)
    (fun x hx => by
      choose e r h using fun i => hcl (x i) (fun m => by
        obtain ⟨w, hw, hw'⟩ := hx m
        obtain ⟨e, he⟩ := hw i
        exact ⟨e, he ▸ Near.mono hτ (Nat.le_add_right _ _) (hw' i)⟩)
      refine ⟨fun i => j (e i), fun i => ⟨_, rfl⟩, r, ?_⟩
      ext i
      simpa using h i)
    (fun y hy => by
      choose n y0 e r h1 h2 using fun i => hnil (y i) (hy i) (c + 1)
      obtain ⟨q, hq⟩ := semi_iterate j φ hφj Pm (Finset.univ.sup n)
      choose e' r' h' using fun i => iterate_persist (p := p) j φ hφj
        (Finset.le_sup (f := n) (Finset.mem_univ i)) ⟨e i, r i, h1 i⟩
      have it : ∀ N : ℕ, Φ^[N] y - Φ^[N] y0 ∈ vecs d (nearSub ι p t (0 + (c + 1))) := by
        intro N
        induction N with
        | zero => intro i; rw [Nat.zero_add]; exact h2 i
        | succ N ih =>
          rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← map_sub]
          exact hFa 0 (hF 0 _ ih)
      refine ⟨Finset.univ.sup n, fun i => j (∑ k, q i k * e' k), fun i => ⟨_, rfl⟩, fun i => ?_⟩
      have h3 : Near ι p t (0 + (c + 1)) _ := it (Finset.univ.sup n) i
      have h4 := h3.add (Near.of_mul _ (∑ k, j (q i k) * r' k))
      change Near ι p t (0 + (c + 1)) _
      convert h4 using 1
      simp only [Pi.sub_apply]
      rw [hq y0 i]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [h', mul_add, Finset.sum_add_distrib, map_sum, map_mul, Finset.mul_sum,
        mul_left_comm (p : R)]
      ring)
    (fun x hx => by
      choose s hs hs' using fun i => hpc (fun n => x n i) (fun n => hx n i)
      refine ⟨s, hs, fun k => ?_⟩
      choose r hr using fun i => hs' i k
      refine ⟨r, ?_⟩
      ext i
      simpa [Finset.sum_apply] using hr i)
    (fun x hx i => by
      obtain ⟨e, he⟩ := hEc (x i) (fun k => by
        obtain ⟨w, hw, r, hr⟩ := hx k
        obtain ⟨e, he⟩ := hw i
        refine ⟨e, r i, ?_⟩
        rw [he]
        simpa using congrFun hr i)
      exact ⟨e, he.symm⟩)
  refine ⟨fun y hy => ?_, fun z hz h i => ?_⟩
  · obtain ⟨z, hz, h⟩ := key.1 y hy
    refine ⟨z, hz, fun i => ?_⟩
    obtain ⟨e, he⟩ := h i
    exact ⟨e, he.symm⟩
  · obtain ⟨e, he⟩ := key.2 z hz (fun i => by
      obtain ⟨e, he⟩ := h i
      exact ⟨e, he.symm⟩) i
    exact ⟨e, he.symm⟩

end GlobalTheory.DecomplMat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemDeRhamFiltrationOfForallAinfLattice
section
namespace GlobalTheory.ExpImage

open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage GlobalTheory.MemLoc
open scoped Formalism.Per

theorem dvd_of_isHausdorff {R : Type} [CommRing R] (p : ℕ) (x a : R)
    (H : IsHausdorff (Ideal.span {(p : R ⧸ Ideal.span {x})}) (R ⧸ Ideal.span {x}))
    (h : ∀ n : ℕ, ∃ c : R, x ∣ a - (p : R) ^ n * c) : x ∣ a := by
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
  refine H.haus _ fun n => ?_
  obtain ⟨c, hc⟩ := h n
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq] at hc
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    hc, map_mul, map_pow, map_natCast]
  exact dvd_mul_right _ _

theorem mem_FilB_of_forall_Lat (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (T : LocTied l P AI) (M : ℕ) (b : P.R.BdR) (hb : ∀ n : ℕ, b ∈ Lat AI M n) :
    b ∈ FilB P (M : ℤ) := by
  obtain ⟨-, h2, -⟩ := _root_.GlobalTheory.BdRQuot.fil_quotient l P AI T (GlobalTheory.ThetaTie.thetaL T) M
  obtain ⟨-, h3⟩ := _root_.GlobalTheory.MemLoc.XiSat.xi_sat l AI.ε (GlobalTheory.ThetaTie.isEps AI) M
  obtain ⟨a₀, ha₀⟩ := hb 0
  rw [pow_zero, one_mul] at ha₀
  have hd : AI.ξ ^ M ∣ a₀ := by
    refine dvd_of_isHausdorff l _ _ h3.toIsHausdorff fun n => ?_
    obtain ⟨a, ha⟩ := hb n
    refine ⟨a, (h2 _).1 ?_⟩
    have := sub_mem ha ha₀
    rw [← io_apply, map_sub]
    convert this using 1
    ring
  have := add_mem ha₀ ((h2 a₀).2 hd)
  rwa [← io_apply, sub_add_cancel] at this

end GlobalTheory.ExpImage
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemIntPts
section
noncomputable section

open Classical

namespace GlobalTheory.PositionData

def intPts (A : Set ℚ) : Finset ℤ :=
  if h : ((fun z : ℤ => (z : ℚ)) ⁻¹' A).Finite then h.toFinset else ∅

theorem mem_intPts {A : Set ℚ} (hA : A.Finite) (z : ℤ) : z ∈ intPts A ↔ (z : ℚ) ∈ A := by
  have h : ((fun z : ℤ => (z : ℚ)) ⁻¹' A).Finite :=
    hA.preimage (Set.injOn_of_injective Int.cast_injective)
  unfold intPts
  rw [dite_eq_left h, Set.Finite.mem_toFinset]
  rfl

def mnLo (Fl : Finset ℤ) : ℤ := (insert 0 Fl).min' (Finset.insert_nonempty _ _)

def mxLo (t : ℕ) (Fl : Finset ℤ) : ℤ := (insert ((t : ℤ) - 1) Fl).max' (Finset.insert_nonempty _ _)

def mnAll (Fl Fc : Finset ℤ) : ℤ := (insert 0 (Fl ∪ Fc)).min' (Finset.insert_nonempty _ _)

def mxAll (t : ℕ) (Fl Fc : Finset ℤ) : ℤ :=
  (insert ((t : ℤ) - 1) (Fl ∪ Fc)).max' (Finset.insert_nonempty _ _)

def wS (up : Bool) (Fl Fc : Finset ℤ) : ℕ :=
  if up then (1 - mnLo Fl).toNat else (1 - mnAll Fl Fc).toNat

def etaS (t : ℕ) (Fl : Finset ℤ) : ℕ := (mxLo t Fl - mnLo Fl + 1).toNat

def hS (up : Bool) (t : ℕ) (Fl Fc : Finset ℤ) : ℕ :=
  if up then (mxAll t Fl Fc + wS up Fl Fc + 1).toNat else (mxLo t Fl + wS up Fl Fc + 1).toNat

def US (up : Bool) (Fl Fc : Finset ℤ) : Multiset ℤ :=
  (Fl ∪ Fc).val.map (fun z => z + (wS up Fl Fc : ℤ))

theorem count_US (up : Bool) (Fl Fc : Finset ℤ) (b : ℤ) :
    (US up Fl Fc).count (b + wS up Fl Fc) = if b ∈ Fl ∪ Fc then 1 else 0 := by
  unfold US
  rw [Multiset.count_map_eq_count' _ _ (add_left_injective _)]
  split_ifs with h
  · exact Multiset.count_eq_one_of_mem (Fl ∪ Fc).nodup h
  · exact Multiset.count_eq_zero.mpr h

end GlobalTheory.PositionData
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLeOfQBMemLat
section
noncomputable section

namespace GlobalTheory.ExpImage

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open scoped Formalism.Per

theorem norm_le_of_qB_mem_Lat (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (T : LocTied l P AI) (M n : ℕ) (hM : 1 ≤ M) (z : ℚ_[l]) (hz : qB P z ∈ Lat AI M n) :
    ‖z‖ ≤ (l : ℝ) ^ (-(n : ℤ)) := by
  let J : ThetaL P AI := GlobalTheory.ThetaTie.thetaL T
  obtain ⟨a, ha⟩ := hz
  have hq : ∀ c : ℚ_[l], ‖J.θ (qB P c)‖ = ‖c‖ := by
    intro c
    have e : qB P c = algebraMap (Om l) P.R.BdR (algebraMap ℚ_[l] (Om l) c) :=
      IsScalarTower.algebraMap_apply _ _ _ c
    rw [e, J.θ_Om]
    exact (PadicComplex.norm_extends _ _).trans (PadicAlgCl.norm_extends _ _)
  have h1 := FilB_anti (P := P) (a := 1) (b := (M : ℤ)) (by exact_mod_cast hM) ha
  have h0 := FilB_anti (P := P) (a := 0) (b := 1) (by norm_num) h1
  have hk := (J.θ_ker _ h0).2 h1
  have hadd := J.θ_add _ h0 _ (io_mem AI (((l : ℕ) : Ainf l) ^ n * a))
  rw [sub_add_cancel, hk, zero_add] at hadd
  have e2 : io AI (((l : ℕ) : Ainf l) ^ n * a) = qB P ((l : ℚ_[l]) ^ n) * io AI a := by
    simp only [map_mul, map_pow, map_natCast]
  rw [e2, J.θ_mul _ (qB_mem _) _ (io_mem AI a)] at hadd
  rw [← hq z, hadd, norm_mul, hq, Padic.norm_p_pow]
  exact mul_le_of_le_one_right (by positivity) (J.θ_int a)

end GlobalTheory.ExpImage
end
end

