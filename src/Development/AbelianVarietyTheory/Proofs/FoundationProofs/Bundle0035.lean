module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIdealInClassOfNormLeSqrtDiscr
public import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerQqPowLevelEqQ
section
noncomputable section

namespace GlobalTheory.KumDlog

open GlobalTheory.K5

variable {p : ℕ} [Fact p.Prime] {Ω : Type*} [Field Ω] [Algebra (O0 p) Ω]

def IsDer (S : Subalgebra (O0 p) Ω) (D : Ω → Ω) : Prop :=
  (∀ x ∈ S, ∀ y ∈ S, IsInt (p := p) (D (x + y) - D x - D y)) ∧
  (∀ x ∈ S, ∀ y ∈ S, IsInt (p := p) (D (x * y) - x * D y - y * D x)) ∧
  ∀ c : O0 p, IsInt (p := p) (D (algebraMap (O0 p) Ω c))

def FixI (G : Subgroup (Gal p Ω)) : Subalgebra (O0 p) Ω where
  carrier := {x | IsInt (p := p) x ∧ ∀ g ∈ G, g x = x}
  mul_mem' := fun {a b} ha hb =>
    ⟨IsIntegral.mul ha.1 hb.1, fun g hg => by rw [map_mul, ha.2 g hg, hb.2 g hg]⟩
  add_mem' := fun {a b} ha hb =>
    ⟨IsIntegral.add ha.1 hb.1, fun g hg => by rw [map_add (f := _), ha.2 g hg, hb.2 g hg]⟩
  algebraMap_mem' := fun c => ⟨isIntegral_algebraMap, fun g _ => g.commutes c⟩

def Hinf (T : Tower p Ω) : Subgroup (Gal p Ω) := ⨅ n, Gn T n

def Hfix (T : Tower p Ω) (r : Ω) : Subgroup (Gal p Ω) :=
  Hinf T ⊓ MulAction.stabilizer (Gal p Ω) r

def Lev (T : Tower p Ω) (m : ℕ) : Subalgebra (O0 p) Ω :=
  Algebra.adjoin (O0 p) {T.ζ m, T.qq m}

def Vals (T : Tower p Ω) (m : ℕ) (dz dq : Ω → Ω) : Prop :=
  IsInt (p := p) (dz (T.ζ m) - p * T.ζ m / (p : Ω) ^ m) ∧ IsInt (p := p) (dz (T.qq m)) ∧
  IsInt (p := p) (dq (T.ζ m)) ∧ IsInt (p := p) (dq (T.qq m) - p * T.qq m / (p : Ω) ^ m)

def DualData (B C : Subalgebra (O0 p) Ω) {ι : Type} [Fintype ι] (u v : ι → Ω) (tr : Ω → Ω) : Prop :=
  B ≤ C ∧ (∀ x ∈ C, IsInt (p := p) x) ∧ (∀ k, u k ∈ C) ∧ (∀ k, v k ∈ C) ∧ (∀ x ∈ C, tr x ∈ B) ∧
  (∀ x ∈ C, ∀ y ∈ C, tr (x + y) = tr x + tr y) ∧ (∀ b ∈ B, ∀ x ∈ C, tr (b * x) = b * tr x) ∧
  (∀ y ∈ C, ∑ k, u k * tr (v k * y) = p * y) ∧ (∀ y ∈ C, ∑ k, v k * tr (u k * y) = p * y) ∧
  ∑ k, u k * v k = p

theorem mem_Gn {T : Tower p Ω} {n : ℕ} {g : Gal p Ω} :
    g ∈ Gn T n ↔ g (T.ζ n) = T.ζ n ∧ g (T.qq n) = T.qq n := Iff.rfl

theorem mem_Hinf {T : Tower p Ω} {g : Gal p Ω} :
    g ∈ Hinf T ↔ ∀ n, g (T.ζ n) = T.ζ n ∧ g (T.qq n) = T.qq n := by
  simp only [Hinf, Subgroup.mem_iInf, mem_Gn]

theorem mem_Hfix {T : Tower p Ω} {r : Ω} {g : Gal p Ω} :
    g ∈ Hfix T r ↔ g ∈ Hinf T ∧ g r = r := Iff.rfl

theorem int_add {x y : Ω} (hx : IsInt (p := p) x) (hy : IsInt (p := p) y) : IsInt (p := p) (x + y) := IsIntegral.add hx hy
theorem int_sub {x y : Ω} (hx : IsInt (p := p) x) (hy : IsInt (p := p) y) : IsInt (p := p) (x - y) := IsIntegral.sub hx hy
theorem int_mul {x y : Ω} (hx : IsInt (p := p) x) (hy : IsInt (p := p) y) : IsInt (p := p) (x * y) := IsIntegral.mul hx hy
theorem int_neg {x : Ω} (hx : IsInt (p := p) x) : IsInt (p := p) (-x) := IsIntegral.neg hx
theorem int_pow {x : Ω} (hx : IsInt (p := p) x) (k : ℕ) : IsInt (p := p) (x ^ k) := IsIntegral.pow hx k
theorem int_alg (c : O0 p) : IsInt (p := p) (algebraMap (O0 p) Ω c) := isIntegral_algebraMap
theorem int_zero : IsInt (p := p) (0 : Ω) := isIntegral_zero
theorem int_one : IsInt (p := p) (1 : Ω) := isIntegral_one
theorem int_nat (k : ℕ) : IsInt (p := p) (k : Ω) := by
  simpa using (int_alg (k : O0 p) : IsInt (p := p) (algebraMap (O0 p) Ω _))
theorem int_int (k : ℤ) : IsInt (p := p) (k : Ω) := by
  simpa using (int_alg (k : O0 p) : IsInt (p := p) (algebraMap (O0 p) Ω _))
theorem int_sum {ι : Type*} (s : Finset ι) (f : ι → Ω) (h : ∀ i ∈ s, IsInt (p := p) (f i)) :
    IsInt (p := p) (∑ i ∈ s, f i) := IsIntegral.sum f h
theorem int_congr {x y : Ω} (hx : IsInt (p := p) x) (h : y = x) : IsInt (p := p) y := h ▸ hx
theorem int_gal (g : Gal p Ω) {x : Ω} (hx : IsInt (p := p) x) : IsInt (p := p) (g x) :=
  IsIntegral.map (g : Ω →ₐ[O0 p] Ω) hx
theorem int_of_pow {x : Ω} {k : ℕ} (hk : 0 < k) (hx : IsInt (p := p) (x ^ k)) : IsInt (p := p) x :=
  IsIntegral.of_pow hk hx

theorem zeta_pow (T : Tower p Ω) (n j : ℕ) : T.ζ (n + j) ^ (p ^ j) = T.ζ n := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ', pow_mul, ← add_assoc, T.ζpow, ih]

theorem qq_pow (T : Tower p Ω) (n j : ℕ) : T.qq (n + j) ^ (p ^ j) = T.qq n := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ', pow_mul, ← add_assoc, T.qpow, ih]

theorem ppow_pos (n : ℕ) : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n

theorem int_zeta (T : Tower p Ω) (n : ℕ) : IsInt (p := p) (T.ζ n) :=
  int_of_pow (ppow_pos n) (by rw [(T.prim n).pow_eq_one]; exact int_one)

theorem zeta_ne (T : Tower p Ω) (n : ℕ) : T.ζ n ≠ 0 := (T.prim n).ne_zero (ppow_pos n).ne'

theorem int_zeta_inv (T : Tower p Ω) (n : ℕ) : IsInt (p := p) (T.ζ n)⁻¹ :=
  int_of_pow (ppow_pos n) (by rw [inv_pow, (T.prim n).pow_eq_one, inv_one]; exact int_one)

theorem kummerTower_qq_pow_level_eq_q (T : Tower p Ω) (n : ℕ) : T.qq n ^ (p ^ n) = algebraMap (O0 p) Ω (qO p) := by
  have := qq_pow T 0 n
  rwa [zero_add, T.q0] at this

theorem isUnit_qO : IsUnit (qO p) := by
  refine IsUnit.map _ (IsUnit.of_mul_eq_one (HahnSeries.single (-1 : ℤ) (1 : ℤ_[p])) ?_)
  rw [HahnSeries.single_mul_single]; simp

theorem int_qq (T : Tower p Ω) (n : ℕ) : IsInt (p := p) (T.qq n) :=
  int_of_pow (ppow_pos n) (by rw [kummerTower_qq_pow_level_eq_q]; exact int_alg _)

theorem qq_ne (T : Tower p Ω) (n : ℕ) : T.qq n ≠ 0 := by
  intro h
  have h1 := kummerTower_qq_pow_level_eq_q T n
  rw [h, zero_pow (ppow_pos (p := p) n).ne'] at h1
  exact ((isUnit_qO (p := p)).map (algebraMap (O0 p) Ω)).ne_zero h1.symm

theorem int_qq_inv (T : Tower p Ω) (n : ℕ) : IsInt (p := p) (T.qq n)⁻¹ := by
  refine int_of_pow (ppow_pos (p := p) n) ?_
  obtain ⟨w, hw⟩ := (isUnit_qO (p := p))
  rw [inv_pow, kummerTower_qq_pow_level_eq_q, ← hw]
  refine int_congr (int_alg (↑w⁻¹ : O0 p)) ?_
  exact inv_eq_of_mul_eq_one_right (by rw [← map_mul]; simp)

theorem Lev_int (T : Tower p Ω) (m : ℕ) : ∀ x ∈ Lev T m, IsInt (p := p) x := by
  have : Lev T m ≤ integralClosure (O0 p) Ω := by
    refine Algebra.adjoin_le ?_
    rintro x (rfl | rfl)
    · exact int_zeta T m
    · exact int_qq T m
  exact fun x hx => this hx

theorem zeta_mem_Lev (T : Tower p Ω) (m : ℕ) : T.ζ m ∈ Lev T m :=
  Algebra.subset_adjoin (by simp)

theorem qq_mem_Lev (T : Tower p Ω) (m : ℕ) : T.qq m ∈ Lev T m :=
  Algebra.subset_adjoin (by simp)

theorem Lev_mono (T : Tower p Ω) {m m' : ℕ} (h : m ≤ m') : Lev T m ≤ Lev T m' := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  refine Algebra.adjoin_le ?_
  rintro x (rfl | rfl)
  · rw [← zeta_pow T m j]; exact pow_mem (zeta_mem_Lev T _) _
  · rw [← qq_pow T m j]; exact pow_mem (qq_mem_Lev T _) _

theorem Lev_le_FixI (T : Tower p Ω) (m : ℕ) {G : Subgroup (Gal p Ω)} (hG : G ≤ Gn T m) :
    Lev T m ≤ FixI G := by
  refine Algebra.adjoin_le ?_
  rintro x (rfl | rfl)
  · exact ⟨int_zeta T m, fun g hg => (hG hg).1⟩
  · exact ⟨int_qq T m, fun g hg => (hG hg).2⟩

theorem Hinf_le (T : Tower p Ω) (m : ℕ) : Hinf T ≤ Gn T m := iInf_le _ m

theorem IsDer.mono {S S' : Subalgebra (O0 p) Ω} {D : Ω → Ω} (h : IsDer S D) (hS : S' ≤ S) :
    IsDer S' D :=
  ⟨fun x hx y hy => h.1 x (hS hx) y (hS hy), fun x hx y hy => h.2.1 x (hS hx) y (hS hy), h.2.2⟩

theorem IsDer.zero {S : Subalgebra (O0 p) Ω} {D : Ω → Ω} (h : IsDer S D) : IsInt (p := p) (D 0) := by
  simpa using h.2.2 0

theorem IsDer.one {S : Subalgebra (O0 p) Ω} {D : Ω → Ω} (h : IsDer S D) : IsInt (p := p) (D 1) := by
  simpa using h.2.2 1

theorem IsDer.sum {S : Subalgebra (O0 p) Ω} {D : Ω → Ω} (h : IsDer S D) {ι : Type*}
    (s : Finset ι) (f : ι → Ω) (hf : ∀ i ∈ s, f i ∈ S) :
    IsInt (p := p) (D (∑ i ∈ s, f i) - ∑ i ∈ s, D (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h.zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have h1 := h.1 (f a) (hf a (by simp)) (∑ i ∈ s, f i)
      (sum_mem fun i hi => hf i (by simp [hi]))
    exact int_congr (int_add h1 (ih fun i hi => hf i (by simp [hi]))) (by ring)

theorem IsDer.pow {S : Subalgebra (O0 p) Ω} {D : Ω → Ω} (h : IsDer S D)
    (hS : ∀ x ∈ S, IsInt (p := p) x) {x : Ω} (hx : x ∈ S) (k : ℕ) :
    IsInt (p := p) (D (x ^ (k + 1)) - (k + 1 : ℕ) * x ^ k * D x) := by
  induction k with
  | zero => simpa using int_zero
  | succ k ih =>
    have h1 := h.2.1 x hx (x ^ (k + 1)) (pow_mem hx _)
    refine int_congr (int_add h1 (int_mul (hS x hx) ih)) ?_
    rw [← pow_succ']; push_cast; ring

theorem IsDer.pow' {S : Subalgebra (O0 p) Ω} {D : Ω → Ω} (h : IsDer S D)
    (hS : ∀ x ∈ S, IsInt (p := p) x) {x : Ω} (hx : x ∈ S) (k : ℕ) :
    IsInt (p := p) (x * D (x ^ k) - k * x ^ k * D x) := by
  rcases k with _ | k
  · simpa using int_mul (hS x hx) h.one
  · exact int_congr (int_mul (hS x hx) (h.pow hS hx k)) (by ring)

theorem IsDer.alg_mul {S : Subalgebra (O0 p) Ω} {D : Ω → Ω} (h : IsDer S D)
    (hS : ∀ x ∈ S, IsInt (p := p) x) (c : O0 p) {x : Ω} (hx : x ∈ S) :
    IsInt (p := p) (D (algebraMap (O0 p) Ω c * x) - algebraMap (O0 p) Ω c * D x) :=
  int_congr (int_add (h.2.1 _ (S.algebraMap_mem c) x hx) (int_mul (hS x hx) (h.2.2 c))) (by ring)

theorem IsDer.sub {S : Subalgebra (O0 p) Ω} {D D' : Ω → Ω} (h : IsDer S D) (h' : IsDer S D') :
    IsDer S (fun x => D x - D' x) :=
  ⟨fun x hx y hy => int_congr (int_sub (h.1 x hx y hy) (h'.1 x hx y hy)) (by ring),
   fun x hx y hy => int_congr (int_sub (h.2.1 x hx y hy) (h'.2.1 x hx y hy)) (by ring),
   fun c => int_sub (h.2.2 c) (h'.2.2 c)⟩

theorem IsDer.smul {S : Subalgebra (O0 p) Ω} {D : Ω → Ω} (h : IsDer S D) {c : Ω}
    (hc : IsInt (p := p) c) : IsDer S (fun x => c * D x) :=
  ⟨fun x hx y hy => int_congr (int_mul hc (h.1 x hx y hy)) (by ring),
   fun x hx y hy => int_congr (int_mul hc (h.2.1 x hx y hy)) (by ring),
   fun a => int_mul hc (h.2.2 a)⟩

theorem IsDer.conj {S : Subalgebra (O0 p) Ω} {D : Ω → Ω} (h : IsDer S D) (g : Gal p Ω)
    (hg : ∀ x ∈ S, g x ∈ S) : IsDer S (fun x => g.symm (D (g x))) := by
  refine ⟨fun x hx y hy => ?_, fun x hx y hy => ?_, fun c => ?_⟩
  · refine int_congr (int_gal g.symm (h.1 _ (hg x hx) _ (hg y hy))) ?_
    simp
  · refine int_congr (int_gal g.symm (h.2.1 _ (hg x hx) _ (hg y hy))) ?_
    simp
  · refine int_gal g.symm ?_
    rw [g.commutes]; exact h.2.2 c

theorem IsDer.adjoin {S : Subalgebra (O0 p) Ω} {D : Ω → Ω} (h : IsDer S D)
    (hS : ∀ x ∈ S, IsInt (p := p) x) {t : Set Ω} (ht : t ⊆ S) (h0 : ∀ x ∈ t, IsInt (p := p) (D x)) :
    ∀ x ∈ Algebra.adjoin (O0 p) t, IsInt (p := p) (D x) := by
  have hle : Algebra.adjoin (O0 p) t ≤ S := Algebra.adjoin_le ht
  intro x hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact h0 x hx
  | algebraMap c => exact h.2.2 c
  | add x y hx hy ihx ihy =>
    exact int_congr (int_add (h.1 x (hle hx) y (hle hy)) (int_add ihx ihy)) (by ring)
  | mul x y hx hy ihx ihy =>
    exact int_congr (int_add (h.2.1 x (hle hx) y (hle hy))
      (int_add (int_mul (hS x (hle hx)) ihy) (int_mul (hS y (hle hy)) ihx))) (by ring)

end GlobalTheory.KumDlog
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LaurentSeriesPadicExistsPthPowerCombination
section
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

noncomputable section

namespace GlobalTheory.K5.LauZ

variable (p : ℕ) [hp : Fact p.Prime]

def red : Lau p →+* LaurentSeries (ZMod p) where
  toFun f := f.map (PadicInt.toZMod (p := p)).toNonUnitalRingHom
  map_one' := by
    ext n
    show PadicInt.toZMod ((1 : Lau p).coeff n) = (1 : LaurentSeries (ZMod p)).coeff n
    rw [HahnSeries.coeff_one, HahnSeries.coeff_one]
    split_ifs <;> simp
  map_mul' x y := HahnSeries.map_mul _
  map_zero' := by ext n; simp
  map_add' x y := by ext n; simp

theorem red_coeff (f : Lau p) (n : ℤ) : (red p f).coeff n = PadicInt.toZMod (f.coeff n) := rfl

def lift (F : LaurentSeries (ZMod p)) : Lau p :=
  ⟨fun n => ((F.coeff n).val : ℤ_[p]), F.isPWO_support'.mono fun n hn => by
    simp only [Function.mem_support] at hn ⊢
    intro h; apply hn; rw [h]; simp⟩

theorem red_lift (F : LaurentSeries (ZMod p)) : red p (lift p F) = F := by
  ext n
  rw [red_coeff]
  show PadicInt.toZMod (((F.coeff n).val : ℕ) : ℤ_[p]) = F.coeff n
  rw [map_natCast, ZMod.natCast_zmod_val]

theorem red_single (a : ℤ) : red p (HahnSeries.single a (1 : ℤ_[p])) = HahnSeries.single a (1 : ZMod p) := by
  ext n
  rw [red_coeff]
  by_cases h : n = a
  · subst h; simp
  · simp [HahnSeries.coeff_single_of_ne h]

theorem exists_pow_comb (f : Lau p) : ∃ (g : Fin p → Lau p) (h : Lau p),
    f = ∑ j : Fin p, HahnSeries.single ((j : ℕ) : ℤ) (1 : ℤ_[p]) * g j ^ p + (p : Lau p) * h := by
  obtain ⟨G, hG⟩ := _root_.GlobalTheory.laurentSeries_eq_sum_single_mul_pow p (red p f)
  set S : Lau p := ∑ j : Fin p, HahnSeries.single ((j : ℕ) : ℤ) (1 : ℤ_[p]) * lift p (G j) ^ p
  have hS : red p S = red p f := by
    rw [hG]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [S, map_sum, map_mul, map_pow, red_single, red_lift]
  have h0 : (f - S).map (PadicInt.toZMod (p := p)).toNonUnitalRingHom = 0 := by
    show red p (f - S) = 0
    rw [map_sub, hS, sub_self]
  obtain ⟨h, hh⟩ := (GlobalTheory.K5.Basic.dvd_iff_map p (f - S)).2 h0
  exact ⟨fun j => lift p (G j), h, by rw [← hh, add_sub_cancel]⟩

end GlobalTheory.K5.LauZ

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LogClassNumberLeLogAbsDiscrDiv
section
open NumberField

namespace GlobalTheory


open NumberField in
theorem _root_.GlobalTheory.log_classNumber_le_log_abs_discr_div :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (f : ℕ),
      Module.finrank ℚ E = 2*f →
      Real.log (classNumber E) ≤ f*(Real.log |(discr E : ℝ)|/(2*f)) +
        2*f*Real.log (1 + f*(Real.log |(discr E : ℝ)|/(2*f))) := by
  intro E _ _ _ f hf
  have hdeg : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hf0 : (f : ℝ) ≠ 0 := by
    have : f ≠ 0 := by
      rintro rfl
      omega
    exact_mod_cast this
  have key : (f : ℝ) * (Real.log |(discr E : ℝ)| / (2 * f)) = Real.log √|(discr E : ℝ)| := by
    rw [Real.log_sqrt (abs_nonneg _)]
    field_simp
  rw [key]
  have hb := _root_.GlobalTheory.classNumber_le_of_finrank_eq_two_mul E hf
  have hpos : (0 : ℝ) < classNumber E := by exact_mod_cast classNumber_pos E
  have hs : 1 ≤ √|(discr E : ℝ)| := _root_.GlobalTheory.one_le_sqrt_abs_discr E
  have hL : 0 ≤ Real.log √|(discr E : ℝ)| := Real.log_nonneg hs
  calc Real.log (classNumber E)
      ≤ Real.log (√|(discr E : ℝ)| * (1 + Real.log √|(discr E : ℝ)|) ^ (2 * f)) :=
        Real.log_le_log hpos hb
    _ = Real.log √|(discr E : ℝ)| + ((2 * f : ℕ) : ℝ) * Real.log (1 + Real.log √|(discr E : ℝ)|) := by
        rw [Real.log_mul (by linarith) (pow_ne_zero _ (by linarith)), Real.log_pow]
    _ = Real.log √|(discr E : ℝ)| + 2 * f * Real.log (1 + Real.log √|(discr E : ℝ)|) := by
        push_cast
        ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MdifferentiableHeckeOperatorsExplicit
section
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

private theorem im_mul_pos' {q : ℕ} (hq : 0 < q) {z : ℂ} (hz : 0 < z.im) : 0 < ((q : ℂ) * z).im := by
  have : (0 : ℝ) < q := by exact_mod_cast hq
  simpa using mul_pos this hz

private theorem im_div_pos' {q : ℕ} (hq : 0 < q) {z : ℂ} (hz : 0 < z.im) (j : ℕ) :
    0 < ((z + j) / (q : ℂ)).im := by
  have : (0 : ℝ) < q := by exact_mod_cast hq
  rw [Complex.div_natCast_im]
  simpa using div_pos hz this

theorem uOp_mdiff {q : ℕ} (hq : 0 < q) {f : ℍ → ℂ} (hf : MDiff f) : MDiff (uOp q f) := by
  rw [UpperHalfPlane.mdifferentiable_iff] at hf ⊢
  have h : DifferentiableOn ℂ (fun z : ℂ =>
      (q : ℂ)⁻¹ * ∑ j ∈ Finset.range q, (f ∘ ofComplex) ((z + j) / q)) {z : ℂ | 0 < z.im} := by
    refine DifferentiableOn.const_mul ?_ _
    refine DifferentiableOn.fun_sum fun j _ => ?_
    exact hf.comp (f := fun z : ℂ => (z + j) / (q : ℂ)) (by fun_prop) fun z hz => im_div_pos' hq hz j
  refine h.congr fun z hz => ?_
  simp only [Function.comp, uOp, ofComplex_apply_of_im_pos hz]

theorem vOp_mdiff {q : ℕ} (hq : 0 < q) {f : ℍ → ℂ} (hf : MDiff f) : MDiff (vOp q f) := by
  rw [UpperHalfPlane.mdifferentiable_iff] at hf ⊢
  have h : DifferentiableOn ℂ (fun z : ℂ => (f ∘ ofComplex) ((q : ℂ) * z)) {z : ℂ | 0 < z.im} :=
    hf.comp (f := fun z : ℂ => (q : ℂ) * z) (by fun_prop) fun z hz => im_mul_pos' hq hz
  refine h.congr fun z hz => ?_
  simp only [Function.comp, vOp, ofComplex_apply_of_im_pos hz]

theorem hecke_mdiff : ∀ (q : ℕ) (k : ℤ) (σ : SL(2, ℤ)) (f : ℍ → ℂ), 0 < q → MDiff f →
    MDiff (GlobalTheory.Hk.uOp q f) ∧ MDiff (GlobalTheory.Hk.vOp q f) ∧ MDiff (GlobalTheory.Hk.heckeT k q σ f) := by
  intro q k σ f hq hf
  refine ⟨uOp_mdiff hq hf, vOp_mdiff hq hf, ?_⟩
  have hs : MDiff (f ∣[k] σ) := by
    rw [ModularForm.SL_slash]
    exact MDifferentiable.slash hf k _
  exact (uOp_mdiff hq hf).add ((vOp_mdiff hq hs).const_smul _)

end GlobalTheory.Hk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemTwInv
section
noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices.CocBound

variable {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E]

def twInv (Γ : Subgroup G) (g : G) (A : E →ₗ[ℂ] E) : Submodule ℂ (G → E) :=
  GlobalTheory.TwistedInverseSubgroups.leftInvRightTwisted Γ g A

def cocyc (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) : Submodule ℂ (Γ → E) where
  carrier := {z | ∀ γ δ : Γ, z (γ * δ) = ρ (δ : G) (z γ) + z δ}
  add_mem' := by
    intro z z' h h' γ δ
    simp only [Pi.add_apply, h γ δ, h' γ δ, map_add (f := _)]
    abel
  zero_mem' := fun _ _ => by simp
  smul_mem' := by
    intro c z h γ δ
    simp only [Pi.smul_apply, h γ δ, map_smul, smul_add]

def extn (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) (s : G) : Submodule ℂ (G → E) where
  carrier := {u | (∀ γ ∈ Γ, ∀ x, u (γ * x) - u x = ρ x (u γ - u 1)) ∧ ∀ x, u (x * s) = ρ s (u x)}
  add_mem' := by
    rintro f f' ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine ⟨fun γ hγ x => ?_, fun x => by simp [h2, h2']⟩
    simp only [Pi.add_apply]
    rw [add_sub_add_comm, h1 γ hγ, h1' γ hγ, add_sub_add_comm, map_add (f := _)]
  zero_mem' := ⟨fun _ _ _ => by simp, fun _ => by simp⟩
  smul_mem' := by
    rintro c f ⟨h1, h2⟩
    refine ⟨fun γ hγ x => ?_, fun x => by simp [h2]⟩
    simp only [Pi.smul_apply]
    rw [← smul_sub, h1 γ hγ, ← smul_sub, map_smul]

def relThree (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) (t : G) : Submodule ℂ (G → E) where
  carrier := {Φ | Φ ∈ twInv Γ (t ^ 3) (ρ (t ^ 3)) ∧
    ∀ x, ρ (t ^ 2) (Φ x) + ρ t (Φ (x * t)) + Φ (x * t ^ 2) = 0}
  add_mem' := by
    rintro f f' ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine ⟨Submodule.add_mem _ h1 h1', fun x => ?_⟩
    simp only [Pi.add_apply, map_add (f := _)]
    rw [← add_zero (0 : E)]
    nth_rewrite 1 [← h2 x]
    rw [← h2' x]
    abel
  zero_mem' := ⟨Submodule.zero_mem _, fun _ => by simp⟩
  smul_mem' := by
    rintro c f ⟨h1, h2⟩
    refine ⟨Submodule.smul_mem _ c h1, fun x => ?_⟩
    simp only [Pi.smul_apply, map_smul]
    rw [← smul_add, ← smul_add, h2, smul_zero]

end GlobalTheory.HeckeFamilyMatrices.CocBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormDegreeBoundPolynomialCombination
section
open Polynomial

namespace GlobalTheory.NormDegree

noncomputable section

variable {k A : Type} [Field k] [CommRing A] [Algebra k[X] A] {n : ℕ}

theorem natDegree_norm_of_coord_degree : ∀ (k A : Type) [Field k] [Infinite k] [CommRing A] [IsDomain A] [Algebra k[X] A] (n : ℕ) (b : Module.Basis (Fin n) k[X] A), ∃ (c : ℕ) (lam : Fin n → k),
 (∀ (d : ℕ) (p : Fin n → k[X]), (∀ i, (p i).natDegree ≤ d) → (Algebra.norm k[X] (∑ i, p i • b i)).natDegree ≤ n * d + c) ∧
 (∀ (d : ℕ) (p : Fin n → k[X]), (∀ i, (p i).degree < d) → (∑ i, (C (lam i) * X ^ d + p i) • b i) ≠ 0 ∧ (Algebra.norm k[X] (∑ i, (C (lam i) * X ^ d + p i) • b i)).natDegree = n * d + c) := by
  first
  | exact @_root_.GlobalTheory.NormFormBound.norm_degree
  | exact _root_.GlobalTheory.NormFormBound.norm_degree
  | (apply _root_.GlobalTheory.NormFormBound.norm_degree <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormFormBound.norm_degree <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormFormBound.norm_degree <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormFormBound.norm_degree ..)

end

end GlobalTheory.NormDegree
end

