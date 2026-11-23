module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimitiveHahnSeriesInvertibleModPrimePow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0106
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCochainEqDlogCombinationFiniteLevel
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0053
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLogDerivQExpansionModPrimePowOfTranslation
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.DlEx

variable {Ω : Type} [Field Ω]

def Sp (L : ℕ) (x : HahnSeries ℚ Ω) : Prop := ∀ r : ℚ, x.coeff r ≠ 0 → (r * L).den = 1

lemma den_add {a b : ℚ} (ha : a.den = 1) (hb : b.den = 1) : (a + b).den = 1 := by
  rw [Rat.den_eq_one_iff] at ha hb
  rw [← ha, ← hb, ← Int.cast_add]; simp

lemma exists_of_coeff_mul_ne {x y : HahnSeries ℚ Ω} {r : ℚ} (h : (x * y).coeff r ≠ 0) :
    ∃ r₁ r₂, r₁ + r₂ = r ∧ x.coeff r₁ ≠ 0 ∧ y.coeff r₂ ≠ 0 := by
  rw [HahnSeries.coeff_mul] at h
  obtain ⟨ij, hij, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [Finset.mem_antidiagonal] at hij
  exact ⟨ij.1, ij.2, hij.2.2, left_ne_zero_of_mul hne, right_ne_zero_of_mul hne⟩

lemma sp_mul {L : ℕ} {x y : HahnSeries ℚ Ω} (hx : Sp L x) (hy : Sp L y) : Sp L (x * y) := by
  intro r hr
  obtain ⟨r₁, r₂, rfl, h1, h2⟩ := exists_of_coeff_mul_ne hr
  rw [add_mul]; exact den_add (hx _ h1) (hy _ h2)

lemma sp_sub {L : ℕ} {x y : HahnSeries ℚ Ω} (hx : Sp L x) (hy : Sp L y) : Sp L (x - y) := by
  intro r hr
  rw [HahnSeries.coeff_sub] at hr
  by_cases h : x.coeff r = 0
  · exact hy r (by intro h'; apply hr; rw [h, h', sub_zero])
  · exact hx r h

variable [Algebra ℚ Ω]

lemma sp_theta {L : ℕ} (s : ℚ) {x : HahnSeries ℚ Ω} (hx : Sp L x) : Sp L (theta s x) := by
  intro r hr
  exact hx r (fun h => hr (by simp [theta, h]))

lemma intA_mul (A : ValuationSubring Ω) {x y : HahnSeries ℚ Ω} (hx : ∀ r, x.coeff r ∈ A)
    (hy : ∀ r, y.coeff r ∈ A) (r : ℚ) : (x * y).coeff r ∈ A := by
  rw [HahnSeries.coeff_mul]
  exact Subring.sum_mem A.toSubring (fun ij _ => mul_mem (hx _) (hy _))

lemma intA_sub (A : ValuationSubring Ω) {x y : HahnSeries ℚ Ω} (hx : ∀ r, x.coeff r ∈ A)
    (hy : ∀ r, y.coeff r ∈ A) (r : ℚ) : (x - y).coeff r ∈ A := by
  rw [HahnSeries.coeff_sub]; exact sub_mem (hx r) (hy r)

lemma intA_theta (A : ValuationSubring Ω) {L : ℕ} {x : HahnSeries ℚ Ω} (hx : ∀ r, x.coeff r ∈ A)
    (hs : Sp L x) (r : ℚ) : (theta (L : ℚ) x).coeff r ∈ A := by
  show algebraMap ℚ Ω ((L : ℚ) * r) * x.coeff r ∈ A
  by_cases h : x.coeff r = 0
  · rw [h, mul_zero]; exact zero_mem A
  · have hd := hs r h
    rw [Rat.den_eq_one_iff] at hd
    rw [mul_comm (L : ℚ) r, ← hd, map_intCast]
    exact mul_mem (intCast_mem A _) (hx r)

end GlobalTheory.DlEx


open GlobalTheory.DlEx in
theorem GlobalTheory.dl_exists : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (n L : ℕ) (f : X.K), 0 < L → f ≠ 0 → f ∈ KT X L → ∃ φ : HahnSeries ℚ Ω, IsDl X A l n L f φ ∧ ∀ r : ℚ, φ.coeff r ≠ 0 → (r * L).den = 1 := by
  intro Ω _ _ _ ε X hj l _ A hl n L f hL hf hfK
  obtain ⟨a, b, κ, S, hκ, hfb, ha, hb, hbinv, -⟩ := _root_.GlobalTheory.exists_prim_frac_level_one ε X hj l A hl f hf
  have hbK : b ∈ KT X L := (RingHom.mem_eqLocusField).2 (hbinv _)
  have hcK : algebraMap Ω X.K κ ∈ KT X L := (RingHom.mem_eqLocusField).2 ((X.sl _).commutes κ)
  have haK : a ∈ KT X L := by
    have e : a = (algebraMap Ω X.K κ)⁻¹ * (f * b) := by
      rw [hfb, ← mul_assoc, inv_mul_cancel₀ ((map_ne_zero _).2 hκ), one_mul]
    rw [e]; exact (KT X L).mul_mem ((KT X L).inv_mem hcK) ((KT X L).mul_mem hfK hbK)
  have hsa : Sp L (X.exp a) := (_root_.GlobalTheory.Glue.KTExp.mem_KT_iff ε X L hL a).1 haK
  have hsb : Sp L (X.exp b) := (_root_.GlobalTheory.Glue.KTExp.mem_KT_iff ε X L hL b).1 hbK
  have hP : Prim A (X.exp a * X.exp b) := _root_.GlobalTheory.Glue.Prim.mul A _ _ ha hb
  obtain ⟨Q, hQA, hQs, hQP⟩ := _root_.GlobalTheory.prim_inv_mod_pow l A hl n L (X.exp a * X.exp b) hL hP (sp_mul hsa hsb)
  have hDA : ∀ r, (theta (L:ℚ) (X.exp a) * X.exp b - X.exp a * theta (L:ℚ) (X.exp b)).coeff r ∈ A :=
    intA_sub A (intA_mul A (intA_theta A ha.1 hsa) hb.1) (intA_mul A ha.1 (intA_theta A hb.1 hsb))
  have hDs : Sp L (theta (L:ℚ) (X.exp a) * X.exp b - X.exp a * theta (L:ℚ) (X.exp b)) :=
    sp_sub (sp_mul (sp_theta _ hsa) hsb) (sp_mul hsa (sp_theta _ hsb))
  refine ⟨Q * (theta (L:ℚ) (X.exp a) * X.exp b - X.exp a * theta (L:ℚ) (X.exp b)),
    ⟨intA_mul A hQA hDA, a, b, κ, hκ, hfb, ha, hb, ?_⟩, sp_mul hQs hDs⟩
  intro r
  generalize theta (L:ℚ) (X.exp a) * X.exp b - X.exp a * theta (L:ℚ) (X.exp b) = D at hDA ⊢
  choose z hzA hz using hQP
  have e : (Q * D * X.exp a * X.exp b).coeff r - D.coeff r = (D * (Q * (X.exp a * X.exp b) - 1)).coeff r := by
    rw [show Q * D * X.exp a * X.exp b = D * (Q * (X.exp a * X.exp b)) by ring, mul_sub, mul_one,
      HahnSeries.coeff_sub]
  refine ⟨∑ ij ∈ Finset.addAntidiagonal D.isPWO_support (Q * (X.exp a * X.exp b) - 1).isPWO_support r,
    D.coeff ij.1 * z ij.2, Subring.sum_mem A.toSubring (fun ij _ => mul_mem (hDA _) (hzA _)), ?_⟩
  rw [e, HahnSeries.coeff_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun ij _ => ?_)
  rw [HahnSeries.coeff_sub, hz ij.2]; ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HodgeTateCupKummerClassesEqDlogDeterminant
section
open GlobalTheory.K5 Polynomial

noncomputable section

namespace GlobalTheory.K5.KummerCup

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem map_mk_mem {n : ℕ} (f : On p n →ₐ[O0 p] Ω) (S : Subalgebra (O0 p) Ω) (hx : f (xn p n) ∈ S)
    (hy : f (yn p n) ∈ S) (x : On p n) : f x ∈ S := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hC : ∀ Q : Polynomial (O0 p), f (Ideal.Quotient.mk (towerIdeal p n) (C Q)) ∈ S := by
    intro Q
    induction Q using Polynomial.induction_on' with
    | add a b ha hb =>
      rw [(C : Polynomial (O0 p) →+* Polynomial (Polynomial (O0 p))).map_add,
        (Ideal.Quotient.mk (towerIdeal p n)).map_add, map_add (f := f)]
      exact S.add_mem ha hb
    | monomial j b =>
      rw [← C_mul_X_pow_eq_monomial, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow]
      refine S.mul_mem ?_ (S.pow_mem hx j)
      have e : (Ideal.Quotient.mk (towerIdeal p n)) (C (C b)) = algebraMap (O0 p) (On p n) b := rfl
      rw [e, f.commutes]
      exact S.algebraMap_mem b
  induction P using Polynomial.induction_on' with
  | add a b ha hb =>
    rw [(Ideal.Quotient.mk (towerIdeal p n)).map_add, map_add (f := f)]
    exact S.add_mem ha hb
  | monomial j Q =>
    rw [← C_mul_X_pow_eq_monomial, map_mul, map_mul, map_pow, map_pow]
    exact S.mul_mem (hC Q) (S.pow_mem hy j)

theorem pp_ne (m : ℕ) : p ^ m ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero

theorem q_pow (T : Tower p Ω) : ∀ m, T.qq m ^ (p ^ m) = T.qq 0
  | 0 => by simp
  | m + 1 => by rw [pow_succ', pow_mul, T.qpow, q_pow T m]

theorem qO_unit : IsUnit (qO p) := by
  have : IsUnit (HahnSeries.single (1 : ℤ) (1 : ℤ_[p]) : Lau p) := by
    refine ⟨⟨HahnSeries.single (1 : ℤ) (1 : ℤ_[p]), HahnSeries.single (-1 : ℤ) (1 : ℤ_[p]), ?_, ?_⟩, rfl⟩
    · rw [HahnSeries.single_mul_single]; simp
    · rw [HahnSeries.single_mul_single]; simp
  exact this.map _

theorem qq_ne_zero (T : Tower p Ω) (m : ℕ) : T.qq m ≠ 0 := by
  intro h
  have h0 := q_pow T m
  rw [h, zero_pow (pp_ne m), T.q0] at h0
  exact ((qO_unit (p := p)).map (algebraMap (O0 p) Ω)).ne_zero h0.symm

theorem zeta_mem (T : Tower p Ω) (m : ℕ) : T.ζ m ∈ integralClosure (O0 p) Ω := by
  refine IsIntegral.of_pow (Nat.pos_of_ne_zero (pp_ne (p := p) m)) ?_
  rw [(T.prim m).pow_eq_one]
  exact isIntegral_one

theorem qq_mem (T : Tower p Ω) (m : ℕ) : T.qq m ∈ integralClosure (O0 p) Ω := by
  refine IsIntegral.of_pow (Nat.pos_of_ne_zero (pp_ne (p := p) m)) ?_
  rw [q_pow, T.q0]
  exact isIntegral_algebraMap

theorem zeta_sub_one_ne (T : Tower p Ω) {n : ℕ} (hn : 1 ≤ n) : T.ζ n - 1 ≠ 0 :=
  sub_ne_zero.mpr ((T.prim n).ne_one (Nat.one_lt_pow (by omega) (Fact.out : p.Prime).one_lt))

theorem p_div_mem (T : Tower p Ω) {n : ℕ} (hn : 1 ≤ n) :
    (p : Ω) / (T.ζ n - 1) ∈ integralClosure (O0 p) Ω := by
  classical
  have hne := zeta_sub_one_ne T hn
  have hpos : 0 < p ^ n := Nat.pos_of_ne_zero (pp_ne n)
  have h1 : eval 1 (cyclotomic (p ^ n) Ω) = (p : Ω) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact eval_one_cyclotomic_prime_pow m
  rw [cyclotomic_eq_prod_X_sub_primitiveRoots (T.prim n), eval_prod,
    ← Finset.mul_prod_erase _ _ ((mem_primitiveRoots hpos).mpr (T.prim n))] at h1
  have hR : (∏ μ ∈ (primitiveRoots (p ^ n) Ω).erase (T.ζ n), eval 1 (X - C μ)) ∈
      integralClosure (O0 p) Ω := by
    refine Subalgebra.prod_mem _ fun μ hμ => ?_
    have hμ' := (mem_primitiveRoots hpos).mp (Finset.mem_of_mem_erase hμ)
    simp only [eval_sub, eval_X, eval_C]
    refine Subalgebra.sub_mem _ (Subalgebra.one_mem _) ?_
    refine IsIntegral.of_pow hpos ?_
    rw [hμ'.pow_eq_one]
    exact isIntegral_one
  generalize (∏ μ ∈ (primitiveRoots (p ^ n) Ω).erase (T.ζ n), eval 1 (X - C μ)) = R at h1 hR
  simp only [eval_sub, eval_X, eval_C] at h1
  have : (p : Ω) / (T.ζ n - 1) = -R := by
    rw [div_eq_iff hne, ← h1]; ring
  rw [this]
  exact Subalgebra.neg_mem _ hR

theorem mem_Gn {T : Tower p Ω} {n : ℕ} {g : Gal p Ω} :
    g ∈ Gn T n ↔ g (T.ζ n) = T.ζ n ∧ g (T.qq n) = T.qq n := Iff.rfl

theorem fix_emb {T : Tower p Ω} {n : ℕ} {ι : On p n →ₐ[O0 p] Ω} (hι : IsEmb T n ι) {g : Gal p Ω}
    (hg : g ∈ Gn T n) (x : On p n) : g (ι x) = ι x :=
  map_mk_mem ι (AlgHom.equalizer (g : Ω →ₐ[O0 p] Ω) (AlgHom.id _ _))
    (by rw [hι.1]; exact (mem_Gn.mp hg).1) (by rw [hι.2]; exact (mem_Gn.mp hg).2) x

theorem emb_mem {T : Tower p Ω} {n : ℕ} {ι : On p n →ₐ[O0 p] Ω} (hι : IsEmb T n ι) (x : On p n) :
    ι x ∈ integralClosure (O0 p) Ω :=
  map_mk_mem ι _ (by rw [hι.1]; exact zeta_mem T n) (by rw [hι.2]; exact qq_mem T n) x

theorem kum_add {T : Tower p Ω} {n : ℕ} {r : Ω} (hr : r ≠ 0) {a : Gal p Ω → ZMod (p ^ n)}
    (ha : IsKum T n (Gn T n) r a) {g h : Gal p Ω} (hg : g ∈ Gn T n) (hh : h ∈ Gn T n) :
    a (g * h) = a g + a h := by
  haveI : NeZero (p ^ n) := ⟨pp_ne n⟩
  have h1 := ha _ ((Gn T n).mul_mem hg hh)
  rw [AlgEquiv.mul_apply, ha h hh, map_mul, map_pow, (mem_Gn.mp hg).1, ha g hg, ← mul_assoc,
    ← pow_add] at h1
  have h2 := mul_right_cancel₀ hr h1
  rw [← pow_mod_orderOf, ← (T.prim n).eq_orderOf] at h2
  have h3 := (T.prim n).pow_inj (Nat.mod_lt _ (Nat.pos_of_ne_zero (pp_ne n))) (ZMod.val_lt _) h2
  apply ZMod.val_injective
  rw [ZMod.val_add, ← h3, add_comm]

theorem kum_eq {T : Tower p Ω} {n : ℕ} {r : Ω} (hr : r ≠ 0) {a : Gal p Ω → ZMod (p ^ n)}
    (ha : IsKum T n (Gn T n) r a) {g h : Gal p Ω} (hg : g ∈ Gn T n) (hh : h ∈ Gn T n)
    (e : h r = g r) : a h = a g := by
  haveI : NeZero (p ^ n) := ⟨pp_ne n⟩
  rw [ha g hg, ha h hh] at e
  exact ZMod.val_injective _
    ((T.prim n).pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (mul_right_cancel₀ hr e))


open Classical in
def ext0 {M : Type} [Zero M] (H : Subgroup (Gal p Ω)) (a : Gal p Ω → M) (g : Gal p Ω) : M :=
  if g ∈ H then a g else 0

theorem cochainExtendByZeroSubgroup_of_mem {M : Type} [Zero M] {H : Subgroup (Gal p Ω)} (a : Gal p Ω → M) {g : Gal p Ω}
    (hg : g ∈ H) : ext0 H a g = a g := if_pos hg

theorem matrixExtendByZero_add {T : Tower p Ω} {n : ℕ} {r : Ω} (hr : r ≠ 0) {a : Gal p Ω → ZMod (p ^ n)}
    (ha : IsKum T n (Gn T n) r a) : ∀ g ∈ Gn T n, ∀ h ∈ Gn T n,
    ext0 (Gn T n) a (g * h) = ext0 (Gn T n) a g + ext0 (Gn T n) a h := by
  intro g hg h hh
  rw [cochainExtendByZeroSubgroup_of_mem a hg, cochainExtendByZeroSubgroup_of_mem a hh, cochainExtendByZeroSubgroup_of_mem a ((Gn T n).mul_mem hg hh), kum_add hr ha hg hh]

theorem cochainExtendByZero_kummer_congr_of_action {T : Tower p Ω} {n : ℕ} {r : Ω} (hr : r ≠ 0) {a : Gal p Ω → ZMod (p ^ n)}
    (ha : IsKum T n (Gn T n) r a) {g h : Gal p Ω} (e1 : h (T.ζ n) = g (T.ζ n))
    (e2 : h (T.qq n) = g (T.qq n)) (e : h r = g r) : ext0 (Gn T n) a h = ext0 (Gn T n) a g := by
  have hiff : h ∈ Gn T n ↔ g ∈ Gn T n := by rw [mem_Gn, mem_Gn, e1, e2]
  by_cases hg : g ∈ Gn T n
  · rw [cochainExtendByZeroSubgroup_of_mem a hg, cochainExtendByZeroSubgroup_of_mem a (hiff.mpr hg), kum_eq hr ha hg (hiff.mpr hg) e]
  · unfold ext0
    rw [if_neg hg, if_neg (fun hh => hg (hiff.mp hh))]

theorem kummerTower_coboundaryOne_prime_smul {k : ℕ} {H : Subgroup (Gal p Ω)} {f f' : Gal p Ω → Ω} (hf : Cob1 k H f)
    (e : ∀ g ∈ H, f' g = (p : Ω) * f g) : Cob1 k H f' := by
  obtain ⟨x, hx, h⟩ := hf
  have hp : IsIntegral (O0 p) (p : Ω) := (integralClosure (O0 p) Ω).natCast_mem p
  refine ⟨(p : Ω) * x, hp.mul hx, fun g hg => ?_⟩
  obtain ⟨z, hz, hz'⟩ := h g hg
  refine ⟨(p : Ω) * z, hp.mul hz, ?_⟩
  rw [e g hg, map_mul, map_natCast]
  linear_combination (p : Ω) * hz'

theorem kummerTower_coboundaryTwo_congr {k : ℕ} {H : Subgroup (Gal p Ω)} {f f' : Gal p Ω → Gal p Ω → Ω} (hf : Cob2 k H f)
    (e : ∀ g ∈ H, ∀ h ∈ H, f' g h = f g h) : Cob2 k H f' := by
  obtain ⟨w, hw, h⟩ := hf
  exact ⟨w, hw, fun g hg g' hg' => (e g hg g' hg') ▸ h g hg g' hg'⟩

theorem root_ne_zero {T : Tower p Ω} {n : ℕ} (hn : 1 ≤ n) (ι : On p n →ₐ[O0 p] Ω) {k : ℤ}
    {w : (On p n)ˣ} {r : Ω} (hr : r ^ (p ^ n) = (T.ζ n - 1) ^ k * ι w) : r ≠ 0 := by
  rintro rfl
  rw [zero_pow (pp_ne n)] at hr
  exact mul_ne_zero (zpow_ne_zero k (zeta_sub_one_ne T hn)) (w.isUnit.map ι).ne_zero hr.symm

theorem coef_int {T : Tower p Ω} {n : ℕ} (hn : 1 ≤ n) {ι : On p n →ₐ[O0 p] Ω} (hι : IsEmb T n ι)
    (c : ℕ) (k : ℤ) (β : On p n) :
    IsInt (p := p) ((p : Ω) ^ (c + 1) * (ι β + (k : Ω) * T.ζ n / (T.ζ n - 1))) := by
  have hp : (p : Ω) ∈ integralClosure (O0 p) Ω := (integralClosure (O0 p) Ω).natCast_mem p
  have e : (p : Ω) ^ (c + 1) * (ι β + (k : Ω) * T.ζ n / (T.ζ n - 1)) =
      (p : Ω) ^ (c + 1) * ι β + (p : Ω) ^ c * (k : Ω) * T.ζ n * ((p : Ω) / (T.ζ n - 1)) := by ring
  rw [e]
  exact add_mem (mul_mem (pow_mem hp _) (emb_mem hι β))
    (mul_mem (mul_mem (mul_mem (pow_mem hp _) (intCast_mem _ k)) (zeta_mem T n)) (p_div_mem T hn))

theorem coef_int' {T : Tower p Ω} {n : ℕ} {ι : On p n →ₐ[O0 p] Ω} (hι : IsEmb T n ι)
    (c : ℕ) (α : On p n) : IsInt (p := p) ((p : Ω) ^ c * ι α) := by
  have hp : (p : Ω) ∈ integralClosure (O0 p) Ω := (integralClosure (O0 p) Ω).natCast_mem p
  exact mul_mem (pow_mem hp _) (emb_mem hι α)

theorem coef_fix {T : Tower p Ω} {n : ℕ} {ι : On p n →ₐ[O0 p] Ω} (hι : IsEmb T n ι) {g : Gal p Ω}
    (hg : g ∈ Gn T n) (k : ℤ) (β : On p n) :
    g (ι β + (k : Ω) * T.ζ n / (T.ζ n - 1)) = ι β + (k : Ω) * T.ζ n / (T.ζ n - 1) := by
  rw [map_add (f := _), map_div₀, map_mul, map_sub, map_one, map_intCast, fix_emb hι hg, (mem_Gn.mp hg).1]

theorem cup_kummer_dlog : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (n : ℕ), 1 ≤ n → ∀ ι : On p n →ₐ[O0 p] Ω, IsEmb T n ι →
  ∀ (k l : ℤ) (w w' : (On p n)ˣ) (α β α' β' : On p n), IsDlog p n (w : On p n) α β → IsDlog p n (w' : On p n) α' β' →
  ∀ r s : Ω, r ^ (p ^ n) = (T.ζ n - 1) ^ k * ι w → s ^ (p ^ n) = (T.ζ n - 1) ^ l * ι w' →
  ∀ a b lz lq : Gal p Ω → ZMod (p ^ n), IsKum T n (Gn T n) r a → IsKum T n (Gn T n) s b →
    IsKum T n (Gn T n) (T.ζ (2 * n)) lz → IsKum T n (Gn T n) (T.qq (2 * n)) lq →
    Cob2 n (Gn T n) (fun g h => (p : Ω) ^ c * (((a g).val : Ω) * ((b h).val : Ω)) +
      (p : Ω) ^ c * (ι (fPi p n k l α β α' β') / (T.ζ n - 1)) * (((lz g).val : Ω) * ((lq h).val : Ω))) := by
  intro p _ hp2
  classical
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.KumDlog.kummer_eq_dlog p hp2
  refine ⟨4 * (c + 1), ?_⟩
  intro Ω _ _ hΩ T n hn ι hι k l w w' α β α' β' hw hw' r s hr hs a b lz lq ha hb hz hq
  have r0 := root_ne_zero hn ι hr
  have s0 := root_ne_zero hn ι hs
  have z0 : T.ζ (2 * n) ≠ 0 := (T.prim (2 * n)).ne_zero (pp_ne _)
  have q0 := qq_ne_zero T (2 * n)
  have h1 := hc Ω hΩ T n hn ι hι k w α β hw r hr a lz lq ha hz hq
  have h2 := hc Ω hΩ T n hn ι hι l w' α' β' hw' s hs b lz lq hb hz hq
  have key := GlobalTheory.T.kummer_cochain_cup_product_congruence p hp2 Ω (Gn T n) n (c + 1) (ext0 (Gn T n) a) (ext0 (Gn T n) b)
    (ext0 (Gn T n) lz) (ext0 (Gn T n) lq) (ι α) (ι β + (k : Ω) * T.ζ n / (T.ζ n - 1))
    (ι α') (ι β' + (l : Ω) * T.ζ n / (T.ζ n - 1))
    (matrixExtendByZero_add r0 ha) (matrixExtendByZero_add s0 hb) (matrixExtendByZero_add z0 hz) (matrixExtendByZero_add q0 hq)
    (fun g hg => ⟨fix_emb hι hg _, coef_fix hι hg _ _, fix_emb hι hg _, coef_fix hι hg _ _⟩)
    (coef_int' hι _ _) (coef_int hn hι _ _ _) (coef_int' hι _ _) (coef_int hn hι _ _ _)
    (fun g => ⟨{T.ζ n, T.qq n, r, s, T.ζ (2 * n), T.qq (2 * n)}, fun h hS =>
      ⟨cochainExtendByZero_kummer_congr_of_action r0 ha (hS _ (by simp)) (hS _ (by simp)) (hS _ (by simp)),
       cochainExtendByZero_kummer_congr_of_action s0 hb (hS _ (by simp)) (hS _ (by simp)) (hS _ (by simp)),
       cochainExtendByZero_kummer_congr_of_action z0 hz (hS _ (by simp)) (hS _ (by simp)) (hS _ (by simp)),
       cochainExtendByZero_kummer_congr_of_action q0 hq (hS _ (by simp)) (hS _ (by simp)) (hS _ (by simp))⟩⟩)
    (kummerTower_coboundaryOne_prime_smul h1 fun g hg => by simp only [cochainExtendByZeroSubgroup_of_mem _ hg]; ring)
    (kummerTower_coboundaryOne_prime_smul h2 fun g hg => by simp only [cochainExtendByZeroSubgroup_of_mem _ hg]; ring)
  refine kummerTower_coboundaryTwo_congr key fun g hg h hh => ?_
  have hne := zeta_sub_one_ne T hn
  have e : ι (fPi p n k l α β α' β') / (T.ζ n - 1) =
      ι α * (ι β' + (l : Ω) * T.ζ n / (T.ζ n - 1)) - (ι β + (k : Ω) * T.ζ n / (T.ζ n - 1)) * ι α' := by
    simp only [fPi, map_sub, map_mul, map_add (f := _), map_intCast, map_one, hι.1]
    field_simp
    ring
  simp only [cochainExtendByZeroSubgroup_of_mem _ hg, cochainExtendByZeroSubgroup_of_mem _ hh, e]

end GlobalTheory.K5.KummerCup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemChainVecsDet
section
noncomputable section

namespace GlobalTheory.GLp.Supp

open Polynomial GlobalTheory.GLq GlobalTheory.GLp TensorProduct
open scoped Classical

variable {g : ℕ} [Fact g.Prime]

def IsUnram (ν : ℚ_[g]ˣ →* ℂˣ) : Prop :=
  ∀ u : ℤ_[g]ˣ, ν (Units.map (algebraMap ℤ_[g] ℚ_[g]).toMonoidHom u) = 1

def MapsToProd {n a b : ℕ} {V W W' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] (π : Representation ℂ (GL (Fin n) ℚ_[g]) V)
    (σ : Representation ℂ (GL (Fin a) ℚ_[g]) W) (ρ : Representation ℂ (GL (Fin b) ℚ_[g]) W') : Prop :=
  n = a + b ∧ ∃ (ν₁ ν₂ : ℚ_[g]ˣ →* ℂˣ) (Λ : V →ₗ[ℂ] W ⊗[ℂ] W'), IsUnram ν₁ ∧ IsUnram ν₂ ∧ Λ ≠ 0 ∧
    ∀ (p : GL (Fin n) ℚ_[g]) (x : GL (Fin a) ℚ_[g]) (y : GL (Fin b) ℚ_[g]),
    (∀ i j : Fin n, (j : ℕ) < a → a ≤ (i : ℕ) → (p : Matrix (Fin n) (Fin n) ℚ_[g]) i j = 0) →
    (∀ i j : Fin a, (x : Matrix (Fin a) (Fin a) ℚ_[g]) i j =
      Formalism.MainNotions.ArithmeticCylinders.entN (p : Matrix (Fin n) (Fin n) ℚ_[g]) i j) →
    (∀ i j : Fin b, (y : Matrix (Fin b) (Fin b) ℚ_[g]) i j =
      Formalism.MainNotions.ArithmeticCylinders.entN (p : Matrix (Fin n) (Fin n) ℚ_[g]) (a + i) (a + j)) →
    ∀ v, Λ (π p v) = ((ν₁ (Matrix.GeneralLinearGroup.det x) * ν₂ (Matrix.GeneralLinearGroup.det y) : ℂˣ) : ℂ) •
      TensorProduct.map (σ x) (ρ y) (Λ v)

abbrev GLRep (g : ℕ) [Fact g.Prime] : Type 1 := Σ n : ℕ, Rep.{0} ℂ (GL (Fin n) ℚ_[g])

inductive InInd : GLRep g → List (GLRep g) → Prop
  | nil (π : GLRep g) : π.1 = 0 → IsIrrRep π.2.ρ → InInd π []
  | cons (π σ ρ : GLRep g) (S : List (GLRep g)) : IsIrrRep π.2.ρ → IsIrrRep ρ.2.ρ → InInd σ S →
      MapsToProd π.2.ρ σ.2.ρ ρ.2.ρ → InInd π (ρ :: S)

end GlobalTheory.GLp.Supp
end
end

