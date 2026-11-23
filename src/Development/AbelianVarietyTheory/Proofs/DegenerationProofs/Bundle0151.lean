module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSumReindex
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstOfNormPeriodic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TxStOfPtSt
section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators
noncomputable section
namespace GlobalTheory.Ex.Arch
variable {O : Type} [CommRing O] [StarRing O] {N : NumD ℂ} {B : AnArc O}

namespace Dict
variable (d : Dict N B)

theorem tx_ex_zero : d.ex 0 = 1 := (d.ab.2.2.1 0).2 B.abelian₂.zero_mem

theorem tx_ex_smul (n : ℕ) (x : Fin B.gB → ℂ) : d.ex ((n : ℂ) • x) = d.ex x ^ n := by
  induction n with
  | zero => simp [d.tx_ex_zero]
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, d.ab.1, ih, pow_succ]

theorem tx_ex_neg (x : Fin B.gB → ℂ) : d.ex (-x) = (d.ex x)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← d.ab.1, neg_add_cancel, d.tx_ex_zero])

theorem tx_dbl (x : Fin B.gB → ℂ) : dbl N.θ N.σ (d.ex x) * d.fr (x + x) = d.fr x ^ 4 := by
  have a := d.ab.2.2.2.2.2.1 x (-x) x
  have b := d.ab.2.2.2.2.2.2.1 x
  rw [add_neg_cancel, neg_add_cancel, zero_add, d.ab.2.2.2.1, d.tx_ex_neg] at a
  replace a := congrArg Additive.ofMul a
  replace b := congrArg Additive.ofMul b
  apply Additive.ofMul.injective
  simp only [dbl, ofMul_mul, ofMul_div, ofMul_pow, ofMul_one] at a b ⊢
  linear_combination (norm := abel) a - b

theorem tx_cubN (x : Fin B.gB → ℂ) (i : ℕ) :
    cubN N.θ i 1 (d.ex x) (d.ex x) * d.fr ((i : ℂ) • x) * d.fr x * d.fr (x + x) ^ i =
      d.fr ((i : ℂ) • x + x) * d.fr x ^ (2 * i) := by
  induction i with
  | zero => simp [cubN, d.ab.2.2.2.1]
  | succ i ih =>
    have a := d.ab.2.2.2.2.2.1 ((i : ℂ) • x) x x
    rw [d.tx_ex_smul] at a
    rw [cubN] at ih
    rw [cubN, Finset.prod_range_succ, Nat.cast_succ, add_smul, one_smul, one_mul, Nat.mul_succ, pow_add (d.fr x), pow_succ (d.fr (x + x))]
    replace a := congrArg Additive.ofMul a
    replace ih := congrArg Additive.ofMul ih
    apply Additive.ofMul.injective
    simp only [ofMul_mul, sq] at a ih ⊢
    linear_combination (norm := abel) a + ih

theorem tx_cubN_div (x : Fin B.gB → ℂ) (i : ℕ) :
    cubN N.θ i 1 (d.ex x) (d.ex x) / dbl N.θ N.σ (d.ex x) ^ i * d.fr ((i : ℂ) • x) * d.fr x * d.fr x ^ (2 * i) =
      d.fr ((i : ℂ) • x + x) := by
  have a := congrArg Additive.ofMul (d.tx_cubN x i)
  have b := congrArg (fun t => Additive.ofMul (t ^ i)) (d.tx_dbl x)
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_pow] at a b ⊢
  linear_combination (norm := module) a - b

theorem tx_mulq (x : Fin B.gB → ℂ) (n : ℕ) :
    mulq N.θ N.σ n (d.ex x) * d.fr x ^ (n ^ 2) = d.fr ((n : ℂ) • x) := by
  induction n with
  | zero => simp [mulq, d.ab.2.2.2.1]
  | succ n ih =>
    rw [mulq] at ih
    rw [mulq, Finset.prod_range_succ, Nat.cast_succ, add_smul, one_smul, ← d.tx_cubN_div, ← ih,
      show (n + 1) ^ 2 = n ^ 2 + 1 + 2 * n by ring, pow_add, pow_succ]
    simp only [mul_assoc, mul_left_comm]

theorem tx_isPt_pow (h : PtSt) {v : B.V} {g : N.Gt} (hg : d.IsPt v g) (n : ℕ) : d.IsPt ((n : ℂ) • v) (g ^ n) := by
  obtain ⟨-, -, h3, h4, -⟩ := h O N B d
  induction n with
  | zero =>
    rw [pow_zero, h4]
    exact ⟨0, rfl, by simp⟩
  | succ n ih =>
    rw [Nat.cast_succ, add_smul, one_smul, pow_succ]
    exact h3 _ _ _ _ ih hg

theorem tx_vt {v : B.V} {g : N.Gt} (hg : d.IsPt v g) (x : B.X) :
    N.vt g (d.eX x) = B.term 1 0 d.th x v * d.fr v.2 := by
  have a := hg.2 x
  have b := congrArg Units.val (d.ψ_eq x)
  rw [NumD.vt, hg.1, d.c_eq, ← d.ab.1, d.ab.2.2.2.2.2.2.2.2, AnArc.term, add_comm v.2, ← b]
  simp only [Units.val_mul, pow_one, map_zero, AnArc.e_zero, zero_add, one_smul]
  linear_combination (N.ψ (d.eX x) : ℂ) * d.th (B.ct x + v.2) * a
end Dict

theorem Dict.tx_wQ (d : Dict N B) {k t : ℕ} (hk : k = 2 * t + 1) {la : B.La} {p : N.QT k} (hp : d.Rep k la p) :
    (N.wQ p : ℂ) * d.fr ((k : ℂ)⁻¹ • B.P0 la).2 ^ k * B.ah la.l (B.ct la.y) =
      B.psi la.y * Complex.exp (lin B la (B.P0 la) / k) ^ t := by
  obtain ⟨hy, hb, hs⟩ := hp
  have k0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  replace hs := hs la.y
  have hx : (k : ℂ) • ((k : ℂ)⁻¹ • B.P0 la).2 = B.ct la.y + la.l := by
    rw [Prod.smul_snd, smul_inv_smul₀ k0, AnArc.degeneratingTori_basePeriodMap_snd]
  have hE : Complex.exp (lin B la (B.P0 la) / k) * eTwoPi (((k : ℂ)⁻¹ • B.P0 la).1 la.y) =
      Complex.exp (Real.pi * B.H ((k : ℂ)⁻¹ • B.P0 la).2 la.l) := by
    rw [eTwoPi, ← Complex.exp_add, lin, Prod.smul_snd, B.H_smul_left, Prod.smul_fst, AddMonoidHom.smul_apply,
      smul_eq_mul]
    congr 1
    ring
  generalize ((k : ℂ)⁻¹ • B.P0 la).2 = x at *
  generalize Complex.exp (lin B la (B.P0 la) / k) = E at *
  generalize eTwoPi (((k : ℂ)⁻¹ • B.P0 la).1 la.y) = e at *
  have f1 := d.ab.2.2.2.2.1 la.l (B.ct la.y)
  have f2 := d.ab.2.2.2.2.1 la.l (B.ct la.y + x)
  rw [B.ah_add, ← hE, add_right_comm] at f2
  have a := congrArg Units.val (d.tx_mulq x k)
  have b := congrArg Units.val (d.tx_cubN_div x k)
  have c := congrArg Units.val (d.ψ_eq la.y)
  rw [hx] at a b
  have ht : (k - 1) / 2 = t := by omega
  rw [NumD.wQ, NumB.wS, hy, hb, ht, mul_div_assoc (p.1.2.s _)]
  generalize cubN N.θ k 1 (d.ex x) (d.ex x) / dbl N.θ N.σ (d.ex x) ^ k = D at *
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_div_eq_div_val] at a b c ⊢
  have hD : (p.1.2.s (d.eX la.y) : ℂ) * D * (d.fr x ^ (2 * k) * E) = 1 := by
    refine mul_right_cancel₀ (b := (d.fr (B.ct la.y) : ℂ) * d.fr x * e) ?_ ?_
    · refine mul_ne_zero (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)) ?_
      rintro rfl
      exact Complex.exp_ne_zero _ (hE.symm.trans (mul_zero _))
    · linear_combination hs - (p.1.2.s (d.eX la.y) : ℂ) * f2 +
        (p.1.2.s (d.eX la.y) : ℂ) * B.ah la.l (B.ct la.y) * E * e * b +
        (p.1.2.s (d.eX la.y) : ℂ) * D * (d.fr x ^ (2 * k) * E) * d.fr x * e * f1
  have hD' := (mul_eq_one_iff_inv_eq₀ (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _))).1 hD
  rw [div_eq_mul_inv, ← inv_pow, hD', mul_pow, ← pow_mul, ← c, f1, ← a,
    show k ^ 2 = 2 * k * t + k by rw [sq]; nth_rw 2 [hk]; ring, pow_add]
  ring

theorem IsPrim.tx_sign {w₀ : O} (h : IsPrim B w₀) (la : B.La) :
    (B.psi la.y : ℂ) =
      (-1) ^ B.EF la (w₀ • la) * Complex.exp (-(lin B la (B.P0 la) / 2)) * B.ah la.l (B.ct la.y) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hy : la.y = w₀ • la.y + star w₀ • la.y := by rw [← add_smul, h1, one_smul]
  have hT : B.T la.y la.y = 2 * B.T la.y (w₀ • la.y) := by
    have : B.T la.y la.y = B.T la.y (w₀ • la.y + star w₀ • la.y) := by rw [← hy]
    rw [this, map_add (f := _), ← B.T_adj, B.T_symm (w₀ • la.y), two_mul]
  have hn : la.n la.y = la.n (w₀ • la.y) + la.n (star w₀ • la.y) := by rw [← map_add (f := _), ← hy]
  have hm : ∀ z : ℤ, (-1 : ℂ) ^ z = Complex.exp (z * (Real.pi * Complex.I)) := fun z => by
    rw [Complex.exp_int_mul, Complex.exp_pi_mul_I]
  rw [h3, AnArc.ah, h2, hm, hm, eTwoPi, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add,
    Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-(la.n (star w₀ • la.y) + B.Ef la.l (B.FLam w₀ la.l)), ?_⟩
  simp only [lin, AnArc.EF_apply, AnArc.La.smul_y, AnArc.La.smul_n_apply, AnArc.La.smul_l, AnArc.degeneratingTori_basePeriodMap_fst_apply,
    AnArc.degeneratingTori_basePeriodMap_snd, AnArc.H_add_left, hT, hn]
  have := Complex.I_ne_zero
  push_cast
  field_simp
  ring

theorem txSt_of_ptSt (h : PtSt) : TxSt := by
  intro O _ _ N B d w₀ hw k β hβ m hm ho w u hu la p hp x
  obtain ⟨t, ht⟩ := ho.pow (n := 2)
  have m0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 ho.pos.ne'
  have hQ := d.tx_wQ ht hp
  have hv := d.tx_vt (d.tx_isPt_pow h hp.2 m) x
  have hq := congrArg Units.val (d.tx_mulq (((m ^ 2 : ℕ) : ℂ)⁻¹ • B.P0 la).2 m)
  have hmm : (m : ℂ) • ((m ^ 2 : ℕ) : ℂ)⁻¹ • B.P0 la = (m : ℂ)⁻¹ • B.P0 la := by
    rw [smul_smul]
    congr 1
    push_cast
    field_simp
  rw [← Prod.smul_snd (m : ℂ), hmm] at hq
  rw [hmm] at hv
  rw [hw.tx_sign, mul_right_comm _ (B.ah _ _), mul_left_inj' (B.ah_ne_zero _ _), mul_assoc, ← Complex.exp_nat_mul,
    ← Complex.exp_add] at hQ
  have hterm : B.term 1 0 d.th x ((m : ℂ)⁻¹ • B.Pw w la) =
      B.term 1 0 d.th x ((m : ℂ)⁻¹ • B.P0 la) * eTwoPi ((m : ℂ)⁻¹ * (w * B.be la.y x)) := by
    have e1 : ((m : ℂ)⁻¹ • B.Pw w la).1 (0 + 1 • x) =
        ((m : ℂ)⁻¹ • B.P0 la).1 (0 + 1 • x) + (m : ℂ)⁻¹ * (w * B.be la.y x) := by
      simp only [zero_add, one_smul, Prod.smul_fst, AddMonoidHom.smul_apply, smul_eq_mul, AnArc.Pw_fst_apply,
        AnArc.degeneratingTori_basePeriodMap_fst_apply]
      ring
    have e2 : ((m : ℂ)⁻¹ • B.Pw w la).2 = ((m : ℂ)⁻¹ • B.P0 la).2 := by
      rw [Prod.smul_snd, Prod.smul_snd, AnArc.Pw_snd, AnArc.degeneratingTori_basePeriodMap_snd]
    rw [AnArc.term, AnArc.term, e1, e2, AnArc.e_add]
    ring
  have hlin : lin B la (B.Pw w la) = lin B la (B.P0 la) - 2 * Real.pi * Complex.I * (w * B.be la.y la.y) := by
    simp only [lin, AnArc.Pw_fst_apply, AnArc.degeneratingTori_basePeriodMap_fst_apply, AnArc.Pw_snd, AnArc.degeneratingTori_basePeriodMap_snd]
    ring
  obtain ⟨c, hc⟩ : (2 * (m : ℤ) ^ 2) ∣ β.be (d.eX la.y + m • d.eX x) (d.eX la.y + m • d.eX x) :=
    (mul_dvd_mul_left 2 (by exact_mod_cast hm)).trans (β.dvd _ _)
  have hc' : 2 * (m : ℤ) ^ 2 * c = B.be la.y la.y + 2 * m * B.be la.y x + m ^ 2 * (2 * B.q x) := by
    rw [← hc, ← map_nsmul, ← map_add (f := _), ← hβ, B.two_mul_q]
    simp only [map_add (f := _), map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul, B.be_symm x la.y]
    ring
  replace hc' : (c : ℂ) = (B.be la.y la.y + 2 * m * B.be la.y x + m ^ 2 * (2 * B.q x)) / (2 * m ^ 2) := by
    rw [eq_div_iff (mul_ne_zero two_ne_zero (pow_ne_zero _ m0)), mul_comm]
    exact_mod_cast hc'
  have ht' : (t : ℂ) = (m ^ 2 - 1) / 2 := by
    have : (m : ℂ) ^ 2 = 2 * t + 1 := by exact_mod_cast ht
    rw [this]; ring
  have key : eTwoPi (w * c) * Complex.exp (-(lin B la (B.P0 la) / 2) + t * (lin B la (B.P0 la) / (m ^ 2 : ℕ))) =
      Complex.exp (-(lin B la (B.Pw w la) / (2 * (m : ℂ) ^ 2))) * eTwoPi ((m : ℂ)⁻¹ * (w * B.be la.y x)) *
        eTwoPi (w * B.exponent 1 0 x) := by
    simp only [eTwoPi, ← Complex.exp_add, hlin, hc', ht', AnArc.exponent, map_zero]
    congr 1
    push_cast
    field_simp
    ring
  have m0' : (2 * (m : ℤ) ^ 2) ≠ 0 := mul_ne_zero two_ne_zero (pow_ne_zero _ (Int.natCast_ne_zero.2 ho.pos.ne'))
  rw [N.twist_txT β u m hm ho, hp.1, hc, Int.mul_ediv_cancel_left _ m0', Units.val_zpow_eq_zpow_val, hu,
    ← AnArc.e_mul_intCast, NumD.txT, hv, hterm, hp.2.1, ← hq, Units.val_div_eq_div_val, Units.val_mul,
    Units.val_pow_eq_pow_val]
  have hmq := (mulq N.θ N.σ m (d.ex (((m ^ 2 : ℕ) : ℂ)⁻¹ • B.P0 la).2)).ne_zero
  linear_combination (eTwoPi (w * c) * B.term 1 0 d.th x ((m : ℂ)⁻¹ • B.P0 la)) * hQ +
    (-1) ^ B.EF la (w₀ • la) * B.term 1 0 d.th x ((m : ℂ)⁻¹ • B.P0 la) * key +
    eTwoPi (w * c) * B.term 1 0 d.th x ((m : ℂ)⁻¹ • B.P0 la) * N.wQ p *
      (d.fr (((m ^ 2 : ℕ) : ℂ)⁻¹ • B.P0 la).2 : ℂ) ^ m ^ 2 * inv_mul_cancel₀ hmq

end GlobalTheory.Ex.Arch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisationGenericFibreCartesianToModelBundle
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

noncomputable section
namespace GlobalTheory.Ex.GenericFibre

theorem exists_iso_section {X₁ X₂ Y : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂} {g : Y ⟶ X₁} {f : Y ⟶ X₂} (i : X₁ ⟶ Y)
    (hi : i ≫ g = 𝟙 X₁) (w₀ : LB.Iso (L₁.pull g) (L₂.pull f)) (hw : w₀.IsGen) :
    ∃ w : LB.Iso L₁ (L₂.pull (i ≫ f)), w.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ X₁) (z : Z) (j : L₂.ι) (k : L₁.ι),
      f (i (r z)) ∈ L₂.U j → r z ∈ L₁.U k → gw w r z j k = BoxExpansion.pw w₀ (r ≫ i) z k j := by
  have pt : ∀ x : X₁, g (i x) = x := fun x => congrArg (fun q : X₁ ⟶ X₁ => q x) hi
  have le : ∀ p : (PUnit → L₂.ι) × L₁.ι, (L₂.pull (i ≫ f)).U p.1 ⊓ L₁.U p.2 ≤
      i ⁻¹ᵁ ((L₂.pull f).U p.1 ⊓ (L₁.pull g).U (fun _ => p.2)) := fun p y hy =>
    ⟨mem_pull.2 ((mem_pull (F := i ≫ f)).1 hy.1), mem_pull.2 (by rw [pt]; exact hy.2)⟩
  let w : LB.Iso L₁ (L₂.pull (i ≫ f)) := ⟨fun p => res (le p) (pullU i _ (w₀.s (p.1, fun _ => p.2)))⟩
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ X₁) (z : Z) (j : L₂.ι) (k : L₁.ι),
      f (i (r z)) ∈ L₂.U j → r z ∈ L₁.U k → gw w r z j k = BoxExpansion.pw w₀ (r ≫ i) z k j := by
    intro Z r z j k hj hk
    have hm : r z ∈ (L₂.pull (i ≫ f)).U (fun _ => j) ⊓ L₁.U k := ⟨(mem_pull (F := i ≫ f)).2 hj, hk⟩
    exact (gm_res r z (le (fun _ => j, k)) hm _).trans (gm_pull r i z _ (le (fun _ => j, k) hm) _)
  refine ⟨w, (isGen_iff w).2 fun Z r z j j' k k' hj hj' hk hk' => ?_, key⟩
  rw [key Z r z j k hj hk, key Z r z j' k' hj' hk',
    BoxExpansion.pw_trans hw (r ≫ i) z (j₁ := k) (j₁' := k') (j₂ := j) (j₂' := j')
      (by show g (i (r z)) ∈ _; rw [pt]; exact hk) (by show g (i (r z)) ∈ _; rw [pt]; exact hk') hj hj',
    Category.assoc, Category.assoc, hi, Category.comp_id]

theorem exists_pull_sec {X Y Y' : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (φ' : K → (Y' ⟶ X)) (e : φ' = fun k => h ≫ φ k) :
    ∃ s' : LB.Sec (LB.LinComb L φ' ε), ∀ z J, Good L z J → sval s' (𝟙 _) z J = sval s h z J := by
  subst e
  exact ⟨pullSec L φ ε s h, fun z J hJ => (SectionScalarValuation.sval_pullSec φ ε s h (𝟙 _) z hJ).trans (by rw [Category.id_comp])⟩

theorem exists_isoData : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G), ∃ (w₀ : W0 U) (ρ : LB.Gen (A.L.pull (eSec A.A))) (w : LB.Iso A.L (U.LG.L.pull (U.gen.inv.left ≫ pullback.fst G.hom (jK R)))), IsGrpPullback A.A G (jK R) (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) ∧ NormW U w₀ ρ ∧ w.IsGen ∧ IsRigidificationPullbackCompatibleIso w (jK R) ρ U.LG.rig ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (σ : H0 U.LG.L k) (th : SecA A F k), (∀ (Z : Scheme.{0}) (r : Z ⟶ (TFK (R := R) F ⊗ A.A).left) (z : Z) (J) (J'), Good U.LG.L z J → Good A.L z J' → sval σ (r ≫ (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R)) z J = (wVal w z J J' (r ≫ (snd (TFK (R := R) F) A.A).left) ^ (k : ℤ)).val * VVRank.sv A.A th r z J') → ∃ σ' : U.SecGF F k, (∀ z J, Good U.LG.L z J → sval σ' (𝟙 _) z J = sval σ (UnifPre.gFK (G := G) F) z J) ∧ ∀ s, U.ExpandsG F k σ' s → U.ExpandsF F k w₀ th s := by
  intro R _ _ I D A G _ _ U
  obtain ⟨w₀, hw₀⟩ := U.ext
  have hi : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, U.gen.inv_hom_id, Over.id_left]
  have hi' : U.gen.hom.left ≫ U.gen.inv.left = 𝟙 _ := by rw [← Over.comp_left, U.gen.hom_inv_id, Over.id_left]
  obtain ⟨w, hw, key⟩ := exists_iso_section U.gen.inv.left hi w₀ hw₀
  haveI := U.gen_hom
  haveI : IsMonHom U.gen.symm.hom := inferInstanceAs (IsMonHom U.gen.inv)
  have hp₁ : IsGrpPullback A.A ((Over.pullback (jK R)).obj G) (𝟙 _) U.gen.inv.left := isGrpPullback_of_iso U.gen.symm
  have hp₂ := isGrpPullback_pullback G (jK R)
  have hp : IsGrpPullback A.A G (jK R) (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) :=
    (hp₁.comp hp₂).congr (Category.id_comp _) rfl
  obtain ⟨ρ, hρ, hr⟩ := exists_rigidificationPullbackCompatibleIso hp hw U.LG.isLB A.isLB (ρ₀ := U.LG.rig) U.LG.rigGen
  refine ⟨w₀, ρ, w, hp, ⟨hw₀, hρ, fun z JA JG hA hG => ?_⟩, hw, hr, fun F _ _ k σ th H => ?_⟩
  · have e₁ : eSec A.A ≫ U.gen.inv.left = eSec ((Over.pullback (jK R)).obj G) :=
      (cubeMapOf hp₁).e_comm.trans (Category.id_comp _)
    have e₂ : eSec ((Over.pullback (jK R)).obj G) ≫ pullback.fst G.hom (jK R) = jK R ≫ eSec G :=
      (cubeMapOf hp₂).e_comm
    have := hr _ (𝟙 _) z JG JA hG hA
    rw [Category.id_comp, Category.id_comp, wVal, key _ _ _ _ _ (hG (eSec A.A ≫ _ ≫ _)) (hA _), ← Category.assoc, e₁, e₂] at this
    exact this.symm
  · obtain ⟨σ', hσ⟩ := exists_pull_sec σ (UnifPre.gFK (G := G) F) (fun _ : Fin 1 => UnifPre.gFK (G := G) F)
      (funext fun _ => (Category.comp_id _).symm)
    have e : (U.genF F).left ≫ (snd (TFK (R := R) F) A.A).left =
        (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left ≫ U.gen.hom.left := by
      rw [← Over.comp_left, lift_snd, Over.comp_left]
    refine ⟨σ', hσ, fun s hs => ⟨σ', BoxExpansion.isoRel_of_val A.isLB U.LG.isLB e (Category.id_comp _)
      fun y J₁ J₂ h₁ h₂ => ?_, hs⟩⟩
    have e' : ((U.genF F).left ≫ (snd (TFK (R := R) F) A.A).left) ≫ U.gen.inv.left =
        (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left := by
      rw [e, Category.assoc, hi', Category.comp_id]
    have := H _ (U.genF F).left y J₂ J₁ h₂ h₁
    rw [wVal, key _ _ _ _ _ (h₂ (((U.genF F).left ≫ (snd (TFK (R := R) F) A.A).left) ≫ _ ≫ _)) (h₁ _),
      ← Category.assoc, ← Category.assoc, e', e, zpow_natCast] at this
    exact (hσ y J₂ h₂).trans this

end GlobalTheory.Ex.GenericFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.VFCorr
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

namespace GlobalTheory.ActValues
open GlobalTheory.TorusExt GlobalTheory.ValuesExist

section Val
variable {F : Type} [Field F] {X Y Y' : Scheme.{0}} {L : LB X} {K K' K'' : Type} [Fintype K] [Fintype K'] [Fintype K'']
  {J : (Sp F ⟶ X) → L.ι}

theorem vF_corr {z : Sp F} (hJ : Good L z J) {φ : K → (Y' ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    {φ'' : K'' → (Y' ⟶ X)} {ε'' : K'' → ℤ} {t : LB.Gen (LB.LinComb L φ ε)} {u : LB.Gen (LB.LinComb L φ' ε')}
    {t' : LB.Gen (LB.LinComb L φ'' ε'')} {h : Y' ⟶ Y}
    (H : LB.Gen.Corr L _ _ _ _ (LB.mulGen L _ _ _ _ t (LB.pullGen L _ _ u h)) t') (r : Sp F ⟶ Y') :
    vF t r J * vF u (r ≫ h) J = vF t' r J := by
  have e := val_corr hJ H r
  rw [val_mul hJ, val_pull hJ] at e
  rw [← coe_val t r hJ, ← coe_val u _ hJ, ← coe_val t' r hJ, ← e, map_mul, Units.val_mul]
end Val

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {N : NumD F} (ν : NumOf D F N)

theorem good (z : Sp F) : Good D.P.L z ν.J := fun ψ => ν.good ψ trivial

theorem psi_eq (y : N.X) :
    (N.ψ y : F) = vF (LB.mulGen D.P.L _ _ _ _ (D.psi (ν.eX y)) D.rigK) (jFK (R := R) F) ν.J := by
  let z : Sp F := IsLocalRing.closedPoint F
  have hJ := good ν z
  rw [ν.ψ_eq, ← coe_val _ _ hJ, ← coe_val _ _ hJ, ← coe_val _ _ hJ, ← Units.val_mul, ← map_mul]
  exact congrArg (fun q => (((stalkUnits z).symm q : Fˣ) : F))
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))).symm

theorem tau_eq (a b : N.X) : (N.τ a b : F) = vF (D.tau (ν.eX a) (ν.eX b)) (jFK (R := R) F) ν.J := by
  let z : Sp F := IsLocalRing.closedPoint F
  have hJ := good ν z
  let e := (stalkUnits z).symm
  let ρ : ((Sp F).presheaf.stalk z)ˣ := val (Z := Sp F) D.rigK (jFK (R := R) F) z ν.J
  let p : D.X → ((Sp F).presheaf.stalk z)ˣ := fun χ => val (Z := Sp F) (D.psi χ) (jFK (R := R) F) z ν.J
  have hτ : ∀ a b, val (Z := Sp F) (D.tau a b) (jFK (R := R) F) z ν.J = p (a + b) * (p a)⁻¹ * (p b)⁻¹ * ρ⁻¹ := fun a b =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
  have hψ : ∀ y, N.ψ y = e (p (ν.eX y) * ρ) := fun y => Units.ext ((psi_eq ν y).trans
    ((coe_val _ _ hJ).symm.trans (congrArg (fun q => ((e q : Fˣ) : F)) (val_mul hJ _ _ _))))
  refine Eq.trans ?_ (coe_val _ _ hJ)
  rw [hτ, NumD.τ, hψ, hψ, hψ, ← map_div, ← map_div, map_add (f := _)]
  refine congrArg (fun q => ((e q : Fˣ) : F)) (Additive.ofMul.injective ?_)
  simp only [ofMul_mul, ofMul_inv, ofMul_div]
  abel

theorem brAct : Laws → BrActSt := by
  intro hL R _ _ D _ _ F _ _ _ N ν O _ _ _ oa
  have hJ := good ν (IsLocalRing.closedPoint F)
  refine ⟨fun a => ?_, fun a => ?_, fun w₀ hw => ?_⟩
  · have := oa.onB.hom a
    have := oa.onB.hom (star a)
    obtain ⟨r, hr, r₀⟩ := exists_ros hL.globalFns D.P.isAb D.P.isLB _ _ (oa.onB.rosati a)
    refine ⟨r, ⟨hr, r₀⟩, fun y y' => ?_⟩
    have h := vF_corr hJ (oa.tau_bal a r hr r₀ (ν.eX y) (ν.eX y')) (jFK (R := R) F)
    have h2 : jFK (R := R) F ≫ D.pt2 (ν.eX y) (ν.eX y') = (lift (ν.eA (N.c y)) (ν.eA (N.c y'))).left := by
      rw [ν.c_eq, ν.c_eq]
      let κ : TF (R := R) F ⟶ TK R := Over.homMk (jFK (R := R) F) rfl
      refine congrArg CommaMorphism.left (show κ ≫ lift _ _ = _ from ?_)
      simp only [comp_lift, comp_toUnit_assoc]
    rw [tau_eq ν, tau_eq ν, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, ← h2]
    exact h
  · have := oa.onB.hom a
    have := oa.onB.hom (star a)
    have hr := oa.onB.rosati (star a)
    rw [star_star] at hr
    obtain ⟨r, hr, r₀⟩ := exists_ros hL.globalFns D.P.isAb D.P.isLB _ _ hr
    refine ⟨r, ⟨hr, r₀⟩, fun g g' c c' hc hc' hg => ⟨by rw [hc.1, hc'.1, hg.1], fun χ => ?_⟩⟩
    have h := vF_corr hJ (hg.2 r hr r₀ (ν.eX χ)) (𝟙 (Sp F))
    rw [hc'.2, hc.2, AddEquiv.apply_symm_apply, ν.c_eq, hc.1]
    exact h.symm.trans (congrArg (fun q => _ * vF r q ν.J) (Category.id_comp _))
  · obtain ⟨t, ht, t₀, hy⟩ := hw
    refine ⟨t, ⟨ht, t₀⟩, fun y => ?_⟩
    have h := vF_corr hJ (hy (ν.eX y)) (jFK (R := R) F)
    have h2 : jFK (R := R) F ≫ D.xK (ν.eX y) = (ν.eA (N.c y)).left := by
      rw [ν.c_eq]
      exact (Category.assoc _ _ _).symm
    rw [tau_eq ν, psi_eq ν, AddEquiv.apply_symm_apply, ← h2]
    exact h

end GlobalTheory.ActValues
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValIso
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

noncomputable section
namespace GlobalTheory.Ex.Arch.FibEx
open GlobalTheory.CubeValues GlobalTheory.SymmetricSemicharacter GlobalTheory.EigenNorm GlobalTheory.FrameValue

theorem val_iso {X : Scheme.{0}} (x : Sp ℂ ⟶ X) {L M : LB X} (hM : M.IsLB) {w : LB.Iso L M} (hw : w.IsGen)
    (m : M.ι) (i j : L.ι) (hm : ⊤ ≤ x ⁻¹ᵁ M.U m) (hi : ⊤ ≤ x ⁻¹ᵁ L.U i) (hj : ⊤ ≤ x ⁻¹ᵁ L.U j) :
    valAt' x _ (w.s (m, i)).val * valAt' x (L.U i ⊓ L.U j) (L.g i j).val = valAt' x _ (w.s (m, j)).val := by
  have h : ⊤ ≤ x ⁻¹ᵁ (M.U m ⊓ L.U i ⊓ (M.U m ⊓ L.U j)) :=
    (le_preimage_inf x _ _).2 ⟨(le_preimage_inf x _ _).2 ⟨hm, hi⟩, (le_preimage_inf x _ _).2 ⟨hm, hj⟩⟩
  have l₁ : M.U m ⊓ L.U i ⊓ (M.U m ⊓ L.U j) ≤ M.U m ⊓ M.U m :=
    le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
  have l₂ : M.U m ⊓ L.U i ⊓ (M.U m ⊓ L.U j) ≤ L.U i ⊓ L.U j :=
    le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
  suffices H : ∀ (a : Γ(X, M.U m ⊓ L.U i)ˣ) (b : Γ(X, M.U m ⊓ L.U j)ˣ), res inf_le_left a =
      res l₁ (M.g m m) * (res l₂ (L.g i j))⁻¹ * res inf_le_right b →
      valAt' x _ a.val * valAt' x (L.U i ⊓ L.U j) (L.g i j).val = valAt' x _ b.val from
    H (w.s (m, i)) (w.s (m, j)) (hw (m, i) (m, j))
  intro a b e
  have e' : res inf_le_left a * res l₂ (L.g i j) = res l₁ (M.g m m) * res inf_le_right b := by
    rw [e, mul_right_comm, inv_mul_cancel_right]
  have o : valAt' x (M.U m ⊓ M.U m) (M.g m m).val = 1 := by
    obtain ⟨ev, hev⟩ := (valueRules X x).2.1 _ hm
    rw [← val_res x valueRules (le_inf le_rfl le_rfl) hm, hM.g_self, hev, Units.val_one, map_one]
  have v := congrArg (fun q : Γ(X, _)ˣ => valAt' x _ q.val) e'
  obtain ⟨ev, hev⟩ := (valueRules X x).2.1 _ h
  simp only [hev, Units.val_mul, map_mul] at v
  simp only [← hev] at v
  rw [val_res x valueRules _ h, val_res x valueRules _ h, val_res x valueRules _ h, val_res x valueRules _ h, o,
    _root_.one_mul] at v
  exact v

theorem fibEx : Laws → ThetaUnifAV → FibExSt := by
  intro hL hT R _ _ _ P J hJ
  obtain ⟨P', φ, hφ, -, hmul, t, ht⟩ := hL.polBaseChange _ _ (TF (R := R) ℂ).hom P
  have gp : IsGrpPullback P'.A P.A (TF (R := R) ℂ).hom φ := ⟨hφ, fun T x y x₀ y₀ hx hy => by
    have ex : x₀ = toBase hφ.w x := Over.OverMorphism.ext hx
    have ey : y₀ = toBase hφ.w y := Over.OverMorphism.ext hy
    rw [ex, ey, ← hmul]; rfl⟩
  obtain ⟨w, hw⟩ := LBIso.symm ⟨t, ht⟩
  obtain ⟨rig, hrig⟩ := P'.rigid
  obtain ⟨u, Hm, χ, Ef, hAH, -, h₁, h₂, h₃, -, hE, hB, -⟩ := hT P' rig hrig
  let ex : (Fin P'.g → ℂ) → (TF (R := R) ℂ ⟶ P.A) := fun z => Over.homMk ((u.ex z).left ≫ φ) (by
    show ((u.ex z).left ≫ φ) ≫ P.A.hom = _
    rw [Category.assoc, hφ.w, ← Category.assoc, Over.w]
    exact Category.id_comp _)
  have hm : ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (P.L.pull φ).U (fun _ => J (ex z).left) := fun z =>
    (le_preimage_wchart _ P.L _ _).2 fun _ => hJ _
  have hc := fun z => le_chartAt P'.isLB (u.ex z).left
  refine ⟨P'.g, u.Λ, Hm, χ, Ef, ex, fun z => Units.mk0
    (valAt' (u.ex z).left _ (w.s (fun _ => J (ex z).left, chartAt P'.isLB (u.ex z).left)).val *
      u.fr (chartAt P'.isLB (u.ex z).left) z)
    (mul_ne_zero (val_unit_ne_zero _ valueRules ((le_preimage_inf _ _ _).2 ⟨hm z, hc z⟩) _) (u.fr_ne _ _ (hc z))),
    ⟨hJ, P', φ, w, u, rfl, gp, hw, hAH, h₁, h₂, h₃, fun _ => rfl, fun z i hi => ?_⟩, hE, hB⟩
  rw [Units.val_mk0, u.fr_compat _ i z ((le_preimage_inf _ _ _).2 ⟨hc z, hi⟩), ← _root_.mul_assoc]
  exact congrArg (· * u.fr i z) (val_iso _ (pull_isLB P.isLB φ) hw _ _ _ (hm z) (hc z) hi)

end GlobalTheory.Ex.Arch.FibEx
end
end

