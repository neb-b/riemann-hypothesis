module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0043
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0257
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeAlgebraMapOC
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0255
public import Formalism.GaloisCohomology.LocalTateDualityK

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraFrobeniusReciprocity
section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial GlobalTheory.GLm.ParBasic
open scoped Classical

noncomputable section

namespace GlobalTheory.GLq.FrobRecHC

variable {g : ℕ} [Fact g.Prime] {a b : ℕ}

theorem inPar_inv (x : Gn g (a + b)) (h : InPar a (x : Mt g (a + b))) :
    InPar a ((x⁻¹ : Gn g (a + b)) : Mt g (a + b)) := by
  obtain ⟨P, hP⟩ := (par_basic g a b (a + b) rfl).1
  exact (hP _).1 (P.inv_mem ((hP x).2 h))

theorem inPar_inv_iff (x : Gn g (a + b)) :
    InPar a ((x⁻¹ : Gn g (a + b)) : Mt g (a + b)) ↔ InPar a (x : Mt g (a + b)) :=
  ⟨fun h => by simpa using inPar_inv x⁻¹ h, inPar_inv x⟩

theorem tl_one : tl a (1 : Mt g (a + b)) = 1 := by
  ext i j
  rw [tl_apply]
  simp [Matrix.one_apply]

theorem br_one : br a b (1 : Mt g (a + b)) = 1 := by
  ext i j
  rw [br_apply]
  simp [Matrix.one_apply]

theorem toG_inv (x : Gn g (a + b)) (h : InPar a (x : Mt g (a + b))) :
    (toG (tl a (x : Mt g (a + b))))⁻¹ = toG (tl a ((x⁻¹ : Gn g (a + b)) : Mt g (a + b))) ∧
    (toG (br a b (x : Mt g (a + b))))⁻¹ = toG (br a b ((x⁻¹ : Gn g (a + b)) : Mt g (a + b))) := by
  have hi := inPar_inv x h
  have hm := blocks_mul (x : Mt g (a + b)) ((x⁻¹ : Gn g (a + b)) : Mt g (a + b)) h hi
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one, tl_one, br_one] at hm
  have u1 := isUnit_blocks x h
  have u2 := isUnit_blocks _ hi
  constructor
  · apply inv_eq_of_mul_eq_one_right
    apply Units.ext
    rw [Units.val_mul, toG_val u1.1, toG_val u2.1, ← hm.2.1, Units.val_one]
  · apply inv_eq_of_mul_eq_one_right
    apply Units.ext
    rw [Units.val_mul, toG_val u1.2, toG_val u2.2, ← hm.2.2, Units.val_one]

def fz (χ : Gn g (a + b) → ℂ) (Φ : Gn g a → Gn g b → ℂ) (z : Gn g (a + b)) : ℂ :=
  χ z * (if InPar a ((z⁻¹ : Gn g (a + b)) : Mt g (a + b)) then
    Φ (toG (tl a ((z⁻¹ : Gn g (a + b)) : Mt g (a + b)))) (toG (br a b ((z⁻¹ : Gn g (a + b)) : Mt g (a + b))))
    else 0)

theorem lhs_eq (χ : Gn g (a + b) → ℂ) (Φ : Gn g a → Gn g b → ℂ) (hχ : IsClass χ) :
    ip χ (hcT a b Φ (a + b)) =
      ((Finset.univ.filter fun p : Gn g (a + b) => InPar a (p : Mt g (a + b))).card : ℂ)⁻¹ *
        ∑ z, fz χ Φ z := by
  have key : ∀ y : Gn g (a + b), (∑ x : Gn g (a + b), χ x *
      (if InPar a ((y⁻¹ * x⁻¹ * y : Gn g (a + b)) : Mt g (a + b)) then
        Φ (toG (tl a ((y⁻¹ * x⁻¹ * y : Gn g (a + b)) : Mt g (a + b))))
          (toG (br a b ((y⁻¹ * x⁻¹ * y : Gn g (a + b)) : Mt g (a + b)))) else 0)) = ∑ z, fz χ Φ z := by
    intro y
    symm
    refine Fintype.sum_equiv (MulAut.conj y).toEquiv _ _ fun z => ?_
    have e : y⁻¹ * ((MulAut.conj y).toEquiv z)⁻¹ * y = z⁻¹ := by
      simp [MulAut.conj_apply, mul_assoc]
    rw [e, fz]
    congr 1
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
    exact (hχ z y).symm
  unfold ip hcT
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hN : (Fintype.card (Gn g (a + b)) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  calc _ = (Fintype.card (Gn g (a + b)) : ℂ)⁻¹ * ∑ y : Gn g (a + b),
        ((Finset.univ.filter fun p : Gn g (a + b) => InPar a (p : Mt g (a + b))).card : ℂ)⁻¹ *
          ∑ z, fz χ Φ z := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [← key y, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        ring
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hN, one_mul, Finset.mul_sum]

theorem fz_eq (χ : Gn g (a + b) → ℂ) (Φ : Gn g a → Gn g b → ℂ) (x : Gn g (a + b)) :
    fz χ Φ x = if InPar a (x : Mt g (a + b)) then
      χ x * Φ (toG (tl a (x : Mt g (a + b))))⁻¹ (toG (br a b (x : Mt g (a + b))))⁻¹ else 0 := by
  rw [fz, inPar_inv_iff]
  split_ifs with h
  · rw [(toG_inv x h).1, (toG_inv x h).2]
  · rw [mul_zero]

theorem fibre_sum (χ : Gn g (a + b) → ℂ) (Φ : Gn g a → Gn g b → ℂ) (x : Gn g (a + b)) :
    (∑ p : Gn g a × Gn g b, if InPar a (x : Mt g (a + b)) ∧ tl a (x : Mt g (a + b)) = (p.1 : Mt g a) ∧
        br a b (x : Mt g (a + b)) = (p.2 : Mt g b) then χ x * Φ p.1⁻¹ p.2⁻¹ else 0) = fz χ Φ x := by
  rw [fz_eq]
  by_cases h : InPar a (x : Mt g (a + b))
  · have hu := isUnit_blocks x h
    rw [if_pos h]
    have hc : ∀ p : Gn g a × Gn g b, (InPar a (x : Mt g (a + b)) ∧ tl a (x : Mt g (a + b)) = (p.1 : Mt g a) ∧
        br a b (x : Mt g (a + b)) = (p.2 : Mt g b)) ↔ (toG (tl a (x : Mt g (a + b))), toG (br a b (x : Mt g (a + b)))) = p := by
      intro p
      rw [Prod.ext_iff, Units.ext_iff, Units.ext_iff, toG_val hu.1, toG_val hu.2]
      simp [h]
    simp_rw [hc]
    rw [Finset.sum_ite_eq]
    simp
  · simp [h]

theorem rhs_eq (χ : Gn g (a + b) → ℂ) (Φ : Gn g a → Gn g b → ℂ) :
    ip (fun p : Gn g a × Gn g b => res a b χ p.1 p.2) (fun p => Φ p.1 p.2) =
      ((Fintype.card (Gn g a) * Fintype.card (Gn g b) * g ^ (a * b) : ℕ) : ℂ)⁻¹ * ∑ z, fz χ Φ z := by
  unfold ip res
  simp only [Prod.fst_inv, Prod.snd_inv, Fintype.card_prod]
  simp_rw [← fibre_sum]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun p _ => ?_
  split_ifs <;> push_cast <;> ring

theorem hcT_adjoint : ∀ (g : ℕ) [Fact g.Prime] (a b n : ℕ), n = a + b → ∀ (χ : Gn g n → ℂ) (Φ : Gn g a → Gn g b → ℂ),
    IsClass χ → ip χ (hcT a b Φ n) = ip (fun p : Gn g a × Gn g b => res a b χ p.1 p.2) (fun p => Φ p.1 p.2) := by
  intro g _ a b n hn χ Φ hχ
  subst hn
  rw [lhs_eq χ Φ hχ, rhs_eq, card_par]

end GlobalTheory.GLq.FrobRecHC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraProductListDegree
section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq.HcDeg

variable {g : ℕ} [Fact g.Prime]

theorem prod_Icc_eq_range (f : ℕ → ℂ) (d : ℕ) : ∏ i ∈ Finset.Icc 1 d, f i = ∏ i ∈ Finset.range d, f (i + 1) := by
  induction d with
  | zero => simp
  | succ d ih => rw [Finset.prod_Icc_succ_top (by omega), ih, Finset.prod_range_succ]

theorem card_GL_C (d : ℕ) : (Fintype.card (Gn g d) : ℂ) =
    (∏ i ∈ Finset.range d, (g : ℂ) ^ i) * ∏ i ∈ Finset.Icc 1 d, ((g : ℂ) ^ i - 1) := by
  rw [← Nat.card_eq_fintype_card, Matrix.card_GL_field, ZMod.card, Nat.cast_prod,
    Fin.prod_univ_eq_prod_range (fun i => (((g ^ d - g ^ i : ℕ)) : ℂ)) d]
  have h1 : ∀ i ∈ Finset.range d, (((g ^ d - g ^ i : ℕ)) : ℂ) = (g : ℂ) ^ i * ((g : ℂ) ^ (d - 1 - i + 1) - 1) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hle : g ^ i ≤ g ^ d := Nat.pow_le_pow_right (Fact.out : g.Prime).pos hi'.le
    rw [Nat.cast_sub hle, mul_sub, mul_one, ← pow_add]
    push_cast
    congr 2
    omega
  rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib, prod_Icc_eq_range,
    Finset.prod_range_reflect (fun i => (g : ℂ) ^ (i + 1) - 1) d]

theorem prod_pow_add (a b : ℕ) : ∏ i ∈ Finset.range (a + b), (g : ℂ) ^ i =
    (∏ i ∈ Finset.range a, (g : ℂ) ^ i) * (∏ i ∈ Finset.range b, (g : ℂ) ^ i) * (g : ℂ) ^ (a * b) := by
  rw [Finset.prod_range_add]
  simp only [pow_add, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul]
  ring

theorem toG_one (n : ℕ) : toG (1 : Mt g n) = 1 := by
  apply Units.ext
  rw [toG, dite_eq_left isUnit_one, IsUnit.unit_spec]
  rfl

theorem tl_one (a b : ℕ) : tl a (1 : Mt g (a + b)) = 1 := by
  ext i j
  rw [GlobalTheory.GLm.ParBasic.tl_apply]
  simp [Matrix.one_apply, Fin.castAdd_inj]

theorem br_one (a b : ℕ) : br a b (1 : Mt g (a + b)) = 1 := by
  ext i j
  rw [GlobalTheory.GLm.ParBasic.br_apply]
  simp [Matrix.one_apply, Fin.natAdd_inj]

theorem hc_one (a b : ℕ) (α : Gn g a → ℂ) (β : Gn g b → ℂ) :
    hc a b α β (a + b) 1 * (Fintype.card (Gn g a) * Fintype.card (Gn g b) * (g : ℂ) ^ (a * b)) =
      Fintype.card (Gn g (a + b)) * (α 1 * β 1) := by
  have hP := GlobalTheory.GLm.ParBasic.card_par (g := g) (a := a) (b := b)
  have hne : ((Finset.univ.filter fun p : Gn g (a + b) => InPar a (p : Mt g (a + b))).card : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero, ← Nat.pos_iff_ne_zero, Finset.card_pos]
    exact ⟨1, by simpa using GlobalTheory.GLm.ParBasic.inPar_one (g := g) a (a + b)⟩
  have hs : hc a b α β (a + b) 1 = ((Finset.univ.filter fun p : Gn g (a + b) => InPar a (p : Mt g (a + b))).card : ℂ)⁻¹ *
      (Fintype.card (Gn g (a + b)) * (α 1 * β 1)) := by
    simp only [hc, hcT, mul_one, inv_mul_cancel, Units.val_one, GlobalTheory.GLm.ParBasic.inPar_one, if_true, tl_one, br_one,
      toG_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hP' : ((Finset.univ.filter fun p : Gn g (a + b) => InPar a (p : Mt g (a + b))).card : ℂ) =
      Fintype.card (Gn g a) * Fintype.card (Gn g b) * (g : ℂ) ^ (a * b) := by
    rw [hP]; push_cast; ring
  rw [hs, ← hP']
  field_simp

theorem prodIcc_ne (d : ℕ) : ∏ i ∈ Finset.Icc 1 d, ((g : ℂ) ^ i - 1) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro i hi
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hg : 1 < g := (Fact.out : g.Prime).one_lt
  have : (1 : ℕ) < g ^ i := Nat.one_lt_pow (by omega) hg
  rw [sub_ne_zero]
  exact_mod_cast this.ne'

theorem hc_degree : ∀ (g : ℕ) [Fact g.Prime] (L : List (Pc g)) (n : ℕ), n = degL L → hcL L n 1 * (L.map fun p => ∏ i ∈ Finset.Icc 1 p.1, ((g : ℂ) ^ i - 1)).prod = (∏ i ∈ Finset.Icc 1 n, ((g : ℂ) ^ i - 1)) * (L.map fun p => p.2 1).prod := by
  intro g _ L
  induction L with
  | nil =>
    intro n hn
    subst hn
    simp [hcL_nil, degL]
  | cons p L ih =>
    intro n hn
    have hn' : n = p.1 + degL L := by rw [hn]; simp [degL]
    subst hn'
    have h1 := hc_one p.1 (degL L) p.2 (hcL L (degL L))
    have h2 := ih (degL L) rfl
    rw [card_GL_C, card_GL_C, card_GL_C, prod_pow_add] at h1
    have hA := prodIcc_ne (g := g) p.1
    have hB := prodIcc_ne (g := g) (degL L)
    have hG : ∀ d, ∏ i ∈ Finset.range d, (g : ℂ) ^ i ≠ 0 := fun d =>
      Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (by exact_mod_cast (Fact.out : g.Prime).ne_zero)
    have hg0 : (g : ℂ) ^ (p.1 * degL L) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : g.Prime).ne_zero)
    simp only [List.map_cons, List.prod_cons, hcL_cons]
    set A := ∏ i ∈ Finset.Icc 1 p.1, ((g : ℂ) ^ i - 1)
    set B := ∏ i ∈ Finset.Icc 1 (degL L), ((g : ℂ) ^ i - 1)
    set C := ∏ i ∈ Finset.Icc 1 (p.1 + degL L), ((g : ℂ) ^ i - 1)
    set Ga := ∏ i ∈ Finset.range p.1, (g : ℂ) ^ i
    set Gb := ∏ i ∈ Finset.range (degL L), (g : ℂ) ^ i
    set X := hc p.1 (degL L) p.2 (hcL L (degL L)) (p.1 + degL L) 1
    set Y := (L.map fun p => ∏ i ∈ Finset.Icc 1 p.1, ((g : ℂ) ^ i - 1)).prod
    set Z := (L.map fun p => p.2 1).prod

    have key : X * (A * B) = C * (p.2 1 * hcL L (degL L) 1) := by
      apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (hG p.1) (hG (degL L))) hg0)
      linear_combination h1
    calc X * (A * Y) = X * (A * B) * Y / B := by field_simp
      _ = C * (p.2 1 * (hcL L (degL L) 1 * Y)) / B := by rw [key]; ring
      _ = C * (p.2 1 * Z) := by rw [h2]; field_simp

end GlobalTheory.GLq.HcDeg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentWittTiltEqZeroOfResidueZero
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct

namespace GlobalTheory.IdemVanish

theorem dvd_of_one_tmul_eq_zero {O k R : Type} [CommRing O] [CommRing k] [CommRing R]
    [Algebra O k] [Algebra O R] (lam : O) (hs : Function.Surjective (algebraMap O k))
    (hk : ∀ x, algebraMap O k x = 0 ↔ lam ∣ x) (x : R)
    (hx : ((1 : k) ⊗ₜ[O] x : k ⊗[O] R) = 0) : algebraMap O R lam ∣ x := by

  let f : O →ₐ[O] k := Algebra.ofId O k
  have hf : Function.Surjective f := hs
  have hker : RingHom.ker f = Ideal.span {lam} := by
    ext a
    rw [RingHom.mem_ker, Ideal.mem_span_singleton]
    exact hk a
  let e : (O ⧸ RingHom.ker f) ≃ₐ[O] k := Ideal.quotientKerAlgEquivOfSurjective hf
  let φ : k ⊗[O] R ≃ₗ[O] R ⧸ (RingHom.ker f • (⊤ : Submodule O R)) :=
    (TensorProduct.congr e.symm.toLinearEquiv (LinearEquiv.refl O R)).trans
      (TensorProduct.quotTensorEquivQuotSMul R (RingHom.ker f))
  have he : e.symm (1 : k) = Ideal.Quotient.mk (RingHom.ker f) 1 := by simp
  have h1 : φ ((1 : k) ⊗ₜ[O] x) = Submodule.Quotient.mk x := by
    simp only [φ, LinearEquiv.trans_apply, TensorProduct.congr_tmul, AlgEquiv.toLinearEquiv_apply,
      LinearEquiv.refl_apply, he, TensorProduct.quotTensorEquivQuotSMul_mk_tmul, one_smul]
  have h2 : x ∈ RingHom.ker f • (⊤ : Submodule O R) := by
    rw [← Submodule.Quotient.mk_eq_zero, ← h1, hx, map_zero]
  rw [hker, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h2
  obtain ⟨y, -, hy⟩ := h2
  exact ⟨y, by rw [← hy, Algebra.smul_def]⟩

theorem idem_eq_zero : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l) (k : Type) [Field k] [Algebra ↥(OL LL) k] (lam : ↥(OL LL)), Function.Surjective (algebraMap ↥(OL LL) k) → (∀ x, algebraMap ↥(OL LL) k x = 0 ↔ lam ∣ x) → ∀ x : RW LL, IsIdempotentElem x → ((1 : k) ⊗ₜ[↥(OL LL)] x : k ⊗[↥(OL LL)] RW LL) = 0 → x = 0 := by
  intro l _ P LL k _ _ lam hs hk x hx h1

  have hd : algebraMap (↥(OL LL)) (RW LL) lam ∣ x := dvd_of_one_tmul_eq_zero lam hs hk x h1
  have hnu : ¬ IsUnit lam := by
    intro hu
    have h0 : algebraMap (↥(OL LL)) k 1 = 0 := (hk 1).2 hu.dvd
    simp at h0
  obtain ⟨m, hm⟩ := (GlobalTheory.EtaleExact.isUnit_or_dvd_pow P LL lam).resolve_left hnu
  apply GlobalTheory.EtaleExact.sep_RW LL x
  intro n
  calc (l : RW LL) ^ n = algebraMap (↥(OL LL)) (RW LL) (((l : ℕ) : ↥(OL LL)) ^ n) := by
        rw [map_pow, map_natCast]
    _ ∣ algebraMap (↥(OL LL)) (RW LL) (lam ^ (m * n)) :=
        map_dvd _ (by rw [pow_mul]; exact pow_dvd_pow_of_dvd hm n)
    _ ∣ algebraMap (↥(OL LL)) (RW LL) lam ^ (m * n + 1) := by
        rw [map_pow]; exact pow_dvd_pow _ (Nat.le_succ _)
    _ ∣ x ^ (m * n + 1) := pow_dvd_pow_of_dvd hd _
    _ = x := hx.pow_succ_eq _

end GlobalTheory.IdemVanish
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfInvertiblePeriodMatrix
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem isDR_of_periodMatrix : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (b : Basis n ℚ_[l] V) (ρ : Representation ℚ_[l] ↥(GK K) V) (Q : GL n P.R.BdR), (∀ g : ↥(GK K), (LinearMap.toMatrix b b (ρ g)).map (algebraMap ℚ_[l] P.R.BdR) * (Q : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) = Q) → IsDR (P.PD K) ρ := by
  intro l _ P n _ _ K V _ _ b ρ Q hQ
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := (P.PD K).finK
  haveI : Nontrivial P.R.BdR := by
    refine ⟨⟨(P.PD K).ι (P.PD K).t, 0, fun h => (P.PD K).not_mem_filtration_two ?_⟩⟩
    rw [h]
    exact Submodule.zero_mem _
  obtain ⟨e, -, -, he⟩ := _root_.GlobalTheory.tensorBasisCoords ℚ_[l] P.R.BdR V n b
  have hact : ∀ (g : ↥(GK K)) (x : P.R.BdR), (P.PD K).actdR g x = P.actQdR (g : GQ l) x :=
    fun g x => P.PD_actdR K g x
  have key := _root_.GlobalTheory.InertiaEigenvalues.finrank_invariants_eq_of_period_matrix ℚ_[l] ↥K.1 P.R.BdR ↥(GK K)
    (fun g => ((P.PD K).actdR g).toRingEquiv.toRingHom) n
    (fun g => (LinearMap.toMatrix b b (ρ g)).map (algebraMap ℚ_[l] P.R.BdR))
    (fun x => ⟨fun h => (P.PD K).invdR x h, by
      rintro ⟨c, rfl⟩ g
      exact ((P.PD K).actdR g).commutes c⟩) Q
    (fun g => by
      have h := hQ g
      have : (⇑((P.PD K).actdR g).toRingEquiv.toRingHom : P.R.BdR → P.R.BdR) = P.actQdR (g : GQ l) :=
        funext (hact g)
      rw [this]
      exact h)
    ((DdR (P.PD K) ρ).map (e : V ⊗[ℚ_[l]] P.R.BdR →ₗ[ℚ_[l]] (n → P.R.BdR)))
    (fun x => by
      obtain ⟨y, rfl⟩ := e.surjective x
      have h1 : e y ∈ (DdR (P.PD K) ρ).map (e : V ⊗[ℚ_[l]] P.R.BdR →ₗ[ℚ_[l]] (n → P.R.BdR)) ↔
          y ∈ DdR (P.PD K) ρ := by
        constructor
        · rintro ⟨z, hz, hzy⟩
          have : z = y := e.injective hzy
          exact this ▸ hz
        · exact fun h => ⟨y, h, rfl⟩
      rw [h1]
      simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero]
      refine forall_congr' fun g => ?_
      have h2 := he (ρ g) ((((P.PD K).actdR g).toAlgHom.toLinearMap).restrictScalars ℚ_[l]) y
      have h3 : actVdR (P.PD K) ρ g y = TensorProduct.map (ρ g)
          ((((P.PD K).actdR g).toAlgHom.toLinearMap).restrictScalars ℚ_[l]) y := rfl
      rw [h3, ← e.injective.eq_iff, h2]
      rfl)
  rw [LinearEquiv.finrank_map_eq, ← finrank_eq_card_basis b] at key
  exact key

end GlobalTheory.PMon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitDetResMat
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.ResR

variable {l : ℕ} [Fact l.Prime] {r : ℕ}

def frobMat (ω : Fin r → ↥(MaximalUnramifiedExtension l)) : Matrix (Fin r) (Fin r) ↥(MaximalUnramifiedExtension l) := Matrix.of fun m k => fr l m (ω k)

def resMat (n : Type) [Fintype n] [DecidableEq n] (ω : Fin r → ↥(MaximalUnramifiedExtension l)) :
    Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) :=
  Matrix.kroneckerMap (· * ·) (1 : Matrix n n ↥(MaximalUnramifiedExtension l)) (frobMat ω)

theorem resMat_apply (n : Type) [Fintype n] [DecidableEq n] (ω : Fin r → ↥(MaximalUnramifiedExtension l)) (a b : n × Fin r) :
    resMat n ω a b = if a.1 = b.1 then fr l a.2 (ω b.2) else 0 := by
  simp [resMat, frobMat, Matrix.kroneckerMap_apply, Matrix.one_apply]

theorem isUnit_det_resMat (n : Type) [Fintype n] [DecidableEq n] (ω : Fin r → ↥(MaximalUnramifiedExtension l))
    (hdet : (frobMat ω).det ≠ 0) : IsUnit (resMat n ω).det := by
  rw [resMat, Matrix.det_kronecker, Matrix.det_one, one_pow, one_mul]
  exact (isUnit_iff_ne_zero.2 hdet).pow _

def resGL (n : Type) [Fintype n] [DecidableEq n] (ω : Fin r → ↥(MaximalUnramifiedExtension l)) (hdet : (frobMat ω).det ≠ 0) :
    GL (n × Fin r) ↥(MaximalUnramifiedExtension l) :=
  Matrix.GeneralLinearGroup.mk'' (resMat n ω) (isUnit_det_resMat n ω hdet)

def blockGL {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (U : Fin r → GL n R) :
    GL (n × Fin r) R where
  val := Matrix.blockDiagonal fun m => (U m : Matrix n n R)
  inv := Matrix.blockDiagonal fun m => (((U m)⁻¹ : GL n R) : Matrix n n R)
  val_inv := by rw [← Matrix.blockDiagonal_mul]; simp only [Units.mul_inv]; exact Matrix.blockDiagonal_one
  inv_val := by rw [← Matrix.blockDiagonal_mul]; simp only [Units.inv_mul]; exact Matrix.blockDiagonal_one

variable (P : LocPrime l) {n : Type} [Fintype n] [DecidableEq n]

def U0 (ω : Fin r → ↥(MaximalUnramifiedExtension l)) (hdet : (frobMat ω).det ≠ 0) (U : Fin r → GL n P.R.BdR) : GL (n × Fin r) P.R.BdR :=
  (Units.map ((kd P).mapMatrix : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) →+* Matrix (n × Fin r) (n × Fin r) P.R.BdR).toMonoidHom
    (resGL n ω hdet))⁻¹ * blockGL U

def Ymat (ω : Fin r → ↥(MaximalUnramifiedExtension l)) (A₀ : GL (n × Fin r) P.R.B) : Matrix (n × Fin r) (n × Fin r) P.R.B :=
  (resMat n ω).map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B) * (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B)

def colv (ω : Fin r → ↥(MaximalUnramifiedExtension l)) (A₀ : GL (n × Fin r) P.R.B) (c : n × Fin r) (i : n) : P.R.B :=
  ∑ k, algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (ω k) * (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) (i, k) c

def LatC (U : Fin r → GL n P.R.BdR) (x y : Fin r × n) (a : n → P.R.B) : Prop :=
  (∀ i, P.φB^[r] (a i) = a i) ∧ ∀ m : Fin r, ∃ w : n → P.R.BdR, (∀ i, w i ∈ Fil P 0) ∧
    (fun i => ev P m (a i)) = ((U m : Matrix n n P.R.BdR) * Matrix.diagonal fun j => tz P (eps x y (m, j))).mulVec w

end GlobalTheory.PMon.ResR

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpsInVOfIsSubFam
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.Pass

theorem jumpsInV_of_isSubFam : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (ι : Type) (k : ℕ) (Ms : ι → (↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1)) (W : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsSubFam Ms W → ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (U : Set ℤ), (∀ x, JumpsInV (P.PD K) (matRep (Ms x)) τ U) → JumpsInV (P.PD K) W.ρ τ U := by
  intro l _ P K LL ι k Ms W hW τ U hU
  obtain ⟨a, x, p, hp, hinj⟩ := hW
  refine GlobalTheory.SubSumJumps.jumpsInV_of_isSubOfSums (P.PD K) W.ρ Ms τ U ⟨a, x, LinearMap.pi p, ?_, ?_⟩ hU
  · rw [injective_iff_map_eq_zero]
    intro v hv
    exact hinj v fun j => congrFun hv j
  · intro g v
    funext j
    exact hp j g v

end GlobalTheory.Pass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KapIdemMemInCStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kap_mem_inC_of_invariant : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (K LL : FinExt l) (f : ℕ) (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) (e : OCO LL), IsActC act → IsIdempotentElem e → (∀ g ∈ GK K, ∀ k, act g (kap o e k) = kap o e k) → ∀ k, kap o e k ∈ inC K.1 := by
  first | exact @GlobalTheory.Cyc.Decomp.kap_idem_mem_inC | exact GlobalTheory.Cyc.Decomp.kap_idem_mem_inC | (intros; apply GlobalTheory.Cyc.Decomp.kap_idem_mem_inC <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeModPowActionIsLocallyConstantStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_modPow_action_isLocallyConstant : ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep G ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) (x : ↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)), IsLocallyConstant fun g : G => actQ LA _ hI g x := by
  first | exact @GlobalTheory.InertiaEigenvalues.actQ_pow_isLocallyConstant | exact GlobalTheory.InertiaEigenvalues.actQ_pow_isLocallyConstant | (intros; apply GlobalTheory.InertiaEigenvalues.actQ_pow_isLocallyConstant <;> assumption)
end

