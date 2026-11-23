module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0219
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0196
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointRowSumEqQExpansionSeries
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private lemma exp_two_pi_I_div_pow_eq_mul (N : ℕ) (hN : (N : ℂ) ≠ 0) (d : ℕ) (τ c : ℂ) (j : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * ((d * τ + c) / N)) ^ j
      = Complex.exp (2 * Real.pi * Complex.I * (j * c) / N)
        * Complex.exp (2 * Real.pi * Complex.I * τ / N) ^ (d * j) := by
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private lemma wpFam_ch_natCast_mul (N : ℕ) [NeZero N] (j : ℕ) (b : ZMod N) :
    _root_.GlobalTheory.WpFam.ch N ((j : ZMod N) * b)
      = Complex.exp (2 * Real.pi * Complex.I * (j * (b.val : ℂ)) / N) := by
  have h := (_root_.GlobalTheory.WpFam.AddCharZMod.main N).1 ((j * b.val : ℕ) : ℤ)
  have hc : (((j * b.val : ℕ) : ℤ) : ZMod N) = (j : ZMod N) * b := by
    push_cast
    rw [ZMod.natCast_zmod_val]
  rw [hc] at h
  rw [h]
  congr 1
  first | (push_cast; ring) | push_cast

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private lemma wpFam_ch_neg_natCast_mul (N : ℕ) [NeZero N] (j : ℕ) (b : ZMod N) :
    _root_.GlobalTheory.WpFam.ch N (-((j : ZMod N) * b))
      = Complex.exp (2 * Real.pi * Complex.I * (j * -(b.val : ℂ)) / N) := by
  have h := (_root_.GlobalTheory.WpFam.AddCharZMod.main N).1 (-((j * b.val : ℕ) : ℤ))
  have hc : ((-((j * b.val : ℕ) : ℤ) : ℤ) : ZMod N) = -((j : ZMod N) * b) := by
    push_cast
    rw [ZMod.natCast_zmod_val]
  rw [hc] at h
  rw [h]
  congr 1
  first | (push_cast; ring) | push_cast


open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
theorem _root_.GlobalTheory.WpFam.torsion_row_series : ∀ (N : ℕ) [NeZero N] (e : ℕ) (τ : ℍ) (b : ZMod N) (d : ℕ+), 1 ≤ e → (∑' m : ℤ, 1 / ((((d : ℕ) : ℂ) * τ + (b.val : ℂ)) / N + m) ^ (e + 1) = (-(2 * (Real.pi : ℂ) * Complex.I)) ^ (e + 1) / (e.factorial : ℂ) * ∑' j : ℕ+, ((j : ℕ) : ℂ) ^ e * _root_.GlobalTheory.WpFam.ch N (((j : ℕ) : ZMod N) * b) * Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * τ / N) ^ ((d : ℕ) * (j : ℕ))) ∧ ∑' m : ℤ, 1 / ((-((d : ℕ) : ℂ) * τ + (b.val : ℂ)) / N + m) ^ (e + 1) = (-(2 * (Real.pi : ℂ) * Complex.I)) ^ (e + 1) / (e.factorial : ℂ) * ((-1) ^ (e + 1) * ∑' j : ℕ+, ((j : ℕ) : ℂ) ^ e * _root_.GlobalTheory.WpFam.ch N (-(((j : ℕ) : ZMod N) * b)) * Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * τ / N) ^ ((d : ℕ) * (j : ℕ))) := by
  intro N _ e τ b d he
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have him : ∀ c : ℂ, c.im = 0 → 0 < ((((d : ℕ) : ℂ) * τ + c) / N).im := by
    intro c hc
    rw [Complex.div_natCast_im]
    have h1 : (((d : ℕ) : ℂ) * (τ : ℂ) + c).im = ((d : ℕ) : ℝ) * τ.im := by
      simp [Complex.mul_im, hc]
    rw [h1]
    exact div_pos (mul_pos (by exact_mod_cast d.pos) τ.im_pos) hN
  constructor
  · have h := EisensteinSeries.qExpansion_identity_pnat he
      ⟨(((d : ℕ) : ℂ) * τ + (b.val : ℂ)) / N, him _ (Complex.natCast_im _)⟩
    simp only [UpperHalfPlane.coe_mk] at h
    have hS : (∑' j : ℕ+, ((j : ℕ) : ℂ) ^ e * Complex.exp (2 * Real.pi * Complex.I
        * ((((d : ℕ) : ℂ) * τ + (b.val : ℂ)) / N)) ^ (j : ℕ))
        = ∑' j : ℕ+, ((j : ℕ) : ℂ) ^ e * _root_.GlobalTheory.WpFam.ch N (((j : ℕ) : ZMod N) * b)
          * Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * τ / N) ^ ((d : ℕ) * (j : ℕ)) :=
      tsum_congr fun j => by
        rw [exp_two_pi_I_div_pow_eq_mul N hNc, wpFam_ch_natCast_mul]
        ring
    rw [h, hS]
    ring
  · have h := EisensteinSeries.qExpansion_identity_pnat he
      ⟨(((d : ℕ) : ℂ) * τ + -(b.val : ℂ)) / N, him _
        (by rw [Complex.neg_im, Complex.natCast_im, neg_zero])⟩
    simp only [UpperHalfPlane.coe_mk] at h
    have hterm : ∀ m : ℤ, 1 / ((-((d : ℕ) : ℂ) * τ + (b.val : ℂ)) / N + m) ^ (e + 1)
        = (-1) ^ (e + 1) * (1 / ((((d : ℕ) : ℂ) * τ + -(b.val : ℂ)) / N + ((-m : ℤ) : ℂ)) ^ (e + 1)) := by
      intro m
      rw [show (-((d : ℕ) : ℂ) * τ + (b.val : ℂ)) / N + m
          = -((((d : ℕ) : ℂ) * τ + -(b.val : ℂ)) / N + ((-m : ℤ) : ℂ)) by push_cast; ring]
      rw [neg_pow, one_div, one_div, mul_inv, ← inv_pow, inv_neg, inv_one]
    have hre : ∑' m : ℤ, 1 / ((((d : ℕ) : ℂ) * τ + -(b.val : ℂ)) / N + ((-m : ℤ) : ℂ)) ^ (e + 1)
        = ∑' m : ℤ, 1 / ((((d : ℕ) : ℂ) * τ + -(b.val : ℂ)) / N + (m : ℂ)) ^ (e + 1) :=
      (Equiv.neg ℤ).tsum_eq
        (fun m : ℤ => 1 / ((((d : ℕ) : ℂ) * τ + -(b.val : ℂ)) / N + (m : ℂ)) ^ (e + 1))
    have hS : (∑' j : ℕ+, ((j : ℕ) : ℂ) ^ e * Complex.exp (2 * Real.pi * Complex.I
        * ((((d : ℕ) : ℂ) * τ + -(b.val : ℂ)) / N)) ^ (j : ℕ))
        = ∑' j : ℕ+, ((j : ℕ) : ℂ) ^ e * _root_.GlobalTheory.WpFam.ch N (-(((j : ℕ) : ZMod N) * b))
          * Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * τ / N) ^ ((d : ℕ) * (j : ℕ)) :=
      tsum_congr fun j => by
        rw [exp_two_pi_I_div_pow_eq_mul N hNc, wpFam_ch_neg_natCast_mul]
        ring
    rw [tsum_congr hterm, tsum_mul_left, hre, h, hS]
    ring

end GlobalTheory.WpFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotallyDisconnectedProductLocallyCompact
section
open scoped TensorProduct
open GlobalTheory.SplitWeil GlobalTheory.LocFlat.CFac

noncomputable section
namespace GlobalTheory.SBProdExt

def comapEquiv {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    SB Y ≃ₗ[ℂ] SB X :=
  LinearEquiv.ofLinear (comapH e) (comapH e.symm)
    (LinearMap.ext fun F => Subtype.ext (funext fun x => by simp))
    (LinearMap.ext fun F => Subtype.ext (funext fun y => by simp))

def restrictEquiv {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : (X → ℂ) →ₗ[ℂ] (Y → ℂ)) (hf : Set.BijOn f (SB X : Set (X → ℂ)) (SB Y : Set (Y → ℂ))) :
    SB X ≃ₗ[ℂ] SB Y :=
  LinearEquiv.ofBijective (f.restrict (p := SB X) (q := SB Y) fun x hx => hf.mapsTo hx)
    ⟨fun a b hab => Subtype.ext (hf.injOn a.2 b.2 (congrArg Subtype.val hab)),
     fun y => by
       obtain ⟨x, hx, hxy⟩ := hf.surjOn y.2
       exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩

theorem exists_prod_equiv {P Q P' Q' : Type} [TopologicalSpace P] [T2Space P] [LocallyCompactSpace P]
    [TotallyDisconnectedSpace P] [TopologicalSpace Q] [T2Space Q] [LocallyCompactSpace Q]
    [TotallyDisconnectedSpace Q] [TopologicalSpace P'] [T2Space P'] [LocallyCompactSpace P']
    [TotallyDisconnectedSpace P'] [TopologicalSpace Q'] [T2Space Q'] [LocallyCompactSpace Q']
    [TotallyDisconnectedSpace Q'] (eP : SB P ≃ₗ[ℂ] SB P') (eQ : SB Q ≃ₗ[ℂ] SB Q') :
    ∃ L : SB (P × Q) ≃ₗ[ℂ] SB (P' × Q'), ∀ a b, L (prodSB a b) = prodSB (eP a) (eQ b) := by
  obtain ⟨l, hl⟩ := exists_linear_of_bilinear_prodSB P Q (SB (P' × Q'))
    ((prodSBBil P' Q').compl₁₂ eP.toLinearMap eQ.toLinearMap)
  obtain ⟨l', hl'⟩ := exists_linear_of_bilinear_prodSB P' Q' (SB (P × Q))
    ((prodSBBil P Q).compl₁₂ eP.symm.toLinearMap eQ.symm.toLinearMap)
  have h1 : l.comp l' = LinearMap.id := by
    refine LinearMap.ext_on_range (Span.span_prodSB_eq_top P' Q') fun q => ?_
    simp [hl, hl', prodSBBil]
  have h2 : l'.comp l = LinearMap.id := by
    refine LinearMap.ext_on_range (Span.span_prodSB_eq_top P Q) fun q => ?_
    simp [hl, hl', prodSBBil]
  refine ⟨LinearEquiv.ofLinear l l' h1 h2, fun a b => ?_⟩
  simp [hl, prodSBBil]

theorem exists_linear_bijOn_prod : ∀ {P Q P' Q' Z Z' : Type} [TopologicalSpace P] [T2Space P] [LocallyCompactSpace P]
    [TotallyDisconnectedSpace P] [TopologicalSpace Q] [T2Space Q] [LocallyCompactSpace Q] [TotallyDisconnectedSpace Q]
    [TopologicalSpace P'] [T2Space P'] [LocallyCompactSpace P'] [TotallyDisconnectedSpace P']
    [TopologicalSpace Q'] [T2Space Q'] [LocallyCompactSpace Q'] [TotallyDisconnectedSpace Q']
    [TopologicalSpace Z] [TopologicalSpace Z'] (eZ : Z ≃ₜ P × Q) (eZ' : Z' ≃ₜ P' × Q')
    (f : (P → ℂ) →ₗ[ℂ] (P' → ℂ)) (g : (Q → ℂ) →ₗ[ℂ] (Q' → ℂ)),
    Set.BijOn f (GlobalTheory.WeilM.SB P : Set (P → ℂ)) (GlobalTheory.WeilM.SB P' : Set (P' → ℂ)) →
    Set.BijOn g (GlobalTheory.WeilM.SB Q : Set (Q → ℂ)) (GlobalTheory.WeilM.SB Q' : Set (Q' → ℂ)) →
    ∃ h : (Z → ℂ) →ₗ[ℂ] (Z' → ℂ), Set.BijOn h (GlobalTheory.WeilM.SB Z : Set (Z → ℂ)) (GlobalTheory.WeilM.SB Z' : Set (Z' → ℂ)) ∧
      ∀ a ∈ GlobalTheory.WeilM.SB P, ∀ b ∈ GlobalTheory.WeilM.SB Q,
        h (fun z => a (eZ z).1 * b (eZ z).2) = fun z' => f a (eZ' z').1 * g b (eZ' z').2 := by
  intro P Q P' Q' Z Z' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eZ eZ' f g hf hg
  simp only [GlobalTheory.WeilM.SB_eq] at hf hg ⊢
  obtain ⟨L, hL⟩ := exists_prod_equiv (restrictEquiv f hf) (restrictEquiv g hg)
  let E : SB Z ≃ₗ[ℂ] SB Z' := ((comapEquiv eZ).symm.trans L).trans (comapEquiv eZ')
  obtain ⟨h, hh⟩ := LinearMap.exists_extend ((SB Z').subtype.comp E.toLinearMap)
  have happ : ∀ F : SB Z, h F.1 = (E F).1 := fun F => LinearMap.congr_fun hh F
  refine ⟨h, ⟨fun x hx => ?_, fun x hx y hy hxy => ?_, fun y hy => ?_⟩, fun a ha b hb => ?_⟩
  · rw [happ ⟨x, hx⟩]; exact (E _).2
  · rw [happ ⟨x, hx⟩, happ ⟨y, hy⟩] at hxy
    exact congrArg Subtype.val (E.injective (Subtype.ext hxy))
  · refine ⟨(E.symm ⟨y, hy⟩).1, (E.symm ⟨y, hy⟩).2, ?_⟩
    rw [happ]; simp
  · have hF : (fun z => a (eZ z).1 * b (eZ z).2) = (comapEquiv eZ (prodSB ⟨a, ha⟩ ⟨b, hb⟩)).1 := rfl
    rw [hF, happ]
    funext z'
    simp only [E, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, hL]
    rfl

end GlobalTheory.SBProdExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedHarishChandraInductionGLIsTwistedClassFunStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedHarishChandraInductionGL_isTwistedClassFunction : ∀ (F : Type) [Field F] [Finite F], ∀ (t : F →+* F) (a b n : ℕ) (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ), (∀ x y, hcTw t a b α β n (y⁻¹ * x * gal t n y) = hcTw t a b α β n x) ∧ IsCl (hc a b α β n) ∧ ∀ S : F[X] → ℂ, IsCl (psiG S n) ∧ IsCl (chG S n) := by
  first | (exact @GlobalTheory.Shin.twisted_class_main) | (exact GlobalTheory.Shin.twisted_class_main) | (intros; apply GlobalTheory.Shin.twisted_class_main  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitEqMulPowOnEtaleExcisionNbhdZeroLocus
section
open GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem unit_eq_mul_qth_power_near_zeroLocus : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] (q : ℕ), IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A₂ : Type) [CommRing A₂] [Algebra B A₂], IsExcisionNbhd B A₂ f → ∀ c : (Localization.Away (algebraMap B A₂ f))ˣ, ∀ (b₁ : B) (m : ℕ) (e : A₂), e - 1 ∈ Ideal.span {algebraMap B A₂ f} → algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (algebraMap B A₂ b₁) = (c : Localization.Away (algebraMap B A₂ f)) * algebraMap A₂ (Localization.Away (algebraMap B A₂ f)) (e * algebraMap B A₂ f ^ m) → ∀ g : B, IsCoprime f g → ∀ (u : (Localization.Away (f * g))ˣ) (n d : B), IsCoprime f n → IsCoprime f d → algebraMap B (Localization.Away (f * g)) (b₁ * d) = (u : Localization.Away (f * g)) * algebraMap B (Localization.Away (f * g)) (n * f ^ m) → ∃ (A₃ : Type) (_ : CommRing A₃) (_ : Algebra B A₃) (_ : Algebra A₂ A₃) (_ : IsScalarTower B A₂ A₃), IsExcisionNbhd B A₃ f ∧ IsUnit (algebraMap B A₃ g) ∧ ∃ v : (Localization.Away (algebraMap B A₃ f))ˣ, ∀ (φ : Localization.Away (algebraMap B A₂ f) →+* Localization.Away (algebraMap B A₃ f)) (ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap B A₃ f)), φ.comp (algebraMap A₂ _) = (algebraMap A₃ _).comp (algebraMap A₂ A₃) → ψ.comp (algebraMap B _) = (algebraMap A₃ _).comp (algebraMap B A₃) → φ (c : Localization.Away (algebraMap B A₂ f)) = ψ (u : Localization.Away (f * g)) * (v : Localization.Away (algebraMap B A₃ f)) ^ q := by
  intro k B _ _ _ _ _ _ q hq f hf A₂ _ _ hA₂ c b₁ m e he hc g hg u n d hn hd hu
  have hq0 : q ≠ 0 := by
    rintro rfl; simp at hq
  obtain ⟨j, rfl⟩ : ∃ j, q = j + 1 := ⟨q - 1, by omega⟩
  obtain ⟨x₁, y₁, hxy₁⟩ := (hg.mul_right hn).mul_right hd
  obtain ⟨a, ha⟩ : ∃ a : A₂, a = algebraMap B A₂ (g * n * d) * e := ⟨_, rfl⟩
  have hab : a * algebraMap B A₂ y₁ - 1 ∈ Ideal.span {algebraMap B A₂ f} := by
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp he
    have h1 := congrArg (algebraMap B A₂) hxy₁
    simp only [map_add (f := _), map_mul, map_one] at h1
    rw [Ideal.mem_span_singleton, ha]
    refine ⟨-(algebraMap B A₂ x₁) * e + t, ?_⟩
    simp only [map_mul]
    linear_combination e * h1 + ht
  have hA₂' : IsExcisionNbhd B (Localization.Away a) f := GlobalTheory.T.isExcisionNbhd_away_of_inverse_mod B A₂ f hA₂ a (algebraMap B A₂ y₁) hab
  have hdvd : ∀ z : A₂, z ∣ a → IsUnit (algebraMap A₂ (Localization.Away a) z) := fun z hz =>
    isUnit_of_dvd_unit (map_dvd _ hz) (IsLocalization.Away.algebraMap_isUnit a)
  have hgu := hdvd (algebraMap B A₂ g) ⟨algebraMap B A₂ n * algebraMap B A₂ d * e, by rw [ha]; simp only [map_mul]; ring⟩
  have hnu := hdvd (algebraMap B A₂ n) ⟨algebraMap B A₂ g * algebraMap B A₂ d * e, by rw [ha]; simp only [map_mul]; ring⟩
  have hdu := hdvd (algebraMap B A₂ d) ⟨algebraMap B A₂ g * algebraMap B A₂ n * e, by rw [ha]; simp only [map_mul]; ring⟩
  have heu := hdvd e ⟨algebraMap B A₂ (g * n * d), by rw [ha]; ring⟩
  obtain ⟨ε₀, hε₀⟩ : ∃ ε₀ : A₂, ε₀ = algebraMap B A₂ n * (algebraMap B A₂ d * e) ^ j := ⟨_, rfl⟩
  have hεu : IsUnit (algebraMap A₂ (Localization.Away a) ε₀) := by
    rw [hε₀, map_mul, map_pow, map_mul]; exact hnu.mul ((hdu.mul heu).pow j)
  obtain ⟨x₂, y₂, h₂⟩ := hn.mul_right (hd.pow_right (n := j))
  obtain ⟨r, hr⟩ := GlobalTheory.T.exists_pow_sub_mem_span_of_isUnit_mod k B (j + 1) hq f hf (n * d ^ j) y₂
    (Ideal.mem_span_singleton.mpr ⟨-x₂, by linear_combination h₂⟩)
  have hcong : ε₀ - algebraMap B A₂ r ^ (j + 1) ∈ Ideal.span {algebraMap B A₂ f} := by
    have h1 : algebraMap B A₂ f ∣ algebraMap B A₂ (n * d ^ j - r ^ (j + 1)) :=
      map_dvd _ (Ideal.mem_span_singleton.mp hr)
    have h2 : algebraMap B A₂ f ∣ e ^ j - 1 :=
      (Ideal.mem_span_singleton.mp he).trans (by simpa using sub_dvd_pow_sub_pow e 1 j)
    have h3 : ε₀ - algebraMap B A₂ r ^ (j + 1) = algebraMap B A₂ (n * d ^ j - r ^ (j + 1)) +
        algebraMap B A₂ n * algebraMap B A₂ d ^ j * (e ^ j - 1) := by
      rw [hε₀]; simp only [map_sub, map_mul, map_pow]; ring
    rw [Ideal.mem_span_singleton, h3]; exact dvd_add h1 (dvd_mul_of_dvd_right h2 _)
  have hcong' : algebraMap A₂ (Localization.Away a) ε₀ - algebraMap B (Localization.Away a) r ^ (j + 1) ∈
      Ideal.span {algebraMap B (Localization.Away a) f} := by
    rw [IsScalarTower.algebraMap_apply B A₂ (Localization.Away a) r,
      IsScalarTower.algebraMap_apply B A₂ (Localization.Away a) f, ← map_pow, ← map_sub,
      Ideal.mem_span_singleton]
    exact map_dvd _ (Ideal.mem_span_singleton.mp hcong)
  have hqu : IsUnit ((j + 1 : ℕ) : Localization.Away a) := by
    have := hq.map ((algebraMap B (Localization.Away a)).comp (algebraMap k B)); rwa [map_natCast] at this
  obtain ⟨A₃, _, _, hA₃, x, hx⟩ := GlobalTheory.T.exists_excisionNbhd_with_root_of_isUnit (Localization.Away a) (algebraMap B (Localization.Away a) f)
    (j + 1) hqu _ _ hεu hcong'
  letI : Algebra B A₃ := RingHom.toAlgebra ((algebraMap (Localization.Away a) A₃).comp (algebraMap B (Localization.Away a)))
  letI : Algebra A₂ A₃ := RingHom.toAlgebra ((algebraMap (Localization.Away a) A₃).comp (algebraMap A₂ (Localization.Away a)))
  haveI t1 : IsScalarTower B (Localization.Away a) A₃ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI t3 : IsScalarTower B A₂ A₃ := IsScalarTower.of_algebraMap_eq (fun z => by
    show algebraMap (Localization.Away a) A₃ (algebraMap B (Localization.Away a) z) =
      algebraMap (Localization.Away a) A₃ (algebraMap A₂ (Localization.Away a) (algebraMap B A₂ z))
    rw [IsScalarTower.algebraMap_apply B A₂ (Localization.Away a) z])
  refine ⟨A₃, inferInstance, inferInstance, inferInstance, t3, GlobalTheory.T.isExcisionNbhd_trans' B (Localization.Away a) A₃ f hA₂' hA₃, ?_, ?_⟩
  · have : algebraMap B A₃ g = algebraMap (Localization.Away a) A₃
        (algebraMap A₂ (Localization.Away a) (algebraMap B A₂ g)) := by
      rw [← IsScalarTower.algebraMap_apply B A₂ (Localization.Away a)]; rfl
    rw [this]; exact hgu.map _
  have hDu : IsUnit (algebraMap A₃ (Localization.Away (algebraMap B A₃ f))
      (algebraMap A₂ A₃ (algebraMap B A₂ d * e))) := by
    have hde : IsUnit (algebraMap A₂ (Localization.Away a) (algebraMap B A₂ d * e)) := by
      rw [map_mul]; exact hdu.mul heu
    exact (hde.map (algebraMap (Localization.Away a) A₃)).map _
  have hX : algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) x ^ (j + 1) =
      algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ n)) *
      (algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ d)) *
       algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ e)) ^ j := by
    rw [← map_pow, ← hx]
    show algebraMap A₃ _ (algebraMap A₂ A₃ ε₀) = _
    rw [hε₀]; simp only [map_mul, map_pow]
  have hXu : IsUnit (algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) x) :=
    (isUnit_pow_iff (Nat.succ_ne_zero j)).mp (by rw [← map_pow, ← hx]; exact (hεu.map _).map _)
  have hFu : IsUnit (algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ f))) := by
    rw [← IsScalarTower.algebraMap_apply B A₂ A₃]; exact IsLocalization.Away.algebraMap_isUnit _
  refine ⟨hXu.unit * hDu.unit⁻¹, fun φ ψ hφ hψ => ?_⟩
  have hφ' : ∀ y, φ (algebraMap A₂ _ y) = algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ y) :=
    fun y => RingHom.congr_fun hφ y
  have hψ' : ∀ z, ψ (algebraMap B _ z) =
      algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ z)) := fun z => by
    have := RingHom.congr_fun hψ z
    simp only [RingHom.comp_apply] at this
    rw [this, IsScalarTower.algebraMap_apply B A₂ A₃ z]
  have H1 := congrArg φ hc
  have H2 := congrArg ψ hu
  simp only [map_mul, map_pow, hφ'] at H1
  simp only [map_mul, map_pow, hψ'] at H2
  have hW := hDu.mul_val_inv
  rw [Units.val_mul, IsUnit.unit_spec]
  generalize (↑hDu.unit⁻¹ : Localization.Away (algebraMap B A₃ f)) = W at hW ⊢
  simp only [map_mul] at hW hFu
  have key0 : φ c * algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ d)) *
      algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ e) =
      ψ u * algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ n)) := by
    apply (hFu.pow m).mul_right_cancel
    linear_combination -(algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ d))) * H1 + H2
  calc φ c = φ c * (algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ d)) *
        algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ e) * W) ^ (j + 1) := by
        rw [hW, one_pow, mul_one]
    _ = _ := by
      linear_combination (algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ (algebraMap B A₂ d)) *
        algebraMap A₃ (Localization.Away (algebraMap B A₃ f)) (algebraMap A₂ A₃ e)) ^ j * W ^ (j + 1) * key0 -
        ψ u * W ^ (j + 1) * hX

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitPowerOnExcisionNeighbourhood
section
open GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem unit_isPow_on_excisionNbhd : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] (q : ℕ), IsUnit (q : k) → ∀ f g : B, g ≠ 0 → ∀ (u : (Localization.Away (f * g))ˣ) (t n' d' : B), IsCoprime g n' → IsCoprime g d' → (u : Localization.Away (f * g)) * algebraMap B (Localization.Away (f * g)) (t ^ q * d') = algebraMap B (Localization.Away (f * g)) n' → ∃ (C : Type) (_ : CommRing C) (_ : Algebra B C), IsExcisionNbhd B C g ∧ ∃ v' : (Localization.Away (algebraMap B C (f * g)))ˣ, Localization.awayMap (algebraMap B C) (f * g) (u : Localization.Away (f * g)) = (v' : Localization.Away (algebraMap B C (f * g))) ^ q := by
  intro k B _ _ _ _ _ _ q hq f g hg u t n' d' hn hd hu
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq
  obtain ⟨a, bn, ha⟩ := hn
  obtain ⟨a', bd, hb⟩ := hd
  have hw : (a * a' * g - a - a') * g = n' * d' * (bn * bd) - 1 := by
    linear_combination (-(bd * d')) * ha + (a * g - 1) * hb
  have hC' : IsExcisionNbhd B (Localization.Away (n' * d')) g :=
    GlobalTheory.T.isExcisionNbhd_away_of_inverse_mod B B g (isExcisionNbhd_self B g) (n' * d') (bn * bd)
      (Ideal.mem_span_singleton'.mpr ⟨_, hw⟩)
  set C' := Localization.Away (n' * d') with hC'def
  have hnd : IsUnit (algebraMap B C' (n' * d')) := IsLocalization.Away.algebraMap_isUnit _
  rw [map_mul] at hnd
  have hnC : IsUnit (algebraMap B C' n') := isUnit_of_mul_isUnit_left hnd
  have hdC : IsUnit (algebraMap B C' d') := isUnit_of_mul_isUnit_right hnd
  set Di : C' := ((hdC.unit⁻¹ : C'ˣ) : C') with hDi
  have hDi1 : Di * algebraMap B C' d' = 1 := by rw [hDi]; exact hdC.val_inv_mul
  set ε : C' := algebraMap B C' n' * Di with hεdef
  have hε : IsUnit ε := hnC.mul (Units.isUnit _)
  have hεd : ε * algebraMap B C' d' = algebraMap B C' n' := by rw [hεdef, mul_assoc, hDi1, mul_one]
  obtain ⟨r, hr⟩ := GlobalTheory.T.exists_pow_sub_mem_span_of_isUnit_mod k B q hq g hg (n' * bd) (bn * d')
    (Ideal.mem_span_singleton'.mpr ⟨a * a' * g - a - a', by linear_combination hw⟩)
  obtain ⟨w, hw'⟩ := Ideal.mem_span_singleton'.mp hr
  have hqC : IsUnit (q : C') := by simpa using hq.map ((algebraMap B C').comp (algebraMap k B))
  have hεr : ε - algebraMap B C' r ^ q ∈ Ideal.span {algebraMap B C' g} := by
    refine Ideal.mem_span_singleton'.mpr ⟨algebraMap B C' n' * Di * algebraMap B C' a' + algebraMap B C' w, ?_⟩
    have e1 := congrArg (algebraMap B C') hw'
    have e2 := congrArg (algebraMap B C') hb
    simp only [map_mul, map_sub, map_add (f := _), map_pow, map_one] at e1 e2
    rw [hεdef]
    linear_combination e1 + (algebraMap B C' n' * Di) * e2 - (algebraMap B C' n' * algebraMap B C' bd) * hDi1
  obtain ⟨C, _, _, hC, x, hx⟩ := GlobalTheory.T.exists_excisionNbhd_with_root_of_isUnit C' (algebraMap B C' g) q hqC ε (algebraMap B C' r) hε hεr
  letI : Algebra B C := ((algebraMap C' C).comp (algebraMap B C')).toAlgebra
  haveI : IsScalarTower B C' C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  refine ⟨C, inferInstance, inferInstance, GlobalTheory.T.isExcisionNbhd_trans' B C' C g hC' hC, ?_⟩
  set L := Localization.Away (algebraMap B C (f * g))
  set ψ : B →+* L := (algebraMap C L).comp (algebraMap B C) with hψ
  set ρ : C' →+* L := (algebraMap C L).comp (algebraMap C' C) with hρ
  have hψρ : ∀ y : B, ψ y = ρ (algebraMap B C' y) := fun _ => rfl
  have hφ : ∀ y : B, Localization.awayMap (algebraMap B C) (f * g)
      (algebraMap B (Localization.Away (f * g)) y) = ψ y := by
    intro y; exact IsLocalization.map_eq _ _
  have hu' : Localization.awayMap (algebraMap B C) (f * g) (u : Localization.Away (f * g)) * (ψ t ^ q * ψ d') = ψ n' := by
    have h := congrArg (Localization.awayMap (algebraMap B C) (f * g)) hu
    rw [map_mul (Localization.awayMap (algebraMap B C) (f * g)), hφ, hφ] at h
    rw [← map_pow ψ, ← map_mul ψ]; exact h
  have hnL : IsUnit (ψ n') := by rw [hψρ]; exact hnC.map ρ
  have hdL : IsUnit (ψ d') := by rw [hψρ]; exact hdC.map ρ
  have hεL : ρ ε * ψ d' = ψ n' := by
    have := congrArg ρ hεd; rw [map_mul] at this; rw [hψρ, hψρ]; exact this
  have hxL : algebraMap C L x ^ q = ρ ε := by
    have := congrArg (algebraMap C L) hx; rw [map_pow] at this; exact this.symm
  have hXU : algebraMap C L x ^ q = Localization.awayMap (algebraMap B C) (f * g) (u : Localization.Away (f * g)) * ψ t ^ q := by
    rw [← hdL.mul_left_inj, hxL, hεL, ← hu', mul_assoc]
  have hTq : IsUnit (ψ t ^ q) := by
    have h : IsUnit (Localization.awayMap (algebraMap B C) (f * g) (u : Localization.Away (f * g)) * (ψ t ^ q * ψ d')) := by
      rw [hu']; exact hnL
    exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_right h)
  have hT : IsUnit (ψ t) := (isUnit_pow_iff hq0).mp hTq
  have hX : IsUnit (algebraMap C L x) := by
    refine (isUnit_pow_iff hq0).mp ?_
    rw [hXU]; exact ((Units.map (Localization.awayMap (algebraMap B C) (f * g) : Localization.Away (f * g) →* L)) u).isUnit.mul hTq
  refine ⟨hX.unit * hT.unit⁻¹, ?_⟩
  rw [Units.val_mul, mul_pow, IsUnit.unit_spec, hXU, mul_assoc, ← mul_pow, hT.mul_val_inv, one_pow, mul_one]

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedPrincipalSeriesNoInvariant
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.PrinTwo.NoFix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


variable (k) in
theorem exists_unif : ∃ ϖ : kˣ, valuation k (ϖ : k) = uniformizer k := by
  obtain ⟨x, hx⟩ := valuation_surjective (uniformizer k)
  exact ⟨Units.mk0 x (by rintro rfl; exact uniformizer_ne_zero (R := k) (by simpa using hx.symm)), hx⟩

end GlobalTheory.PrinTwo.NoFix

namespace GlobalTheory.PrinTwo.NoFix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end GlobalTheory.PrinTwo.NoFix
end
end

