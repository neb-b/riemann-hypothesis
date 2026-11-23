module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.FderivFnCongr
section
set_option autoImplicit false

noncomputable section

open TopologicalSpace Filter Topology

namespace GlobalTheory.AnPer

variable {E E' E'' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [NormedAddCommGroup E''] [NormedSpace ℂ E'']

def holSub (W : Opens E) : Subalgebra ℂ (W → ℂ) where
  carrier := {f | ∃ F : E → ℂ, AnalyticOnNhd ℂ F W ∧ ∀ p : W, f p = F p}
  mul_mem' := by
    rintro f g ⟨F, hF, e⟩ ⟨G, hG, e'⟩
    exact ⟨fun p ↦ F p * G p, hF.mul hG, fun p ↦ by simp [e, e']⟩
  add_mem' := by
    rintro f g ⟨F, hF, e⟩ ⟨G, hG, e'⟩
    exact ⟨fun p ↦ F p + G p, hF.add hG, fun p ↦ by simp [e, e']⟩
  algebraMap_mem' c := ⟨fun _ ↦ c, analyticOnNhd_const, fun _ ↦ rfl⟩

abbrev Hol (W : Opens E) : Type := holSub W

namespace Hol

variable {W : Opens E} {W' : Opens E'} {W'' : Opens E''}

open Classical in
def fn (f : Hol W) (p : E) : ℂ := by
  classical
  exact if h : p ∈ W then f.1 ⟨p, h⟩ else 0

set_option autoImplicit false in
open TopologicalSpace Filter Topology in
variable {E E' E'' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [NormedAddCommGroup E''] [NormedSpace ℂ E''] in
variable {W : Opens E} {W' : Opens E'} {W'' : Opens E''} in
theorem _root_.GlobalTheory.AnPer.Hol.fn_of_mem (f : _root_.GlobalTheory.AnPer.Hol W) {p : E} (h : p ∈ W) :
    f.fn p = f.1 ⟨p, h⟩ := by
  simp [_root_.GlobalTheory.AnPer.Hol.fn, h]

set_option autoImplicit false in
open TopologicalSpace Filter Topology in
variable {E E' E'' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [NormedAddCommGroup E''] [NormedSpace ℂ E''] in
variable {W : Opens E} {W' : Opens E'} {W'' : Opens E''} in
theorem _root_.GlobalTheory.AnPer.Hol.ext_fn {f g : _root_.GlobalTheory.AnPer.Hol W}
    (h : ∀ p ∈ W, f.fn p = g.fn p) : f = g := by
  refine Subtype.ext (funext fun p ↦ ?_)
  have hp := h p p.2
  rw [_root_.GlobalTheory.AnPer.Hol.fn_of_mem f p.2, _root_.GlobalTheory.AnPer.Hol.fn_of_mem g p.2] at hp
  exact hp

set_option autoImplicit false in
open TopologicalSpace Filter Topology in
variable {E E' E'' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [NormedAddCommGroup E''] [NormedSpace ℂ E''] in
variable {W : Opens E} {W' : Opens E'} {W'' : Opens E''} in
theorem _root_.GlobalTheory.AnPer.Hol.analytic (f : _root_.GlobalTheory.AnPer.Hol W) :
    AnalyticOnNhd ℂ f.fn W := by
  obtain ⟨F, hF, e⟩ : ∃ F : E → ℂ, AnalyticOnNhd ℂ F W ∧ ∀ p : W, f.1 p = F p := f.2
  intro p hp
  refine (hF p hp).congr ?_
  filter_upwards [W.isOpen.mem_nhds hp] with q hq
  rw [_root_.GlobalTheory.AnPer.Hol.fn_of_mem f hq, e]

def mk (F : E → ℂ) (h : AnalyticOnNhd ℂ F W) : Hol W := ⟨fun p ↦ F p, F, h, fun _ ↦ rfl⟩

set_option autoImplicit false in
open TopologicalSpace Filter Topology in
variable {E E' E'' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [NormedAddCommGroup E''] [NormedSpace ℂ E''] in
variable {W : Opens E} {W' : Opens E'} {W'' : Opens E''} in
theorem _root_.GlobalTheory.AnPer.Hol.fn_mk (F : E → ℂ) (h : AnalyticOnNhd ℂ F W) {p : E} (hp : p ∈ W) :
    (_root_.GlobalTheory.AnPer.Hol.mk F h).fn p = F p := by
  rw [_root_.GlobalTheory.AnPer.Hol.fn_of_mem _ hp]
  rfl

def ev (p : E) (hp : p ∈ W) : Hol W →ₐ[ℂ] ℂ :=
  (Pi.evalAlgHom ℂ (fun _ : W ↦ ℂ) ⟨p, hp⟩).comp (holSub W).val

set_option autoImplicit false in
open TopologicalSpace Filter Topology in
variable {E E' E'' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [NormedAddCommGroup E''] [NormedSpace ℂ E''] in
variable {W : Opens E} {W' : Opens E'} {W'' : Opens E''} in
theorem _root_.GlobalTheory.AnPer.Hol.ev_apply (p : E) (hp : p ∈ W) (f : _root_.GlobalTheory.AnPer.Hol W) :
    _root_.GlobalTheory.AnPer.Hol.ev p hp f = f.fn p := by
  rw [_root_.GlobalTheory.AnPer.Hol.fn_of_mem f hp]
  rfl

set_option autoImplicit false in
open TopologicalSpace Filter Topology in
variable {E E' E'' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [NormedAddCommGroup E''] [NormedSpace ℂ E''] in
variable {W : Opens E} {W' : Opens E'} {W'' : Opens E''} in
theorem _root_.GlobalTheory.AnPer.Hol.fn_add (f g : _root_.GlobalTheory.AnPer.Hol W) {p : E} (hp : p ∈ W) :
    (f + g).fn p = f.fn p + g.fn p := by
  rw [_root_.GlobalTheory.AnPer.Hol.fn_of_mem _ hp, _root_.GlobalTheory.AnPer.Hol.fn_of_mem _ hp, _root_.GlobalTheory.AnPer.Hol.fn_of_mem _ hp]
  rfl

set_option autoImplicit false in
open TopologicalSpace Filter Topology in
variable {E E' E'' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [NormedAddCommGroup E''] [NormedSpace ℂ E''] in
variable {W : Opens E} {W' : Opens E'} {W'' : Opens E''} in
theorem _root_.GlobalTheory.AnPer.Hol.fn_mul (f g : _root_.GlobalTheory.AnPer.Hol W) {p : E} (hp : p ∈ W) :
    (f * g).fn p = f.fn p * g.fn p := by
  rw [_root_.GlobalTheory.AnPer.Hol.fn_of_mem _ hp, _root_.GlobalTheory.AnPer.Hol.fn_of_mem _ hp, _root_.GlobalTheory.AnPer.Hol.fn_of_mem _ hp]
  rfl

set_option autoImplicit false in
open TopologicalSpace Filter Topology in
variable {E E' E'' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [NormedAddCommGroup E''] [NormedSpace ℂ E''] in
variable {W : Opens E} {W' : Opens E'} {W'' : Opens E''} in
theorem _root_.GlobalTheory.AnPer.Hol.fn_smul (c : ℂ) (f : _root_.GlobalTheory.AnPer.Hol W) {p : E} (hp : p ∈ W) :
    (c • f).fn p = c * f.fn p := by
  rw [_root_.GlobalTheory.AnPer.Hol.fn_of_mem _ hp, _root_.GlobalTheory.AnPer.Hol.fn_of_mem _ hp]
  rfl

set_option autoImplicit false in
open TopologicalSpace Filter Topology in
variable {E E' E'' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [NormedAddCommGroup E''] [NormedSpace ℂ E''] in
variable {W : Opens E} {W' : Opens E'} {W'' : Opens E''} in
theorem _root_.GlobalTheory.AnPer.Hol.fn_algebraMap (c : ℂ) {p : E} (hp : p ∈ W) :
    (algebraMap ℂ (_root_.GlobalTheory.AnPer.Hol W) c).fn p = c := by
  rw [_root_.GlobalTheory.AnPer.Hol.fn_of_mem _ hp]
  rfl

def comap (Φ : E' → E) (hΦ : AnalyticOnNhd ℂ Φ W') (h : ∀ p ∈ W', Φ p ∈ W) : Hol W →ₐ[ℂ] Hol W' where
  toFun f := ⟨fun p ↦ f.1 ⟨Φ p, h p p.2⟩, fun p ↦ f.fn (Φ p), f.analytic.comp hΦ h,
    fun p ↦ (fn_of_mem f (h p p.2)).symm⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

set_option autoImplicit false in
open TopologicalSpace Filter Topology in
variable {E E' E'' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [NormedAddCommGroup E''] [NormedSpace ℂ E''] in
variable {W : Opens E} {W' : Opens E'} {W'' : Opens E''} in
theorem _root_.GlobalTheory.AnPer.Hol.fn_comap (Φ : E' → E) (hΦ : AnalyticOnNhd ℂ Φ W') (h : ∀ p ∈ W', Φ p ∈ W)
    (f : _root_.GlobalTheory.AnPer.Hol W) {p : E'} (hp : p ∈ W') :
    (_root_.GlobalTheory.AnPer.Hol.comap Φ hΦ h f).fn p = f.fn (Φ p) := by
  rw [_root_.GlobalTheory.AnPer.Hol.fn_of_mem _ hp]
  exact (_root_.GlobalTheory.AnPer.Hol.fn_of_mem f (h p hp)).symm

set_option autoImplicit false in
open TopologicalSpace Filter Topology in
variable {E E' E'' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [NormedAddCommGroup E''] [NormedSpace ℂ E''] in
variable {W : Opens E} {W' : Opens E'} {W'' : Opens E''} in
theorem _root_.GlobalTheory.AnPer.Hol.fderiv_fn_congr (f : _root_.GlobalTheory.AnPer.Hol W) {F : E → ℂ}
    (e : ∀ q ∈ W, f.fn q = F q) {p : E} (hp : p ∈ W) :
    fderiv ℂ f.fn p = fderiv ℂ F p := by
  refine Filter.EventuallyEq.fderiv_eq ?_
  filter_upwards [W.isOpen.mem_nhds hp] with q hq using e q hq

def derFun (v : E) (f : Hol W) : Hol W :=
  mk (fun p ↦ fderiv ℂ f.fn p v) fun p hp ↦
    ((ContinuousLinearMap.apply ℂ ℂ v).analyticAt _).comp (f.analytic p hp).fderiv

set_option autoImplicit false in
open TopologicalSpace Filter Topology in
variable {E E' E'' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [NormedAddCommGroup E''] [NormedSpace ℂ E''] in
variable {W : Opens E} {W' : Opens E'} {W'' : Opens E''} in
theorem _root_.GlobalTheory.AnPer.Hol.fn_derFun (v : E) (f : _root_.GlobalTheory.AnPer.Hol W) {p : E} (hp : p ∈ W) :
    (_root_.GlobalTheory.AnPer.Hol.derFun v f).fn p =
      fderiv ℂ f.fn p v :=
  _root_.GlobalTheory.AnPer.Hol.fn_mk _ _ hp

def der (v : E) : Derivation ℂ (Hol W) (Hol W) :=
  Derivation.mk'
    { toFun := derFun v
      map_add' f g := ext_fn fun p hp ↦ by
        rw [fn_add _ _ hp, fn_derFun _ _ hp, fn_derFun _ _ hp, fn_derFun _ _ hp,
          fderiv_fn_congr (f + g) (F := fun q ↦ f.fn q + g.fn q) (fun q hq ↦ fn_add f g hq) hp,
          fderiv_fun_add (f.analytic p hp).differentiableAt (g.analytic p hp).differentiableAt]
        rfl
      map_smul' c f := ext_fn fun p hp ↦ by
        rw [RingHom.id_apply, fn_smul _ _ hp, fn_derFun _ _ hp, fn_derFun _ _ hp,
          fderiv_fn_congr (c • f) (F := fun q ↦ c * f.fn q) (fun q hq ↦ fn_smul c f hq) hp,
          fderiv_const_mul (f.analytic p hp).differentiableAt]
        rfl }
    fun f g ↦ ext_fn fun p hp ↦ by
      change (derFun v (f * g)).fn p = (f * derFun v g + g * derFun v f).fn p
      rw [fn_add _ _ hp, fn_mul _ _ hp, fn_mul _ _ hp, fn_derFun _ _ hp, fn_derFun _ _ hp, fn_derFun _ _ hp,
        fderiv_fn_congr (f * g) (F := fun q ↦ f.fn q * g.fn q) (fun q hq ↦ fn_mul f g hq) hp,
        fderiv_fun_mul (f.analytic p hp).differentiableAt (g.analytic p hp).differentiableAt]
      rfl

set_option autoImplicit false in
open TopologicalSpace Filter Topology in
variable {E E' E'' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [NormedAddCommGroup E''] [NormedSpace ℂ E''] in
variable {W : Opens E} {W' : Opens E'} {W'' : Opens E''} in
theorem _root_.GlobalTheory.AnPer.Hol.fn_der (v : E) (f : _root_.GlobalTheory.AnPer.Hol W) {p : E} (hp : p ∈ W) :
    (_root_.GlobalTheory.AnPer.Hol.der v f).fn p =
      fderiv ℂ f.fn p v :=
  _root_.GlobalTheory.AnPer.Hol.fn_derFun v f hp

set_option autoImplicit false in
open TopologicalSpace Filter Topology in
variable {E E' E'' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [NormedAddCommGroup E''] [NormedSpace ℂ E''] in
variable {W : Opens E} {W' : Opens E'} {W'' : Opens E''} in
theorem _root_.GlobalTheory.AnPer.Hol.fn_der_comap (Φ : E' → E) (hΦ : AnalyticOnNhd ℂ Φ W')
    (h : ∀ p ∈ W', Φ p ∈ W) (v : E') (f : _root_.GlobalTheory.AnPer.Hol W) {p : E'} (hp : p ∈ W') :
    (_root_.GlobalTheory.AnPer.Hol.der v (_root_.GlobalTheory.AnPer.Hol.comap Φ hΦ h f)).fn p =
      fderiv ℂ f.fn (Φ p) (fderiv ℂ Φ p v) := by
  rw [_root_.GlobalTheory.AnPer.Hol.fn_der v _ hp,
    _root_.GlobalTheory.AnPer.Hol.fderiv_fn_congr _ (F := f.fn ∘ Φ)
      (fun q hq ↦ _root_.GlobalTheory.AnPer.Hol.fn_comap Φ hΦ h f hq) hp,
    fderiv_comp p (f.analytic (Φ p) (h p hp)).differentiableAt
      (hΦ p hp).differentiableAt]
  rfl

end Hol

end GlobalTheory.AnPer
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
section
noncomputable section

open scoped UpperHalfPlane MatrixGroups ModularForm

namespace GlobalTheory.QFam

def HasQ (N : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ) : Prop :=
  ∀ τ : ℍ, HasSum (fun n : ℕ => a n * Complex.exp (2 * Real.pi * Complex.I * n * τ / N)) (f τ)

def IsFam {ι : Type} (act : ι → SL(2, ℤ) → ι) (w : ℤ) (f : ι → ℍ → ℂ) : Prop :=
  ∀ (i : ι) (γ : SL(2, ℤ)), (f i) ∣[w] γ = f (act i γ)

def IsRAct {ι : Type} (act : ι → SL(2, ℤ) → ι) : Prop :=
  (∀ i, act i 1 = i) ∧ ∀ i γ δ, act (act i γ) δ = act i (γ * δ)

def ActBij {ι : Type} (act : ι → SL(2, ℤ) → ι) : Prop :=
  ∀ γ, Function.Bijective fun i => act i γ

def conv (a b : ℕ → ℂ) (n : ℕ) : ℂ := ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, a p.1 * b p.2

def spread (M : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ := if M ∣ n then a (n / M) else 0

def QAll (p : ℂ → Prop) (N : ℕ) (f : ℍ → ℂ) : Prop := ∃ a, HasQ N f a ∧ ∀ n, p (a n)

def QConj (g : ℂ ≃+* ℂ) (N : ℕ) (f f' : ℍ → ℂ) : Prop := ∃ a, HasQ N f a ∧ HasQ N f' fun n => g (a n)

def tauPair (τ : ℍ) : PeriodPair where
  ω₁ := τ
  ω₂ := 1
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have him := congrArg Complex.im h
    have hre := congrArg Complex.re h
    have hs : s = 0 := by
      have : s * τ.im = 0 := by simpa using him
      exact (mul_eq_zero.mp this).resolve_right τ.im_pos.ne'
    subst hs
    exact ⟨rfl, by simpa using hre⟩

theorem IsRAct.actBij {ι : Type} {act : ι → SL(2, ℤ) → ι} (h : IsRAct act) : ActBij act := by
  obtain ⟨hone, hmul⟩ := h
  intro γ
  refine Function.bijective_iff_has_inverse.mpr ⟨fun i => act i γ⁻¹, fun i => ?_, fun i => ?_⟩
  · show act (act i γ) γ⁻¹ = i
    rw [hmul, mul_inv_cancel, hone]
  · show act (act i γ⁻¹) γ = i
    rw [hmul, inv_mul_cancel, hone]

theorem hasQ_iff (N : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ) :
    HasQ N f a ↔ ∀ τ : ℍ, HasSum (fun n : ℕ => a n * Complex.exp (2 * Real.pi * Complex.I * τ / N) ^ n) (f τ) := by
  have key : ∀ (τ : ℍ) (n : ℕ), Complex.exp (2 * Real.pi * Complex.I * n * τ / N)
      = Complex.exp (2 * Real.pi * Complex.I * τ / N) ^ n := by
    intro τ n
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  simp only [HasQ, key]

end GlobalTheory.QFam
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.NormSub
section
noncomputable section

namespace GlobalTheory.LKTorus

variable (k : Type) [Field k] {A : Type} [CommRing A] [Algebra k A]

def simT (c : A →ₐ[k] A) : Subgroup Aˣ where
  carrier := {x | ∃ t : kˣ, (x : A) * c x = algebraMap k A t}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro x y ⟨s, hs⟩ ⟨t, ht⟩
    refine ⟨s * t, ?_⟩
    simp only [Units.val_mul, map_mul]
    rw [show (x : A) * y * (c x * c y) = (x * c x) * (y * c y) by ring, hs, ht]
  inv_mem' := by
    rintro x ⟨s, hs⟩
    refine ⟨s⁻¹, ?_⟩
    have h1 : ((x⁻¹ : Aˣ) : A) * c ((x⁻¹ : Aˣ) : A) * algebraMap k A s = 1 := by
      rw [← hs, show ((x⁻¹ : Aˣ) : A) * c ((x⁻¹ : Aˣ) : A) * ((x : A) * c x)
          = (((x⁻¹ : Aˣ) : A) * x) * c (((x⁻¹ : Aˣ) : A) * x) by rw [map_mul]; ring]
      simp
    calc ((x⁻¹ : Aˣ) : A) * c ((x⁻¹ : Aˣ) : A)
        = ((x⁻¹ : Aˣ) : A) * c ((x⁻¹ : Aˣ) : A) * (algebraMap k A s * algebraMap k A ((s⁻¹ : kˣ) : k)) := by
          rw [← map_mul, Units.mul_inv, map_one, mul_one]
      _ = algebraMap k A ((s⁻¹ : kˣ) : k) := by rw [← mul_assoc, h1, one_mul]

end GlobalTheory.LKTorus
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.XiMulNu
section
noncomputable section

open WittVector Ideal Matrix

namespace GlobalTheory.Sandwich

variable (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

abbrev Ainf : Type := WittVector p (PreTilt O p)

def phiInv : Ainf p O →+* Ainf p O :=
  WittVector.map ((_root_.frobeniusEquiv (PreTilt O p) p).symm : PreTilt O p →+* PreTilt O p)

def ofPadic : ℤ_[p] →+* Ainf p O :=
  (WittVector.map (ZMod.castHom (dvd_refl p) (PreTilt O p))).comp (WittVector.equiv p).symm.toRingHom

def padicToO : ℤ_[p] →+* O := (fontaineTheta O p).comp (ofPadic p O)

variable {p O}

def root (ε : PreTilt O p) : PreTilt O p := (_root_.frobeniusEquiv (PreTilt O p) p).symm ε

def mu (ε : PreTilt O p) : Ainf p O := teichmuller p ε - 1

def nu (ε : PreTilt O p) : Ainf p O := teichmuller p (root ε) - 1

def xi (ε : PreTilt O p) : Ainf p O := ∑ i ∈ Finset.range p, teichmuller p (root ε) ^ i

open WittVector Ideal Matrix in
variable (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O] in
variable {p O} in
theorem _root_.GlobalTheory.Sandwich.xi_mul_nu (ε : PreTilt O p) :
    _root_.GlobalTheory.Sandwich.xi ε * _root_.GlobalTheory.Sandwich.nu ε = _root_.GlobalTheory.Sandwich.mu ε := by
  unfold _root_.GlobalTheory.Sandwich.xi _root_.GlobalTheory.Sandwich.nu _root_.GlobalTheory.Sandwich.mu
  rw [geom_sum_mul, ← map_pow]
  congr 2
  unfold _root_.GlobalTheory.Sandwich.root
  rw [← frobenius_def, frobenius_apply_frobeniusEquiv_symm]

open WittVector Ideal Matrix in
variable (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O] in
variable {p O} in
theorem _root_.GlobalTheory.Sandwich.phiInv_mu (ε : PreTilt O p) :
    _root_.GlobalTheory.Sandwich.phiInv p O (_root_.GlobalTheory.Sandwich.mu ε) = _root_.GlobalTheory.Sandwich.nu ε := by
  unfold _root_.GlobalTheory.Sandwich.phiInv _root_.GlobalTheory.Sandwich.mu _root_.GlobalTheory.Sandwich.nu
  rw [map_sub, map_one, WittVector.map_teichmuller]
  rfl

structure Datum (ε : PreTilt O p) (h : ℕ) (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] where

  F : Matrix (Fin h) (Fin h) (Ainf p O)

  G : Matrix (Fin h) (Fin h) (Ainf p O)

  Ψ : Matrix (Fin h) (Fin h) (Ainf p O)

  Ψ' : Matrix (Fin h) (Fin h) (Ainf p O)

  ρT : Λ →ₐ[ℤ_[p]] Matrix (Fin h) (Fin h) ℤ_[p]

  ρM : Λ →+* Matrix (Fin h) (Fin h) (Ainf p O)
  G_mul_F : G * F = mu ε • (1 : Matrix (Fin h) (Fin h) (Ainf p O))
  F_eq : F = Ψ * F.map (phiInv p O)
  Ψ_mul : Ψ * Ψ' = xi ε • (1 : Matrix (Fin h) (Fin h) (Ainf p O))
  F_act : ∀ a, F * (ρT a).map (ofPadic p O) = ρM a * F

def etale (ε : PreTilt O p) (h : ℕ) : Datum ε h ℤ_[p] where
  F := 1
  G := mu ε • 1
  Ψ := 1
  Ψ' := xi ε • 1
  ρT := Algebra.ofId _ _
  ρM := (RingHom.mapMatrix (ofPadic p O)).comp (algebraMap _ _)
  G_mul_F := by simp
  F_eq := by simp
  Ψ_mul := by simp
  F_act := by intro a; simp [Algebra.ofId_apply]

namespace Datum

variable {ε : PreTilt O p} {h : ℕ} {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ] (D : Datum ε h Λ)

def al : (Fin h → O) →ₗ[O] (Fin h → O) := Matrix.toLin' (D.F.map (fontaineTheta O p))

def bb : (Fin h → O) →ₗ[O] (Fin h → O) := Matrix.toLin' (D.G.map (fontaineTheta O p))

def Fil : Submodule O (Fin h → O) := LinearMap.ker D.bb

def Lie : Submodule O (Fin h → O) := LinearMap.range D.bb

def Tsub (τ : Λ →+* O) : Submodule O (Fin h → O) :=
  ⨅ a : Λ, Module.End.eigenspace (Matrix.toLin' ((D.ρT a).map (padicToO p O))) (τ a)

def Hsub (τ : Λ →+* O) : Submodule O (Fin h → O) :=
  ⨅ a : Λ, Module.End.eigenspace (Matrix.toLin' ((D.ρM a).map (fontaineTheta O p))) (τ a)

def W (τ : Λ →+* O) : Submodule O (Fin h → O) := D.Tsub τ ⊓ LinearMap.ker D.al

end Datum

end GlobalTheory.Sandwich
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ZetaPair
section
noncomputable section

open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.HenQ

def eulerL (K : Type) [Field K] [NumberField K] (B : HeightOneSpectrum (𝓞 K) → Multiset ℂ)
    (S : Set (HeightOneSpectrum (𝓞 K))) (s : ℂ) : ℂ :=
  ∏' w : {w : HeightOneSpectrum (𝓞 K) // w ∉ S},
    ((B w.1).map fun b => (1 - b * ((Ideal.absNorm w.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹).prod

def eulerLd (K : Type) [Field K] [NumberField K] (B : HeightOneSpectrum (𝓞 K) → Multiset ℂ)
    (S : Set (HeightOneSpectrum (𝓞 K))) (s : ℂ) : ℂ :=
  eulerL K (fun w => (B w).map (·⁻¹)) S (1 - s)

end GlobalTheory.HenQ
end
end

