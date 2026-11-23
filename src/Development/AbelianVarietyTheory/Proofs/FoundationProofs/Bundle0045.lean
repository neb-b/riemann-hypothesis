module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0028

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDerivationModIntegralExtensionPCube
section
noncomputable section

namespace GlobalTheory.DerExt

open GlobalTheory.K5 GlobalTheory.KumDlog

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]
variable {ι : Type} [Fintype ι]

def D0 (u v : ι → Ω) (tr d : Ω → Ω) (x : Ω) : Ω := ∑ k, u k * d (tr (v k * x))

def phi (D : Ω → Ω) (x y : Ω) : Ω := D (x * y) - x * D y - y * D x

def psi (u v : ι → Ω) (D : Ω → Ω) (x : Ω) : Ω := ∑ k, u k * phi D (v k) x

theorem phi_comm (D : Ω → Ω) (x y : Ω) : phi D x y = phi D y x := by
  unfold phi; rw [mul_comm x y]; ring

theorem phi_one (D : Ω → Ω) (y : Ω) : phi D 1 y = -(y * D 1) := by
  unfold phi; simp

theorem phi_ident (D : Ω → Ω) (w x y : Ω) :
    w * phi D x y - phi D (w * x) y + phi D w (x * y) - y * phi D w x = 0 := by
  unfold phi; rw [show w * x * y = w * (x * y) by ring]; ring

variable {B C : Subalgebra (O0 p) Ω} {u v : ι → Ω} {tr : Ω → Ω} {d : Ω → Ω}

private theorem isInt_congr {x y : Ω} (hx : IsInt (p := p) x) (h : y = x) :
    IsInt (p := p) y := h ▸ hx

theorem traceDerivationFirstApprox_add_isInt (h : DualData B C u v tr) (hd : IsDer B d) {x y : Ω} (hx : x ∈ C) (hy : y ∈ C) :
    IsInt (p := p) (D0 u v tr d (x + y) - D0 u v tr d x - D0 u v tr d y) := by
  obtain ⟨_, hCi, hu, hv, htr, hadd, -⟩ := h
  refine isInt_congr (IsIntegral.sum (s := Finset.univ) _ fun k _ => IsIntegral.mul (hCi _ (hu k))
    (hd.1 _ (htr _ (C.mul_mem (hv k) hx)) _ (htr _ (C.mul_mem (hv k) hy)))) ?_
  simp only [D0, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_add, hadd _ (C.mul_mem (hv k) hx) _ (C.mul_mem (hv k) hy)]; ring

theorem traceDerivationFirstApprox_mul_left_isInt (h : DualData B C u v tr) (hd : IsDer B d) {b x : Ω} (hb : b ∈ B) (hx : x ∈ C) :
    IsInt (p := p) (D0 u v tr d (b * x) - b * D0 u v tr d x - p * x * d b) := by
  obtain ⟨_, hCi, hu, hv, htr, -, hlin, hdual, -⟩ := h
  refine isInt_congr (IsIntegral.sum (s := Finset.univ) _ fun k _ => IsIntegral.mul (hCi _ (hu k))
    (hd.2.1 b hb _ (htr _ (C.mul_mem (hv k) hx)))) ?_
  rw [← hdual x hx]
  simp only [D0, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show v k * (b * x) = b * (v k * x) by ring, hlin b hb _ (C.mul_mem (hv k) hx)]; ring

theorem phi_add (h : DualData B C u v tr) (hd : IsDer B d) {x x' y : Ω} (hx : x ∈ C) (hx' : x' ∈ C)
    (hy : y ∈ C) :
    IsInt (p := p) (phi (D0 u v tr d) (x + x') y - phi (D0 u v tr d) x y - phi (D0 u v tr d) x' y) := by
  refine isInt_congr (IsIntegral.sub (traceDerivationFirstApprox_add_isInt h hd (C.mul_mem hx hy) (C.mul_mem hx' hy))
    (IsIntegral.mul (h.2.1 y hy) (traceDerivationFirstApprox_add_isInt h hd hx hx'))) ?_
  simp only [phi, add_mul]; ring

theorem phi_bmul (h : DualData B C u v tr) (hd : IsDer B d) {b x y : Ω} (hb : b ∈ B) (hx : x ∈ C)
    (hy : y ∈ C) :
    IsInt (p := p) (phi (D0 u v tr d) (b * x) y - b * phi (D0 u v tr d) x y) := by
  refine isInt_congr (IsIntegral.sub (traceDerivationFirstApprox_mul_left_isInt h hd hb (C.mul_mem hx hy))
    (IsIntegral.mul (h.2.1 y hy) (traceDerivationFirstApprox_mul_left_isInt h hd hb hx))) ?_
  simp only [phi]; rw [show b * x * y = b * (x * y) by ring]; ring

theorem lin_sum (h : DualData B C u v tr) (f : Ω → Ω)
    (hadd : ∀ x ∈ C, ∀ y ∈ C, IsInt (p := p) (f (x + y) - f x - f y))
    (hlin : ∀ b ∈ B, ∀ x ∈ C, IsInt (p := p) (f (b * x) - b * f x))
    {κ : Type} (s : Finset κ) (w b : κ → Ω) (hw : ∀ i, w i ∈ C) (hb : ∀ i, b i ∈ B) :
    IsInt (p := p) (f (∑ i ∈ s, w i * b i) - ∑ i ∈ s, b i * f (w i)) := by
  classical
  have hBC := h.1
  induction s using Finset.induction_on with
  | empty =>
    simpa using hlin 0 B.zero_mem 0 C.zero_mem
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hS : ∑ i ∈ s, w i * b i ∈ C := C.sum_mem fun i _ => C.mul_mem (hw i) (hBC (hb i))
    have h1 := hadd _ (C.mul_mem (hw a) (hBC (hb a))) _ hS
    have h2 := hlin (b a) (hb a) (w a) (hw a)
    rw [mul_comm (b a) (w a)] at h2
    exact isInt_congr (IsIntegral.add h1 (IsIntegral.add h2 ih)) (by ring)

theorem sum_swap_eq (h : DualData B C u v tr) (D : Ω → Ω) {x : Ω} (hx : x ∈ C) (y : Ω) :
    ∑ k, u k * ∑ l, tr (u l * (v k * x)) * phi D (v l) y = p * x * psi u v D y := by
  obtain ⟨_, -, hu, -, -, -, -, hdual, -⟩ := h
  calc ∑ k, u k * ∑ l, tr (u l * (v k * x)) * phi D (v l) y
      = ∑ k, ∑ l, u k * tr (v k * (x * u l)) * phi D (v l) y := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [show u l * (v k * x) = v k * (x * u l) by ring]; ring
    _ = ∑ l, ∑ k, u k * tr (v k * (x * u l)) * phi D (v l) y := Finset.sum_comm
    _ = ∑ l, (∑ k, u k * tr (v k * (x * u l))) * phi D (v l) y := by
        simp only [Finset.sum_mul]
    _ = ∑ l, p * (x * u l) * phi D (v l) y := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hdual _ (C.mul_mem hx (hu l))]
    _ = p * x * psi u v D y := by
        simp only [psi, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        ring

theorem S_congr (h : DualData B C u v tr) (hd : IsDer B d) {x y : Ω} (hx : x ∈ C) (hy : y ∈ C) :
    IsInt (p := p) (p * ∑ k, u k * phi (D0 u v tr d) (v k * x) y - p * x * psi u v (D0 u v tr d) y) := by
  have hBC := h.1
  have hCi := h.2.1
  have hu := h.2.2.1
  have hv := h.2.2.2.1
  have htr := h.2.2.2.2.1
  have hdual2 := h.2.2.2.2.2.2.2.2.1
  have hpB : (p : Ω) ∈ B := natCast_mem B p
  have key : ∀ k, IsInt (p := p) (u k * (p * phi (D0 u v tr d) (v k * x) y -
      ∑ l, tr (u l * (v k * x)) * phi (D0 u v tr d) (v l) y)) := by
    intro k
    have hz : v k * x ∈ C := C.mul_mem (hv k) hx
    have ha := phi_bmul h hd hpB hz hy
    have hb := lin_sum h (fun z => phi (D0 u v tr d) z y)
      (fun a ha b hb => phi_add h hd ha hb hy) (fun b hb a ha => phi_bmul h hd hb ha hy)
      Finset.univ v (fun l => tr (u l * (v k * x))) hv
      (fun l => htr _ (C.mul_mem (hu l) hz))
    rw [hdual2 _ hz] at hb
    exact IsIntegral.mul (hCi _ (hu k)) (isInt_congr (IsIntegral.sub hb ha) (by ring))
  refine isInt_congr (IsIntegral.sum (s := Finset.univ) _ fun k _ => key k) ?_
  rw [← sum_swap_eq h (D0 u v tr d) hx y, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

def Dext (p : ℕ) (u v : ι → Ω) (tr d : Ω → Ω) (x : Ω) : Ω :=
  (p : Ω) ^ 2 * D0 u v tr d x + p * psi u v (D0 u v tr d) x

theorem Dext_mul (h : DualData B C u v tr) (hd : IsDer B d) {x y : Ω} (hx : x ∈ C) (hy : y ∈ C) :
    IsInt (p := p) (Dext p u v tr d (x * y) - x * Dext p u v tr d y - y * Dext p u v tr d x) := by
  have hsum := h.2.2.2.2.2.2.2.2.2
  have hid : (p : Ω) * phi (D0 u v tr d) x y - ∑ k, u k * phi (D0 u v tr d) (v k * x) y +
      psi u v (D0 u v tr d) (x * y) - y * psi u v (D0 u v tr d) x = 0 := by
    calc (p : Ω) * phi (D0 u v tr d) x y - ∑ k, u k * phi (D0 u v tr d) (v k * x) y +
          psi u v (D0 u v tr d) (x * y) - y * psi u v (D0 u v tr d) x
        = ∑ k, u k * (v k * phi (D0 u v tr d) x y - phi (D0 u v tr d) (v k * x) y +
            phi (D0 u v tr d) (v k) (x * y) - y * phi (D0 u v tr d) (v k) x) := by
          rw [← hsum]
          simp only [psi, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
            ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
      _ = 0 := by simp [phi_ident]
  refine isInt_congr (S_congr h hd hx hy) ?_
  simp only [Dext, phi, psi] at hid ⊢
  linear_combination (p : Ω) * hid

theorem Dext_add (h : DualData B C u v tr) (hd : IsDer B d) {x y : Ω} (hx : x ∈ C) (hy : y ∈ C) :
    IsInt (p := p) (Dext p u v tr d (x + y) - Dext p u v tr d x - Dext p u v tr d y) := by
  have hCi := h.2.1
  have hu := h.2.2.1
  have hv := h.2.2.2.1
  have h1 := traceDerivationFirstApprox_add_isInt h hd hx hy
  have h2 : IsInt (p := p) (∑ k, u k * (phi (D0 u v tr d) (x + y) (v k) - phi (D0 u v tr d) x (v k) -
      phi (D0 u v tr d) y (v k))) :=
    IsIntegral.sum (s := Finset.univ) _ fun k _ => IsIntegral.mul (hCi _ (hu k)) (phi_add h hd hx hy (hv k))
  have hp : IsIntegral (O0 p) (p : Ω) := isIntegral_natCast p
  refine isInt_congr (IsIntegral.add ((hp.pow 2).mul h1) (hp.mul h2)) ?_
  have e : psi u v (D0 u v tr d) (x + y) - psi u v (D0 u v tr d) x - psi u v (D0 u v tr d) y =
      ∑ k, u k * (phi (D0 u v tr d) (x + y) (v k) - phi (D0 u v tr d) x (v k) -
        phi (D0 u v tr d) y (v k)) := by
    simp only [psi, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [phi_comm _ (v k) (x + y), phi_comm _ (v k) x, phi_comm _ (v k) y]; ring
  simp only [Dext]
  linear_combination (p : Ω) * e

theorem Dext_B (h : DualData B C u v tr) (hd : IsDer B d) {b : Ω} (hb : b ∈ B) :
    IsInt (p := p) (Dext p u v tr d b - (p : Ω) ^ 3 * d b) := by
  have hCi := h.2.1
  have hu := h.2.2.1
  have hv := h.2.2.2.1
  have hsum := h.2.2.2.2.2.2.2.2.2
  have h1 := traceDerivationFirstApprox_mul_left_isInt h hd hb C.one_mem
  rw [mul_one, mul_one] at h1
  have h2 : IsInt (p := p) (psi u v (D0 u v tr d) b + p * b * D0 u v tr d 1) := by
    refine isInt_congr (IsIntegral.sum (s := Finset.univ) _ fun k _ => IsIntegral.mul (hCi _ (hu k))
      (phi_bmul h hd hb C.one_mem (hv k))) ?_
    rw [← hsum]
    simp only [psi, phi_one, mul_one, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [phi_comm _ (v k) b]; ring
  have hp : IsIntegral (O0 p) (p : Ω) := isIntegral_natCast p
  refine isInt_congr (IsIntegral.add ((hp.pow 2).mul h1) (hp.mul h2)) ?_
  simp only [Dext]; ring

theorem Dext_isDer (h : DualData B C u v tr) (hd : IsDer B d) : IsDer C (Dext p u v tr d) :=
  ⟨fun x hx y hy => Dext_add h hd hx hy, fun x hx y hy => Dext_mul h hd hx hy,
   fun c => isInt_congr (IsIntegral.add (Dext_B h hd (B.algebraMap_mem c))
     (((isIntegral_natCast (R := O0 p) (B := Ω) p).pow 3).mul (hd.2.2 c))) (by ring)⟩

theorem exists_ext : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
    ∀ (B C : Subalgebra (O0 p) Ω) (ι : Type) [Fintype ι] (u v : ι → Ω) (tr : Ω → Ω),
    DualData B C u v tr →
    ∀ d : Ω → Ω, IsDer B d → ∃ D : Ω → Ω, IsDer C D ∧ ∀ b ∈ B, IsInt (p := p) (D b - (p : Ω) ^ 3 * d b) := by
  intro p _ Ω _ _ B C ι _ u v tr h d hd
  exact ⟨Dext p u v tr d, Dext_isDer h hd, fun b hb => Dext_B h hd hb⟩

end GlobalTheory.DerExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDerivationOnExtensionCubeDefect
section
noncomputable section

namespace GlobalTheory.AlmostEt

variable {A S M : Type} [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M] [Module S M]

def trTwist (tr : S → S) {n : ℕ} (a b : Fin n → S) (D : S → M) (x : S) : M :=
  ∑ i, a i • D (tr (b i * x))

def trTwistDefect (tr : S → S) {n : ℕ} (a b : Fin n → S) (D : S → M) (x u : S) : M :=
  trTwist tr a b D (x * u) - x • trTwist tr a b D u

def trExtDer (tr : S → S) {n : ℕ} (a b : Fin n → S) (e : S) (D : S → M) (y : S) : M :=
  e • ∑ j, b j • trTwistDefect tr a b D y (a j)

variable {B C : Subalgebra A S} {tr : S → S} {n : ℕ} {a b : Fin n → S} {e : S} {D : S → M}

theorem trTwist_add (h : IsTrData B C tr a b e) (hD : IsDerOn B D) {x y : S} (hx : x ∈ C)
    (hy : y ∈ C) : trTwist tr a b D (x + y) = trTwist tr a b D x + trTwist tr a b D y := by
  unfold trTwist
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 := C.mul_mem (h.b_mem i) hx
  have h2 := C.mul_mem (h.b_mem i) hy
  rw [mul_add, h.tr_add _ h1 _ h2, hD.add _ (h.tr_mem _ h1) _ (h.tr_mem _ h2), smul_add]

theorem trTwist_smul (h : IsTrData B C tr a b e) (hD : IsDerOn B D) {β x : S} (hβ : β ∈ B)
    (hx : x ∈ C) : trTwist tr a b D (β * x) = β • trTwist tr a b D x + (e * x) • D β := by
  unfold trTwist
  have key : ∀ i, a i • D (tr (b i * (β * x))) =
      β • (a i • D (tr (b i * x))) + (a i * tr (b i * x)) • D β := by
    intro i
    have h1 := C.mul_mem (h.b_mem i) hx
    have hm : b i * (β * x) = β * (b i * x) := by ring
    rw [hm, h.tr_mul _ hβ _ h1, hD.mul _ hβ _ (h.tr_mem _ h1), smul_add, mul_smul, smul_comm (a i) β]
  simp_rw [key, Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.sum_smul, h.left x hx]

theorem trTwist_zero (h : IsTrData B C tr a b e) (hD : IsDerOn B D) :
    trTwist tr a b D (0 : S) = 0 := by
  have := trTwist_add h hD C.zero_mem C.zero_mem
  rw [add_zero] at this
  simpa using this

theorem defect_add (h : IsTrData B C tr a b e) (hD : IsDerOn B D) {x u v : S} (hx : x ∈ C)
    (hu : u ∈ C) (hv : v ∈ C) :
    trTwistDefect tr a b D x (u + v) = trTwistDefect tr a b D x u + trTwistDefect tr a b D x v := by
  unfold trTwistDefect
  rw [mul_add, trTwist_add h hD (C.mul_mem hx hu) (C.mul_mem hx hv), trTwist_add h hD hu hv, smul_add]
  abel

theorem defect_zero (h : IsTrData B C tr a b e) (hD : IsDerOn B D) {x : S} (hx : x ∈ C) :
    trTwistDefect tr a b D x 0 = 0 := by
  unfold trTwistDefect
  rw [mul_zero, trTwist_zero h hD, smul_zero, sub_zero]

theorem defect_smul (h : IsTrData B C tr a b e) (hD : IsDerOn B D) {x β u : S} (hx : x ∈ C)
    (hβ : β ∈ B) (hu : u ∈ C) :
    trTwistDefect tr a b D x (β * u) = β • trTwistDefect tr a b D x u := by
  unfold trTwistDefect
  have hm : x * (β * u) = β * (x * u) := by ring
  rw [hm, trTwist_smul h hD hβ (C.mul_mem hx hu), trTwist_smul h hD hβ hu, smul_add, smul_sub,
    smul_smul x (e * u), smul_comm x β]
  have : x * (e * u) = e * (x * u) := by ring
  rw [this]
  abel

theorem defect_sum (h : IsTrData B C tr a b e) (hD : IsDerOn B D) {x : S} (hx : x ∈ C)
    (c : Fin n → S) (hc : ∀ i, c i ∈ B) :
    trTwistDefect tr a b D x (∑ i, c i * a i) = ∑ i, c i • trTwistDefect tr a b D x (a i) := by
  have : ∀ s : Finset (Fin n), trTwistDefect tr a b D x (∑ i ∈ s, c i * a i) =
      ∑ i ∈ s, c i • trTwistDefect tr a b D x (a i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using defect_zero h hD hx
    | insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj,
        defect_add h hD hx (C.mul_mem (h.le (hc j)) (h.a_mem j))
          (C.sum_mem fun i _ => C.mul_mem (h.le (hc i)) (h.a_mem i)),
        defect_smul h hD hx (hc j) (h.a_mem j), ih]
  exact this Finset.univ

theorem defect_mul (x y u : S) :
    trTwistDefect tr a b D (x * y) u =
      trTwistDefect tr a b D x (y * u) + x • trTwistDefect tr a b D y u := by
  unfold trTwistDefect
  rw [smul_sub, mul_assoc, mul_smul]
  abel

theorem trExtDer_swap (h : IsTrData B C tr a b e) (hD : IsDerOn B D) {x y : S} (hx : x ∈ C)
    (hy : y ∈ C) : y • trExtDer tr a b e D x =
      e • ∑ j, b j • trTwistDefect tr a b D x (y * a j) := by

  have step1 : ∀ j, e • (b j • trTwistDefect tr a b D x (y * a j)) =
      ∑ i, (tr (b i * (y * a j)) * b j) • trTwistDefect tr a b D x (a i) := by
    intro j
    have hya := C.mul_mem hy (h.a_mem j)
    have hl : e * (y * a j) = ∑ i, tr (b i * (y * a j)) * a i := by
      rw [← h.left _ hya]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [smul_comm, ← defect_smul h hD hx h.e_mem hya, hl,
      defect_sum h hD hx _ fun i => h.tr_mem _ (C.mul_mem (h.b_mem i) hya), Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_smul, mul_comm (b j)]
  rw [Finset.smul_sum]
  simp_rw [step1]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  have hr : ∀ i, ∑ j, tr (b i * (y * a j)) * b j = y • (e • b i) := by
    intro i
    have := h.right _ (C.mul_mem (h.b_mem i) hy)
    rw [smul_eq_mul, smul_eq_mul, ← mul_assoc, mul_comm y e, mul_assoc, mul_comm y (b i), ← this]
    exact Finset.sum_congr rfl fun j _ => by rw [mul_comm]; congr 2; ring
  simp_rw [hr]
  unfold trExtDer
  rw [Finset.smul_sum, Finset.smul_sum]
  simp_rw [smul_smul, smul_eq_mul, mul_assoc]

theorem trExtDer_isDerOn (h : IsTrData B C tr a b e) (hD : IsDerOn B D) :
    IsDerOn C (trExtDer tr a b e D) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy
    unfold trExtDer
    rw [← smul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold trTwistDefect
    rw [← smul_add, add_mul, trTwist_add h hD (C.mul_mem hx (h.a_mem j)) (C.mul_mem hy (h.a_mem j)),
      add_smul]
    congr 1
    abel
  · intro x hx y hy
    have e1 : trExtDer tr a b e D (x * y) =
        e • ∑ j, b j • trTwistDefect tr a b D x (y * a j) + x • trExtDer tr a b e D y := by
      unfold trExtDer
      simp_rw [defect_mul, smul_add, Finset.sum_add_distrib, smul_add]
      congr 1
      rw [Finset.smul_sum, Finset.smul_sum, Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [smul_comm (b j) x, smul_comm e x]
    rw [e1, ← trExtDer_swap h hD hx hy, add_comm]
  · intro c
    unfold trExtDer
    have hc : algebraMap A S c ∈ B := B.algebraMap_mem c
    have : ∀ j, b j • trTwistDefect tr a b D (algebraMap A S c) (a j) =
        (b j * (e * a j)) • D (algebraMap A S c) := by
      intro j
      unfold trTwistDefect
      rw [trTwist_smul h hD hc (h.a_mem j), add_sub_cancel_left, smul_smul]
    simp [this, hD.alg c]

theorem trExtDer_apply_of_mem (h : IsTrData B C tr a b e) (hD : IsDerOn B D) {β : S} (hβ : β ∈ B) :
    trExtDer tr a b e D β = (e ^ 3) • D β := by
  unfold trExtDer
  have : ∀ j, b j • trTwistDefect tr a b D β (a j) = (b j * (e * a j)) • D β := by
    intro j
    unfold trTwistDefect
    rw [trTwist_smul h hD hβ (h.a_mem j), add_sub_cancel_left, smul_smul]
  simp_rw [this, ← Finset.sum_smul, smul_smul]
  have hs : ∑ j, b j * (e * a j) = e * e := by
    rw [← h.sum, Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [hs]; congr 1; ring

theorem exists_derOn_ext : ∀ (A S M : Type) [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M]
    [Module S M] (B C : Subalgebra A S) (tr : S → S) (n : ℕ) (a b : Fin n → S) (e : S),
    IsTrData B C tr a b e → ∀ D : S → M, IsDerOn B D →
      ∃ D' : S → M, IsDerOn C D' ∧ ∀ β ∈ B, D' β = (e ^ 3) • D β := by
  intro A S M _ _ _ _ _ B C tr n a b e h D hD
  exact ⟨trExtDer tr a b e D, trExtDer_isDerOn h hD, fun β hβ => trExtDer_apply_of_mem h hD hβ⟩

end GlobalTheory.AlmostEt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEqPrimePowMulNotDvdCompletedLaurent
section
open GlobalTheory.K5

namespace GlobalTheory.K5.Basic

theorem exists_not_prime_pow_dvd_completedLaurent (p : ℕ) [Fact p.Prime] (x : O0 p) (hx : x ≠ 0) :
    ∃ a : ℕ, ¬ (p : O0 p) ^ a ∣ x := by
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective (pI p) (Lau p) x
  obtain ⟨a, ha⟩ := exists_not_dvd p s hx
  refine ⟨a, ?_⟩
  rintro ⟨z, hz⟩
  apply ha a le_rfl
  have h1 := congrArg (AdicCompletion.evalₐ (pI p) a) hz
  rw [AdicCompletion.evalₐ_mk, map_mul, map_pow, map_natCast,
    ← map_natCast (Ideal.Quotient.mk (pI p ^ a)), ← map_pow] at h1
  have h2 : Ideal.Quotient.mk (pI p ^ a) ((p : Lau p) ^ a) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem, mem_pI_pow]
  rw [h2, zero_mul, Ideal.Quotient.eq_zero_iff_mem, mem_pI_pow] at h1
  exact h1

theorem exists_eq_prime_pow_mul_not_dvd_completedLaurent : ∀ (p : ℕ) [Fact p.Prime], ∀ x : O0 p, x ≠ 0 →
    ∃ (k : ℕ) (y : O0 p), x = (p : O0 p) ^ k * y ∧ ¬ (p : O0 p) ∣ y := by
  intro p _ x hx
  obtain ⟨a, ha⟩ := exists_not_prime_pow_dvd_completedLaurent p x hx
  have hfin : FiniteMultiplicity (p : O0 p) x :=
    ⟨a, fun h => ha ((pow_dvd_pow _ (Nat.le_succ a)).trans h)⟩
  obtain ⟨y, hy, hnd⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  exact ⟨_, y, hy, hnd⟩

end GlobalTheory.K5.Basic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLagrangeResolventOfPGroupFaithful
section
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem exists_lagrange_resolvent : ∀ (L : Type) [Field L] (p : ℕ), p.Prime → ∀ (G : Type) [Group G]
    [MulSemiringAction G L] [Finite G] [Nontrivial G] [FaithfulSMul G L], IsPGroup p G →
    ∀ ζ : L, IsPrimitiveRoot ζ p → (∀ g : G, g • ζ = ζ) →
    ∃ (σ : G) (α : L), α ≠ 0 ∧ σ • α = ζ * α ∧ ∀ g : G, g • α ^ p = α ^ p := by
  intro L _ p hp G _ _ _ _ _ hG ζ hζ hfix
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  classical
  letI : Fintype G := Fintype.ofFinite G
  obtain ⟨χ, hχ⟩ := _root_.GlobalTheory.AlmostEt.exists_surj_hom_zmod_of_isPGroup p G hG
  set ψ : G → L := fun g => ζ ^ (Multiplicative.toAdd (χ g)).val with hψdef
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  have hmod : ∀ n : ℕ, ζ ^ n = ζ ^ (n % p) := fun n => by
    conv_lhs => rw [← Nat.div_add_mod n p, pow_add, pow_mul, hζp, one_pow, one_mul]
  have hψmul : ∀ a b, ψ (a * b) = ψ a * ψ b := by
    intro a b
    simp only [hψdef, map_mul, toAdd_mul, ZMod.val_add, ← pow_add]
    exact (hmod _).symm
  have hψp : ∀ g, ψ g ^ p = 1 := by
    intro g; simp only [hψdef]; rw [← pow_mul, mul_comm, pow_mul, hζp, one_pow]
  have hψne : ∀ g, ψ g ≠ 0 := fun g h => by
    have := hψp g; rw [h, zero_pow hp.ne_zero] at this; exact zero_ne_one this
  have hψfix : ∀ g h : G, g • ψ h = ψ h := fun g h => by simp only [hψdef, smul_pow', hfix]
  let f : G → (L →* L) := fun g => (MulSemiringAction.toRingHom G L g : L →* L)
  have hf : Function.Injective f := by
    intro g h hgh
    apply FaithfulSMul.eq_of_smul_eq_smul (α := L)
    intro x
    exact DFunLike.congr_fun hgh x
  have hli : LinearIndependent L (fun g : G => ((f g : L →* L) : L → L)) :=
    (linearIndependent_monoidHom L L).comp f hf
  have hex : ∃ x : L, ∑ g : G, ψ g⁻¹ * (g • x) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have h0 : ∑ g : G, ψ g⁻¹ • ((f g : L →* L) : L → L) = 0 := by
      funext x
      simpa [f, Finset.sum_apply] using hcon x
    exact hψne _ ((Fintype.linearIndependent_iff.mp hli) (fun g => ψ g⁻¹) h0 1)
  obtain ⟨x, hx⟩ := hex
  set α := ∑ g : G, ψ g⁻¹ * (g • x) with hα
  have hact : ∀ h : G, h • α = ψ h * α := by
    intro h
    rw [hα, Finset.smul_sum, Finset.mul_sum]
    simp only [smul_mul', hψfix, smul_smul]
    refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun g => ?_)
    simp only [Equiv.coe_mulLeft]
    have e : ψ h * ψ h⁻¹ = 1 := by
      rw [← hψmul, mul_inv_cancel]; simp [hψdef]
    rw [mul_inv_rev, hψmul g⁻¹ h⁻¹]
    linear_combination (-(ψ g⁻¹ * ((h * g) • x))) * e
  obtain ⟨σ, hσ⟩ := hχ (Multiplicative.ofAdd 1)
  refine ⟨σ, α, hx, ?_, ?_⟩
  · rw [hact σ]
    congr 1
    simp [hψdef, hσ, ZMod.val_one]
  · intro g
    rw [smul_pow', hact g, mul_pow, hψp, one_mul]

end GlobalTheory.AlmostEt
end

