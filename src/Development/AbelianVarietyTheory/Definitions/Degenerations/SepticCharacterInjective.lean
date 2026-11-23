module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators

noncomputable section
namespace GlobalTheory.Ex

def dbl {A U : Type} [CommGroup A] [CommGroup U] (θ : A → A → A → U) (σ : A → U) (x : A) : U := θ x x⁻¹ x / σ x

def mulq {A U : Type} [CommGroup A] [CommGroup U] (θ : A → A → A → U) (σ : A → U) (n : ℕ) (x : A) : U :=
  ∏ i ∈ Finset.range n, cubN θ i 1 x x / dbl θ σ x ^ i

theorem sym_of_mul {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (hθ : IsCub θ) {σ : A → U} (h1 : σ 1 = 1)
    (h : ∀ x y, σ (x * y) * θ x x⁻¹ y⁻¹ = σ x * σ y * θ y y⁻¹ x) :
    (∀ x, σ x * σ x⁻¹ = 1) ∧
      ∀ x y u, θ x⁻¹ y⁻¹ u⁻¹ * σ (x * y) * σ (x * u) * σ (y * u) = θ x y u * σ (x * y * u) * σ x * σ y * σ u := by
  refine ⟨fun x => ?_, fun x y u => ?_⟩
  · have := h x x⁻¹
    rw [mul_inv_cancel, h1, inv_inv, one_mul, hθ.s01 x⁻¹] at this
    exact (mul_eq_right.1 this.symm)
  · have E := fun {p q : U} (e : p = q) => congrArg Additive.ofMul e
    have a := E (h (x * y) u); have b := E (h x u); have c := E (h y u)
    have d := hθ.compat x y u u⁻¹
    have k1 := hθ.coc x y (x * y)⁻¹ u⁻¹
    have k2 := hθ.coc y y⁻¹ x⁻¹ u⁻¹
    have r : ∀ z, θ u u⁻¹ z = θ z u u⁻¹ := fun z => by rw [hθ.s12, hθ.s01]
    rw [mul_inv_cancel, hθ.face₃] at d
    rw [show y * (x * y)⁻¹ = x⁻¹ by rw [mul_inv, mul_comm x⁻¹, mul_inv_cancel_left]] at k1
    rw [mul_inv_cancel, hθ.face, mul_comm y⁻¹, ← mul_inv, hθ.s01 y⁻¹] at k2
    have d := E d; have k1 := E k1; have k2 := E k2
    apply Additive.ofMul.injective
    simp only [r, ofMul_mul, ofMul_one] at a b c d k1 k2 ⊢
    linear_combination (norm := abel) b + c - a - d + k1 - k2

structure NumB (O : Type) [CommRing O] where
  A : Type
  [grp : CommGroup A]
  θ : A → A → A → Oˣ
  cub : IsCub θ
  σ : A → Oˣ
  σ_one : σ 1 = 1
  σ_mul : ∀ x y, σ (x * y) * θ x x⁻¹ y⁻¹ = σ x * σ y * θ y y⁻¹ x
  σ_inv : ∀ x, σ x * σ x⁻¹ = 1 := (sym_of_mul cub σ_one σ_mul).1
  σ_cub : ∀ x y u, θ x⁻¹ y⁻¹ u⁻¹ * σ (x * y) * σ (x * u) * σ (y * u) = θ x y u * σ (x * y * u) * σ x * σ y * σ u :=
    (sym_of_mul cub σ_one σ_mul).2
  th : A → O
attribute [instance] NumB.grp

structure NumD (O : Type) [CommRing O] extends NumB O where
  X : Type
  [add : AddCommGroup X]
  [free : Module.Free ℤ X]
  [fin : Module.Finite ℤ X]
  c : X → A
  c_add : ∀ a b, c (a + b) = c a * c b
  ψ : X → Oˣ
  even : ∀ χ, ψ (-χ) * σ (c χ) = ψ χ
  bimult : ∀ a a' b, ψ (a + a' + b) / ψ (a + a') / ψ b * θ (c a) (c a') (c b) =
    (ψ (a + b) / ψ a / ψ b) * (ψ (a' + b) / ψ a' / ψ b)
attribute [instance] NumD.add NumD.free NumD.fin
variable {O : Type} [CommRing O]
namespace NumB
variable (B : NumB O)

def weil (k : ℕ) (b b' : B.A) : Oˣ := cubN B.θ k 1 b' b / cubN B.θ k 1 b b'

def uV (k : ℕ) (a b x : B.A) : Oˣ := cubN B.θ k a b x / B.θ a x b

def wS (k : ℕ) (b : B.A) (ψy yg : Oˣ) : Oˣ :=
  ψy * mulq B.θ B.σ k b / (yg * cubN B.θ k 1 b b / dbl B.θ B.σ b ^ k) ^ ((k - 1) / 2)

def mth (m : ℕ) (x : B.A) : O := B.th (x ^ m) * ((mulq B.θ B.σ m x)⁻¹ : Oˣ)

def uth (m : ℕ) (b x : B.A) : O := (B.uV (m ^ 2) 1 b x * B.wS (m ^ 2) b 1 1 : Oˣ) * B.mth m (x * b)

structure Iso (B' B : NumB O) where
  φ : B'.A ≃* B.A
  h : B'.A → Oˣ
  h_one : h 1 = 1
  θ_eq : ∀ x y u, B.θ (φ x) (φ y) (φ u) * h (x * y) * h (x * u) * h (y * u) = B'.θ x y u * h (x * y * u) * h x * h y * h u
  σ_eq : ∀ x, B.σ (φ x) * h x = B'.σ x * h x⁻¹
  lam : Oˣ
  th_eq : ∀ x, B.th (φ x) = (lam * h x : Oˣ) * B'.th x
end NumB
namespace NumD
variable (N : NumD O)

def τ (a b : N.X) : Oˣ := N.ψ (a + b) / N.ψ a / N.ψ b

@[simp] theorem c_zero : N.c 0 = 1 := by
  have := N.c_add 0 0
  rw [add_zero] at this
  exact mul_eq_left.1 this.symm

theorem c_neg (a : N.X) : N.c (-a) = (N.c a)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← N.c_add, neg_add_cancel, N.c_zero])

theorem c_nsmul (k : ℕ) (a : N.X) : N.c (k • a) = N.c a ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [succ_nsmul, N.c_add, ih, pow_succ]

theorem τ_symm (a b : N.X) : N.τ a b = N.τ b a := by
  simp only [τ, add_comm a b, div_right_comm]

theorem τ_add_left (a a' b : N.X) :
    N.τ (a + a') b * N.θ (N.c a) (N.c a') (N.c b) = N.τ a b * N.τ a' b := N.bimult a a' b

theorem τ_add_right (a b b' : N.X) :
    N.τ a (b + b') * N.θ (N.c b) (N.c b') (N.c a) = N.τ a b * N.τ a b' := by
  rw [N.τ_symm a, N.τ_symm a, N.τ_symm a, N.τ_add_left]

@[simp] theorem τ_zero_left (b : N.X) : N.τ 0 b = 1 := by
  have := N.τ_add_left 0 0 b
  rw [add_zero, N.c_zero, N.cub.face, mul_one] at this
  exact mul_eq_left.1 this.symm

@[simp] theorem τ_zero_right (a : N.X) : N.τ a 0 = 1 := by rw [N.τ_symm, N.τ_zero_left]

@[simp] theorem ψ_zero : N.ψ 0 = 1 := by
  have := N.τ_zero_left 0
  simpa [τ] using this

theorem ψ_add (a b : N.X) : N.ψ (a + b) = N.τ a b * N.ψ a * N.ψ b := by
  rw [τ, mul_right_comm, div_mul_cancel, div_mul_cancel]

@[ext] structure Gt where
  b : N.A
  s : N.X → Oˣ
  mult : ∀ χ χ', s (χ + χ') * N.θ (N.c χ) (N.c χ') b = s χ * s χ'

instance : CommGroup N.Gt where
  mul g g' := ⟨g.b * g'.b, fun χ => g.s χ * g'.s χ / N.θ (N.c χ) g.b g'.b, fun χ χ' => by
    have a := congrArg Additive.ofMul (N.cub.compat (N.c χ) (N.c χ') g.b g'.b)
    have b := congrArg Additive.ofMul (g.mult χ χ')
    have c := congrArg Additive.ofMul (g'.mult χ χ')
    rw [N.c_add]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div] at a b c ⊢
    linear_combination (norm := abel) b + c - a⟩
  one := ⟨1, fun _ => 1, fun χ χ' => by rw [N.cub.face₃]⟩
  inv g := ⟨g.b⁻¹, fun χ => N.θ (N.c χ) g.b g.b⁻¹ / g.s χ, fun χ χ' => by
    have a := N.cub.compat (N.c χ) (N.c χ') g.b g.b⁻¹
    rw [mul_inv_cancel, N.cub.face₃, one_mul] at a
    replace a := congrArg Additive.ofMul a
    have b := congrArg Additive.ofMul (g.mult χ χ')
    rw [N.c_add]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div] at a b ⊢
    linear_combination (norm := abel) a - b⟩
  mul_assoc g g' g'' := by
    refine Gt.ext (mul_assoc g.b g'.b g''.b) (funext fun χ => ?_)
    change g.s χ * g'.s χ / N.θ (N.c χ) g.b g'.b * g''.s χ / N.θ (N.c χ) (g.b * g'.b) g''.b =
      g.s χ * (g'.s χ * g''.s χ / N.θ (N.c χ) g'.b g''.b) / N.θ (N.c χ) g.b (g'.b * g''.b)
    have r : ∀ x y, N.θ x y (N.c χ) = N.θ (N.c χ) x y := fun x y => by rw [N.cub.s12, N.cub.s01]
    have a := N.cub.coc g.b g'.b g''.b (N.c χ)
    simp only [r] at a
    replace a := congrArg Additive.ofMul a
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div] at a ⊢
    linear_combination (norm := abel) -a
  one_mul g := by
    refine Gt.ext (one_mul g.b) (funext fun χ => ?_)
    change 1 * g.s χ / N.θ (N.c χ) 1 g.b = g.s χ
    rw [N.cub.face₂, one_mul, div_one]
  mul_one g := by
    refine Gt.ext (mul_one g.b) (funext fun χ => ?_)
    change g.s χ * 1 / N.θ (N.c χ) g.b 1 = g.s χ
    rw [N.cub.face₃, mul_one, div_one]
  inv_mul_cancel g := by
    refine Gt.ext (inv_mul_cancel g.b) (funext fun χ => ?_)
    change N.θ (N.c χ) g.b g.b⁻¹ / g.s χ * g.s χ / N.θ (N.c χ) g.b⁻¹ g.b = 1
    rw [div_mul_cancel, N.cub.s12, div_self']
  mul_comm g g' := by
    refine Gt.ext (mul_comm g.b g'.b) (funext fun χ => ?_)
    change g.s χ * g'.s χ / N.θ (N.c χ) g.b g'.b = g'.s χ * g.s χ / N.θ (N.c χ) g'.b g.b
    rw [N.cub.s12, mul_comm]
namespace Gt
variable {N}

@[simp] theorem mul_b (g g' : N.Gt) : (g * g').b = g.b * g'.b := rfl

theorem mul_s (g g' : N.Gt) (χ : N.X) : (g * g').s χ = g.s χ * g'.s χ / N.θ (N.c χ) g.b g'.b := rfl

@[simp] theorem one_b : (1 : N.Gt).b = 1 := rfl

@[simp] theorem generator_inv_base (χ : N.X) : (1 : N.Gt).s χ = 1 := rfl

@[simp] theorem inv_b (g : N.Gt) : g⁻¹.b = g.b⁻¹ := rfl

@[simp] theorem s_zero (g : N.Gt) : g.s 0 = 1 := by
  have := g.mult 0 0
  rw [add_zero, N.c_zero, N.cub.face, mul_one] at this
  exact mul_eq_left.1 this.symm

@[simp] theorem pow_b (g : N.Gt) (k : ℕ) : (g ^ k).b = g.b ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, mul_b, ih]

theorem pow_s (g : N.Gt) (k : ℕ) (χ : N.X) : (g ^ k).s χ * cubN N.θ k 1 g.b (N.c χ) = g.s χ ^ k := by
  induction k with
  | zero => simp [cubN]
  | succ k ih =>
    rw [cubN] at ih
    rw [pow_succ, pow_succ, mul_s, cubN, Finset.prod_range_succ, ← ih, pow_b, one_mul, N.cub.s12 (g.b ^ k),
      N.cub.s01 (g.b ^ k), ← mul_assoc, mul_right_comm, div_mul_cancel, mul_right_comm]
end Gt

def projB : N.Gt →* N.A where
  toFun g := g.b
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem projB_apply (g : N.Gt) : N.projB g = g.b := rfl

def io (y : N.X) : N.Gt := ⟨N.c y, fun χ => N.τ y χ, fun χ χ' => N.τ_add_right y χ χ'⟩

@[simp] theorem io_b (y : N.X) : (N.io y).b = N.c y := rfl

@[simp] theorem io_s (y χ : N.X) : (N.io y).s χ = N.τ y χ := rfl

theorem io_add (a b : N.X) : N.io (a + b) = N.io a * N.io b := by
  refine Gt.ext (N.c_add a b) (funext fun χ => ?_)
  rw [Gt.mul_s, io_s, io_s, io_s, io_b, io_b, ← N.τ_add_left, N.cub.s12 (N.c a), N.cub.s01 (N.c a),
    mul_div_cancel_right]

def ioHom : Multiplicative N.X →* N.Gt :=
  MonoidHom.mk' (fun y => N.io y.toAdd) fun a b => N.io_add a.toAdd b.toAdd

@[simp] theorem io_zero : N.io 0 = 1 := N.ioHom.map_one

theorem io_neg (a : N.X) : N.io (-a) = (N.io a)⁻¹ := N.ioHom.map_inv (Multiplicative.ofAdd a)

theorem io_nsmul (k : ℕ) (a : N.X) : N.io (k • a) = N.io a ^ k := N.ioHom.map_pow (Multiplicative.ofAdd a) k

def tor (t : Multiplicative N.X →* Oˣ) : N.Gt := ⟨1, fun χ => t (Multiplicative.ofAdd χ), fun χ χ' => by
  rw [N.cub.face₃, mul_one, ofAdd_add, map_mul]⟩

@[simp] theorem tor_b (t : Multiplicative N.X →* Oˣ) : (N.tor t).b = 1 := rfl

@[simp] theorem torus_generator_apply (t : Multiplicative N.X →* Oˣ) (χ : N.X) : (N.tor t).s χ = t (Multiplicative.ofAdd χ) := rfl

theorem tor_mul (t t' : Multiplicative N.X →* Oˣ) : N.tor (t * t') = N.tor t * N.tor t' := by
  refine Gt.ext (mul_one (1 : N.A)).symm (funext fun χ => ?_)
  rw [Gt.mul_s, tor_b, tor_b, N.cub.face₃, div_one]
  rfl

def torHom : (Multiplicative N.X →* Oˣ) →* N.Gt := MonoidHom.mk' N.tor N.tor_mul

@[simp] theorem tor_one : N.tor 1 = 1 := N.torHom.map_one

theorem tor_pow (t : Multiplicative N.X →* Oˣ) (k : ℕ) : N.tor (t ^ k) = N.tor t ^ k := N.torHom.map_pow t k

theorem tor_injective : Function.Injective N.tor := fun t t' h =>
  MonoidHom.ext fun χ => congrArg (fun g : N.Gt => g.s χ.toAdd) h

theorem exists_tor_iff (g : N.Gt) : (∃ t, N.tor t = g) ↔ g.b = 1 := by
  constructor
  · rintro ⟨t, rfl⟩; rfl
  · intro h
    refine ⟨MonoidHom.mk' (fun χ => g.s χ.toAdd) fun a b => ?_, Gt.ext h.symm rfl⟩
    have := g.mult a.toAdd b.toAdd
    rwa [h, N.cub.face₃, mul_one] at this

theorem tor_mul_s_apply (t : Multiplicative N.X →* Oˣ) (g : N.Gt) (χ : N.X) :
    (N.tor t * g).s χ = t (Multiplicative.ofAdd χ) * g.s χ := by
  rw [Gt.mul_s, tor_b, N.cub.face₂, div_one, torus_generator_apply]

def QT (k : ℕ) : Subgroup (Multiplicative N.X × N.Gt) where
  carrier := {p | p.2 ^ k = N.io p.1.toAdd}
  mul_mem' {p p'} h h' := by
    change (p.2 * p'.2) ^ k = N.io (p.1.toAdd + p'.1.toAdd)
    rw [mul_pow, N.io_add, (show p.2 ^ k = _ from h), (show p'.2 ^ k = _ from h')]
  one_mem' := by
    change (1 : N.Gt) ^ k = N.io 0
    rw [one_pow, N.io_zero]
  inv_mem' {p} h := by
    change p.2⁻¹ ^ k = N.io (-p.1.toAdd)
    rw [inv_pow, N.io_neg, (show p.2 ^ k = _ from h)]

theorem mem_QT {k : ℕ} {p : Multiplicative N.X × N.Gt} : p ∈ N.QT k ↔ p.2 ^ k = N.io p.1.toAdd := Iff.rfl

theorem QT_pow_b {k : ℕ} (p : N.QT k) : p.1.2.b ^ k = N.c p.1.1.toAdd := by
  rw [← Gt.pow_b, N.mem_QT.1 p.2, io_b]

def qTriv (k : ℕ) (z : N.X) : N.QT k := ⟨(Multiplicative.ofAdd (k • z), N.io z), (N.io_nsmul k z).symm⟩

def qTor {k : ℕ} (t : Multiplicative N.X →* Oˣ) (ht : t ^ k = 1) : N.QT k :=
  ⟨(1, N.tor t), by rw [mem_QT, ← N.tor_pow, ht, N.tor_one]; exact N.io_zero.symm⟩

def QEq {k : ℕ} (p p' : N.QT k) : Prop :=
  ∃ z : N.X, p'.1.1.toAdd = p.1.1.toAdd + k • z ∧ p'.1.2 = p.1.2 * N.io z

theorem qEq_iff {k : ℕ} (p p' : N.QT k) : N.QEq p p' ↔ ∃ z, p' = p * N.qTriv k z :=
  exists_congr fun _ => ⟨fun h => Subtype.ext (Prod.ext h.1 h.2),
    fun h => ⟨congrArg (fun q : N.QT k => q.1.1.toAdd) h, congrArg (fun q : N.QT k => q.1.2) h⟩⟩

theorem qEq_equivalence (k : ℕ) : Equivalence (N.QEq (k := k)) := by
  refine ⟨fun p => ⟨0, by simp, by simp⟩, ?_, ?_⟩
  · rintro p p' ⟨z, h, h'⟩
    exact ⟨-z, by rw [h, smul_neg, add_neg_cancel_right], by rw [h', N.io_neg, mul_inv_cancel_right]⟩
  · rintro p p' p'' ⟨z, h, h'⟩ ⟨w, e, e'⟩
    exact ⟨z + w, by rw [e, h, smul_add, add_assoc], by rw [e', h', N.io_add, mul_assoc]⟩

def tk {k : ℕ} (p p' : N.QT k) : Oˣ := p.1.2.s p'.1.1.toAdd * cubN N.θ k 1 p'.1.2.b p.1.2.b

def wp {k : ℕ} (p p' : N.QT k) : Oˣ := N.tk p p' / N.tk p' p

theorem wp_self {k : ℕ} (p : N.QT k) : N.wp p p = 1 := div_self' _

theorem wp_swap {k : ℕ} (p p' : N.QT k) : N.wp p' p = (N.wp p p')⁻¹ := (inv_div _ _).symm

theorem wp_qTor {k : ℕ} (t : Multiplicative N.X →* Oˣ) (ht : t ^ k = 1) (p' : N.QT k) :
    N.wp (N.qTor t ht) p' = t p'.1.1 := by
  have a : cubN N.θ k 1 1 p'.1.2.b = 1 := Finset.prod_eq_one fun _ _ => N.cub.face₂ _ _
  change t p'.1.1 * cubN N.θ k 1 p'.1.2.b 1 / (p'.1.2.s 0 * cubN N.θ k 1 1 p'.1.2.b) = _
  rw [a, N.cub.N_one, Gt.s_zero, mul_one, mul_one, div_one]

theorem wp_of_eq_zero {k : ℕ} (p p' : N.QT k) (h : p.1.1.toAdd = 0) (h' : p'.1.1.toAdd = 0) :
    N.wp p p' = N.weil k p.1.2.b p'.1.2.b := by
  simp only [wp, tk, h, h', Gt.s_zero, one_mul, NumB.weil]

def wQ {k : ℕ} (p : N.QT k) : Oˣ := N.wS k p.1.2.b (N.ψ p.1.1.toAdd) (p.1.2.s p.1.1.toAdd)

def vt (g : N.Gt) (χ : N.X) : O := (N.ψ χ * g.s χ : Oˣ) * N.th (N.c χ * g.b)

def txT (m : ℕ) (p : N.QT (m ^ 2)) (χ : N.X) : O :=
  (N.wQ p / mulq N.θ N.σ m p.1.2.b : Oˣ) * N.vt (p.1.2 ^ m) χ

def tx [TopologicalSpace O] (m : ℕ) (p : N.QT (m ^ 2)) : O := ∑' χ, N.txT m p χ

def FE (k : ℕ) (s : N.X → N.A → O) : Prop :=
  ∀ μ α x, s (α + k • μ) x = (N.uV k (N.c α) (N.c μ) x * N.ψ μ ^ k * N.τ μ α : Oˣ) * s α (x * N.c μ)

def phi {k : ℕ} (p : N.QT k) (w : Oˣ) (s : N.X → N.A → O) : N.X → N.A → O := fun α x =>
  (N.uV k (N.c (α - p.1.1.toAdd)) p.1.2.b x * p.1.2.s (α - p.1.1.toAdd) * w : Oˣ) * s (α - p.1.1.toAdd) (x * p.1.2.b)

def vth : N.X → N.A → O := fun α x => (N.ψ α : O) * N.th (x * N.c α)

structure Iso (N' N : NumD O) extends NumB.Iso N'.toNumB N.toNumB where
  e : N'.X ≃+ N.X
  c_eq : ∀ χ, N.c (e χ) = φ (N'.c χ)
  ψ_eq : ∀ χ, N.ψ (e χ) * h (N'.c χ) = N'.ψ χ

def Iso.Rel {N' N : NumD O} (I : Iso N' N) (g' : N'.Gt) (g : N.Gt) : Prop :=
  g.b = I.φ g'.b ∧ ∀ χ, g.s (I.e χ) * I.h (N'.c χ * g'.b) = g'.s χ * I.h (N'.c χ) * I.h g'.b

theorem Iso.rel_one {N' N : NumD O} (I : Iso N' N) : I.Rel 1 1 :=
  ⟨(map_one I.φ).symm, fun χ => by simp [I.h_one]⟩
end NumD

structure NumD.Int {C : Type} [NormedField C] (N : NumD C) (q : QuadraticMap ℤ N.X ℝ) : Prop where
  θ : ∀ x y u, ‖(N.θ x y u : C)‖ = 1
  σ : ∀ x, ‖(N.σ x : C)‖ = 1
  th : ∀ x, ‖N.th x‖ ≤ 1
  ψ : ∀ χ, ‖(N.ψ χ : C)‖ = Real.exp (-q χ)
  pos : Filter.Tendsto q Filter.cofinite Filter.atTop

structure NumB.Tors {C : Type} [NormedField C] (B : NumB C) (n g : ℕ) : Prop where
  div : ∀ x : B.A, ∃ y, y ^ n = x
  str : ∀ j : ℕ, Nonempty ((powMonoidHom (n ^ j) : B.A →* B.A).ker ≃* Multiplicative (Fin (2 * g) → ZMod (n ^ j)))
  nondeg : ∀ (j : ℕ) (b : B.A), b ^ n ^ j = 1 → (∀ b', b' ^ n ^ j = 1 → B.weil (n ^ j) b b' = 1) → b = 1
  good : ∀ a : B.A, ∃ t, t ^ n = 1 ∧ ‖B.th (a * t)‖ = 1
  sep : ∀ (j : ℕ), 1 ≤ j → ∀ (x x' : B.A) (l : C), l ≠ 0 →
    (∀ b, b ^ (n ^ j) ^ 2 = 1 → B.uth (n ^ j) b x = l * B.uth (n ^ j) b x') → x = x'

namespace NumB

def regauge (B : NumB O) (h : B.A → Oˣ) (h₁ : h 1 = 1) : NumB O where
  A := B.A
  θ x y u := B.θ x y u * h (x * y) * h (x * u) * h (y * u) / (h (x * y * u) * h x * h y * h u)
  cub :=
    { face := fun x y => by
        apply Additive.ofMul.injective
        simp only [B.cub.face, one_mul, h₁, ofMul_mul, ofMul_div, ofMul_one]
        abel
      s01 := fun x y z => by
        apply Additive.ofMul.injective
        simp only [B.cub.s01 x y z, mul_comm y x, ofMul_mul, ofMul_div]
        abel
      s12 := fun x y z => by
        apply Additive.ofMul.injective
        simp only [B.cub.s12 x y z, mul_comm z y, mul_right_comm x z y, ofMul_mul, ofMul_div]
        abel
      coc := fun x x' x'' y => by
        have a := congrArg Additive.ofMul (B.cub.coc x x' x'' y)
        apply Additive.ofMul.injective
        simp only [← mul_assoc x, ← mul_assoc (x * x'), ofMul_mul, ofMul_div] at a ⊢
        linear_combination (norm := abel) a }
  σ x := B.σ x * h x / h x⁻¹
  σ_one := by rw [B.σ_one, inv_one, one_mul, div_self']
  σ_mul x y := by
    have a := congrArg Additive.ofMul (B.σ_mul x y)
    apply Additive.ofMul.injective
    simp only [mul_inv_cancel, one_mul, h₁, mul_inv, mul_comm y x, mul_comm y⁻¹ x, ofMul_mul, ofMul_div, ofMul_one] at a ⊢
    linear_combination (norm := abel) a
  th x := ((h x)⁻¹ : Oˣ) * B.th x

def triv (A : Type) [CommGroup A] (f : A → O) : NumB O where
  A := A
  θ _ _ _ := 1
  cub := ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩
  σ _ := 1
  σ_one := rfl
  σ_mul _ _ := by simp
  th := f
end NumB
namespace NumD

def regauge (N : NumD O) (h : N.A → Oˣ) (h₁ : h 1 = 1) : NumD O where
  toNumB := N.toNumB.regauge h h₁
  X := N.X
  c := N.c
  c_add := N.c_add
  ψ χ := N.ψ χ * h (N.c χ)
  even χ := by
    change N.ψ (-χ) * h (N.c (-χ)) * (N.σ (N.c χ) * h (N.c χ) / h (N.c χ)⁻¹) = N.ψ χ * h (N.c χ)
    have a := congrArg Additive.ofMul (N.even χ)
    apply Additive.ofMul.injective
    simp only [N.c_neg, ofMul_mul, ofMul_div] at a ⊢
    linear_combination (norm := abel) a
  bimult a a' b := by
    change _ * (N.θ (N.c a) (N.c a') (N.c b) * h (N.c a * N.c a') * h (N.c a * N.c b) * h (N.c a' * N.c b) /
      (h (N.c a * N.c a' * N.c b) * h (N.c a) * h (N.c a') * h (N.c b))) = _
    have e := congrArg Additive.ofMul (N.bimult a a' b)
    apply Additive.ofMul.injective
    simp only [N.c_add, ofMul_mul, ofMul_div] at e ⊢
    linear_combination (norm := abel) e

end NumD

def tate (q : Oˣ) : NumD O where
  toNumB := NumB.triv PUnit fun _ => 1
  X := ℤ
  c _ := 1
  c_add _ _ := rfl
  ψ n := q ^ n ^ 2
  even n := by
    change q ^ (-n) ^ 2 * 1 = _
    rw [neg_sq, mul_one]
  bimult a a' b := by
    change _ * 1 = _
    simp only [mul_one, div_eq_mul_inv, ← zpow_neg, ← zpow_add]
    congr 1
    ring

theorem tate_τ (q : Oˣ) (a b : ℤ) : (tate q).τ a b = q ^ (2 * a * b) := by
  change q ^ (a + b) ^ 2 / q ^ a ^ 2 / q ^ b ^ 2 = _
  simp only [div_eq_mul_inv, ← zpow_neg, ← zpow_add]
  congr 1
  ring

def tateQ (r : Oˣ) (k : ℕ) (y : ℤ) : (tate (r ^ k)).QT k :=
  ⟨(Multiplicative.ofAdd y, (tate (r ^ k)).tor (zpowersHom Oˣ (r ^ (2 * y)))), by
    refine ((tate (r ^ k)).tor_pow _ k).symm.trans ?_
    refine NumD.Gt.ext rfl (funext fun (χ : ℤ) => ?_)
    refine Eq.trans ?_ (tate_τ (r ^ k) y χ).symm
    change ((r ^ (2 * y)) ^ χ) ^ k = _
    simp only [← zpow_natCast, ← zpow_mul]
    congr 1
    ring⟩

namespace Level3

end Level3

end GlobalTheory.Ex
end
