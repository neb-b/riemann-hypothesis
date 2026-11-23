module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators
noncomputable section
namespace GlobalTheory.Ex
variable {O : Type} [CommRing O]
namespace NumD
variable (N : NumD O)

structure Form (k : ℕ) where
  be : LinearMap.BilinForm ℤ N.X
  symm : ∀ y z, be y z = be z y
  pos : ∀ y, y ≠ 0 → 0 < be y y
  dvd : ∀ y z, (2 * k : ℤ) ∣ be y z


open scoped BigOperators in
variable {O : Type} [CommRing O] in
variable (N : _root_.GlobalTheory.Ex.NumD O) in
theorem _root_.GlobalTheory.Ex.NumD.Form.half_add {N : _root_.GlobalTheory.Ex.NumD O} {k : ℕ}
    (β : N.Form k) (x y : N.X) :
    β.be (x + y) (x + y) / 2 =
      β.be x x / 2 + β.be y y / 2 +
        β.be x y := by
  have hsum : β.be (x + y) (x + y) = β.be x x +
      β.be y y + 2 * β.be x y := by
    simp only [map_add (f := _), LinearMap.add_apply, β.symm y x]
    ring
  have hx : (2 : ℤ) ∣ β.be x x :=
    dvd_trans (dvd_mul_right 2 (k : ℤ)) (β.dvd x x)
  have hy : (2 : ℤ) ∣ β.be y y :=
    dvd_trans (dvd_mul_right 2 (k : ℤ)) (β.dvd y y)
  omega


open scoped BigOperators in
variable {O : Type} [CommRing O] in
variable (N : _root_.GlobalTheory.Ex.NumD O) in
theorem _root_.GlobalTheory.Ex.NumD.Form.div_mul {N : _root_.GlobalTheory.Ex.NumD O}
    {k : ℕ} (β : N.Form k) {j : ℕ} (hj : j ∣ k)
    (x y : N.X) :
    β.be x y / j * j = β.be x y :=
  Int.ediv_mul_cancel (dvd_trans (Int.natCast_dvd_natCast.2 hj)
    (dvd_trans (dvd_mul_left (k : ℤ) 2) (β.dvd x y)))


open scoped BigOperators in
variable {O : Type} [CommRing O] in
variable (N : _root_.GlobalTheory.Ex.NumD O) in
theorem _root_.GlobalTheory.Ex.NumD.Form.div_add {N : _root_.GlobalTheory.Ex.NumD O} {k : ℕ}
    (β : N.Form k) {j : ℕ} (hj : j ∣ k)
    (x y z : N.X) :
    β.be x (y + z) / j =
      β.be x y / j + β.be x z / j := by
  rw [map_add (f := _)]
  exact Int.add_ediv_of_dvd_left (dvd_trans (Int.natCast_dvd_natCast.2 hj)
    (dvd_trans (dvd_mul_left (k : ℤ) 2) (β.dvd x y)))

def twist {k : ℕ} (β : N.Form k) (u : Oˣ) : NumD O :=
  { N with ψ := fun χ => N.ψ χ * u ^ (β.be χ χ / 2)
           even := fun χ => by
             simp only [map_neg, LinearMap.neg_apply, neg_neg]
             rw [← N.even χ]; exact mul_right_comm _ _ _
           bimult := fun a a' b => by
             have h := N.bimult a a' b
             have e : ∀ x y : N.X, N.ψ (x + y) * u ^ (β.be (x + y) (x + y) / 2) / (N.ψ x * u ^ (β.be x x / 2)) /
                 (N.ψ y * u ^ (β.be y y / 2)) = N.ψ (x + y) / N.ψ x / N.ψ y * u ^ β.be x y := fun x y => by
               rw [β.half_add, zpow_add, zpow_add]
               apply Additive.ofMul.injective
               simp only [ofMul_mul, ofMul_div]; abel
             rw [e, e, e, mul_right_comm, h, map_add (f := _), LinearMap.add_apply, zpow_add]
             exact mul_mul_mul_comm _ _ _ _ }


open scoped BigOperators in
variable {O : Type} [CommRing O] in
variable (N : _root_.GlobalTheory.Ex.NumD O) in
theorem _root_.GlobalTheory.Ex.NumD.twist_τ {k : ℕ} (β : N.Form k) (u : Oˣ)
    (x y : N.X) :
    (N.twist β u).τ x y =
      N.τ x y * u ^ β.be x y := by
  show N.ψ (x + y) * u ^ (β.be (x + y) (x + y) / 2) /
      (N.ψ x * u ^ (β.be x x / 2)) /
      (N.ψ y * u ^ (β.be y y / 2)) =
    N.ψ (x + y) / N.ψ x / N.ψ y *
      u ^ β.be x y
  rw [β.half_add, zpow_add, zpow_add]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div]; abel

def twG {k : ℕ} (β : N.Form k) (u : Oˣ) (g : N.Gt) (l : N.X → ℤ) (hl : ∀ a b, l (a + b) = l a + l b) : (N.twist β u).Gt :=
  ⟨g.b, fun z => g.s z * u ^ l z, fun (χ χ' : N.X) => by
    show g.s (χ + χ') * u ^ l (χ + χ') * N.θ (N.c χ) (N.c χ') g.b = g.s χ * u ^ l χ * (g.s χ' * u ^ l χ')
    rw [mul_right_comm, g.mult, hl, zpow_add]; exact mul_mul_mul_comm _ _ _ _⟩


open scoped BigOperators in
variable {O : Type} [CommRing O] in
variable (N : _root_.GlobalTheory.Ex.NumD O) in
theorem _root_.GlobalTheory.Ex.NumD.twG_pow {k : ℕ} (β : N.Form k) (u : Oˣ)
    (g : N.Gt) (l : N.X → ℤ)
    (hl : ∀ a b, l (a + b) = l a + l b) (n : ℕ) :
    (N.twG β u g l hl ^ n).b =
        (g ^ n).b ∧
      ∀ z : N.X,
        (N.twG β u g l hl ^ n).s z = (g ^ n).s z * u ^ (l z * n) := by
  have hθ : ∀ a b c, (N.twist β u).θ a b c = N.θ a b c :=
    fun _ _ _ => rfl
  have hc : ∀ χ, (N.twist β u).c χ = N.c χ :=
    fun _ => rfl
  have hb : (N.twG β u g l hl).b =
      g.b := rfl
  have hs : ∀ z, (N.twG β u g l hl).s z = g.s z * u ^ l z := fun _ => rfl
  induction n with
  | zero =>
    refine ⟨?_, fun z => ?_⟩
    · rw [pow_zero, pow_zero, _root_.GlobalTheory.Ex.NumD.Gt.one_b (N := N.twist β u),
        _root_.GlobalTheory.Ex.NumD.Gt.one_b (N := N)]
      rfl
    · rw [pow_zero, pow_zero]
      refine (_root_.GlobalTheory.Ex.NumD.Gt.generator_inv_base (N := N.twist β u) z).trans ?_
      rw [_root_.GlobalTheory.Ex.NumD.Gt.generator_inv_base (N := N)]
      simp
  | succ n ih =>
    refine ⟨?_, fun z => ?_⟩
    · rw [pow_succ, pow_succ, _root_.GlobalTheory.Ex.NumD.Gt.mul_b (N := N.twist β u),
        _root_.GlobalTheory.Ex.NumD.Gt.mul_b (N := N), ih.1, hb]
      rfl
    · rw [pow_succ, pow_succ]
      refine (_root_.GlobalTheory.Ex.NumD.Gt.mul_s (N := N.twist β u)
        (N.twG β u g l hl ^ n) (N.twG β u g l hl)
        z).trans ?_
      rw [_root_.GlobalTheory.Ex.NumD.Gt.mul_s (N := N), hθ]
      erw [hc, ih.1, ih.2 z, hb, hs]
      push_cast
      rw [mul_add, mul_one, zpow_add]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_div]; abel

def twQ {k : ℕ} (β : N.Form k) (u : Oˣ) {j : ℕ} (hj : j ∣ k) (p : N.QT j) : (N.twist β u).QT j :=
  ⟨(p.1.1, N.twG β u p.1.2 (fun z => β.be p.1.1.toAdd z / j) (β.div_add hj _)), by
    have h : p.1.2 ^ j = N.io p.1.1.toAdd := p.2
    have h' := N.twG_pow β u p.1.2 (fun z => β.be p.1.1.toAdd z / j) (β.div_add hj _) j
    refine NumD.Gt.ext (h'.1.trans (by rw [h]; rfl)) (funext fun (z : N.X) => (h'.2 z).trans ?_)
    rw [h, β.div_mul hj]; exact (N.twist_τ β u _ z).symm⟩

def evT (m : ℕ) (p : N.QT (m ^ 2)) (h : N.Gt) (χ : N.X) : O :=
  (h.s p.1.1.toAdd * cubN N.θ (m ^ 2) 1 p.1.2.b h.b * N.wQ p / mulq N.θ N.σ m (h.b * p.1.2.b) : Oˣ) *
    N.vt ((h * p.1.2) ^ m) χ

def ev [TopologicalSpace O] (m : ℕ) (p : N.QT (m ^ 2)) (h : N.Gt) : O := ∑' χ, N.evT m p h χ

def arcTx (be : LinearMap.BilinForm ℤ N.X) (m : ℕ) (p : N.QT (m ^ 2)) : PowerSeries O :=
  PowerSeries.mk fun n => ∑ᶠ (χ : N.X) (_ : be (p.1.1.toAdd + m • χ) (p.1.1.toAdd + m • χ) / (2 * m ^ 2) = n), N.txT m p χ

def arcEv (be : LinearMap.BilinForm ℤ N.X) (m : ℕ) (p : N.QT (m ^ 2)) {j : ℕ} (q : N.QT j) (s : ℕ) : PowerSeries O :=
  PowerSeries.mk fun n => ∑ᶠ (χ : N.X) (_ : be (p.1.1.toAdd + m • χ) (p.1.1.toAdd + m • χ) / (2 * m ^ 2) +
    be q.1.1.toAdd (p.1.1.toAdd + m • χ) / j + s = n), N.evT m p q.1.2 χ

structure Hom {O' : Type} [CommRing O'] (f : O →+* O') (N : NumD O) (N' : NumD O') where
  φ : N.A →* N'.A
  h : N.A → O'ˣ
  h_one : h 1 = 1
  θ_eq : ∀ x y u, N'.θ (φ x) (φ y) (φ u) * h (x * y) * h (x * u) * h (y * u) =
    Units.map f.toMonoidHom (N.θ x y u) * h (x * y * u) * h x * h y * h u
  σ_eq : ∀ x, N'.σ (φ x) * h x = Units.map f.toMonoidHom (N.σ x) * h x⁻¹
  lam : O'ˣ
  th_eq : ∀ x, N'.th (φ x) = (lam * h x : O'ˣ) * f (N.th x)
  e : N.X ≃+ N'.X
  c_eq : ∀ χ, N'.c (e χ) = φ (N.c χ)
  ψ_eq : ∀ χ, N'.ψ (e χ) * h (N.c χ) = Units.map f.toMonoidHom (N.ψ χ)

def Hom.Rel {O' : Type} [CommRing O'] {f : O →+* O'} {N : NumD O} {N' : NumD O'} (I : Hom f N N') (g : N.Gt) (g' : N'.Gt) : Prop :=
  g'.b = I.φ g.b ∧ ∀ χ, g'.s (I.e χ) * I.h (N.c χ * g.b) = Units.map f.toMonoidHom (g.s χ) * I.h (N.c χ) * I.h g.b

def InG {k : ℕ} (p : N.QT k) : Prop := ∃ z, p.1.1.toAdd = k • z

def InT {k : ℕ} (p : N.QT k) : Prop := ∃ p' : N.QT k, N.QEq p p' ∧ p'.1.1 = 1 ∧ p'.1.2.b = 1
end NumD

structure Match {C : Type} [NormedField C] (N N' : NumD C) (n : ℕ) where
  r : ∀ k : ℕ, N.QT k → N'.QT k → Prop
  tot : ∀ j p, ∃ p', r (n ^ j) p p'
  cotot : ∀ j p', ∃ p, r (n ^ j) p p'
  mul : ∀ k p q p' q', r k p p' → r k q q' → r k (p * q) (p' * q')
  eqv : ∀ k p q p' q', r k p p' → N.QEq p q → (r k q q' ↔ N'.QEq p' q')
  inj : ∀ k p q p', r k p p' → r k q p' → N.QEq p q
  incl : ∀ k k' (p : N.QT k) (p' : N'.QT k) (q : N.QT (k * k')) (q' : N'.QT (k * k')), k' ≠ 0 →
    q.1.1 = p.1.1 ^ k' → q.1.2 = p.1.2 → q'.1.1 = p'.1.1 ^ k' → q'.1.2 = p'.1.2 → (r k p p' ↔ r (k * k') q q')
  wp : ∀ k p q p' q', r k p p' → r k q q' → N'.wp p' q' = N.wp p q
  c₀ : C
  c₀_ne : c₀ ≠ 0
  tx : ∀ j p p', r ((n ^ j) ^ 2) p p' → N'.tx (n ^ j) p' = c₀ * N.tx (n ^ j) p

def AllMatch (P : ∀ {C : Type} [NontriviallyNormedField C] {N N' : NumD C} {n : ℕ}, Match N N' n → ℕ → ℕ → Prop) : Prop :=
  ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] (N N' : NumD C)
    (q : QuadraticMap ℤ N.X ℝ) (q' : QuadraticMap ℤ N'.X ℝ) (n g g' : ℕ), n.Prime → Odd n → ‖(n : C)‖ = 1 →
    N.Int q → N'.Int q' → N.Tors n g → N'.Tors n g' → ∀ μ : Match N N' n, P μ g g'
namespace Match
variable {C : Type} [NormedField C] {N N' : NumD C} {n : ℕ} (μ : Match N N' n)

def A : Prop := ‖μ.c₀‖ = 1 ∧ ∀ j p p', μ.r (n ^ j) p p' → (N.InG p ↔ N'.InG p') ∧ (N.InT p ↔ N'.InT p')

def B (e : N.X ≃+ N'.X) : Prop := ∀ j p p', μ.r (n ^ j) p p' → ∃ z, p'.1.1.toAdd = e p.1.1.toAdd + n ^ j • z

def Term (e : N.X ≃+ N'.X) : Prop := ∀ j p p', μ.r ((n ^ j) ^ 2) p p' → p.1.1 = 1 → p'.1.1 = 1 →
  ∀ χ, N'.txT (n ^ j) p' (e χ) = μ.c₀ * N.txT (n ^ j) p χ

def OnB (I : NumB.Iso N.toNumB N'.toNumB) : Prop := ∀ j p p', μ.r (n ^ j) p p' → p.1.1 = 1 → p'.1.1 = 1 → p'.1.2.b = I.φ p.1.2.b

def OnG (I : NumD.Iso N N') : Prop := ∀ j p p', μ.r (n ^ j) p p' → p.1.1 = 1 → p'.1.1 = 1 → I.Rel p.1.2 p'.1.2

def OnQ (I : NumD.Iso N N') : Prop := ∀ j p p', p'.1.1.toAdd = I.e p.1.1.toAdd → I.Rel p.1.2 p'.1.2 → μ.r (n ^ j) p p'
end Match

namespace TateInh

def homOfIso {N N' : NumD O} (I : NumD.Iso N N') : NumD.Hom (RingHom.id O) N N' where
  φ := I.φ.toMonoidHom
  h := I.h
  h_one := I.h_one
  θ_eq := I.θ_eq
  σ_eq := I.σ_eq
  lam := I.lam
  th_eq := I.th_eq
  e := I.e
  c_eq := I.c_eq
  ψ_eq := I.ψ_eq


open scoped BigOperators in
variable {O : Type} [CommRing O] in
theorem _root_.GlobalTheory.Ex.TateInh.evT_one (N : _root_.GlobalTheory.Ex.NumD O) (m : ℕ)
    (p : N.QT (m ^ 2)) (χ : N.X) :
    N.evT m p 1 χ = N.txT m p χ := by
  unfold _root_.GlobalTheory.Ex.NumD.evT
    _root_.GlobalTheory.Ex.NumD.txT
  simp only [_root_.GlobalTheory.Ex.NumD.Gt.generator_inv_base,
    _root_.GlobalTheory.Ex.NumD.Gt.one_b, one_mul, N.cub.N_one]


open scoped BigOperators in
variable {O : Type} [CommRing O] in
theorem _root_.GlobalTheory.Ex.TateInh.qEq_mul (N : _root_.GlobalTheory.Ex.NumD O) {k : ℕ}
    {p p' q q' : N.QT k} (h : N.QEq p p')
    (h' : N.QEq q q') :
    N.QEq (p * q) (p' * q') := by
  unfold _root_.GlobalTheory.Ex.NumD.QEq at *
  obtain ⟨z, hz1, hz2⟩ := h
  obtain ⟨z', hz1', hz2'⟩ := h'
  refine ⟨z + z', ?_, ?_⟩
  · simp only [Subgroup.coe_mul, Prod.fst_mul, toAdd_mul, hz1, hz1', smul_add]
    abel
  · simp only [Subgroup.coe_mul, Prod.snd_mul, hz2, hz2', N.io_add]
    exact mul_mul_mul_comm _ _ _ _

end TateInh
end GlobalTheory.Ex
end
