module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0569
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0540
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0571
public import Formalism.PieriBlockIdeals.StatementE
public import Formalism.PieriBlockIdeals.Bundle0007
public import Formalism.PieriBlockIdeals.PieriColumnMinors.WeightBounds

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatibleSimilitudeLevelTower
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev

noncomputable section

namespace GlobalTheory.TowerLev

theorem compat_seq {X : Type} (A : ℕ → Set X) (hfin : ∀ j, (A j).Finite)
    (hne : ∀ j, (A j).Nonempty) (φ : ℕ → X → X) (hφ : ∀ j, ∀ x ∈ A (j + 1), φ j x ∈ A j) :
    ∃ s : ℕ → X, ∀ j, s j ∈ A j ∧ φ j (s (j + 1)) = s j := by
  let F : ℕᵒᵖ ⥤ Type := Functor.ofOpSequence (X := fun j => ↥(A j))
    (fun j => TypeCat.ofHom (fun x => ⟨φ j x.1, hφ j x.1 x.2⟩ : ↥(A (j + 1)) → ↥(A j)))
  haveI : ∀ j : ℕᵒᵖ, Finite (F.obj j) := fun j => (hfin j.unop).to_subtype
  haveI : ∀ j : ℕᵒᵖ, Nonempty (F.obj j) := fun j => (hne j.unop).to_subtype
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_inverse_system F
  refine ⟨fun j => (s (Opposite.op j)).1, fun j => ⟨(s (Opposite.op j)).2, ?_⟩⟩
  have h := hs (homOfLE (Nat.le_add_right j 1)).op
  rw [Functor.ofOpSequence_map_homOfLE_succ] at h
  exact congrArg Subtype.val h

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] {Q : Type} [CommGroup Q]

def IsLev (D : Datum p) (act : D.O → Q → Q) (W : ℕ → Q → Q → kˣ) (ζ : ℕ → kˣ) (r : ℕ) (f : D.La → Q) : Prop :=
  ((∀ x y, f (x + y) = f x * f y) ∧ (∀ (c : D.O) x, f (c • x) = act c (f x)) ∧
    (∀ x, f x = 1 ↔ ∃ y, x = (p ^ r) • y) ∧ (∀ g : Q, g ^ (p ^ r) = 1 ↔ ∃ x, f x = g)) ∧
    ∀ x y, W r (f x) (f y) = ζ r ^ D.EF x y

variable {D : Datum p}

theorem map_zero_of_add {f : D.La → Q} (hf : ∀ x y, f (x + y) = f x * f y) : f 0 = 1 := by
  have h := hf 0 0
  rw [add_zero] at h
  simpa using h.symm

theorem map_nsmul_of_add {f : D.La → Q} (hf : ∀ x y, f (x + y) = f x * f y) (n : ℕ) (x : D.La) :
    f (n • x) = f x ^ n := by
  induction n with
  | zero => simp [map_zero_of_add hf]
  | succ n ih => rw [succ_nsmul, hf, ih, pow_succ]

theorem cancel_nsmul (D : Datum p) (n : ℕ) (hn : n ≠ 0) {a b : D.La} (h : n • a = n • b) : a = b := by
  haveI := D.freeLa
  have h' : (n : ℤ) • a = (n : ℤ) • b := by simpa [natCast_zsmul] using h
  exact smul_right_injective D.La (by exact_mod_cast hn : (n : ℤ) ≠ 0) h'

theorem IsLev.step {act : D.O → Q → Q} {W : ℕ → Q → Q → kˣ} {ζ : ℕ → kˣ}
    (hact : ∀ c a b, act c (a * b) = act c a * act c b) (hζ : ∀ r, ζ (r + 1) ^ p = ζ r)
    (hW : ∀ r (a b : Q), a ^ (p ^ (r + 1)) = 1 → b ^ (p ^ (r + 1)) = 1 →
      W r (a ^ p) (b ^ p) = W (r + 1) a b ^ p)
    (r : ℕ) (f : D.La → Q) (hf : IsLev D act W ζ (r + 1) f) : IsLev D act W ζ r (fun x => f x ^ p) := by
  obtain ⟨⟨hadd, hlin, hker, honto⟩, hpair⟩ := hf
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hkill : ∀ x, f x ^ (p ^ (r + 1)) = 1 := fun x => (honto _).2 ⟨x, rfl⟩
  refine ⟨⟨fun x y => ?_, fun c x => ?_, fun x => ?_, fun g => ?_⟩, fun x y => ?_⟩
  · simp only
    rw [hadd, mul_pow]
  · simp only
    rw [hlin]
    exact (map_pow (MonoidHom.mk' (act c) (hact c)) (f x) p).symm
  · simp only
    rw [← map_nsmul_of_add hadd, hker]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, cancel_nsmul D p hp0 (by rw [hy, pow_succ', mul_smul])⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, by rw [pow_succ', mul_smul]⟩
  · simp only
    constructor
    · intro hg
      have hg' : g ^ (p ^ (r + 1)) = 1 := by rw [pow_succ, pow_mul, hg, one_pow]
      obtain ⟨x, rfl⟩ := (honto g).1 hg'
      rw [← map_nsmul_of_add hadd, hker] at hg
      obtain ⟨y, hy⟩ := hg
      have hx : x = p • y := cancel_nsmul D (p ^ r) (pow_ne_zero _ hp0) (by rw [hy, pow_succ, mul_smul])
      exact ⟨y, by rw [hx, map_nsmul_of_add hadd]⟩
    · rintro ⟨x, rfl⟩
      rw [← pow_mul, ← pow_succ', hkill]
  · simp only
    rw [hW r (f x) (f y) (hkill x) (hkill y), hpair, ← hζ r, ← zpow_natCast (ζ (r + 1) ^ _),
      ← zpow_natCast (ζ (r + 1)), ← zpow_mul, ← zpow_mul, mul_comm]

theorem finite_range_of_add {f : D.La → Q} (hadd : ∀ x y, f (x + y) = f x * f y) {n : ℕ} (hn : n ≠ 0)
    (hker : ∀ y, f (n • y) = 1) : (Set.range f).Finite := by
  haveI := D.freeLa
  haveI := D.finLa
  let B := Module.Free.chooseBasis ℤ D.La
  have hpos : (0 : ℤ) < (n : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  refine ((Set.Finite.pi (fun _ : Module.Free.ChooseBasisIndex ℤ D.La => Set.finite_Ico (0 : ℤ) n)).image
    (fun v => f (∑ i, v i • B i))).subset ?_
  rintro _ ⟨x, rfl⟩
  refine ⟨fun i => B.repr x i % n, fun i _ => ⟨Int.emod_nonneg _ hpos.ne', Int.emod_lt_of_pos _ hpos⟩, ?_⟩
  have hx : x = ∑ i, (B.repr x i % n) • B i + n • ∑ i, (B.repr x i / n) • B i := by
    rw [← natCast_zsmul, Finset.smul_sum, ← Finset.sum_add_distrib]
    conv_lhs => rw [← B.sum_repr x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, ← add_smul, Int.emod_add_mul_ediv]
  rw [congrArg f hx, hadd, hker, _root_.mul_one]

def toLin (f : D.La → Q) (hf : ∀ x y, f (x + y) = f x * f y) : D.La →ₗ[ℤ] Additive Q :=
  (AddMonoidHom.mk' (fun x => Additive.ofMul (f x)) (fun x y => by rw [hf]; rfl)).toIntLinearMap

theorem finite_isLev {act : D.O → Q → Q} {W : ℕ → Q → Q → kˣ} {ζ : ℕ → kˣ} (r : ℕ) :
    {f | IsLev D act W ζ r f}.Finite := by
  rcases Set.eq_empty_or_nonempty {f | IsLev D act W ζ r f} with h | ⟨f0, hf0⟩
  · rw [h]; exact Set.finite_empty
  haveI := D.freeLa
  haveI := D.finLa
  let B := Module.Free.chooseBasis ℤ D.La
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hT : (Set.range f0).Finite :=
    finite_range_of_add hf0.1.1 (pow_ne_zero r hp0) (fun y => (hf0.1.2.2.1 _).2 ⟨y, rfl⟩)
  refine Set.Finite.of_finite_image (f := fun f : D.La → Q => fun i => f (B i)) ?_ ?_
  · refine (Set.Finite.pi (fun _ => hT)).subset ?_
    rintro _ ⟨f, hf, rfl⟩ i _
    exact (hf0.1.2.2.2 _).1 ((hf.1.2.2.2 _).2 ⟨B i, rfl⟩)
  · intro f hf g hg hfg
    have key : toLin f hf.1.1 = toLin g hg.1.1 :=
      B.ext (fun i => congrArg Additive.ofMul (congrFun hfg i))
    funext x
    exact congrArg Additive.toMul (LinearMap.congr_fun key x)

theorem exists_compatible : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (k : Type) [Field k] (Q : Type) [CommGroup Q]
    (act : D.O → Q → Q) (W : ℕ → Q → Q → kˣ) (ζ : ℕ → kˣ), (∀ c a b, act c (a * b) = act c a * act c b) →
    (∀ r, ζ (r + 1) ^ p = ζ r) →
    (∀ r (a b : Q), a ^ (p ^ (r + 1)) = 1 → b ^ (p ^ (r + 1)) = 1 → W r (a ^ p) (b ^ p) = W (r + 1) a b ^ p) →
    (∀ r, ∃ f : D.La → Q, ((∀ x y, f (x + y) = f x * f y) ∧ (∀ (c : D.O) x, f (c • x) = act c (f x)) ∧
      (∀ x, f x = 1 ↔ ∃ y, x = (p ^ r) • y) ∧ (∀ g : Q, g ^ (p ^ r) = 1 ↔ ∃ x, f x = g)) ∧
      ∀ x y, W r (f x) (f y) = ζ r ^ D.EF x y) →
    ∃ ev : ℕ → D.La → Q, (∀ r, ((∀ x y, ev r (x + y) = ev r x * ev r y) ∧
      (∀ (c : D.O) x, ev r (c • x) = act c (ev r x)) ∧ (∀ x, ev r x = 1 ↔ ∃ y, x = (p ^ r) • y) ∧
      (∀ g : Q, g ^ (p ^ r) = 1 ↔ ∃ x, ev r x = g)) ∧ ∀ x y, W r (ev r x) (ev r y) = ζ r ^ D.EF x y) ∧
      ∀ r x, ev (r + 1) x ^ p = ev r x := by
  intro p _ D k _ Q _ act W ζ hact hζ hW hex
  obtain ⟨s, hs⟩ := compat_seq (fun r => {f | IsLev D act W ζ r f}) (fun r => finite_isLev r) hex
    (fun _ f x => f x ^ p) (fun r f hf => IsLev.step hact hζ hW r f hf)
  exact ⟨s, fun r => (hs r).1, fun r x => congrFun (hs r).2 x⟩

end GlobalTheory.TowerLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordsOfGenericPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev

namespace GlobalTheory.TateGlue

theorem bezout {N P : ℕ} (h : N.Coprime P) : (N : ℤ) * N.gcdA P + (P : ℤ) * N.gcdB P = 1 := by
  rw [← Nat.gcd_eq_gcd_ab, h.gcd_eq_one]; rfl

theorem eq_of_pow_eq {G : Type} [CommGroup G] {N P : ℕ} (h : N.Coprime P) {a b : G}
    (h1 : a ^ N = b ^ N) (h2 : a ^ P = b ^ P) : a = b := by
  have key : ∀ g : G, g = (g ^ N) ^ N.gcdA P * (g ^ P) ^ N.gcdB P := fun g => by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, bezout h, zpow_one]
  rw [key a, key b, h1, h2, ← h1, ← h2]

def glue {G : Type} [CommGroup G] (N P : ℕ) (a b : G) : G := a ^ N.gcdA P * b ^ N.gcdB P

theorem zpow_left {G : Type} [CommGroup G] {N P : ℕ} (h : N.Coprime P) {a : G} (ha : a ^ P = 1) :
    a ^ ((N : ℤ) * N.gcdA P) = a := by
  have : a ^ ((N : ℤ) * N.gcdA P + (P : ℤ) * N.gcdB P) = a := by rw [bezout h, zpow_one]
  rwa [zpow_add, zpow_mul a (P : ℤ), zpow_natCast, ha, one_zpow, _root_.mul_one] at this

theorem zpow_right {G : Type} [CommGroup G] {N P : ℕ} (h : N.Coprime P) {b : G} (hb : b ^ N = 1) :
    b ^ ((P : ℤ) * N.gcdB P) = b := by
  have : b ^ ((N : ℤ) * N.gcdA P + (P : ℤ) * N.gcdB P) = b := by rw [bezout h, zpow_one]
  rwa [zpow_add, zpow_mul b (N : ℤ), zpow_natCast, hb, one_zpow, _root_.one_mul] at this

theorem zpow_pow_comm {G : Type} [CommGroup G] (a : G) (z : ℤ) (n : ℕ) : (a ^ z) ^ n = (a ^ n) ^ z := by
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]

theorem glue_pow_left {G : Type} [CommGroup G] {N P : ℕ} (h : N.Coprime P) {a b : G} (ha : a ^ P = 1)
    (hb : b ^ N = 1) : glue N P a b ^ N = a := by
  rw [glue, mul_pow, zpow_pow_comm b, hb, one_zpow, _root_.mul_one, zpow_pow_comm, ← zpow_natCast, ← zpow_mul,
    zpow_left h ha]

theorem glue_pow_right {G : Type} [CommGroup G] {N P : ℕ} (h : N.Coprime P) {a b : G} (ha : a ^ P = 1)
    (hb : b ^ N = 1) : glue N P a b ^ P = b := by
  rw [glue, mul_pow, zpow_pow_comm a, ha, one_zpow, _root_.one_mul, zpow_pow_comm, ← zpow_natCast, ← zpow_mul,
    zpow_right h hb]

theorem glue_mul {G : Type} [CommGroup G] (N P : ℕ) (a b a' b' : G) :
    glue N P (a * a') (b * b') = glue N P a b * glue N P a' b' := by
  simp only [glue, mul_zpow]; exact mul_mul_mul_comm _ _ _ _

theorem map_glue {G : Type} [CommGroup G] (N P : ℕ) (f : G → G) (hf : ∀ a b, f (a * b) = f a * f b) (a b : G) :
    f (glue N P a b) = glue N P (f a) (f b) := by
  let φ : G →* G := MonoidHom.mk' f hf
  change φ (glue N P a b) = glue N P (φ a) (φ b)
  simp only [glue, map_mul, map_zpow]

theorem hom_zsmul {A G : Type} [AddCommGroup A] [CommGroup G] (f : A → G) (hf : ∀ x y, f (x + y) = f x * f y)
    (z : ℤ) (x : A) : f (z • x) = f x ^ z := by
  let φ : Multiplicative A →* G := MonoidHom.mk' (fun x => f x.toAdd) (fun a b => hf _ _)
  change φ (Multiplicative.ofAdd (z • x)) = φ (Multiplicative.ofAdd x) ^ z
  rw [ofAdd_zsmul, map_zpow]

theorem tower_add {G : Type} [CommGroup G] (p : ℕ) (f : ℕ → G) (hf : ∀ r, f (r + 1) ^ p = f r) (r s : ℕ) :
    f (r + s) ^ (p ^ s) = f r := by
  induction s with
  | zero => simp
  | succ s ih => rw [pow_succ', pow_mul, ← add_assoc, hf, ih]

def sys {G : Type} [CommGroup G] (p : ℕ) (f g : ℕ → G) (n : ℕ) : G :=
  glue (n / p ^ n.factorization p) (p ^ n.factorization p) (f (n.factorization p)) (g (n / p ^ n.factorization p))

theorem cop {p n : ℕ} (hp : p.Prime) (hn : 0 < n) :
    (n / p ^ n.factorization p).Coprime (p ^ n.factorization p) :=
  ((Nat.coprime_ordCompl hp hn.ne').pow_left _).symm

theorem sys_left {G : Type} [CommGroup G] {p : ℕ} (hp : p.Prime) {f g : ℕ → G} (hf : ∀ r, f r ^ (p ^ r) = 1)
    (hg : ∀ n, 0 < n → n.Coprime p → g n ^ n = 1) {n : ℕ} (hn : 0 < n) :
    sys p f g n ^ (n / p ^ n.factorization p) = f (n.factorization p) :=
  glue_pow_left (cop hp hn) (hf _) (hg _ (Nat.ordCompl_pos p hn.ne') (Nat.coprime_ordCompl hp hn.ne').symm)

theorem sys_right {G : Type} [CommGroup G] {p : ℕ} (hp : p.Prime) {f g : ℕ → G} (hf : ∀ r, f r ^ (p ^ r) = 1)
    (hg : ∀ n, 0 < n → n.Coprime p → g n ^ n = 1) {n : ℕ} (hn : 0 < n) :
    sys p f g n ^ (p ^ n.factorization p) = g (n / p ^ n.factorization p) :=
  glue_pow_right (cop hp hn) (hf _) (hg _ (Nat.ordCompl_pos p hn.ne') (Nat.coprime_ordCompl hp hn.ne').symm)

theorem sys_pow_self {G : Type} [CommGroup G] {p : ℕ} (hp : p.Prime) {f g : ℕ → G} (hf : ∀ r, f r ^ (p ^ r) = 1)
    (hg : ∀ n, 0 < n → n.Coprime p → g n ^ n = 1) {n : ℕ} (hn : 0 < n) : sys p f g n ^ n = 1 := by
  have h := congrArg (· ^ (p ^ n.factorization p)) (sys_left hp hf hg hn)
  rwa [hf, ← pow_mul, mul_comm, Nat.ordProj_mul_ordCompl_eq_self] at h

theorem sys_tower {G : Type} [CommGroup G] {p : ℕ} (hp : p.Prime) {f g : ℕ → G} (hf : ∀ r, f r ^ (p ^ r) = 1)
    (hg : ∀ n, 0 < n → n.Coprime p → g n ^ n = 1) (hf' : ∀ r, f (r + 1) ^ p = f r)
    (hg' : ∀ n m, 0 < n → 0 < m → (n * m).Coprime p → g (n * m) ^ m = g n) {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    sys p f g (n * m) ^ m = sys p f g n := by
  have hnm : 0 < n * m := Nat.mul_pos hn hm
  have hl := sys_left hp hf hg hnm
  have hr := sys_right hp hf hg hnm
  have hfac : (n * m).factorization p = n.factorization p + m.factorization p := by
    rw [Nat.factorization_mul hn.ne' hm.ne']; rfl
  have hc := Nat.ordCompl_mul n m p
  have hcp := (Nat.coprime_ordCompl hp hnm.ne').symm
  rw [hc] at hl hr hcp
  rw [hfac] at hl hr
  have hm' := Nat.ordProj_mul_ordCompl_eq_self m p
  have hnp := Nat.ordCompl_pos p hn.ne'
  have hmp := Nat.ordCompl_pos p hm.ne'
  refine eq_of_pow_eq (cop hp hn) ?_ ?_
  · rw [sys_left hp hf hg hn, ← tower_add p f hf' _ (m.factorization p), ← hl, ← pow_mul, ← pow_mul]
    congr 1
    generalize n / p ^ n.factorization p = a at *
    generalize m / p ^ m.factorization p = b at *
    generalize p ^ m.factorization p = c at *
    rw [← hm']; ring
  · rw [sys_right hp hf hg hn, ← hg' _ _ hnp hmp hcp, ← hr, ← pow_mul, ← pow_mul, pow_add]
    congr 1
    generalize m / p ^ m.factorization p = b at *
    generalize p ^ m.factorization p = c at *
    rw [← hm']; ring

theorem exists_gTateIso : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (k : Type) [Field k] (Q : Type) [CommGroup Q] (act : D.O → Q → Q) (E : ℕ → Q → Q → kˣ → Prop), (∀ c a b, act c (a * b) = act c a * act c b) → (∀ n, 0 < n → ∀ a b : Q, a ^ n = 1 → b ^ n = 1 → ∃ c, E n a b c) → (∀ n, 0 < n → ∀ (a b : Q) (c c' : kˣ), E n a b c → E n a b c' → c = c') → (∀ n m, 0 < n → 0 < m → ∀ (a b : Q) (c : kˣ), a ^ (n * m) = 1 → b ^ (n * m) = 1 → E (n * m) a b c → E n (a ^ m) (b ^ m) (c ^ m)) → ∀ (I : TateIsoO D k Q act E) (ζ : ℕ → kˣ) (ev : ℕ → D.La → Q), (∀ r, IsPrimitiveRoot (ζ r) (p ^ r)) → (∀ r, ζ (r + 1) ^ p = ζ r) → (∀ r, (∀ x y, ev r (x + y) = ev r x * ev r y) ∧ (∀ (c : D.O) x, ev r (c • x) = act c (ev r x)) ∧ (∀ x, ev r x = 1 ↔ ∃ y, x = (p ^ r) • y) ∧ (∀ g : Q, g ^ (p ^ r) = 1 ↔ ∃ x, ev r x = g)) → (∀ r x, ev (r + 1) x ^ p = ev r x) → (∀ r x y, E (p ^ r) (ev r x) (ev r y) (ζ r ^ (2 * D.EF x y))) → ∃ J : GTateIso D.toG k Q act E, ∀ n, 0 < n → n.Coprime p → ∀ y : D.La, J.ev n y = I.ev n y := by
  intro p hpF D k _ Q _ act E hact hex huniq hlev I ζ ev hζ hζ' hev hev' hE
  have hp : p.Prime := hpF.out
  have ζ1 : ∀ r, ζ r ^ (p ^ r) = 1 := fun r => (hζ r).pow_eq_one
  have ζ2 : ∀ n, 0 < n → n.Coprime p → I.ζ n ^ n = 1 := fun n hn hc => (I.ζ_prim n hn hc).pow_eq_one
  have e1 : ∀ (y : D.La) r, ev r y ^ (p ^ r) = 1 := fun y r => ((hev r).2.2.2 _).2 ⟨y, rfl⟩
  have e2 : ∀ (y : D.La) n, 0 < n → n.Coprime p → I.ev n y ^ n = 1 := fun y n hn hc =>
    (I.onto n hn hc _).2 ⟨y, rfl⟩
  let Z : ℕ → kˣ := sys p ζ I.ζ
  let V : ℕ → D.La → Q := fun n y => sys p (fun r => ev r y) (fun n => I.ev n y) n
  have Zl : ∀ n, 0 < n → Z n ^ (n / p ^ n.factorization p) = ζ (n.factorization p) := fun n hn =>
    sys_left hp ζ1 ζ2 hn
  have Zr : ∀ n, 0 < n → Z n ^ (p ^ n.factorization p) = I.ζ (n / p ^ n.factorization p) := fun n hn =>
    sys_right hp ζ1 ζ2 hn
  have Vl : ∀ n, 0 < n → ∀ y, V n y ^ (n / p ^ n.factorization p) = ev (n.factorization p) y := fun n hn y =>
    sys_left hp (e1 y) (e2 y) hn
  have Vr : ∀ n, 0 < n → ∀ y, V n y ^ (p ^ n.factorization p) = I.ev (n / p ^ n.factorization p) y :=
    fun n hn y => sys_right hp (e1 y) (e2 y) hn
  have V1 : ∀ n, 0 < n → ∀ y, V n y ^ n = 1 := fun n hn y => sys_pow_self hp (e1 y) (e2 y) hn
  have hker : ∀ n, 0 < n → ∀ x : D.La, V n x = 1 ↔ ∃ y, x = n • y := by
    intro n hn x
    have hl := Vl n hn x
    have hr := Vr n hn x
    have hc := cop hp hn
    have hN := Nat.ordCompl_pos p hn.ne'
    have hNp := (Nat.coprime_ordCompl hp hn.ne').symm
    have hn' := Nat.ordProj_mul_ordCompl_eq_self n p
    have k1 := (hev (n.factorization p)).2.2.1 x
    have k2 := I.ker _ hN hNp x
    generalize V n x = q at *
    generalize n / p ^ n.factorization p = N at *
    generalize ev (n.factorization p) x = a at *
    generalize p ^ n.factorization p = P at *
    constructor
    · rintro rfl
      obtain ⟨y1, h1⟩ := k1.1 (by rw [← hl, one_pow])
      obtain ⟨y2, h2⟩ := k2.1 (by rw [← hr, one_pow])
      refine ⟨N.gcdA P • y1 + N.gcdB P • y2, ?_⟩
      have hx : x = ((N : ℤ) * N.gcdA P) • x + ((P : ℤ) * N.gcdB P) • x := by
        rw [← add_smul, bezout hc, one_smul]
      rw [hx, ← hn']
      nth_rewrite 1 [h1]
      rw [h2]
      simp only [← natCast_zsmul, smul_add, smul_smul]
      congr 2 <;> push_cast <;> ring
    · rintro ⟨y, hy⟩
      refine eq_of_pow_eq hc ?_ ?_
      · rw [hl, one_pow]; exact k1.2 ⟨N • y, by rw [hy, ← hn', mul_smul]⟩
      · rw [hr, one_pow]; exact k2.2 ⟨P • y, by rw [hy, ← hn', mul_comm, mul_smul]⟩
  have honto : ∀ n, 0 < n → ∀ q : Q, q ^ n = 1 ↔ ∃ x, V n x = q := by
    intro n hn q
    refine ⟨fun hq => ?_, fun ⟨x, hx⟩ => hx ▸ V1 n hn x⟩
    have hl := Vl n hn
    have hr := Vr n hn
    have hc := cop hp hn
    have hN := Nat.ordCompl_pos p hn.ne'
    have hNp := (Nat.coprime_ordCompl hp hn.ne').symm
    have hn' := Nat.ordProj_mul_ordCompl_eq_self n p
    have a1 := (hev (n.factorization p)).1
    have o1 := (hev (n.factorization p)).2.2.2
    have a2 := I.add (n / p ^ n.factorization p)
    have o2 := I.onto _ hN hNp
    generalize n / p ^ n.factorization p = N at *
    generalize ev (n.factorization p) = f at *
    generalize p ^ n.factorization p = P at *
    obtain ⟨x1, h1⟩ := (o1 (q ^ N)).1 (by rw [← pow_mul, mul_comm, hn', hq])
    obtain ⟨x2, h2⟩ := (o2 (q ^ P)).1 (by rw [← pow_mul, hn', hq])
    refine ⟨((N : ℤ) * N.gcdA P) • x1 + ((P : ℤ) * N.gcdB P) • x2, eq_of_pow_eq hc ?_ ?_⟩
    · rw [hl, a1, hom_zsmul f a1, hom_zsmul f a1, zpow_left hc ((o1 _).2 ⟨x1, rfl⟩), zpow_mul, zpow_natCast,
        (o1 _).2 ⟨x2, rfl⟩, one_zpow, _root_.mul_one, h1]
    · rw [hr, a2, hom_zsmul _ a2, hom_zsmul _ a2, zpow_right hc ((o2 _).2 ⟨x2, rfl⟩), zpow_mul, zpow_natCast,
        (o2 _).2 ⟨x1, rfl⟩, one_zpow, _root_.one_mul, h2]
  have hisom : ∀ n, 0 < n → ∀ x y : D.La, E n (V n x) (V n y) (Z n ^ (2 * D.EF x y)) := by
    intro n hn x y
    obtain ⟨c, hc0⟩ := hex n hn _ _ (V1 n hn x) (V1 n hn y)
    have hc := cop hp hn
    have hN := Nat.ordCompl_pos p hn.ne'
    have hP : 0 < p ^ n.factorization p := pow_pos hp.pos _
    have hNp := (Nat.coprime_ordCompl hp hn.ne').symm
    have hn' := Nat.ordProj_mul_ordCompl_eq_self n p
    have hn'' := (mul_comm _ _).trans hn'
    have l1 := hlev _ _ hP hN (V n x) (V n y) c (by rw [hn']; exact V1 n hn x) (by rw [hn']; exact V1 n hn y)
      (by rw [hn']; exact hc0)
    have l2 := hlev _ _ hN hP (V n x) (V n y) c (by rw [hn'']; exact V1 n hn x) (by rw [hn'']; exact V1 n hn y)
      (by rw [hn'']; exact hc0)
    rw [Vl n hn, Vl n hn] at l1
    rw [Vr n hn, Vr n hn] at l2
    have c1 := huniq _ hP _ _ _ _ l1 (hE _ x y)
    have c2 := huniq _ hN _ _ _ _ l2 (I.isom _ hN hNp x y)
    have : c = Z n ^ (2 * D.EF x y) := by
      refine eq_of_pow_eq hc ?_ ?_
      · rw [c1, zpow_pow_comm, Zl n hn]
      · rw [c2, zpow_pow_comm, Zr n hn]
    exact this ▸ hc0
  refine ⟨{ ζ := Z
            ζ_prim := fun n hn => ⟨sys_pow_self hp ζ1 ζ2 hn, fun l hl => ?_⟩
            ζ_pow := fun n m hn hm => sys_tower hp ζ1 ζ2 hζ' I.ζ_pow hn hm
            ev := V
            add := fun n (x y : D.La) => ?_
            lin := fun n (b : D.O) (x : D.La) => ?_
            ker := hker
            onto := honto
            tower := fun n m hn hm x => sys_tower hp (e1 x) (e2 x) (fun r => hev' r x)
              (fun n m hn hm hc => I.tower n m hn hm hc x) hn hm
            isom := hisom }, fun n hn hc y => ?_⟩
  · have hN := Nat.ordCompl_pos p hn.ne'
    have hNp := (Nat.coprime_ordCompl hp hn.ne').symm
    have d1 := (hζ (n.factorization p)).dvd_of_pow_eq_one l (by
      rw [← Zl n hn, ← pow_mul, mul_comm, pow_mul, hl, one_pow])
    have d2 := (I.ζ_prim _ hN hNp).dvd_of_pow_eq_one l (by
      rw [← Zr n hn, ← pow_mul, mul_comm, pow_mul, hl, one_pow])
    have := (cop hp hn).symm.mul_dvd_of_dvd_of_dvd d1 d2
    rwa [Nat.ordProj_mul_ordCompl_eq_self] at this
  · change glue _ _ (ev _ (x + y)) (I.ev _ (x + y)) = glue _ _ (ev _ x) (I.ev _ x) * glue _ _ (ev _ y) (I.ev _ y)
    rw [(hev _).1, I.add, glue_mul]
  · change glue _ _ (ev _ (b • x)) (I.ev _ (b • x)) = act b (glue _ _ (ev _ x) (I.ev _ x))
    rw [(hev _).2.1, I.lin, map_glue _ _ (act b) (hact b)]
  · have h0 : n.factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd ((Nat.Prime.coprime_iff_not_dvd hp).1 hc.symm)
    have := Vr n hn y
    rw [h0, pow_zero, pow_one, Nat.div_one] at this
    exact this

end GlobalTheory.TateGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatLiftingObstructionClass
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

theorem exists_bock : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)), SmallExt t σ σ₀ → Flat s → ∀ x : HO1 s', ∃ z : HO2 s₀, Bock h.w h₀.w t x z := by
  intro R R' R₀ _ _ _ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ hS hF x
  have hc : IsClosedImmersion (spMap σ) := IsClosedImmersion.spec_of_surjective _ hS.1
  have hc₀ : IsClosedImmersion (spMap σ₀) := IsClosedImmersion.spec_of_surjective _ hS.2.2.1
  haveI : IsClosedImmersion φ := MorphismProperty.of_isPullback h.flip hc
  haveI : IsClosedImmersion φ₀ := MorphismProperty.of_isPullback h₀.flip hc₀
  have sec := fun U ↦ GlobalTheory.T.surjective_deformation_affine_sections R R' R₀ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ hS hF U
  have red := _root_.GlobalTheory.AbCoh.red_iff_pre R R' X X' s s' σ φ h.w
  have red₀ := _root_.GlobalTheory.AbCoh.red_iff_pre R R₀ X X₀ s s₀ σ₀ φ₀ h₀.w
  have bij₀ := (_root_.GlobalTheory.AbCoh.preRes_bijective R₀ X X₀ φ₀ s₀).2.1
  obtain ⟨c, hc⟩ := GlobalTheory.CatCoh.H1.mk_surjective _ ((preRes φ s').pull1 x)
  choose f hf using fun (U V : AffOp X) (a : U ⟶ V) ↦ (sec V).1 (c.1 U V a)
  have hd : ∀ (U V W : AffOp X) (a : U ⟶ V) (b : V ⟶ W), preα φ s s' W (d1 (OAff s) f U V W a b) = 0 := by
    intro U V W a b
    have nat := (preCoef h.w).naturality b (f U V a)
    have cc := c.2 a b
    rw [d1_apply, map_add (f := _), map_sub, hf, hf]
    erw [nat, hf]
    rw [cc]; ring
  choose w hw using fun (U V W : AffOp X) (a : U ⟶ V) (b : V ⟶ W) ↦ ((sec W).2.1 _).1 (hd U V W a b)
  have hdw : d1 (OAff s) f = t • w := by
    funext U V W a b; exact hw U V W a b
  have hw2 : ∀ ⦃U V W Y : AffOp X⦄ (a : U ⟶ V) (b : V ⟶ W) (e : W ⟶ Y),
      t • (mp (OAff s) e (w U V W a b) + w U W Y (a ≫ b) e - (w U V Y a (b ≫ e) + w V W Y b e)) = 0 := by
    intro U V W Y a b e
    have := (differential_one_mem_scaled_lattice (OAff s) f) a b e
    rw [hdw] at this
    simp only [Pi.smul_apply, map_smul] at this
    rw [smul_sub, smul_add, smul_add, this, sub_self]
  have hc0 : (fun U V W (a : U ⟶ V) (b : V ⟶ W) ↦ preα φ₀ s s₀ W (w U V W a b) : C2 (OPre φ₀ s₀)) ∈
      Z2 (OPre φ₀ s₀) := by
    intro U V W Y a b e
    have h1 := ((sec Y).2.2.2 _).2 (hw2 a b e)
    have nat := (preCoef h₀.w).naturality e (w U V W a b)
    simp only [map_add (f := _), map_sub] at h1
    erw [nat] at h1
    dsimp only
    exact sub_eq_zero.1 h1
  obtain ⟨z, hz⟩ := bij₀.2 (GlobalTheory.CatCoh.H2.mk _ ⟨_, hc0⟩)
  exact ⟨z, f, w, hdw, (red.1 f x).2 ⟨c, fun U V a ↦ (hf U V a).symm, hc⟩,
    (red₀.2.1 w z).2 ⟨⟨_, hc0⟩, fun U V W a b ↦ rfl, hz.symm⟩⟩

end GlobalTheory.AbCoh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpoFrobIndep
section
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds

namespace GlobalTheory

theorem expo_frob_indep : ∀ P : Par, P.Hyp → P.Large → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι), W.Ok P →
    ∀ (fr : ℕ → ι → ι) (cj : ℕ → ι → Bool), ({ W with fr := fr, cj := cj } : Wts ι).Ok P ∧
      ∀ l : ℕ, l.Prime → W.WRange P l → ({ W with fr := fr, cj := cj } : Wts ι).coarseWeightBound P l = W.coarseWeightBound P l := by
  intro P hH hL ι _ _ W hW fr cj
  have hW' : ({ W with fr := fr, cj := cj } : Wts ι).Ok P :=
    { anti := hW.anti, what₂ := hW.what₂, block := hW.block, centre := hW.centre, window := hW.window,
      cloud := hW.cloud, low := hW.low, thick := hW.thick, other := hW.other }
  refine ⟨hW', ?_⟩
  intro l hl hR
  have hN := (places_real_holds P hH hL ι W hW (fun _ => 0)).2
  have hN' := (places_real_holds P hH hL ι ({ W with fr := fr, cj := cj } : Wts ι) hW' (fun _ => 0)).2
  have hi : ({ W with fr := fr, cj := cj } : Wts ι).iW P l = W.iW P l := by
    funext τ
    unfold Wts.iW SizeData₂.depth
    obtain ⟨a1, a2⟩ := hN l hl hR.1 hR.2.2.1 τ
    obtain ⟨b1, b2⟩ := hN' l hl hR.1 hR.2.2.1 τ
    rw [a1, a2, b1, b2]
    rfl
  unfold Wts.coarseWeightBound
  rw [hi]
  rfl

end GlobalTheory
end

