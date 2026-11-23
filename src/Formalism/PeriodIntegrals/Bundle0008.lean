module

public import Mathlib

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.TwNormLat
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace PI.TwNormLat

section LocS

variable {R : Type*} [CommRing R]

def locS {W : Type*} [AddCommGroup W] [Module R W] (S : Submonoid R) (L : Submodule R W) :
    Submodule R W where
  carrier := {x | ∃ s ∈ S, s • x ∈ L}
  zero_mem' := ⟨1, S.one_mem, by simp⟩
  add_mem' := by
    rintro x y ⟨s, hs, hx⟩ ⟨t, ht, hy⟩
    refine ⟨s * t, S.mul_mem hs ht, ?_⟩
    have e : (s * t) • (x + y) = t • (s • x) + s • (t • y) := by
      rw [smul_add, mul_smul, smul_comm s t x, mul_smul]
    rw [e]
    exact L.add_mem (L.smul_mem t hx) (L.smul_mem s hy)
  smul_mem' := by
    rintro r x ⟨s, hs, hx⟩
    refine ⟨s, hs, ?_⟩
    rw [smul_comm]
    exact L.smul_mem r hx

def localization₂ {W : Type*} [AddCommGroup W] [Module R W] (p : Ideal R) [p.IsPrime] (L : Submodule R W) :
    Submodule R W :=
  locS p.primeCompl L

end LocS

abbrev Sp (E : Type) (n : ℕ) : Type := Fin n → E

section Red

variable {E : Type} [Field E] [NumberField E]

def IntAt (P : HeightOneSpectrum (𝓞 E)) (a : E) : Prop :=
  ∃ r s : 𝓞 E, s ∉ P.asIdeal ∧ algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r

end Red

section Deco

variable (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ)

def stdLat : Submodule (𝓞 E) (Sp E n) := Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)

end Deco

section Frames

variable (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ)

def stabL (M : Submodule (𝓞 E) (Sp E n)) : Subgroup (Sp E n ≃ₗ[E] Sp E n) where
  carrier := {c | ∀ x, c x ∈ M ↔ x ∈ M}
  one_mem' := fun _ => Iff.rfl
  mul_mem' := fun {a b} ha hb x => (ha (b x)).trans (hb x)
  inv_mem' := fun {a} ha x => by
    have h := ha (a⁻¹ x)
    rw [show a (a⁻¹ x) = x from LinearEquiv.apply_symm_apply a x] at h
    exact h.symm

def stdAt (P : HeightOneSpectrum (𝓞 E)) : Submodule (𝓞 E) (Sp E n) := localization₂ P.asIdeal (stdLat E n)

def GLint (P : HeightOneSpectrum (𝓞 E)) : Subgroup (Sp E n ≃ₗ[E] Sp E n) := stabL E n (stdAt E n P)

end Frames

namespace Loc

section Groups

variable (k : Type) [CommRing k] (n c : ℕ)

def atN {k : Type} [CommRing k] {N : ℕ} (v : Fin N → k) (i : ℕ) : k := if h : i < N then v ⟨i, h⟩ else 0

def eN (N i : ℕ) : Fin N → k := fun l => if l.1 = i then 1 else 0

def supp (N : ℕ) (s : Set ℕ) : Submodule k (Fin N → k) where
  carrier := {v | ∀ l : Fin N, l.1 ∉ s → v l = 0}
  add_mem' := fun {a b} ha hb l hl => by simp [ha l hl, hb l hl]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun r a ha l hl => by simp [ha l hl]

def Ufl (i : ℕ) : Submodule k (Fin (n + c) → k) := supp k (n + c) {l | l < n + i}

def inX : (Fin n → k) →ₗ[k] (Fin (n + c) → k) :=
  LinearMap.pi fun l => if h : l.1 < n then LinearMap.proj ⟨l.1, h⟩ else 0

def R1cond (r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) : Prop :=
  (∀ i, ∀ v ∈ Ufl k n c i, r v ∈ Ufl k n c i) ∧ r (eN k (n + c) n) = eN k (n + c) n ∧
    ∀ i, r (eN k (n + c) (n + i)) - eN k (n + c) (n + i) ∈ Ufl k n c i

variable {k n c} in
theorem R1cond.mul {r s : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} (hr : R1cond k n c r) (hs : R1cond k n c s) :
    R1cond k n c (r * s) := by
  refine ⟨fun i v hv => hr.1 i _ (hs.1 i v hv), ?_, fun i => ?_⟩
  · show r (s _) = _
    rw [hs.2.1, hr.2.1]
  · have h1 : (r * s) (eN k (n + c) (n + i)) - eN k (n + c) (n + i) =
        r (s (eN k (n + c) (n + i)) - eN k (n + c) (n + i)) + (r (eN k (n + c) (n + i)) - eN k (n + c) (n + i)) := by
      rw [map_sub]
      show r (s _) - _ = _
      abel
    rw [h1]
    exact add_mem (hr.1 i _ (hs.2.2 i)) (hr.2.2 i)

theorem R1cond_one : R1cond k n c 1 :=
  ⟨fun _ _ hv => hv, rfl, fun i => by
    show eN k (n + c) (n + i) - eN k (n + c) (n + i) ∈ _
    rw [sub_self]
    exact zero_mem _⟩

def R1 : Subgroup ((Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) where
  carrier := {r | R1cond k n c r ∧ R1cond k n c r⁻¹}
  one_mem' := ⟨R1cond_one k n c, by rw [inv_one]; exact R1cond_one k n c⟩
  mul_mem' := fun {a b} ha hb => ⟨ha.1.mul hb.1, by rw [mul_inv_rev]; exact hb.2.mul ha.2⟩
  inv_mem' := fun {a} ha => ⟨ha.2, by rw [inv_inv]; exact ha.1⟩

variable {k n c}

def Cbe (J : Subgroup ((Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k))) (h : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) :
    Subgroup ((Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)) :=
  R1 k n c ⊓ J.comap (MulAut.conj h⁻¹).toMonoidHom

def prX (C : Subgroup ((Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k))) : Subgroup ((Fin n → k) ≃ₗ[k] (Fin n → k)) where
  carrier := {g | ∃ r ∈ C, ∀ x, r (inX k n c x) = inX k n c (g x)}
  one_mem' := ⟨1, C.one_mem, fun _ => rfl⟩
  mul_mem' := by
    rintro a b ⟨r, hr, h1⟩ ⟨s, hs, h2⟩
    refine ⟨r * s, C.mul_mem hr hs, fun x => ?_⟩
    show r (s _) = _
    rw [h2, h1]
    rfl
  inv_mem' := by
    rintro a ⟨r, hr, h1⟩
    refine ⟨r⁻¹, C.inv_mem hr, fun x => ?_⟩
    show r.symm _ = _
    rw [LinearEquiv.symm_apply_eq, h1]
    show _ = inX k n c (a (a.symm x))
    rw [LinearEquiv.apply_symm_apply]

end Groups

end Loc

namespace LocE

open Loc

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ)



def sclLat (N : ℕ) (e : ℕ → ℤ) : Submodule (𝓞 E) (Sp E N) :=
  (stdAt E N P).comap
    ((LinearMap.pi fun l : Fin N => ((q : E) ^ e l.1)⁻¹ • (LinearMap.proj l : Sp E N →ₗ[E] E)).restrictScalars (𝓞 E))

def scE (n : ℕ) (ex : ℕ → ℕ) (l : ℕ) : ℤ := if l < n then 0 else (ex (l - n) : ℤ)

def lamY (n c : ℕ) (ex : ℕ → ℕ) : Submodule (𝓞 E) (Sp E (n + c)) := sclLat P q (n + c) (scE n ex)

section AtQ

variable (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)

def parL (kj n c : ℕ) : Submodule (𝓞 E) (Sp E (n + c)) := sclLat P q (n + c) fun l => if kj ≤ l ∧ l < n then 1 else 0

def JQ (kj n c : ℕ) : Subgroup (Sp E (n + c) ≃ₗ[E] Sp E (n + c)) :=
  stabL E (n + c) (stdAt E (n + c) P) ⊓ stabL E (n + c) (parL P q kj n c)

variable {P}

end AtQ

end LocE

section Target

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def Bdd (P : HeightOneSpectrum (𝓞 E)) (N c j : ℕ) (h : Sp E (N + c) ≃ₗ[E] Sp E (N + c)) : Prop :=
  ∀ x ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0, h⁻¹ x ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0 ∧
    (((Ideal.absNorm P.asIdeal : ℕ) : E) ^ j) • h x ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0

def NF (P : HeightOneSpectrum (𝓞 E)) (N c j : ℕ) (h : Sp E (N + c) ≃ₗ[E] Sp E (N + c)) : Prop :=
  ∃ (n : ℕ → ℤ) (z : Sp E N), (∀ i, -(j : ℤ) ≤ n i ∧ n i ≤ 0) ∧ z ∈ stdAt E N P ∧
    ∀ v : Sp E (N + c), h⁻¹ v ∈ LocE.lamY P (Ideal.absNorm P.asIdeal) N c 0 ↔
      (∀ l : Fin N, IntAt P (v (Fin.castAdd _ l) - Loc.atN v N * z l)) ∧
        ∀ i : Fin c, IntAt P ((((Ideal.absNorm P.asIdeal : ℕ) : E) ^ n i.1)⁻¹ * v (Fin.natAdd _ i))

end Target

def TwNormLat : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (N c kj j : ℕ),
    (Ideal.absNorm P.asIdeal).Prime → ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 →
    ∀ h : Sp E (N + c) ≃ₗ[E] Sp E (N + c), Bdd P N c j h →
      ∃ r ∈ Loc.R1 E N c, ∃ κ ∈ LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c,
        Bdd P N c j (r * h * κ) ∧ NF P N c j (r * h * κ) ∧
          Loc.prX (Loc.Cbe (LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c) (r * h * κ)) ≤ GLint E N P

end PI.TwNormLat
end
end

-- bundled from Formalism.PeriodIntegrals.UnimodGenus
section
open NumberField

noncomputable section

namespace PI.UG

section Defs

variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

def isom (h : V →ₗ⋆[K] V →ₗ[K] K) : Subgroup (V ≃ₗ[K] V) where
  carrier := {g | ∀ x y, h (g x) (g y) = h x y}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro a b ha hb x y
    change h (a (b x)) (a (b y)) = h x y
    rw [ha, hb]
  inv_mem' := by
    intro a ha x y
    have := ha (a.symm x) (a.symm y)
    change h (a.symm x) (a.symm y) = h x y
    simpa using this.symm

def gmap (g : V ≃ₗ[K] V) (L : Submodule R V) : Submodule R V :=
  L.map ((g : V →ₗ[K] V).restrictScalars R)

def dual (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule R V) : Submodule R V :=
  ⨅ y ∈ L, (1 : Submodule R K).comap ((h y).restrictScalars R)

def IsUnimodular (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule R V) : Prop :=
  dual h L = L

def locS {W : Type*} [AddCommGroup W] [Module R W] (S : Submonoid R) (L : Submodule R W) :
    Submodule R W where
  carrier := {x | ∃ s ∈ S, s • x ∈ L}
  zero_mem' := ⟨1, S.one_mem, by simp⟩
  add_mem' := by
    rintro x y ⟨s, hs, hx⟩ ⟨t, ht, hy⟩
    refine ⟨s * t, S.mul_mem hs ht, ?_⟩
    have e : (s * t) • (x + y) = t • (s • x) + s • (t • y) := by
      rw [smul_add, mul_smul, smul_comm s t x, mul_smul]
    rw [e]
    exact L.add_mem (L.smul_mem t hx) (L.smul_mem s hy)
  smul_mem' := by
    rintro r x ⟨s, hs, hx⟩
    refine ⟨s, hs, ?_⟩
    rw [smul_comm]
    exact L.smul_mem r hx

def hcompl (p : Ideal R) : Submonoid R :=
  Submonoid.closure {s | s ∉ p ∧ ∀ t : R, algebraMap R K t = star (algebraMap R K s) → t ∉ p}

def loc {W : Type*} [AddCommGroup W] [Module R W] (p : Ideal R) (L : Submodule R W) :
    Submodule R W :=
  locS (hcompl (K := K) p) L

def SameGenus (h : V →ₗ⋆[K] V →ₗ[K] K) (L M : Submodule R V) : Prop :=
  ∀ p : Ideal R, p.IsMaximal → ∃ g ∈ isom h, gmap g (loc (K := K) p L) = loc (K := K) p M

end Defs

abbrev Sp (E : Type) (n : ℕ) : Type := Fin n → E

def hStd (E : Type) [Field E] [StarRing E] (n : ℕ) : Sp E n →ₗ⋆[E] Sp E n →ₗ[E] E :=
  LinearMap.mk₂'ₛₗ (starRingEnd E) (RingHom.id E) (fun x y => ∑ i, star (x i) * y i)
    (by intro x y z; simp [add_mul, Finset.sum_add_distrib])
    (by intro c x y; simp [Finset.mul_sum, mul_assoc, starRingEnd_apply])
    (by intro x y z; simp [mul_add, Finset.sum_add_distrib])
    (by intro c x y; simp [Finset.mul_sum, mul_left_comm])

def stdLat (E : Type) [Field E] [NumberField E] (n : ℕ) : Submodule (𝓞 E) (Sp E n) :=
  Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)

def IsCMUnram (K : Type*) [Field K] [NumberField K] [StarRing K] : Prop :=
  IsTotallyComplex K ∧ (∀ (φ : K →+* ℂ) (a : K), φ (star a) = starRingEnd ℂ (φ a)) ∧
    ∀ P : Ideal (RingOfIntegers K), P.IsMaximal →
      ∃ θ t : RingOfIntegers K, algebraMap (RingOfIntegers K) K t =
        star (algebraMap (RingOfIntegers K) K θ) ∧ θ - t ∉ P

end PI.UG

namespace PI

open PI.UG

def UnimodGenus : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ), IsCMUnram E →
    ∀ N : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E N → IsUnimodular (hStd E n) N →
      SameGenus (hStd E n) (stdLat E n) N

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.UnimodLocStd
section
noncomputable section
open scoped BigOperators ComplexConjugate

namespace PI.ULS

abbrev Sesq (V : Type*) [AddCommGroup V] [Module ℂ V] := V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ

section General

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def altE (H : Sesq V) (x y : V) : ℝ := (H x y).im

def dualLat (H : Sesq V) (Λ : AddSubgroup V) : AddSubgroup V where
  carrier := {x | ∀ y ∈ Λ, ∃ m : ℤ, altE H x y = (m : ℝ)}
  zero_mem' := fun y _ => ⟨0, by simp [altE]⟩
  add_mem' := by
    intro a b ha hb y hy
    obtain ⟨m, hm⟩ := ha y hy
    obtain ⟨k, hk⟩ := hb y hy
    exact ⟨m + k, by simp only [altE] at hm hk ⊢; simp [hm, hk]⟩
  neg_mem' := by
    intro a ha y hy
    obtain ⟨m, hm⟩ := ha y hy
    exact ⟨-m, by simp only [altE] at hm ⊢; simp [hm]⟩

def IsSelfDual (H : Sesq V) (Λ : AddSubgroup V) : Prop := dualLat H Λ = Λ

def relIdx (Λ₁ Λ₂ : AddSubgroup V) : ℕ := Λ₁.relIndex Λ₂

def IsIsom {W : Type*} [AddCommGroup W] [Module ℂ W] (H : Sesq V) (H' : Sesq W) (g : V →ₗ[ℂ] W) : Prop :=
  ∀ x y, H' (g x) (g y) = H x y

def imgLat {W : Type*} [AddCommGroup W] [Module ℂ W] (g : V →ₗ[ℂ] W) (Λ : AddSubgroup V) : AddSubgroup W :=
  Λ.map g.toAddMonoidHom

end General

def area (L : PeriodPair) : ℝ := |(conj L.ω₁ * L.ω₂).im|

section Coordinates

variable {n : Type*} [Fintype n]

def matH (h : Matrix n n ℂ) : Sesq (n → ℂ) :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun z w => ∑ i, ∑ j, z i * h i j * conj (w j))
    (by intro a b c; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib])
    (by intro c a b; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc])
    (by intro a b c; simp only [Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib])
    (by
      intro c a b
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring)

def stdH (L : PeriodPair) (n : Type*) [Fintype n] [DecidableEq n] : Sesq (n → ℂ) :=
  matH (((area L : ℝ) : ℂ)⁻¹ • (1 : Matrix n n ℂ))

def stdLat (L : PeriodPair) (n : Type*) : AddSubgroup (n → ℂ) :=
  AddSubgroup.pi Set.univ fun _ => L.lattice.toAddSubgroup

end Coordinates

def scalePair (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) : PeriodPair where
  ω₁ := c * L.ω₁
  ω₂ := c * L.ω₂
  indep := by
    have h := L.indep
    rw [LinearIndependent.pair_iff] at h ⊢
    intro s t hst
    apply h s t
    have : c * (s • L.ω₁ + t • L.ω₂) = 0 := by
      rw [← hst]; simp only [Complex.real_smul]; ring
    exact (mul_eq_zero.mp this).resolve_left hc

def cmTheta (b : ℤ) (d : ℕ) : ℂ := ((b : ℂ) + Complex.I * ((Real.sqrt d : ℝ) : ℂ)) / 2

def cmPair (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) : PeriodPair where
  ω₁ := (a : ℂ)
  ω₂ := cmTheta b d
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
    have him := congrArg Complex.im h
    have hre := congrArg Complex.re h
    simp [cmTheta] at him hre
    have ht : t = 0 := by
      rcases him with h1 | h1
      · exact h1
      · exact absurd h1 (by positivity)
    subst ht
    simp at hre
    refine ⟨?_, rfl⟩
    rcases hre with h1 | h1
    · exact h1
    · exact absurd h1 (by positivity)

def cmL (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0) : PeriodPair :=
  scalePair (cmPair a b d ha hd) lam hlam

def CmOK (a : ℕ) (b c : ℤ) (d : ℕ) : Prop := 4 * (a : ℤ) * c = b ^ 2 + d ∧ Odd a ∧ d % 8 = 7 ∧ d.Prime

end PI.ULS

namespace PI


open PI.ULS in
def UnimodLocStd : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a b c d →
    ∀ (m : Type) [Fintype m] [DecidableEq m] (Λa : AddSubgroup (m → ℂ)),
      IsSelfDual (stdH (cmL a b d ha hd lam hlam) m) Λa →
      (∀ x ∈ Λa, cmTheta b d • x ∈ Λa) →
      relIdx (stdLat (cmL a b d ha hd lam hlam) m) Λa ≠ 0 →
      relIdx Λa (stdLat (cmL a b d ha hd lam hlam) m) ≠ 0 →
      ∀ l : ℕ, l.Prime → ∃ δ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ),
        IsIsom (stdH (cmL a b d ha hd lam hlam) m) (stdH (cmL a b d ha hd lam hlam) m)
          (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) ∧ (∀ x, δ x = x → x = 0) ∧
        relIdx (stdLat (cmL a b d ha hd lam hlam) m) (imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) ≠ 0 ∧
        ¬ l ∣ relIdx (stdLat (cmL a b d ha hd lam hlam) m) (imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) ∧
        relIdx (imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) (stdLat (cmL a b d ha hd lam hlam) m) ≠ 0

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryDense
section
open Matrix
open scoped ComplexOrder

namespace PI

def UnitaryDense : Prop :=
  ∀ (n : ℕ) (P : MvPolynomial (Fin n × Fin n) ℂ),
    (∀ u : Matrix (Fin n) (Fin n) ℂ, uᴴ * u = 1 →
      MvPolynomial.eval (fun x : Fin n × Fin n => u x.1 x.2) P = 0) → P = 0

def FramesDense : Prop :=
  ∀ (ι : Type) [Fintype ι] (n : ℕ) (G : ι → Matrix (Fin n) (Fin n) ℂ), (∀ τ, (G τ).PosDef) →
    ∀ P : MvPolynomial (ι × Fin n × Fin n) ℂ,
      (∀ y : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ, (y τ)ᴴ * G τ * y τ = 1) →
        MvPolynomial.eval (fun x : ι × Fin n × Fin n => y x.1 x.2.1 x.2.2) P = 0) → P = 0

end PI
end

-- bundled from Formalism.PeriodIntegrals.WeakApproxDVR
section
noncomputable section

namespace PI

def WeakApproxDVR : Prop :=
  ∀ (E : Type) [Field E] (ι : Type) [Fintype ι] (W Q : ι → Type) [∀ i, CommRing (W i)]
    [∀ i, IsDomain (W i)] [∀ i, IsDiscreteValuationRing (W i)] [∀ i, Field (Q i)]
    [∀ i, Algebra (W i) (Q i)] [∀ i, IsFractionRing (W i) (Q i)] (iw : ∀ i, E →+* Q i) (p : ℕ),
    (∀ i, (p : Q i) ≠ 0) → (∀ i, ¬ IsUnit (p : W i)) →
    (∀ i (x : Q i) (N : ℕ), ∃ a : E, ∃ c : W i, iw i a = x + (p : Q i) ^ N * algebraMap (W i) (Q i) c) →
    (∀ i j, i ≠ j → ∃ a : E, iw i a ∈ Set.range (algebraMap (W i) (Q i)) ∧
      iw j a ∉ Set.range (algebraMap (W j) (Q j))) →
    ∀ (x : ∀ i, Q i) (N : ℕ), ∃ a : E, ∀ i, ∃ c : W i,
      iw i a = x i + (p : Q i) ^ N * algebraMap (W i) (Q i) c

end PI
end
end

