module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle0012

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.HermitianBasisBelowSecond
section
noncomputable section

namespace PI.OmLocU.SdB

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.VolStabSW
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

def hd {a : ℕ} (i : Fin a) : HermR (Fv F v) σ a :=
  ⟨Matrix.single i i 1, fun p q => by
    rw [Matrix.single_apply, Matrix.single_apply, apply_ite (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ), map_one, map_zero]
    exact if_congr and_comm rfl rfl⟩

theorem hm_apply_ne {a : ℕ} (hinv : ∀ y, σ (σ y) = y) {k l i j : Fin a} (c : Fv F v ⊗[F] E)
    (h1 : ¬(k = i ∧ l = j)) (h2 : ¬(l = i ∧ k = j)) :
    (hm σ v hinv k l c : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j = 0 := by
  show (Matrix.single k l c + Matrix.single l k (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ c)) i j = 0
  rw [Matrix.add_apply, Matrix.single_apply, Matrix.single_apply, if_neg h1, if_neg h2, add_zero]

theorem hd_apply_ne {a : ℕ} {k i j : Fin a} (h : ¬(k = i ∧ k = j)) :
    (hd σ v k : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j = 0 := by
  show Matrix.single k k (1 : Fv F v ⊗[F] E) i j = 0
  rw [Matrix.single_apply, if_neg h]

def hb {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) (p : Fin a × Fin a) : HermR (Fv F v) σ a :=
  if p.1 < p.2 then hm σ v hinv p.1 p.2 (β 0) else if p.2 < p.1 then hm σ v hinv p.2 p.1 (β 1) else hd σ v p.1

theorem hb_zero {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) {p : Fin a × Fin a} {i j : Fin a}
    (hp1 : p ≠ (i, j)) (hp2 : p ≠ (j, i)) : (hb σ v hinv β p : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j = 0 := by
  obtain ⟨k, l⟩ := p
  unfold hb
  dsimp only
  split_ifs with hkl hlk
  · exact hm_apply_ne σ v hinv _ (fun e => hp1 (Prod.ext e.1 e.2)) (fun e => hp2 (Prod.ext e.2 e.1))
  · exact hm_apply_ne σ v hinv _ (fun e => hp2 (Prod.ext e.2 e.1)) (fun e => hp1 (Prod.ext e.1 e.2))
  · have hkl' : k = l := le_antisymm (not_lt.1 hlk) (not_lt.1 hkl)
    subst hkl'
    exact hd_apply_ne σ v (fun e => hp1 (Prod.ext e.1 e.2))

theorem hermitian_basis_above_first {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) {i j : Fin a} (h : i < j) :
    (hb σ v hinv β (i, j) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j = β 0 := by
  unfold hb
  rw [if_pos h]
  show (Matrix.single i j (β 0) + Matrix.single j i (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (β 0))) i j = β 0
  rw [Matrix.add_apply, Matrix.single_apply, Matrix.single_apply, if_pos ⟨rfl, rfl⟩,
    if_neg (fun e => h.ne e.2), add_zero]

theorem hermitian_basis_above_second {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) {i j : Fin a} (h : i < j) :
    (hb σ v hinv β (j, i) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j = β 1 := by
  unfold hb
  rw [if_neg (not_lt.2 h.le), if_pos h]
  show (Matrix.single i j (β 1) + Matrix.single j i (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (β 1))) i j = β 1
  rw [Matrix.add_apply, Matrix.single_apply, Matrix.single_apply, if_pos ⟨rfl, rfl⟩,
    if_neg (fun e => h.ne e.2), add_zero]

theorem hermitian_basis_below_first {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) {i j : Fin a} (h : j < i) :
    (hb σ v hinv β (i, j) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (β 1) := by
  unfold hb
  rw [if_neg (not_lt.2 h.le), if_pos h]
  show (Matrix.single j i (β 1) + Matrix.single i j (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (β 1))) i j = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (β 1)
  rw [Matrix.add_apply, Matrix.single_apply, Matrix.single_apply, if_neg (fun e => h.ne e.1),
    if_pos ⟨rfl, rfl⟩, zero_add]

theorem hermitian_basis_below_second {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) {i j : Fin a} (h : j < i) :
    (hb σ v hinv β (j, i) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (β 0) := by
  unfold hb
  rw [if_pos h]
  show (Matrix.single j i (β 0) + Matrix.single i j (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (β 0))) i j = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (β 0)
  rw [Matrix.add_apply, Matrix.single_apply, Matrix.single_apply, if_neg (fun e => h.ne e.1),
    if_pos ⟨rfl, rfl⟩, zero_add]

theorem hb_eq {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) (i : Fin a) :
    (hb σ v hinv β (i, i) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i i = 1 := by
  unfold hb
  rw [if_neg (lt_irrefl i), if_neg (lt_irrefl i)]
  show Matrix.single i i (1 : Fv F v ⊗[F] E) i i = 1
  rw [Matrix.single_apply, if_pos ⟨rfl, rfl⟩]

theorem coe_sum_hb {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) (c : Fin a × Fin a → Fv F v)
    (i j : Fin a) :
    ((∑ p, c p • hb σ v hinv β p : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j =
      ∑ p, c p • (hb σ v hinv β p : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j := by
  rw [AddSubmonoidClass.coe_finsetSum, Matrix.sum_apply]
  rfl

theorem sum_lt {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) (c : Fin a × Fin a → Fv F v)
    {i j : Fin a} (h : i < j) :
    ((∑ p, c p • hb σ v hinv β p : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j =
      c (i, j) • β 0 + c (j, i) • β 1 := by
  have hne : ((i, j) : Fin a × Fin a) ≠ (j, i) := fun e => h.ne (Prod.ext_iff.1 e).1
  rw [coe_sum_hb, Fintype.sum_eq_add (i, j) (j, i) hne
    (fun p hp => by rw [hb_zero σ v hinv β hp.1 hp.2, smul_zero]), hermitian_basis_above_first σ v hinv β h, hermitian_basis_above_second σ v hinv β h]

theorem sum_gt {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) (c : Fin a × Fin a → Fv F v)
    {i j : Fin a} (h : j < i) :
    ((∑ p, c p • hb σ v hinv β p : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j =
      c (i, j) • Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (β 1) + c (j, i) • Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (β 0) := by
  have hne : ((i, j) : Fin a × Fin a) ≠ (j, i) := fun e => h.ne' (Prod.ext_iff.1 e).1
  rw [coe_sum_hb, Fintype.sum_eq_add (i, j) (j, i) hne
    (fun p hp => by rw [hb_zero σ v hinv β hp.1 hp.2, smul_zero]), hermitian_basis_below_first σ v hinv β h, hermitian_basis_below_second σ v hinv β h]

theorem sum_diag {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) (c : Fin a × Fin a → Fv F v)
    (i : Fin a) :
    ((∑ p, c p • hb σ v hinv β p : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i i =
      sc (E := E) v (c (i, i)) := by
  rw [coe_sum_hb, Fintype.sum_eq_single (i, i) (fun p hp => by rw [hb_zero σ v hinv β hp hp, smul_zero]),
    hb_eq, sc, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end PI.OmLocU.SdB
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.IdemCases
section
noncomputable section

namespace PI.OmLocU.Red

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Formalism.UG
open PI.VolStabSW PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

def QProd : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v → ¬ (IE (E := E) v).IsPrime →
    ∃ e : QE (E := E) v ≃+* (𝓞 F ⧸ v.asIdeal) × (𝓞 F ⧸ v.asIdeal),
      ∀ c, e (algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) c) = (c, c)

theorem sq_mem (h : IsCMExt F E σ) (x : QE (E := E) v) (hx : sigQ σ v x = x) :
    ∃ c, algebraMap (𝓞 F ⧸ v.asIdeal) (QE (E := E) v) c = x * x := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hs : Ideal.Quotient.mk (IE (E := E) v) (sigO σ y) = Ideal.Quotient.mk _ y := by
    rw [← sigQ_mk]; exact hx
  have hss : sigO σ (sigO σ y) = y := RingOfIntegers.ext (by simp only [sigO_coe]; exact sig_sig σ h _)
  obtain ⟨b, hb⟩ := fix_int σ h (y * sigO σ y) (by rw [map_mul, hss, mul_comm])
  refine ⟨Ideal.Quotient.mk _ b, ?_⟩
  rw [Ideal.Quotient.algebraMap_quotient_map_quotient, hb, map_mul, hs]

theorem idem_cases {k : Type} [Field k] {a : k} (ha : a * a = a) : a = 0 ∨ a = 1 := by
  have : a * (a - 1) = 0 := by rw [mul_sub, ha, mul_one, sub_self]
  rcases mul_eq_zero.1 this with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.1 h)

theorem qSplit_of (hP : QProd σ J ψ v) : QSplit σ J ψ v := by
  intro hstd hun hp
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  obtain ⟨e, he⟩ := hP hstd hun hp
  refine ⟨e, ?_⟩
  set z : QE (E := E) v := e.symm (1, 0) with hz
  have hez : e z = (1, 0) := by rw [hz, RingEquiv.apply_symm_apply]
  have hinv : ∀ x, sigQ σ v (sigQ σ v x) = x := sigQ_sigQ σ v hstd.1
  have hw : e (sigQ σ v z) = (0, 1) := by
    have hzz : z * z = z := e.injective (by rw [map_mul, hez]; simp)
    have hid : e (sigQ σ v z) * e (sigQ σ v z) = e (sigQ σ v z) := by rw [← map_mul, ← map_mul, hzz]
    have h1 := idem_cases ((Prod.fst_mul _ _).symm.trans (congrArg Prod.fst hid))
    have h2 := idem_cases ((Prod.snd_mul _ _).symm.trans (congrArg Prod.snd hid))
    have h10 : ((1, 0) : (𝓞 F ⧸ v.asIdeal) × (𝓞 F ⧸ v.asIdeal)).1 ≠ ((1, 0) : (𝓞 F ⧸ v.asIdeal) × (𝓞 F ⧸ v.asIdeal)).2 :=
      one_ne_zero
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exfalso
      have h0 : sigQ σ v z = 0 := (map_eq_zero_iff e e.injective).1 (Prod.ext h1 h2)
      have : e z = 0 := by rw [← hinv z, h0, map_zero, map_zero]
      rw [hez] at this
      exact one_ne_zero (congrArg Prod.fst this)
    · exact Prod.ext h1 h2
    · exfalso
      have hf : sigQ σ v z = z := e.injective (by rw [hez]; exact Prod.ext h1 h2)
      obtain ⟨c, hc⟩ := sq_mem σ v hstd.1 z hf
      rw [hzz] at hc
      have := he c
      rw [hc, hez] at this
      apply h10
      rw [this]
    · exfalso
      have h0 : sigQ σ v z = 1 := e.injective (by rw [map_one]; exact Prod.ext h1 h2)
      have : e z = 1 := by rw [← hinv z, h0, map_one, map_one]
      rw [hez] at this
      exact zero_ne_one (congrArg Prod.snd this)
  intro x
  have hx : x = algebraMap _ (QE (E := E) v) (e x).1 * z + algebraMap _ (QE (E := E) v) (e x).2 * (1 - z) := by
    apply e.injective
    rw [map_add (f := _), map_mul, map_mul, he, he, map_sub, map_one, hez]
    ext <;> simp
  have key : e (sigQ σ v x) = ((e x).2, (e x).1) := by
    conv_lhs => rw [hx]
    rw [map_add (f := _), map_mul, map_mul, sigQ_alg, sigQ_alg, map_sub, map_one, map_add (f := _), map_mul, map_mul, he, he,
      map_sub, map_one, hw]
    ext <;> simp
  rw [key]
  rfl

end PI.OmLocU.Red
end
end

