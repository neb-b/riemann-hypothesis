module

public import Mathlib
public import Development.AutomorphicArithmetic.IntegralCasts.TransposeInverse.TransposeInv
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0039
public import Development.AutomorphicArithmetic.IntegralCasts.AlgebraicInfinityType.InfinityType

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
section
noncomputable section

open Matrix

namespace GlobalTheory.CuspRep

abbrev BlockIx (a r : ℕ) := {p : Fin a × Fin a // p.1.val < r ∧ r ≤ p.2.val}

section
variable {a : ℕ} {R : Type} [CommRing R]

def nilM {r : ℕ} (x : BlockIx a r → R) : Matrix (Fin a) (Fin a) R :=
  Matrix.of fun i j => if h : i.val < r ∧ r ≤ j.val then x ⟨(i, j), h⟩ else 0

theorem nilM_mul_self {r : ℕ} (x : BlockIx a r → R) : nilM x * nilM x = 0 := by
  ext i j
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases h : l.val < r
  · simp [nilM, not_le.2 h]
  · simp [nilM, h]

theorem nilM_mul {r : ℕ} (x y : BlockIx a r → R) : nilM x * nilM y = 0 := by
  ext i j
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases h : l.val < r
  · simp [nilM, not_le.2 h]
  · simp [nilM, h]

def unip {r : ℕ} (x : BlockIx a r → R) : GL (Fin a) R where
  val := 1 + nilM x
  inv := 1 - nilM x
  val_inv := by simp [add_mul, mul_sub, nilM_mul_self]
  inv_val := by simp [sub_mul, mul_add, nilM_mul_self]

end

def invT (a : ℕ) (R : Type) [CommRing R] : GL (Fin a) R →* GL (Fin a) R :=
  (Reformulated.TransposeInverseTheory.transposeInv : GL (Fin a) R ≃* GL (Fin a) R).toMonoidHom

def twRep {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (χ : G →* ℂˣ) : Representation ℂ G V where
  toFun g := (χ g : ℂ) • ρ g
  map_one' := by simp
  map_mul' g h := by
    simp only [map_mul, Units.val_mul, smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [mul_comm (χ h : ℂ)]

theorem isOpen_stab_of_mem_nhds {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : G →* Module.End ℂ V) (v : V)
    (h : {g : G | ρ g v = v} ∈ nhds (1 : G)) : IsOpen {g : G | ρ g v = v} :=
  UpperTheory.Reformulated.B.IsOpenStabilizer.isOpen_stab_of_mem_nhds ρ v h

end GlobalTheory.CuspRep
end
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.RegAlgFam
section
open NumberField

namespace UpperTheory.RegAlgFam

theorem exists_pairs {α : Type*} (s t : Multiset α) (h : s.card = t.card) :
    ∃ P : Multiset (α × α), P.map Prod.fst = s ∧ P.map Prod.snd = t := by
  induction s using Quotient.inductionOn with | _ l =>
  induction t using Quotient.inductionOn with | _ k =>
  have hl : l.length = k.length := by simpa using h
  refine ⟨(l.zip k : List (α × α)), ?_, ?_⟩
  · simp [List.map_fst_zip hl.le]
  · simp [List.map_snd_zip hl.ge]

theorem exists_iff {F : Type*} [Field F] [IsTotallyComplex F] {n : ℕ} (μ : (F →+* ℂ) → Multiset ℂ)
    (hc : ∀ τ, (μ τ).card = n) :
    (∃ t : Reformulated.AlgebraicInfinityType.InfinityType F n, t.IsRegularAlgebraic ∧ ∀ τ, t.exponents τ = μ τ) ↔
      ∀ τ, (μ τ).Nodup ∧ ∀ z ∈ μ τ, ∃ m : ℤ, z = (m : ℂ) + ((n : ℂ) - 1) / 2 := by
  classical
  constructor
  · rintro ⟨t, ⟨ha, hr⟩, he⟩ τ
    refine ⟨he τ ▸ hr τ, fun z hz => ?_⟩
    obtain ⟨m, hm⟩ := ha τ z (he τ ▸ hz)
    exact ⟨m, by rw [hm, add_comm]⟩
  · intro h
    choose P h1 h2 using fun τ : F →+* ℂ =>
      exists_pairs (μ τ) (μ (ComplexEmbedding.conjugate τ)) ((hc _).trans (hc _).symm)
    have cc : ∀ τ : F →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ :=
      fun τ => star_star τ
    let g : (F →+* ℂ) → Prop := fun τ => (InfinitePlace.mk τ).embedding = τ
    have hg : ∀ τ, g (ComplexEmbedding.conjugate τ) ↔ ¬ g τ := by
      intro τ
      have hne : ComplexEmbedding.conjugate τ ≠ τ := fun e =>
        (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk τ)))
          ⟨τ, ComplexEmbedding.isReal_iff.2 e, rfl⟩
      simp only [g, InfinitePlace.mk_conjugate_eq]
      rcases InfinitePlace.embedding_mk_eq τ with e | e
      · rw [e]; simp [hne.symm]
      · rw [e]; simp [hne]
    let Q : (F →+* ℂ) → Multiset (ℂ × ℂ) := fun τ =>
      if g τ then P τ else (P (ComplexEmbedding.conjugate τ)).map Prod.swap
    have q1 : ∀ τ, (Q τ).map Prod.fst = μ τ := by
      intro τ
      by_cases e : g τ
      · simp [Q, e, h1]
      · have := h2 (ComplexEmbedding.conjugate τ)
        rw [cc] at this
        simpa [Q, e, Multiset.map_map] using this
    have qc : ∀ τ, Q (ComplexEmbedding.conjugate τ) = (Q τ).map Prod.swap := by
      intro τ
      by_cases e : g τ
      · have e' : ¬ g (ComplexEmbedding.conjugate τ) := fun x => (hg τ).1 x e
        simp only [Q, if_pos e, if_neg e', cc]
      · simp only [Q, if_neg e, if_pos ((hg τ).2 e), Multiset.map_map]
        simp
    refine ⟨⟨Q, fun τ => by rw [← hc τ, ← q1 τ, Multiset.card_map], fun τ p hp => ?_, qc⟩,
      ⟨fun τ z hz => ?_, fun τ => ?_⟩, q1⟩
    · obtain ⟨a, ha⟩ := (h τ).2 p.1 (q1 τ ▸ Multiset.mem_map_of_mem _ hp)
      have hp' : p.2 ∈ μ (ComplexEmbedding.conjugate τ) := by
        rw [← q1, qc]
        exact Multiset.mem_map.2 ⟨p.swap, Multiset.mem_map_of_mem _ hp, rfl⟩
      obtain ⟨b, hb⟩ := (h _).2 p.2 hp'
      exact ⟨a - b, by rw [ha, hb]; push_cast; ring⟩
    · obtain ⟨m, hm⟩ := (h τ).2 z (q1 τ ▸ hz)
      exact ⟨m, by rw [hm, add_comm]⟩
    · have := (h τ).1
      rwa [← q1 τ] at this

end UpperTheory.RegAlgFam
end

