module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.Development
public import Formalism.PeriodIntegrals.Bundle0003

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.ClassFiniteOf
section
noncomputable section

open Matrix NumberField IsDedekindDomain
open scoped TensorProduct ComplexOrder

namespace PI.UnitaryGroupMassFormula.UJClassFin

open PI.UJClassFin

def SigPos : Prop :=
  ∀ (M : ℕ) (A : Matrix (Fin M) (Fin M) ℂ), HasSignature A M 0 → A.PosDef

def AdelBounds : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (L : Set (Fin M → E)),
    (∀ a, σ a = star a) →
    (∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) →
    (∀ τ : E →+* ℂ, HasSignature (J.map τ) M 0) →
    (∃ c : 𝓞 F, c ≠ 0 ∧ ∀ x ∈ L, ∀ i, IsIntegral ℤ ((c : F) • x i)) →
    (∃ c : 𝓞 F, c ≠ 0 ∧ ∀ i, ∀ e : E, IsIntegral ℤ e → Pi.single i ((c : F) • e) ∈ L) →
    ∃ D T c0 : ℕ, 0 < D ∧ 0 < T ∧ 0 < c0 ∧ ∀ h : HA (AF F) σ J,
      (∀ x ∈ abelian₂ σ J L h, ∀ e : E, IsIntegral ℤ e → ((c0 : E) * e) • x ∈ abelian₂ σ J L h) ∧
      (∃ k : ℕ, 0 < k ∧ ∀ i, ∀ e : E, IsIntegral ℤ e → Pi.single i ((k : E) * e) ∈ abelian₂ σ J L h) ∧
      (∀ x ∈ abelian₂ σ J L h, ∀ y ∈ abelian₂ σ J L h,
        IsIntegral ℤ ((D : E) * PI.HermLatFin.herm (σ : E →+* E) J x y)) ∧
      (∀ y, (∀ x ∈ abelian₂ σ J L h, IsIntegral ℤ ((D : E) * PI.HermLatFin.herm (σ : E →+* E) J x y)) →
        (T : E) • y ∈ abelian₂ σ J L h)

def LatFin : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (σ : E →+* E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (D T c0 : ℕ),
    (∀ (τ : E →+* ℂ) (a : E), τ (σ a) = starRingEnd ℂ (τ a)) →
    (∀ τ : E →+* ℂ, (J.map τ).PosDef) → 0 < D → 0 < T → 0 < c0 →
    ∃ S : Set (Set (Fin M → E)), S.Finite ∧ ∀ Λ : AddSubgroup (Fin M → E),
      (∀ x ∈ Λ, ∀ e : E, IsIntegral ℤ e → ((c0 : E) * e) • x ∈ Λ) →
      (∃ k : ℕ, 0 < k ∧ ∀ i, ∀ e : E, IsIntegral ℤ e → Pi.single i ((k : E) * e) ∈ Λ) →
      (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ ((D : E) * PI.HermLatFin.herm σ J x y)) →
      (∀ y, (∀ x ∈ Λ, IsIntegral ℤ ((D : E) * PI.HermLatFin.herm σ J x y)) → (T : E) • y ∈ Λ) →
      ∃ s ∈ S, ∃ g : UJ σ J, (Λ : Set (Fin M → E)) =
        (fun x => ((g : GL (Fin M) E) : Matrix (Fin M) (Fin M) E).mulVec x) '' s

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def LamG (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (L : Set (Fin M → E)) (h : HA (AF F) σ J) :
    AddSubgroup (Fin M → E) where
  carrier := abelian₂ σ J L h
  add_mem' {x y} hx hy := by
    show (finMat σ J h⁻¹).mulVec (vinc (x + y)) ∈ latHat F E L
    have : vinc (F := F) (x + y) = vinc x + vinc y := by funext i; simp [vinc]
    rw [this, Matrix.mulVec_add]
    exact add_mem hx hy
  zero_mem' := by
    show (finMat σ J h⁻¹).mulVec (vinc 0) ∈ latHat F E L
    have : vinc (F := F) (0 : Fin M → E) = 0 := by funext i; simp [vinc]
    rw [this, Matrix.mulVec_zero]
    exact zero_mem _
  neg_mem' {x} hx := by
    show (finMat σ J h⁻¹).mulVec (vinc (-x)) ∈ latHat F E L
    have : vinc (F := F) (-x) = -vinc x := by funext i; simp [vinc]
    rw [this, Matrix.mulVec_neg]
    exact neg_mem hx

theorem classFinite_of (hS : SigPos) (hA : AdelBounds) (hB : LatFin) : ClassFinite := by
  intro F E _ _ _ _ _ _ σ M J L hst hτ hsig hL1 hL2
  obtain ⟨D, T, c0, hD, hT, hc0, hbd⟩ := hA F E σ M J L hst hτ hsig hL1 hL2
  have hσ : ∀ (τ : E →+* ℂ) (a : E), τ ((σ : E →+* E) a) = starRingEnd ℂ (τ a) := by
    intro τ a
    change τ (σ a) = _
    rw [hst a]
    exact hτ τ a
  obtain ⟨S, hSf, hS'⟩ := hB E (σ : E →+* E) M J D T c0 hσ (fun τ => hS M _ (hsig τ)) hD hT hc0
  refine ⟨S, hSf, fun h => ?_⟩
  obtain ⟨b1, b2, b3, b4⟩ := hbd h
  obtain ⟨s, hs, g, hg⟩ := hS' (LamG σ J L h) b1 b2 b3 b4
  exact ⟨s, hs, g, hg⟩

end PI.UnitaryGroupMassFormula.UJClassFin
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassFiniteness.UJClassFinOf
section
noncomputable section

open Matrix NumberField IsDedekindDomain
open scoped TensorProduct

namespace PI.UnitaryGroupMassFormula.UJClassFin

open PI.UJClassFin

theorem uJClassFin_of (hR : RatDense) (hC : ClassFinite) : UJClassFin := by
  unfold UJClassFin
  intro F E _ _ _ _ _ _ σ M J L h1 h2 h3 h4 h5
  have hRL := hR F E σ M J L h4 h5
  obtain ⟨S, hSf, hS⟩ := hC F E σ M J L h1 h2 h3 h4 h5

  let rel : HA (AF F) σ J → HA (AF F) σ J → Prop := fun x y =>
    ∃ γ ∈ GamG σ J, ∃ k ∈ SFin σ J L, x = γ * y * k
  have hrefl : ∀ x, rel x x := fun x => ⟨1, one_mem _, 1, one_mem _, by simp⟩
  have hsymm : ∀ {x y}, rel x y → rel y x := by
    rintro x y ⟨γ, hγ, k, hk, rfl⟩
    exact ⟨γ⁻¹, inv_mem hγ, k⁻¹, inv_mem hk, by group⟩
  have htrans : ∀ {x y z}, rel x y → rel y z → rel x z := by
    rintro x y z ⟨γ, hγ, k, hk, rfl⟩ ⟨γ', hγ', k', hk', rfl⟩
    exact ⟨γ * γ', mul_mem hγ hγ', k' * k, mul_mem hk' hk, by group⟩
  let st : Setoid (HA (AF F) σ J) := ⟨rel, ⟨hrefl, hsymm, htrans⟩⟩
  choose f hfS g hg using hS

  have key : ∀ x y, f x = f y → rel y x := by
    intro x y hxy
    have hL : abelian₂ σ J L (emb σ J (g y * (g x)⁻¹) * x) = abelian₂ σ J L y := by
      rw [Lam_emb_mul (σ := σ) (J := J) L, hg x, hg y, Set.image_image, hxy]
      congr 1
      funext v
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel_right]
    have hk := sfin_of_Lam_eq (σ := σ) (J := J) L hRL _ _ hL
    exact ⟨emb σ J (g y * (g x)⁻¹), emb_mem (σ := σ) (J := J) _, _, hk,
      (mul_inv_cancel_left _ _).symm⟩
  have hQ : Finite (Quotient st) := by
    have hfin : (Set.range f).Finite := hSf.subset (by rintro _ ⟨x, rfl⟩; exact hfS x)
    have : Finite (Set.range f) := hfin.to_subtype
    refine Finite.of_surjective (fun s : Set.range f => Quotient.mk st s.2.choose) ?_
    intro q
    induction q using Quotient.inductionOn with
    | h x =>
      refine ⟨⟨f x, x, rfl⟩, ?_⟩
      exact Quotient.sound (s := st) (key _ _ (Exists.choose_spec (⟨x, rfl⟩ : f x ∈ Set.range f)).symm)
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin (Quotient st)
  refine ⟨n, fun i => (e.symm i).out, ?_, ?_⟩
  · intro x
    have hq : rel (Quotient.mk st x).out x := Quotient.exact (Quotient.out_eq (Quotient.mk st x))
    obtain ⟨γ, hγ, k, hk, hx⟩ := hsymm hq
    refine ⟨e (Quotient.mk st x), ⟨γ, hγ⟩, ⟨k, hk⟩, ?_⟩
    simp only [Equiv.symm_apply_apply]
    exact hx
  · intro i j γ γ' k k' hEq
    simp only at hEq
    have hr : rel (e.symm i).out (e.symm j).out := by
      refine ⟨(γ : HA (AF F) σ J)⁻¹ * γ', mul_mem (inv_mem γ.2) γ'.2, (k' : HA (AF F) σ J) * (k : HA (AF F) σ J)⁻¹,
        mul_mem k'.2 (inv_mem k.2), ?_⟩
      have h0 : (e.symm i).out = (γ : HA (AF F) σ J)⁻¹ * (γ * (e.symm i).out * k) * (k : HA (AF F) σ J)⁻¹ := by
        group
      rw [h0, hEq]
      group
    have := Quotient.sound (s := st) hr
    rw [Quotient.out_eq, Quotient.out_eq] at this
    exact e.symm.injective this

end PI.UnitaryGroupMassFormula.UJClassFin
end
end

