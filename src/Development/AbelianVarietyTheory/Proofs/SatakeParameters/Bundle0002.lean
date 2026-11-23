module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOneOfNormOneValuationSubOneSmall
section
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem abs_norm_eq_prod_embeddings_closeOne {E : Type} [Field E] [NumberField E] (x : E) :
    |((Algebra.norm ℚ x : ℚ) : ℝ)| = ∏ σ : E →+* ℂ, ‖σ x‖ := by
  have h : ((Algebra.norm ℚ x : ℚ) : ℂ) = ∏ σ : E →+* ℂ, σ x := by
    rw [Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) (fun f => f x) (fun φ => φ x)
      (fun _ => rfl), ← Algebra.norm_eq_prod_embeddings ℚ ℂ x]
    simp
  rw [← norm_prod, ← h, Complex.norm_ratCast]

theorem eq_one_of_norm_one_of_valuation_sub_one_le (E : Type) [Field E] [NumberField E] (ε : E)
    (w : HeightOneSpectrum (𝓞 E)) (K : ℕ) (hK : Module.finrank ℚ E < K)
    (hint : ∀ v : HeightOneSpectrum (𝓞 E), v.valuation E ε ≤ 1)
    (habs : ∀ φ : E →+* ℂ, ‖φ ε‖ = 1)
    (hw : w.valuation E (ε - 1) ≤ WithZero.exp (-(K : ℤ))) : ε = 1 := by
  obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one E ε hint
  by_contra hne
  have hxE : algebraMap (𝓞 E) E (r - 1) = ε - 1 := by simp [hr]
  have hx0 : r - 1 ≠ 0 := by
    intro h
    rw [h, map_zero] at hxE
    exact hne (sub_eq_zero.mp hxE.symm)
  have hmem : r - 1 ∈ w.asIdeal ^ K := by
    rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem, ← HeightOneSpectrum.valuation_of_algebraMap (K := E)]
    convert hw using 2
  have hdvd : w.asIdeal ^ K ∣ Ideal.span {r - 1} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact hmem
  have hN := map_dvd Ideal.absNorm hdvd
  rw [map_pow, Ideal.absNorm_span_singleton] at hN
  have hnz : (Algebra.norm ℤ (r - 1)).natAbs ≠ 0 := by
    rw [← Ideal.absNorm_span_singleton, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hx0
  have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hnz) hN
  have h2 : 2 ≤ Ideal.absNorm w.asIdeal := by
    have h0 : Ideal.absNorm w.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot
    have h1 : Ideal.absNorm w.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact w.isPrime.ne_top
    omega
  have hlow : 2 ^ K ≤ (Algebra.norm ℤ (r - 1)).natAbs :=
    le_trans (Nat.pow_le_pow_left h2 K) hle
  have hup : ((Algebra.norm ℤ (r - 1)).natAbs : ℝ) ≤ 2 ^ Module.finrank ℚ E := by
    have h1 : ((Algebra.norm ℤ (r - 1)).natAbs : ℝ) = |((Algebra.norm ℚ (ε - 1) : ℚ) : ℝ)| := by
      rw [← hxE, ← Algebra.coe_norm_int (r - 1), Nat.cast_natAbs]
      push_cast
      rfl
    rw [h1, abs_norm_eq_prod_embeddings_closeOne]
    calc ∏ φ : E →+* ℂ, ‖φ (ε - 1)‖ ≤ ∏ _φ : E →+* ℂ, (2 : ℝ) := by
          refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun φ _ => ?_)
          rw [map_sub, map_one]
          calc ‖φ ε - 1‖ ≤ ‖φ ε‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
            _ = 2 := by rw [habs φ, norm_one]; norm_num
      _ = 2 ^ Module.finrank ℚ E := by
          rw [Finset.prod_const, Finset.card_univ, NumberField.Embeddings.card]
  have hlowR : (2 : ℝ) ^ K ≤ 2 ^ Module.finrank ℚ E := by
    have : ((2 ^ K : ℕ) : ℝ) ≤ ((Algebra.norm ℤ (r - 1)).natAbs : ℝ) := by exact_mod_cast hlow
    push_cast at this
    linarith
  have := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hlowR
  omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCombinationNormNeZeroOfLinearIndependentAl
section
open scoped TensorProduct
open Matrix

namespace GlobalTheory

theorem exists_combination_norm_ne_zero_of_linearIndependent
    {B A : Type} [CommRing B] [IsDomain B] [CommRing A] [Algebra B A]
    [Module.Free B A] [Module.Finite B A] {d : ℕ} (hd : Module.finrank B A = d)
    (y : Fin d → A) (hy : LinearIndependent B y) :
    ∃ x : Fin d → B, Algebra.norm B (∑ i, x i • y i) ≠ 0 := by
  classical
  let e := Module.finBasisOfFinrankEq B A hd
  let Y : Matrix (Fin d) (Fin d) B := fun i j => e.equivFun (y j) i
  have key : ∀ v : Fin d → B, e.equivFun (∑ j, v j • y j) = Y *ᵥ v := by
    intro v
    ext i
    simp [Y, Matrix.mulVec, dotProduct, mul_comm]
  have hdet : Y.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have h1 : ∑ j, v j • y j = 0 := by
      apply e.equivFun.injective
      rw [key, hv, map_zero]
    exact hv0 (funext fun j => Fintype.linearIndependent_iff.mp hy v h1 j)
  refine ⟨Y.adjugate *ᵥ e.equivFun 1, ?_⟩
  have hsum : ∑ j, (Y.adjugate *ᵥ e.equivFun 1) j • y j = algebraMap B A Y.det := by
    apply e.equivFun.injective
    rw [key, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
      Matrix.one_mulVec, Algebra.algebraMap_eq_smul_one, map_smul]
  rw [hsum, Algebra.norm_algebraMap]
  exact pow_ne_zero _ hdet

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCommonEigenvalueOfMemAdjoin
section
namespace GlobalTheory.CommonEigenvalueAdjoin

theorem exists_common_eigenvalue_of_mem_adjoin {M : Type} [AddCommGroup M] [Module ℂ M]
    (s : Set (Module.End ℂ M)) (u u' : M)
    (h : ∀ x ∈ s, ∃ l : ℂ, x u = l • u ∧ x u' = l • u') :
    ∀ a ∈ Algebra.adjoin ℂ s, ∃ l : ℂ, a u = l • u ∧ a u' = l • u' := by
  intro a ha
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact h x hx
  | algebraMap r => exact ⟨r, by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨l, h1, h2⟩ := hx
    obtain ⟨m, h3, h4⟩ := hy
    exact ⟨l + m, by rw [LinearMap.add_apply, h1, h3, add_smul],
      by rw [LinearMap.add_apply, h2, h4, add_smul]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨l, h1, h2⟩ := hx
    obtain ⟨m, h3, h4⟩ := hy
    exact ⟨m * l, by rw [Module.End.mul_apply, h3, map_smul, h1, smul_smul],
      by rw [Module.End.mul_apply, h4, map_smul, h2, smul_smul]⟩

end GlobalTheory.CommonEigenvalueAdjoin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsComplementWithoutCommonIrreducibleTypes
section
namespace GlobalTheory

namespace TypeComplement

variable {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ K V}

def supRep (P : Subrepresentation ρ → Prop) : Subrepresentation ρ where
  toSubmodule := ⨆ (S : Subrepresentation ρ) (_ : P S), S.toSubmodule
  apply_mem_toSubmodule k := by
    have h : (⨆ (S : Subrepresentation ρ) (_ : P S), S.toSubmodule) ≤
        (⨆ (S : Subrepresentation ρ) (_ : P S), S.toSubmodule).comap (ρ k) := by
      refine iSup₂_le fun S hS x hx => ?_
      exact (le_iSup₂ (f := fun (S : Subrepresentation ρ) (_ : P S) => S.toSubmodule) S hS)
        (S.apply_mem_toSubmodule k hx)
    exact fun v hv => h hv

def imRep (f : V →ₗ[ℂ] V) (hf : ∀ k v, f (ρ k v) = ρ k (f v)) (S : Subrepresentation ρ) :
    Subrepresentation ρ where
  toSubmodule := S.toSubmodule.map f
  apply_mem_toSubmodule k := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨ρ k s, S.apply_mem_toSubmodule k hs, hf k s⟩

def preRep (f : V →ₗ[ℂ] V) (hf : ∀ k v, f (ρ k v) = ρ k (f v)) (S C : Subrepresentation ρ) :
    Subrepresentation ρ where
  toSubmodule := S.toSubmodule ⊓ C.toSubmodule.comap f
  apply_mem_toSubmodule k := by
    rintro v ⟨hv1, hv2⟩
    refine ⟨S.apply_mem_toSubmodule k hv1, ?_⟩
    show f (ρ k v) ∈ C.toSubmodule
    rw [hf k v]
    exact C.apply_mem_toSubmodule k hv2

theorem toSubmodule_bot : (⊥ : Subrepresentation ρ).toSubmodule = ⊥ := rfl

theorem ne_bot_iff_toSubmodule {S : Subrepresentation ρ} : S ≠ ⊥ ↔ S.toSubmodule ≠ ⊥ := by
  constructor
  · intro h h'
    exact h (Subrepresentation.toSubmodule_injective h')
  · rintro h rfl
    exact h rfl

end TypeComplement

end GlobalTheory

namespace GlobalTheory
namespace TypeComplement
variable {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ K V}

theorem imRep_atom (f : V →ₗ[ℂ] V) (hf : ∀ k v, f (ρ k v) = ρ k (f v)) {S : Subrepresentation ρ}
    (hS : IsAtom S) (hne : ∃ s ∈ S.toSubmodule, f s ≠ 0) :
    IsAtom (imRep f hf S) ∧
      Nonempty (S.toRepresentation.Equiv (imRep f hf S).toRepresentation) := by
  obtain ⟨s₀, hs₀, hfs₀⟩ := hne

  have hinj : Function.Injective (f ∘ₗ S.toSubmodule.subtype) := by
    let Kr : Subrepresentation ρ := preRep f hf S ⊥
    have hK : Kr ≤ S := fun v hv => hv.1
    rcases hS.le_iff.mp hK with h | h
    · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro x hx
      have hx' : (x : V) ∈ Kr.toSubmodule := by
        refine ⟨x.2, ?_⟩
        show f x ∈ (⊥ : Submodule ℂ V)
        simpa using hx
      rw [h] at hx'
      simp only [toSubmodule_bot, Submodule.mem_bot] at hx'
      simpa using Subtype.ext hx'
    · exfalso
      have : s₀ ∈ Kr.toSubmodule := by rw [h]; exact hs₀
      exact hfs₀ ((Submodule.mem_bot ℂ).mp (show f s₀ ∈ (⊥ : Submodule ℂ V) from this.2))
  refine ⟨⟨?_, fun C hC => ?_⟩, ?_⟩
  · rw [ne_bot_iff_toSubmodule]
    intro h
    have : f s₀ ∈ (imRep f hf S).toSubmodule := ⟨s₀, hs₀, rfl⟩
    rw [h] at this
    exact hfs₀ ((Submodule.mem_bot ℂ).mp this)
  · by_contra hC0
    obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (ne_bot_iff_toSubmodule.mp hC0)
    obtain ⟨s, hs, rfl⟩ : c ∈ (imRep f hf S).toSubmodule := hC.le hc
    have hB : preRep f hf S C ≤ S := fun v hv => hv.1
    rcases hS.le_iff.mp hB with h | h
    · have : s ∈ (preRep f hf S C).toSubmodule := ⟨hs, hc⟩
      rw [h] at this
      simp only [toSubmodule_bot, Submodule.mem_bot] at this
      exact hc0 (by simp [this])
    · have hle : imRep f hf S ≤ C := by
        rintro _ ⟨t, ht, rfl⟩
        have : t ∈ (preRep f hf S C).toSubmodule := by rw [h]; exact ht
        exact this.2
      exact lt_irrefl _ (lt_of_lt_of_le hC hle)
  · have hr : LinearMap.range (f ∘ₗ S.toSubmodule.subtype) = (imRep f hf S).toSubmodule := by
      rw [LinearMap.range_comp, Submodule.range_subtype]; rfl
    let e : S.toSubmodule ≃ₗ[ℂ] (imRep f hf S).toSubmodule :=
      (LinearEquiv.ofInjective _ hinj).trans (LinearEquiv.ofEq _ _ hr)
    refine ⟨Representation.Equiv.mk e fun k => ?_⟩
    ext x
    simp [e, Subrepresentation.toRepresentation, hf]

end TypeComplement
end GlobalTheory

namespace GlobalTheory
namespace TypeComplement

theorem exists_typeComplement : ∀ (K V : Type) [Group K] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ K V), ρ.IsSemisimpleRepresentation → (∀ X : Subrepresentation ρ, X.toSubmodule = ⨆ (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X), S.toSubmodule) → ∀ X : Subrepresentation ρ, (∀ S₁ S₂ : Subrepresentation ρ, IsAtom S₁ → S₂ ≤ X → Nonempty (S₁.toRepresentation.Equiv S₂.toRepresentation) → S₁ ≤ X) → ∃ Y : Subrepresentation ρ, IsCompl X.toSubmodule Y.toSubmodule ∧ (∀ S₁ S₂ : Subrepresentation ρ, IsAtom S₁ → IsAtom S₂ → S₁ ≤ Y → S₂ ≤ X → IsEmpty (S₁.toRepresentation.Equiv S₂.toRepresentation)) ∧ ∀ T : V →ₗ[ℂ] V, (∀ k v, T (ρ k v) = ρ k (T v)) → (∀ v ∈ X.toSubmodule, T v ∈ X.toSubmodule) ∧ ∀ v ∈ Y.toSubmodule, T v ∈ Y.toSubmodule := by
  intro K V _ _ _ ρ hss hsum X hcl
  haveI : ComplementedLattice (Subrepresentation ρ) := hss
  let Y : Subrepresentation ρ := supRep (fun S => IsAtom S ∧ ¬ S ≤ X)
  have hYle : ∀ S : Subrepresentation ρ, IsAtom S → ¬ S ≤ X → S.toSubmodule ≤ Y.toSubmodule :=
    fun S hA hn => le_iSup₂ (f := fun (S : Subrepresentation ρ) (_ : IsAtom S ∧ ¬ S ≤ X) =>
      S.toSubmodule) S ⟨hA, hn⟩

  obtain ⟨Y₀, hY₀⟩ := exists_isCompl X
  have hXY₀ : IsCompl X.toSubmodule Y₀.toSubmodule := by
    constructor
    · rw [disjoint_iff]
      exact congrArg Subrepresentation.toSubmodule hY₀.inf_eq_bot
    · rw [codisjoint_iff]
      exact congrArg Subrepresentation.toSubmodule hY₀.sup_eq_top
  let p : V →ₗ[ℂ] V := X.toSubmodule.projection Y₀.toSubmodule hXY₀
  have hp : ∀ k v, p (ρ k v) = ρ k (p v) := by
    intro k v
    have hv : v ∈ X.toSubmodule ⊔ Y₀.toSubmodule := by rw [hXY₀.sup_eq_top]; trivial
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
    have h1 : ∀ {a b : V}, a ∈ X.toSubmodule → b ∈ Y₀.toSubmodule → p (a + b) = a := by
      intro a b ha hb
      rw [map_add (f := _), Submodule.projection_apply_of_mem_left _ ha]
      have : p b = 0 := (Submodule.projection_apply_eq_zero_iff hXY₀).mpr hb
      rw [this, add_zero]
    rw [map_add (f := _), h1 (X.apply_mem_toSubmodule k hx) (Y₀.apply_mem_toSubmodule k hy), h1 hx hy]

  have hYY₀ : Y.toSubmodule ≤ Y₀.toSubmodule := by
    refine iSup₂_le fun S ⟨hA, hn⟩ => ?_
    by_contra hc
    have hne : ∃ s ∈ S.toSubmodule, p s ≠ 0 := by
      by_contra h
      push_neg at h
      exact hc fun s hs => (Submodule.projection_apply_eq_zero_iff hXY₀).mp (h s hs)
    obtain ⟨_, ⟨e⟩⟩ := imRep_atom p hp hA hne
    have hle : imRep p hp S ≤ X := by
      rintro _ ⟨s, _, rfl⟩
      exact Submodule.projection_apply_mem hXY₀ s
    exact hn (hcl S _ hA hle ⟨e⟩)
  have hdisj : X.toSubmodule ⊓ Y.toSubmodule = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_left _ hYY₀).trans (disjoint_iff.mp hXY₀.disjoint).le)
  refine ⟨Y, ⟨disjoint_iff.mpr hdisj, codisjoint_iff.mpr ?_⟩, ?_, ?_⟩
  ·
    refine eq_top_iff.mpr ?_
    show (⊤ : Subrepresentation ρ).toSubmodule ≤ _
    refine (hsum ⊤).le.trans (iSup₂_le fun S ⟨hA, _⟩ => ?_)
    by_cases hSX : S ≤ X
    · exact le_sup_of_le_left hSX
    · exact le_sup_of_le_right (hYle S hA hSX)
  ·
    intro S₁ S₂ hS₁ _ hY hX
    refine ⟨fun e => ?_⟩
    have h₁ : S₁ ≤ X := hcl S₁ S₂ hS₁ hX ⟨e⟩
    apply hS₁.1
    apply Subrepresentation.toSubmodule_injective
    rw [toSubmodule_bot, eq_bot_iff, ← hdisj]
    exact le_inf h₁ hY
  · intro T hT
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · have hX : X.toSubmodule ≤ X.toSubmodule.comap T := by
        refine (hsum X).le.trans (iSup₂_le fun S ⟨hA, hSX⟩ => ?_)
        by_cases hne : ∃ s ∈ S.toSubmodule, T s ≠ 0
        · obtain ⟨hA', ⟨e⟩⟩ := imRep_atom T hT hA hne
          have hle : imRep T hT S ≤ X := hcl _ S hA' hSX ⟨e.symm⟩
          exact fun s hs => hle ⟨s, hs, rfl⟩
        · push_neg at hne
          intro s hs
          show T s ∈ X.toSubmodule
          rw [hne s hs]
          exact zero_mem _
      exact hX hv
    · have hY : Y.toSubmodule ≤ Y.toSubmodule.comap T := by
        refine iSup₂_le fun S ⟨hA, hn⟩ => ?_
        by_cases hne : ∃ s ∈ S.toSubmodule, T s ≠ 0
        · obtain ⟨hA', ⟨e⟩⟩ := imRep_atom T hT hA hne
          have hnX : ¬ imRep T hT S ≤ X := fun hle => hn (hcl S _ hA hle ⟨e⟩)
          exact fun s hs => hYle _ hA' hnX ⟨s, hs, rfl⟩
        · push_neg at hne
          intro s hs
          show T s ∈ Y.toSubmodule
          rw [hne s hs]
          exact zero_mem _
      exact hY hv

end TypeComplement
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsConjIntegral
section
noncomputable section
open Matrix Module

namespace GlobalTheory.StableLattice

theorem lift_of_integral {O K : Type} [CommRing O] [Field K] [Algebra O K]
    (hinj : Function.Injective (algebraMap O K)) {Γ : Type} [Group Γ] {n : ℕ}
    (φ : Γ →* GL (Fin n) K)
    (h : ∀ g i j, ((φ g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j ∈ (algebraMap O K).range) :
    ∃ r : Γ →* GL (Fin n) O, ∀ g, Matrix.GeneralLinearGroup.map (algebraMap O K) (r g) = φ g := by
  classical
  let f : O →+* K := algebraMap O K
  have h' : ∀ g i j, ∃ x : O, f x = ((φ g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j :=
    fun g i j => RingHom.mem_range.1 (h g i j)
  choose c hc using h'
  let M : Γ → Matrix (Fin n) (Fin n) O := fun g => Matrix.of fun i j => c g i j
  have hmi : Function.Injective (f.mapMatrix : Matrix (Fin n) (Fin n) O →+* Matrix (Fin n) (Fin n) K) :=
    fun A B hAB => Matrix.ext fun i j => hinj (by simpa using congrFun (congrFun hAB i) j)
  have hM : ∀ g, f.mapMatrix (M g) = ((φ g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    fun g => Matrix.ext fun i j => hc g i j
  let ρ : Γ →* GL (Fin n) O :=
    { toFun := fun g => ⟨M g, M g⁻¹,
        hmi (by rw [map_mul, hM, hM, map_one, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]),
        hmi (by rw [map_mul, hM, hM, map_one, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one])⟩
      map_one' := Units.ext (hmi (by rw [hM, map_one, Units.val_one, Units.val_one, map_one]))
      map_mul' := fun g h => Units.ext (hmi (by
        show f.mapMatrix (M (g * h)) = f.mapMatrix (M g * M h)
        rw [map_mul, hM, hM, hM, map_mul, Units.val_mul])) }
  exact ⟨ρ, fun g => Units.ext (hM g)⟩

theorem exists_conj_integral {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    {Γ : Type} [Group Γ] {n : ℕ} (σ : Γ →* GL (Fin n) (FractionRing O)) (T : Finset Γ)
    (hT : ∀ x : Γ, ∃ t ∈ T, ∀ i j, ((σ (t⁻¹ * x) : GL (Fin n) (FractionRing O)) :
      Matrix (Fin n) (Fin n) (FractionRing O)) i j ∈ (algebraMap O (FractionRing O)).range) :
    ∃ P : GL (Fin n) (FractionRing O), ∀ g i j,
      ((P⁻¹ * σ g * P : GL (Fin n) (FractionRing O)) : Matrix (Fin n) (Fin n) (FractionRing O)) i j
        ∈ (algebraMap O (FractionRing O)).range := by
  classical
  let K := FractionRing O
  let S : Γ → Matrix (Fin n) (Fin n) K := fun g => ((σ g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  let gen : T × Fin n → (Fin n → K) := fun p => S p.1 *ᵥ Pi.single p.2 1
  let M : Submodule O (Fin n → K) := Submodule.span O (Set.range gen)
  have hA : ∀ t (ht : t ∈ T), ∀ w : Fin n → K, (∀ k, w k ∈ (algebraMap O K).range) → S t *ᵥ w ∈ M := by
    intro t ht w hw
    choose u hu using fun k => RingHom.mem_range.1 (hw k)
    have : S t *ᵥ w = ∑ k, u k • gen (⟨t, ht⟩, k) := by
      ext a
      simp only [gen, Matrix.mulVec_single_one]
      simp only [Finset.sum_apply, Pi.smul_apply, Matrix.transpose_apply, Matrix.col_apply, Algebra.smul_def,
        Matrix.mulVec, dotProduct, ← hu]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    rw [this]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  have he : ∀ i, (Pi.single i 1 : Fin n → K) ∈ M := by
    intro i
    obtain ⟨t, ht, hU⟩ := hT 1
    have h1 : S t * S (t⁻¹ * 1) = 1 := by
      simp only [S]
      rw [← Units.val_mul, ← map_mul, mul_one, mul_inv_cancel, map_one, Units.val_one]
    have : (Pi.single i 1 : Fin n → K) = S t *ᵥ (S (t⁻¹ * 1) *ᵥ Pi.single i 1) := by
      rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
    rw [this]
    refine hA t ht _ fun k => ?_
    rw [Matrix.mulVec_single_one]
    exact hU k i
  have hstab : ∀ g, ∀ x ∈ M, S g *ᵥ x ∈ M := by
    intro g
    let A : (Fin n → K) →ₗ[O] (Fin n → K) := (Matrix.toLin' (S g)).restrictScalars O
    have hle : M.map A ≤ M := by
      rw [Submodule.map_span_le]
      rintro _ ⟨⟨⟨t, ht⟩, i⟩, rfl⟩
      obtain ⟨t', ht', hU⟩ := hT (g * t)
      have h1 : S g * S t = S t' * S (t'⁻¹ * (g * t)) := by
        simp only [S]
        rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, mul_inv_cancel_left]
      show S g *ᵥ (S t *ᵥ Pi.single i 1) ∈ M
      rw [Matrix.mulVec_mulVec, h1, ← Matrix.mulVec_mulVec]
      refine hA t' ht' _ fun k => ?_
      rw [Matrix.mulVec_single_one]
      exact hU k i
    intro x hx
    exact hle ⟨x, hx, rfl⟩
  haveI : Module.Finite O M := Module.Finite.span_of_finite (R := O) (Set.finite_range gen)
  haveI : Module.Free O M := Module.free_of_finite_type_torsion_free'
  let ι := Module.Free.ChooseBasisIndex O M
  let b : Basis ι O M := Module.Free.chooseBasis O M
  let v : ι → (Fin n → K) := fun i => (b i : Fin n → K)
  have hcoord : ∀ x (hx : x ∈ M), x = ∑ i, algebraMap O K (b.repr ⟨x, hx⟩ i) • v i := by
    intro x hx
    have := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at this
    simp only [algebraMap_smul, v]
    exact this.symm
  have hli : LinearIndependent K v :=
    (LinearIndependent.iff_fractionRing O K).1 (b.linearIndependent.map' M.subtype M.ker_subtype)
  have hsp : ⊤ ≤ Submodule.span K (Set.range v) := by
    rw [← (Pi.basisFun K (Fin n)).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [Pi.basisFun_apply, hcoord _ (he i)]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  let bK : Basis ι K (Fin n → K) := Basis.mk hli hsp
  have hrep : ∀ x (hx : x ∈ M) k, bK.repr x k = algebraMap O K (b.repr ⟨x, hx⟩ k) := by
    intro x hx k
    have h1 : x = bK.equivFun.symm (fun i => algebraMap O K (b.repr ⟨x, hx⟩ i)) := by
      rw [Basis.equivFun_symm_apply]
      simp only [bK, Basis.coe_mk]
      exact hcoord x hx
    rw [← Basis.equivFun_apply]
    conv_lhs => rw [h1]
    rw [LinearEquiv.apply_symm_apply]
  have hcard : Fintype.card ι = n :=
    (Module.finrank_eq_card_basis bK).symm.trans (Module.finrank_fin_fun K)
  let e : ι ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let bK' : Basis (Fin n) K (Fin n → K) := bK.reindex e
  let E := Pi.basisFun K (Fin n)
  let Pu : GL (Fin n) K := ⟨E.toMatrix bK', bK'.toMatrix E, E.toMatrix_mul_toMatrix_flip bK',
    bK'.toMatrix_mul_toMatrix_flip E⟩
  refine ⟨Pu, fun g i j => ?_⟩
  have hmat : ((Pu⁻¹ * σ g * Pu : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      LinearMap.toMatrix bK' bK' (Matrix.toLin' (S g)) := by
    rw [← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix (b := bK') (c := bK') (b' := E) (c' := E),
      LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
    simp only [Units.val_mul]
    rfl
  have hmem : S g *ᵥ bK' j ∈ M := by
    refine hstab g _ ?_
    simp only [bK', Basis.reindex_apply, bK, Basis.coe_mk, v]
    exact (b _).2
  rw [hmat, LinearMap.toMatrix_apply, Matrix.toLin'_apply, Basis.repr_reindex_apply, hrep _ hmem]
  exact ⟨_, rfl⟩

end GlobalTheory.StableLattice
end
end

