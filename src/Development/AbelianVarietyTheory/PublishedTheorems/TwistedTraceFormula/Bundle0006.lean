module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BesselFormsTrivialNeBot
section
noncomputable section

open Formalism.MainNotions.S Formalism.L2.Theta Formalism.QuantumDeterminants GlobalTheory.SmVec Matrix

namespace GlobalTheory.RealBessel

variable {n m r : ℕ}

structure IsFrame (J : Matrix (Fin n) (Fin n) ℂ) (J₀ : Matrix (Fin m) (Fin m) ℂ) (F : Matrix (Fin n) (Fin m) ℂ)
    (e : Matrix (Fin n) (Fin r) ℂ) (z : Fin n → ℂ) : Prop where
  herm : Jᴴ = J
  unit : IsUnit J
  unit₀ : IsUnit J₀
  codim : m + 2 * r + 1 = n
  gram : Fᴴ * J * F = J₀
  e_indep : LinearIndependent ℂ eᵀ
  e_iso : eᴴ * J * e = 0
  e_perp : Fᴴ * J * e = 0
  z_perpF : (Fᴴ * J) *ᵥ z = 0
  z_perpE : (eᴴ * J) *ᵥ z = 0
  z_ne : Formalism.QuantumDeterminants.herm J z z ≠ 0

def unipRad (J : Matrix (Fin n) (Fin n) ℂ) (e : Matrix (Fin n) (Fin r) ℂ) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {u | u ∈ UH J ∧
    (∀ i : Fin r, ∃ a : Fin r → ℂ, (∀ j, i ≤ j → a j = 0) ∧ (u - 1) *ᵥ (fun k => e k i) = e *ᵥ a) ∧
    ∀ x : Fin n → ℂ, (eᴴ * J) *ᵥ x = 0 → ∃ a : Fin r → ℂ, (u - 1) *ᵥ x = e *ᵥ a}

def flagVec (e : Matrix (Fin n) (Fin r) ℂ) (z : Fin n → ℂ) : Fin (r + 1) → Fin n → ℂ :=
  Fin.snoc (α := fun _ => Fin n → ℂ) (fun i k => e k i) z

def IsCharWith (J : Matrix (Fin n) (Fin n) ℂ) (e : Matrix (Fin n) (Fin r) ℂ) (z : Fin n → ℂ) (c : Fin r → ℂ)
    (χ : Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop :=
  ∀ u ∈ unipRad J e, ∀ a : Fin r → Fin r → ℂ, (∀ j : Fin r, (u - 1) *ᵥ flagVec e z j.succ = e *ᵥ a j) →
    χ u = Complex.exp (Complex.I * ((∑ j, c j * a j j).re : ℂ))

def IsGeneric (J : Matrix (Fin n) (Fin n) ℂ) (e : Matrix (Fin n) (Fin r) ℂ) (z : Fin n → ℂ)
    (χ : Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop :=
  ∃ c : Fin r → ℂ, (∀ j, c j ≠ 0) ∧ IsCharWith J e z c χ

def IsEmb (J : Matrix (Fin n) (Fin n) ℂ) (F : Matrix (Fin n) (Fin m) ℂ) (g : Matrix (Fin n) (Fin n) ℂ)
    (h : Matrix (Fin m) (Fin m) ℂ) : Prop :=
  g * F = F * h ∧ ∀ x : Fin n → ℂ, (Fᴴ * J) *ᵥ x = 0 → g *ᵥ x = x

section Forms

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {W : Type} [AddCommGroup W] [Module ℂ W]

def IsContIrred (G : Set (Matrix (Fin m) (Fin m) ℂ)) (π₀ : Matrix (Fin m) (Fin m) ℂ → Module.End ℂ W) : Prop :=
  IsRepOn G π₀ ∧ (∀ (w : W) (l : Module.Dual ℂ W), ContinuousOn (fun h => l (π₀ h w)) G) ∧
    ∀ U : Submodule ℂ W, (∀ h ∈ G, ∀ w ∈ U, π₀ h w ∈ U) → U = ⊥ ∨ U = ⊤

structure IsBesselForm (J : Matrix (Fin n) (Fin n) ℂ) (J₀ : Matrix (Fin m) (Fin m) ℂ) (F : Matrix (Fin n) (Fin m) ℂ)
    (e : Matrix (Fin n) (Fin r) ℂ) (χ : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (π₀ : Matrix (Fin m) (Fin m) ℂ → Module.End ℂ W)
    (V : Submodule ℂ H) (β : W →ₗ[ℂ] V →ₗ[ℂ] ℂ) : Prop where
  cont : ∀ w : W, ∃ l : H →ₗ[ℂ] ℂ, Sobolev₂ (lieG J) σ l ∧ ∀ x : V, l x = β w x
  inv : ∀ h ∈ UH J₀, ∀ g ∈ UH J, IsEmb J F g h → ∀ (w : W) (x y : V), (y : H) = σ g x → β (π₀ h w) y = β w x
  equiv : ∀ u ∈ unipRad J e, ∀ (w : W) (x y : V), (y : H) = σ u x → β w y = χ u * β w x

def besselForms (J : Matrix (Fin n) (Fin n) ℂ) (J₀ : Matrix (Fin m) (Fin m) ℂ) (F : Matrix (Fin n) (Fin m) ℂ)
    (e : Matrix (Fin n) (Fin r) ℂ) (χ : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (π₀ : Matrix (Fin m) (Fin m) ℂ → Module.End ℂ W)
    (V : Submodule ℂ H) : Submodule ℂ (W →ₗ[ℂ] V →ₗ[ℂ] ℂ) where
  carrier := {β | IsBesselForm J J₀ F e χ σ π₀ V β}
  zero_mem' := ⟨fun _ => ⟨0, ⟨[], 0, by simp, by simp⟩, fun _ => rfl⟩, fun _ _ _ _ _ _ _ _ _ => rfl,
    fun _ _ _ _ _ _ => by simp⟩
  add_mem' := fun {β β'} hβ hβ' =>
    ⟨fun w => by
      obtain ⟨l, h1, h2⟩ := hβ.cont w
      obtain ⟨l', h1', h2'⟩ := hβ'.cont w
      exact ⟨l + l', GlobalTheory.MultMem.sobCont_add h1 h1', fun x => by simp [h2, h2']⟩,
    fun h hh g hg hE w x y hy => by
      simp only [LinearMap.add_apply, hβ.inv h hh g hg hE w x y hy, hβ'.inv h hh g hg hE w x y hy],
    fun u hu w x y hy => by
      simp only [LinearMap.add_apply, hβ.equiv u hu w x y hy, hβ'.equiv u hu w x y hy, mul_add]⟩
  smul_mem' := fun c β hβ =>
    ⟨fun w => by
      obtain ⟨l, h1, h2⟩ := hβ.cont w
      exact ⟨c • l, GlobalTheory.MultMem.sobCont_smul c h1, fun x => by simp [h2]⟩,
    fun h hh g hg hE w x y hy => by simp only [LinearMap.smul_apply, hβ.inv h hh g hg hE w x y hy],
    fun u hu w x y hy => by
      simp only [LinearMap.smul_apply, hβ.equiv u hu w x y hy, smul_eq_mul, mul_left_comm]⟩

end Forms

variable {J : Matrix (Fin n) (Fin n) ℂ} {J₀ : Matrix (Fin m) (Fin m) ℂ} {F : Matrix (Fin n) (Fin m) ℂ}
  {e : Matrix (Fin n) (Fin r) ℂ} {z : Fin n → ℂ}

theorem IsFrame.exists_coords (hf : IsFrame J J₀ F e z) {u : Matrix (Fin n) (Fin n) ℂ} (hu : u ∈ unipRad J e) :
    ∃ a : Fin r → Fin r → ℂ, ∀ j : Fin r, (u - 1) *ᵥ flagVec e z j.succ = e *ᵥ a j := by
  have : ∀ i : Fin (r + 1), ∃ a, (u - 1) *ᵥ flagVec e z i = e *ᵥ a := fun i => by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [flagVec] using hu.2.2 z hf.z_perpE
    · obtain ⟨a, -, ha⟩ := hu.2.1 j
      exact ⟨a, by simpa [flagVec] using ha⟩
  exact ⟨fun j => (this j.succ).choose, fun j => (this j.succ).choose_spec⟩

end GlobalTheory.RealBessel

namespace GlobalTheory.Published

open GlobalTheory.RealBessel

def BesselUniquenessReal : Prop :=
  ∀ (n m r : ℕ) (J : Matrix (Fin n) (Fin n) ℂ) (J₀ : Matrix (Fin m) (Fin m) ℂ) (F : Matrix (Fin n) (Fin m) ℂ)
    (e : Matrix (Fin n) (Fin r) ℂ) (z : Fin n → ℂ), IsFrame J J₀ F e z →
    ∀ χ : Matrix (Fin n) (Fin n) ℂ → ℂ, IsGeneric J e z χ →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UH J) σ → IsIrredOn (UH J) σ →
    ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
      (π₀ : Matrix (Fin m) (Fin m) ℂ → Module.End ℂ W), IsContIrred (UH J₀) π₀ →
      Module.rank ℂ (besselForms J J₀ F e χ σ π₀ (smSub J σ)) ≤ 1


end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
section
noncomputable section

open Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants Formalism.L2.Theta

namespace GlobalTheory.HolDS

variable {n : ℕ}

def IsHolChamber (ε : Fin n → Bool) (lam : Fin n → ℝ) : Prop :=
  ∀ a b, ε a = true → ε b = false → lam b < lam a

def pPlus (ε : Fin n → Bool) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {Z | ∀ a b, ¬ (ε a = true ∧ ε b = false) → Z a b = 0}

def pMinus (ε : Fin n → Bool) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {Z | ∀ b a, ¬ (ε b = false ∧ ε a = true) → Z b a = 0}

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def raisingSpan (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H) :
    Submodule ℂ H :=
  Submodule.span ℂ {w | ∃ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ Z ∈ l, Z ∈ pPlus ε) ∧
    ∃ v ∈ S, w = l.foldr (GlobalTheory.SmVec.dRepC (Jm ε) σ) v}

def IsLowestWeightOver (ε : Fin n → Bool) (lam : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  (∀ (μ : Fin n → ℝ) (S : Submodule ℂ H), IsKTypeOf ε σ μ S →
    ∃ c : Fin n → Fin n → ℕ, (∀ a b, c a b ≠ 0 → ε a = true ∧ ε b = false) ∧
      μ = lowK ε lam + ∑ a, ∑ b, (c a b : ℝ) • root a b) ∧
  (∀ v, IsKFin ε σ v → SmoothVec {X | inG ε X} σ v) ∧
  (∀ Z ∈ pMinus ε, ∀ v ∈ lowKSub ε lam σ, GlobalTheory.SmVec.dRepC (Jm ε) σ Z v = 0) ∧
  ∀ v, IsKFin ε σ v ↔ v ∈ raisingSpan ε σ (lowKSub ε lam σ)

end GlobalTheory.HolDS

namespace GlobalTheory.Published

open GlobalTheory.HolDS

def HolomorphicDiscreteSeries : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), IsHCParam lam → IsHolChamber ε lam →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
      IsDS ε lam σ → IsLowestWeightOver ε lam σ

end GlobalTheory.Published

namespace GlobalTheory.HolDS

open Formalism.L2.NTheta

variable {n : ℕ}

theorem single_mem_pPlus {ε : Fin n → Bool} {a b : Fin n} (ha : ε a = true) (hb : ε b = false) (z : ℂ) :
    Matrix.single a b z ∈ pPlus ε := by
  intro c d h
  rw [Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact h ⟨ha, hb⟩

theorem IsHolChamber.lt {ε : Fin n → Bool} {lam : Fin n → ℝ} (h : IsHolChamber ε lam) (hl : StrictAnti lam)
    {a b : Fin n} (ha : ε a = true) (hb : ε b = false) : a < b :=
  hl.lt_iff_gt.1 (h a b ha hb)

variable {p q : ℕ} {κ : Fin p ⊕ Fin q → ℤ}

theorem strictAnti_holEnt (h : HolOK p q κ) :
    StrictAnti fun c : Fin (p + q) => holEnt p q κ (finSumFinEquiv.symm c) := by
  intro c d hcd
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective c
  obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective d
  simp only [Equiv.symm_apply_apply]
  rw [Fin.lt_def] at hcd
  rcases x with i | i <;> rcases y with j | j <;> simp at hcd
  · have h1 : ((κ (Sum.inl j) : ℤ) : ℚ) ≤ κ (Sum.inl i) := by exact_mod_cast h.1 i j (Fin.le_def.2 (by omega))
    have h2 : ((i : ℕ) : ℚ) < (j : ℕ) := by exact_mod_cast hcd
    simp only [holEnt, Sum.elim_inl]
    linarith
  · exact h.2.2 i j
  · omega
  · have h1 : ((κ (Sum.inr j) : ℤ) : ℚ) ≤ κ (Sum.inr i) := by exact_mod_cast h.2.1 i j (Fin.le_def.2 (by omega))
    have h2 : ((i : ℕ) : ℚ) < (j : ℕ) := by exact_mod_cast hcd
    simp only [holEnt, Sum.elim_inr]
    linarith

theorem enum_holPar (h : HolOK p q κ) {lam : Fin n → ℝ} {ε : Fin n → Bool} (he : IsEnum (holPar p q κ) lam ε) :
    ∃ hn : p + q = n, ∀ x, lam (Fin.cast hn (finSumFinEquiv x)) = holEnt p q κ x ∧
      ε (Fin.cast hn (finSumFinEquiv x)) = Sum.elim (fun _ => true) (fun _ => false) x := by
  obtain ⟨hl, r, hr, hS⟩ := he
  have hra : StrictAnti r := fun a b hab => by
    have := hl hab
    rw [hr, hr] at this
    exact_mod_cast this
  have hs := strictAnti_holEnt h
  have hinj : Function.Injective (holEnt p q κ) := fun x y hxy =>
    finSumFinEquiv.injective (hs.injective (by simpa using hxy))
  have hn : p + q = n := by
    have := congrArg Finset.card hS
    unfold holPar at this
    rw [Finset.card_image_of_injective _ fun x y hxy => hinj (congrArg Prod.fst hxy),
      Finset.card_image_of_injective _ fun x y hxy => hra.injective (congrArg Prod.fst hxy)] at this
    simpa using this
  subst hn
  have hm : ∀ z, (∃ x, (holEnt p q κ x, Sum.elim (fun _ => true) (fun _ => false) x) = z) ↔
      ∃ a, (r a, ε a) = z := fun z => by
    simpa [holPar] using Finset.ext_iff.1 hS z
  have hrr : (fun c : Fin (p + q) => holEnt p q κ (finSumFinEquiv.symm c)) = r := by
    rw [← hs.range_inj hra]
    ext z
    constructor
    · rintro ⟨c, rfl⟩
      obtain ⟨a, ha⟩ := (hm _).1 ⟨finSumFinEquiv.symm c, rfl⟩
      exact ⟨a, congrArg Prod.fst ha⟩
    · rintro ⟨a, rfl⟩
      obtain ⟨x, hx⟩ := (hm _).2 ⟨a, rfl⟩
      exact ⟨finSumFinEquiv x, by simpa using congrArg Prod.fst hx⟩
  refine ⟨rfl, fun x => ?_⟩
  have h1 : r (finSumFinEquiv x) = holEnt p q κ x := by rw [← hrr]; simp
  refine ⟨by rw [Fin.cast_eq_self, hr, h1], ?_⟩
  obtain ⟨y, hy⟩ := (hm _).2 ⟨finSumFinEquiv x, rfl⟩
  obtain rfl : y = x := hinj ((congrArg Prod.fst hy).trans h1)
  exact (congrArg Prod.snd hy).symm

theorem lowK_holPar (h : HolOK p q κ) {lam : Fin n → ℝ} {ε : Fin n → Bool} (he : IsEnum (holPar p q κ) lam ε) :
    ∃ hn : p + q = n, ∀ x, lowK ε lam (Fin.cast hn (finSumFinEquiv x)) = κ x := by
  obtain ⟨rfl, hx⟩ := enum_holPar h he
  simp only [Fin.cast_eq_self] at hx
  refine ⟨rfl, fun x => ?_⟩
  have hc : ∀ P : Fin (p + q) → Prop, ∀ _ : DecidablePred P, (univ.filter P).card =
      (univ.filter fun i : Fin p => P (finSumFinEquiv (Sum.inl i))).card +
        (univ.filter fun j : Fin q => P (finSumFinEquiv (Sum.inr j))).card := by
    intro P _
    simp only [Finset.card_filter]
    rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [Fin.cast_eq_self, lowK, Pi.add_apply, Pi.sub_apply, rhoN, rhoC]
  rw [hc, hc, hc, hc, (hx x).1]
  simp only [(hx _).2]
  rcases x with i | i
  · have h1 : ∀ j : Fin q, Fin.castAdd q i < Fin.natAdd p j := fun j => by
      rw [Fin.lt_def]; simp; omega
    have h2 : ∀ j : Fin q, ¬ Fin.natAdd p j < Fin.castAdd q i := fun j => (h1 j).not_gt
    have h3 : ∀ j j' : Fin p, Fin.castAdd q j < Fin.castAdd q j' ↔ j < j' := fun j j' => by
      rw [Fin.lt_def, Fin.lt_def (a := j)]; simp
    have h4 : (((p - 1 - i : ℕ)) : ℝ) = p - 1 - (i : ℕ) := by
      have := i.2
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
    simp [holEnt, h1, h2, h3, Finset.filter_lt_eq_Ioi, Finset.filter_gt_eq_Iio, h4]
    ring
  · have h1 : ∀ j : Fin p, Fin.castAdd q j < Fin.natAdd p i := fun j => by
      rw [Fin.lt_def]; simp; omega
    have h2 : ∀ j : Fin p, ¬ Fin.natAdd p i < Fin.castAdd q j := fun j => (h1 j).not_gt
    have h3 : ∀ j j' : Fin q, Fin.natAdd p j < Fin.natAdd p j' ↔ j < j' := fun j j' => by
      rw [Fin.lt_def, Fin.lt_def (a := j)]; simp
    have h4 : (((q - 1 - i : ℕ)) : ℝ) = q - 1 - (i : ℕ) := by
      have := i.2
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
    simp [holEnt, h1, h2, h3, Finset.filter_lt_eq_Ioi, Finset.filter_gt_eq_Iio, h4]
    ring

end GlobalTheory.HolDS

namespace GlobalTheory.Published

end GlobalTheory.Published

end
end

