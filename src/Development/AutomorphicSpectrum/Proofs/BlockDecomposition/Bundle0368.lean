module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0360
public import GroundTheory.AutomorphicForms.HarishChandraCentre.VermaCoordEqZeroOfMemNPlusU
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0363
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0030
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0333
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActEqZeroOfMem
section
set_option maxSynthPendingDepth 1

noncomputable section

open GroundTheory.Automorphic.HarishChandra

namespace GlobalTheory.CompanionTheory.PresRho

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ}

theorem rhoVec_sub {i j : Fin n} (h : (j : ℕ) = i + 1) : rhoVec n i - rhoVec n j = 1 := by
  have : (j : ℂ) = (i : ℂ) + 1 := by exact_mod_cast h
  simp only [rhoVec, this]; ring

def sqSpan (n : ℕ) : Submodule ℂ (U n) :=
  Submodule.span ℂ {x | ∃ (u : U n) (i j : Fin n), (j : ℕ) = i + 1 ∧ u * e (j, i) ^ 2 = x}

def Jp (n : ℕ) : Submodule ℂ (U n) := vermaIdeal (rhoVec n) ⊔ sqSpan n

theorem vermaIdeal_le_Jp : vermaIdeal (rhoVec n) ≤ Jp n := le_sup_left

theorem sqSpan_le_Jp : sqSpan n ≤ Jp n := le_sup_right

theorem mul_mem_sqSpan (v : U n) {x : U n} (hx : x ∈ sqSpan n) : v * x ∈ sqSpan n := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, i, j, hij, rfl⟩ := hx
    exact Submodule.subset_span ⟨v * u, i, j, hij, mul_assoc _ _ _⟩
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hx

theorem mul_mem_Jp (v : U n) {x : U n} (hx : x ∈ Jp n) : v * x ∈ Jp n := by
  obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 hx
  rw [mul_add]
  exact Submodule.add_mem _ (vermaIdeal_le_Jp (mul_mem_vermaIdeal _ v hy))
    (sqSpan_le_Jp (mul_mem_sqSpan v hw))

theorem mul_sq_mem_Jp (u : U n) {i j : Fin n} (hij : (j : ℕ) = i + 1) :
    u * e (j, i) ^ 2 ∈ Jp n :=
  sqSpan_le_Jp (Submodule.subset_span ⟨u, i, j, hij, rfl⟩)

def IsAdW (μ : Fin n → ℤ) (x : U n) : Prop :=
  ∀ k, e (k, k) * x - x * e (k, k) = (μ k : ℂ) • x

def LowExp (m : Fin n × Fin n →₀ ℕ) : Prop := ∀ a ∈ m.support, IsLower a

def lowSpan (n : ℕ) : Submodule ℂ (U n) :=
  Submodule.span ℂ {x | ∃ m : Fin n × Fin n →₀ ℕ, LowExp m ∧ canon m = x}

def lowSpanW (μ : Fin n → ℤ) : Submodule ℂ (U n) :=
  Submodule.span ℂ {x | ∃ m : Fin n × Fin n →₀ ℕ, LowExp m ∧ wt m = μ ∧ canon m = x}

def casC (τ : Fin n → ℂ) : ℂ :=
  ∑ a, τ a ^ 2 + ∑ a, ∑ b, if a < b then τ a - τ b else 0

def ht (μ : Fin n → ℤ) : ℤ := ∑ k : Fin n, ((n : ℤ) - 1 - 2 * (k : ℕ)) * μ k

theorem exists_act {A : Type} [AddCommGroup A] [Module ℂ A] (G : Fin n → Fin n → Module.End ℂ A)
    (h : Formalism.REAL.GlRel G) : ∃ φ : U n →ₐ[ℂ] Module.End ℂ A, ∀ i j, φ (e (i, j)) = G i j := by
  let L : gl n →ₗ[ℂ] Module.End ℂ A :=
    { toFun := fun X => ∑ a : Fin n × Fin n, X a.1 a.2 • G a.1 a.2
      map_add' := fun X Y => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun r X => by simp [Finset.smul_sum, smul_smul] }
  have hL : ∀ a : Fin n × Fin n, L (E a) = G a.1 a.2 := by
    intro a
    show ∑ b : Fin n × Fin n, (E a) b.1 b.2 • G b.1 b.2 = _
    rw [Finset.sum_eq_single a]
    · simp [E]
    · intro b _ hb
      have : ¬ (a.1 = b.1 ∧ a.2 = b.2) := fun h => hb (Prod.ext h.1 h.2).symm
      simp [E, Matrix.single_apply, this]
    · simp
  have hE : ∀ a b : Fin n × Fin n, L ⁅E a, E b⁆ = ⁅L (E a), L (E b)⁆ := by
    intro a b
    rw [LieRing.of_associative_ring_bracket, LieRing.of_associative_ring_bracket, E_mul_sub_mul,
      hL, hL, h, map_sub, apply_ite L, apply_ite L, hL, hL, map_zero]
  let ρ : gl n →ₗ⁅ℂ⁆ Module.End ℂ A :=
    { L with
      map_lie' := fun {X Y} => by
        show L ⁅X, Y⁆ = ⁅L X, L Y⁆
        rw [eq_sum_E X, eq_sum_E Y]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [sum_lie, lie_sum, smul_lie, lie_smul, map_sum, map_smul, hE] }
  refine ⟨UniversalEnvelopingAlgebra.lift ℂ ρ, fun i j => ?_⟩
  rw [e, UniversalEnvelopingAlgebra.lift_ι_apply]
  exact hL (i, j)

theorem act_word {A : Type} [AddCommGroup A] [Module ℂ A] {G : Fin n → Fin n → Module.End ℂ A}
    (φ : U n →ₐ[ℂ] Module.End ℂ A) (hφ : ∀ i j, φ (e (i, j)) = G i j)
    (l : List (Fin n × Fin n)) : φ (word l) = (l.map fun p => G p.1 p.2).prod := by
  induction l with
  | nil => simp
  | cons a l ih => rw [word_cons, map_mul, ih, List.map_cons, List.prod_cons, hφ]

theorem glRel_e (n : ℕ) : Formalism.REAL.GlRel (fun i j : Fin n => e (i, j)) :=
  fun a b c d => e_mul_sub_mul (a, b) (c, d)

theorem IsAdW.e_mul {μ : Fin n → ℤ} {x : U n} (hx : IsAdW μ x) (a : Fin n × Fin n) :
    IsAdW (fun k => μ k + rootAt a k) (e a * x) := by
  intro k
  have h1 := e_diag_mul_sub k a
  have h2 := hx k
  have : e (k, k) * (e a * x) - e a * x * e (k, k) =
      (e (k, k) * e a - e a * e (k, k)) * x + e a * (e (k, k) * x - x * e (k, k)) := by
    noncomm_ring
  rw [this, h1, h2, smul_mul_assoc, mul_smul_comm, ← add_smul]
  push_cast; ring_nf

theorem ht_rootAt (a : Fin n × Fin n) :
    ht (rootAt a) = 2 * ((a.2 : ℕ) : ℤ) - 2 * ((a.1 : ℕ) : ℤ) := by
  simp only [ht, rootAt, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

theorem ht_add_rootAt (μ : Fin n → ℤ) (a : Fin n × Fin n) :
    ht (fun k => μ k + rootAt a k) = ht μ + ht (rootAt a) := by
  simp only [ht, mul_add, Finset.sum_add_distrib]

theorem ht_wt (m : Fin n × Fin n →₀ ℕ) :
    ht (wt m) = m.sum fun a c => (c : ℤ) * ht (rootAt a) := by
  simp only [ht, wt, Finsupp.sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem ht_wt_nonpos {m : Fin n × Fin n →₀ ℕ} (hm : LowExp m) : ht (wt m) ≤ 0 := by
  rw [ht_wt]
  refine Finset.sum_nonpos fun a ha => ?_
  have h : (a.2 : ℕ) < a.1 := hm a ha
  show (m a : ℤ) * ht (rootAt a) ≤ 0
  rw [ht_rootAt]
  have : (0 : ℤ) ≤ (m a : ℤ) := by positivity
  nlinarith

theorem act_eq_zero_of_mem {A : Type} [AddCommGroup A] [Module ℂ A]
    (φ : U n →ₐ[ℂ] Module.End ℂ A) (t : A) (hd : ∀ k, φ (e (k, k)) t = rhoVec n k • t)
    (hu : ∀ a : Fin n × Fin n, IsUpper a → φ (e a) t = 0) {x : U n}
    (hx : x ∈ vermaIdeal (rhoVec n)) : φ x t = 0 := by
  obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 hx
  clear hx
  have h1 : φ y t = 0 := by
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, a, ha, rfl⟩ := hx
      simp [hu a ha]
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul r x _ hx => simp [hx]
  have h2 : φ w t = 0 := by
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, k, rfl⟩ := hx
      simp [hd k, Algebra.algebraMap_eq_smul_one]
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul r x _ hx => simp [hx]
  simp [h1, h2]

end GlobalTheory.CompanionTheory.PresRho
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnnSubsetOfMemNhds
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier ValuativeRel
open scoped Topology

namespace GlobalTheory.CompanionTheory.MirFourier

theorem ann_subset_of_mem_nhds {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (hψ : ψ ≠ 1) (n : ℕ)
    {S : Set (Multiplicative (Fin n → k))} (hS : S ∈ 𝓝 (1 : Multiplicative (Fin n → k))) :
    ∃ t : kˣ, (ann ψ n t : Set (Multiplicative (Fin n → k))) ⊆ S := by
  obtain ⟨y, hy⟩ : ∃ y, ψ y ≠ 1 := by
    by_contra h
    push Not at h
    exact hψ (by ext a; simp [h a])
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hy (AddChar.map_zero_eq_one ψ)
  have hS' : {v : Fin n → k | Multiplicative.ofAdd v ∈ S} ∈ 𝓝 (0 : Fin n → k) := hS
  obtain ⟨s, hs⟩ := FourierPi.exists_box_subset hS'
  refine ⟨Units.mk0 y hy0 * s⁻¹, fun x hx => ?_⟩
  have hbox : x.toAdd ∈ FourierPi.box (Fin n) s := by
    intro i _
    show valuation k (x.toAdd i) ≤ valuation k (s : k)
    by_contra hlt
    have hlt' : valuation k (s : k) < valuation k (x.toAdd i) := not_le.mp hlt
    have hxi : x.toAdd i ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hlt'
      exact not_lt_zero hlt'
    have hmem : Multiplicative.ofAdd (Pi.single i (y / x.toAdd i) : Fin n → k) ∈ polyBall n
        (Units.mk0 y hy0 * s⁻¹) := by
      intro j
      by_cases hj : j = i
      · subst hj
        show valuation k ((Pi.single j (y / x.toAdd j) : Fin n → k) j) ≤
          valuation k ((Units.mk0 y hy0 * s⁻¹ : kˣ) : k)
        have hs0 : 0 < valuation k (s : k) :=
          zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr s.ne_zero)
        rw [Pi.single_eq_same, map_div₀, Units.val_mul, map_mul, Units.val_mk0,
          Units.val_inv_eq_inv_val, map_inv₀, div_eq_mul_inv]
        exact mul_le_mul_right ((inv_le_inv₀ (hs0.trans hlt') hs0).mpr hlt'.le) _
      · simp [Pi.single_eq_of_ne hj, cball]
    have h1 := hx _ hmem
    rw [toAdd_ofAdd, single_dotProduct, div_mul_cancel₀ _ hxi] at h1
    exact hy h1
  exact hs hbox

end GlobalTheory.CompanionTheory.MirFourier

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CPoly
section
noncomputable section

open Matrix Finset

namespace GlobalTheory.CompanionTheory.RealCount.Tope

variable {n : ℕ}

abbrev LP (n : ℕ) := AddMonoidAlgebra ℂ (Fin n → ℤ)

def chr (z : Fin n → ℂˣ) : Multiplicative (Fin n → ℤ) →* ℂ where
  toFun μ := ∏ a, ((z a ^ (Multiplicative.toAdd μ a) : ℂˣ) : ℂ)
  map_one' := by simp
  map_mul' μ ν := by
    simp only [toAdd_mul, Pi.add_apply, _root_.zpow_add, Units.val_mul, Finset.prod_mul_distrib]

def evL (z : Fin n → ℂˣ) : LP n →ₐ[ℂ] ℂ := AddMonoidAlgebra.lift ℂ ℂ (Fin n → ℤ) (chr z)

def altL (m : Fin n → ℤ) : LP n :=
  ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) • AddMonoidAlgebra.single (fun i => m (σ i)) (1 : ℂ)

def delZ (n : ℕ) : Fin n → ℤ := fun j => ((n - 1 - (j : ℕ) : ℕ) : ℤ)

def pPL (n : ℕ) : LP n :=
  ∏ a : Fin n, ∏ b : Fin n, (1 + AddMonoidAlgebra.single (Pi.single a 1 - Pi.single b 1 : Fin n → ℤ) (1 : ℂ))

def frL (n : ℕ) : LP n →ₐ[ℂ] LP n :=
  AddMonoidAlgebra.mapDomainAlgHom ℂ ℂ (2 • AddMonoidHom.id (Fin n → ℤ))

def cPoly (s : Finset (Fin n → ℤ)) (c : (Fin n → ℤ) → ℂ) : LP n :=
  ∑ μ ∈ s, AddMonoidAlgebra.single μ (c μ)

end GlobalTheory.CompanionTheory.RealCount.Tope
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliLeviFactorizationSum
section
noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin GlobalTheory.SmGL

namespace GlobalTheory.CompanionTheory.CTFin.CapFactor

theorem two_sum (n : Fin 2 → ℕ) : ∑ i, n i = n 0 + n 1 := Fin.sum_univ_two n

theorem std_zero (n : Fin 2 → ℕ) (h : ∑ i, n i = n 0 + n 1) (i : Fin (n 0)) :
    stdBlocks n h ⟨0, i⟩ = Fin.castAdd (n 1) i := by
  apply Fin.ext
  refine (stdBlocks_val n h 0 i).trans ?_
  simp

theorem std_one (n : Fin 2 → ℕ) (h : ∑ i, n i = n 0 + n 1) (i : Fin (n 1)) :
    stdBlocks n h ⟨1, i⟩ = Fin.natAdd (n 0) i := by
  apply Fin.ext
  refine (stdBlocks_val n h 1 i).trans ?_
  simp

theorem modExp_zero (n : Fin 2 → ℕ) : modExp (fun i => Fin (n i)) 0 = n 1 := by
  have h1 : (Finset.univ.filter fun b : Fin 2 => (0 : Fin 2) < b) = {1} := by decide
  simp [modExp, h1]

theorem modExp_one (n : Fin 2 → ℕ) : modExp (fun i => Fin (n i)) 1 = -(n 0 : ℤ) := by
  have h1 : (Finset.univ.filter fun b : Fin 2 => (1 : Fin 2) < b) = ∅ := by decide
  simp [modExp, h1, Finset.sum_filter]

theorem exists_unip_of_mem {R : Type} [CommRing R] (n : Fin 2 → ℕ) (h : ∑ i, n i = n 0 + n 1)
    {v : GL (Fin (n 0 + n 1)) R} (hv : v ∈ unipRad R (stdBlocks n h)) :
    ∃ x : BlockIx (n 0 + n 1) (n 0) → R, v = unip x := by
  obtain ⟨hp, hd⟩ := mem_unipRad.1 hv
  have hp' := mem_parab_iff.1 hp
  have A : ∀ i j : Fin (n 0), (v : Matrix _ _ R) (Fin.castAdd (n 1) i) (Fin.castAdd (n 1) j) =
      (1 : Matrix (Fin (n 0)) (Fin (n 0)) R) i j := by
    intro i j
    have := hd 0 i j
    rwa [std_zero, std_zero] at this
  have B : ∀ i j : Fin (n 1), (v : Matrix _ _ R) (Fin.natAdd (n 0) i) (Fin.natAdd (n 0) j) =
      (1 : Matrix (Fin (n 1)) (Fin (n 1)) R) i j := by
    intro i j
    have := hd 1 i j
    rwa [std_one, std_one] at this
  have C : ∀ (i : Fin (n 1)) (j : Fin (n 0)), (v : Matrix _ _ R) (Fin.natAdd (n 0) i) (Fin.castAdd (n 1) j) = 0 := by
    intro i j
    have := hp' 1 0 i j (by decide)
    rwa [std_one, std_zero] at this
  refine ⟨fun p => (v : Matrix (Fin (n 0 + n 1)) (Fin (n 0 + n 1)) R) p.1.1 p.1.2, Units.ext ?_⟩
  change (v : Matrix (Fin (n 0 + n 1)) (Fin (n 0 + n 1)) R) = 1 + nilM _
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · have : ¬ (((Fin.castAdd (n 1) i : Fin (n 0 + n 1)) : ℕ) < n 0 ∧ n 0 ≤ ((Fin.castAdd (n 1) j : Fin (n 0 + n 1)) : ℕ)) := by
      simp only [Fin.val_castAdd]; omega
    simp only [Matrix.add_apply, nilM, Matrix.of_apply, dif_neg this, add_zero, A, Matrix.one_apply, Fin.castAdd_inj]
  · have : (((Fin.castAdd (n 1) i : Fin (n 0 + n 1)) : ℕ) < n 0 ∧ n 0 ≤ ((Fin.natAdd (n 0) j : Fin (n 0 + n 1)) : ℕ)) := by
      simp only [Fin.val_castAdd, Fin.val_natAdd]; omega
    have hne : (Fin.castAdd (n 1) i : Fin (n 0 + n 1)) ≠ Fin.natAdd (n 0) j := by
      intro e; have := congrArg Fin.val e; simp only [Fin.val_castAdd, Fin.val_natAdd] at this; omega
    simp only [Matrix.add_apply, nilM, Matrix.of_apply, dif_pos this, Matrix.one_apply, if_neg hne, zero_add]
  · have : ¬ (((Fin.natAdd (n 0) i : Fin (n 0 + n 1)) : ℕ) < n 0 ∧ n 0 ≤ ((Fin.castAdd (n 1) j : Fin (n 0 + n 1)) : ℕ)) := by
      simp only [Fin.val_castAdd, Fin.val_natAdd]; omega
    have hne : (Fin.natAdd (n 0) i : Fin (n 0 + n 1)) ≠ Fin.castAdd (n 1) j := by
      intro e; have := congrArg Fin.val e; simp only [Fin.val_castAdd, Fin.val_natAdd] at this; omega
    simp only [Matrix.add_apply, nilM, Matrix.of_apply, dif_neg this, Matrix.one_apply, if_neg hne, add_zero, C]
  · have : ¬ (((Fin.natAdd (n 0) i : Fin (n 0 + n 1)) : ℕ) < n 0 ∧ n 0 ≤ ((Fin.natAdd (n 0) j : Fin (n 0 + n 1)) : ℕ)) := by
      simp only [Fin.val_natAdd]; omega
    simp only [Matrix.add_apply, nilM, Matrix.of_apply, dif_neg this, add_zero, B, Matrix.one_apply, Fin.natAdd_inj]

def levPair {R : Type} [CommRing R] {n : Fin 2 → ℕ} (g : GL (Fin (n 0)) R × GL (Fin (n 1)) R) :
    ∀ i : Fin 2, GL (Fin (n i)) R
  | ⟨0, _⟩ => g.1
  | ⟨1, _⟩ => g.2

theorem lev_eq_leviEmb {R : Type} [CommRing R] (n : Fin 2 → ℕ) (h : ∑ i, n i = n 0 + n 1)
    (g : GL (Fin (n 0)) R × GL (Fin (n 1)) R) :
    lev R (n 0) (n 1) g = leviEmb R (stdBlocks n h) (levPair g) := by
  have p0 : ∀ i : Fin (n 0), two (stdSum (rfl : n 0 + n 1 = n 0 + n 1)) ⟨false, i⟩ = stdBlocks n h ⟨0, i⟩ := fun i => by
    rw [std_zero, two_false]; exact Fin.ext (by simp)
  have p1 : ∀ i : Fin (n 1), two (stdSum (rfl : n 0 + n 1 = n 0 + n 1)) ⟨true, i⟩ = stdBlocks n h ⟨1, i⟩ := fun i => by
    rw [std_one, two_true]; exact Fin.ext (by simp)
  have key : ∀ (a b : Fin 2) (i : Fin (n a)) (j : Fin (n b)),
      (lev R (n 0) (n 1) g : Matrix _ _ R) (stdBlocks n h ⟨a, i⟩) (stdBlocks n h ⟨b, j⟩) =
      (leviEmb R (stdBlocks n h) (levPair g) : Matrix _ _ R) (stdBlocks n h ⟨a, i⟩) (stdBlocks n h ⟨b, j⟩) := by
    refine Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨fun i j => ?_, fun i j => ?_⟩,
      Fin.forall_fin_two.2 ⟨fun i j => ?_, fun i j => ?_⟩⟩
    · rw [leviEmb_apply_same, ← p0, ← p0]
      exact leviEmb_apply_same R (two _) (leviTwo R _ _ g) false i j
    · rw [leviEmb_apply_ne R _ _ (a := 0) (b := 1) (by decide), ← p0, ← p1]
      exact leviEmb_apply_ne R (two _) (leviTwo R _ _ g) (a := false) (b := true) (by simp) i j
    · rw [leviEmb_apply_ne R _ _ (a := 1) (b := 0) (by decide), ← p0, ← p1]
      exact leviEmb_apply_ne R (two _) (leviTwo R _ _ g) (a := true) (b := false) (by simp) i j
    · rw [leviEmb_apply_same, ← p1, ← p1]
      exact leviEmb_apply_same R (two _) (leviTwo R _ _ g) true i j
  apply Units.ext
  ext i j
  obtain ⟨⟨a, i⟩, rfl⟩ := (stdBlocks n h).surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := (stdBlocks n h).surjective j
  exact key a b i j

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem qdet_mem {A : Type} [Ring A] [Algebra ℂ A] {a : ℕ} (S : Subalgebra ℂ A) (X : Fin a → Fin a → A)
    (hX : ∀ i j, X i j ∈ S) (u : ℂ) : Formalism.REAL.qdet X u ∈ S := by
  have := map_qdet S.val (fun i j => (⟨X i j, hX i j⟩ : S)) u
  simp only [Subalgebra.coe_val] at this
  rw [← this]
  exact (Formalism.REAL.qdet _ _ : S).2

theorem Eop_commute_blocks (r s : ℕ) (τ : E →+* ℂ) (i j : Fin r) (k l : Fin s) :
    Commute (Eop (a := r + s) τ (Fin.castAdd s i) (Fin.castAdd s j))
      (Eop (a := r + s) τ (Fin.natAdd r k) (Fin.natAdd r l)) := by
  have h := glRel_Eop (a := r + s) τ (Fin.castAdd s i) (Fin.castAdd s j) (Fin.natAdd r k) (Fin.natAdd r l)
  have h1 : (Fin.castAdd s j : Fin (r + s)) ≠ Fin.natAdd r k := by
    intro e; have := congrArg Fin.val e; simp only [Fin.val_castAdd, Fin.val_natAdd] at this; omega
  have h2 : (Fin.natAdd r l : Fin (r + s)) ≠ Fin.castAdd s i := by
    intro e; have := congrArg Fin.val e; simp only [Fin.val_castAdd, Fin.val_natAdd] at this; omega
  rw [if_neg h1, if_neg h2, sub_zero] at h
  exact sub_eq_zero.1 h

theorem capR_commute_capS (r s : ℕ) (τ : E →+* ℂ) (u v : ℂ) : Commute (capR r s τ u) (capS r s τ v) := by
  let T : Set (Module.End ℂ (Sm E (r + s))) :=
    Set.range fun kl : Fin s × Fin s => Eop (a := r + s) τ (Fin.natAdd r kl.1) (Fin.natAdd r kl.2)
  have h1 : capR r s τ u ∈ Subalgebra.centralizer ℂ T := by
    refine qdet_mem _ _ (fun i j => ?_) _
    rw [Subalgebra.mem_centralizer_iff]
    rintro _ ⟨kl, rfl⟩
    exact (Eop_commute_blocks r s τ i j kl.1 kl.2).symm.eq
  have h2 : capS r s τ v ∈ Subalgebra.centralizer ℂ {capR r s τ u} := by
    refine qdet_mem _ _ (fun k l => ?_) _
    rw [Subalgebra.mem_centralizer_iff]
    rintro _ rfl
    exact ((Subalgebra.mem_centralizer_iff ℂ).1 h1 _ ⟨(k, l), rfl⟩).symm
  exact ((Subalgebra.mem_centralizer_iff ℂ).1 h2 _ rfl)

theorem capelli_levi_factorization (n : Fin 2 → ℕ) (τ : E →+* ℂ) (u : ℂ) (F : Sm E (n 0 + n 1))
    (hF : ∀ (x : BlockIx (n 0 + n 1) (n 0) → Ad E) (g : GA E (n 0 + n 1)), F.1 (unip x * g) = F.1 g)
    (m : GA E (n 0) × GA E (n 1)) :
    (cap (a := n 0 + n 1) τ u F).1 (lev (Ad E) (n 0) (n 1) m) =
      (capS (n 0) (n 1) τ (u + (n 0 : ℂ) / 2) (capR (n 0) (n 1) τ (u - (n 1 : ℂ) / 2) F)).1
        (lev (Ad E) (n 0) (n 1) m) := by
  have h : ∑ i, n i = n 0 + n 1 := two_sum n
  let S : Subalgebra ℂ (Module.End ℂ (Sm E (n 0 + n 1))) :=
    Algebra.adjoin ℂ (Set.range fun pq : Fin (n 0 + n 1) × Fin (n 0 + n 1) => Eop τ pq.1 pq.2)
  have hSE : ∀ p q, Eop τ p q ∈ S := fun p q => Algebra.subset_adjoin ⟨(p, q), rfl⟩
  have hSL : S ≤ GlobalTheory.SpehInfChar.leftInvAlg (unipRad (Ad E) (stdBlocks n h)) :=
    Algebra.adjoin_le (by rintro _ ⟨pq, rfl⟩; exact GlobalTheory.SpehInfChar.Eop_mem_leftInvAlg _ τ pq.1 pq.2)
  let X : Fin (n 0 + n 1) → Fin (n 0 + n 1) → S := fun p q => ⟨Eop τ p q, hSE p q⟩
  have hX : Formalism.REAL.GlRel X := fun a b c' d => Subtype.ext (by
    have := glRel_Eop (a := n 0 + n 1) τ a b c' d
    split_ifs at this ⊢ <;> simpa [X] using this)
  have key := GlobalTheory.SpehInfChar.qdet_sub_blocks_mem S n h X hX u
  have hB0 : Formalism.REAL.qdet (fun p q : Fin (n 0) => Eop (a := n 0 + n 1) τ (stdBlocks n h ⟨0, p⟩) (stdBlocks n h ⟨0, q⟩))
      (u + ((n 0 : ℂ) - 1) / 2 - (modExp (fun i => Fin (n i)) 0 : ℂ) / 2) = capR (n 0) (n 1) τ (u - (n 1 : ℂ) / 2) := by
    have e1 : (fun p q : Fin (n 0) => Eop (a := n 0 + n 1) τ (stdBlocks n h ⟨0, p⟩) (stdBlocks n h ⟨0, q⟩)) =
        fun p q => Eop (a := n 0 + n 1) τ (Fin.castAdd (n 1) p) (Fin.castAdd (n 1) q) := by
      funext p q
      rw [std_zero, std_zero]
    rw [e1, modExp_zero, capR]
    congr 1
    push_cast
    ring
  have hB1 : Formalism.REAL.qdet (fun p q : Fin (n 1) => Eop (a := n 0 + n 1) τ (stdBlocks n h ⟨1, p⟩) (stdBlocks n h ⟨1, q⟩))
      (u + ((n 1 : ℂ) - 1) / 2 - (modExp (fun i => Fin (n i)) 1 : ℂ) / 2) = capS (n 0) (n 1) τ (u + (n 0 : ℂ) / 2) := by
    have e1 : (fun p q : Fin (n 1) => Eop (a := n 0 + n 1) τ (stdBlocks n h ⟨1, p⟩) (stdBlocks n h ⟨1, q⟩)) =
        fun p q => Eop (a := n 0 + n 1) τ (Fin.natAdd (n 0) p) (Fin.natAdd (n 0) q) := by
      funext p q
      rw [std_one, std_one]
    rw [e1, modExp_one, capS]
    congr 1
    push_cast
    ring
  have hval : S.val (List.ofFn fun i : Fin 2 => Formalism.REAL.qdet (fun p q : Fin (n i) => X (stdBlocks n h ⟨i, p⟩) (stdBlocks n h ⟨i, q⟩))
      (u + ((n i : ℂ) - 1) / 2 - (modExp (fun i => Fin (n i)) i : ℂ) / 2)).prod =
      capR (n 0) (n 1) τ (u - (n 1 : ℂ) / 2) * capS (n 0) (n 1) τ (u + (n 0 : ℂ) / 2) := by
    rw [map_list_prod, List.map_ofFn, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
    simp only [Function.comp_apply, List.prod_cons, List.prod_nil, mul_one, Fin.succ_zero_eq_one]
    rw [← hB0, ← hB1, map_qdet, map_qdet]
    rfl
  have hcap : S.val (Formalism.REAL.qdet X (u + (((n 0 + n 1 : ℕ) : ℂ) - 1) / 2)) = cap τ u := by
    rw [map_qdet]
    rfl
  have hψ : ∀ v ∈ unipRad (Ad E) (stdBlocks n h), ∀ g, F.1 (v * g) = F.1 g := fun v hv g => by
    obtain ⟨x, rfl⟩ := exists_unip_of_mem n h hv
    exact hF x g
  rw [lev_eq_leviEmb n h m]
  set ℓ := leviEmb (Ad E) (stdBlocks n h) (levPair m) with hℓ
  let L : S →ₗ[ℂ] ℂ :=
    { toFun := fun w => ((w : Module.End ℂ (Sm E (n 0 + n 1))) F).1 ℓ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hker : Submodule.span ℂ {y : S | ∃ (p q : Fin (n 0 + n 1)) (w : S), blk (stdBlocks n h) p < blk (stdBlocks n h) q ∧ y = X p q * w} ≤
      LinearMap.ker L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨p, q, w, hpq, rfl⟩
    change (Eop τ p q ((w : Module.End ℂ (Sm E (n 0 + n 1))) F)).1 ℓ = 0
    exact GlobalTheory.SpehInfChar.Eop_leviEmb_eq_zero E n h _ (hSL w.2 F hψ) τ p q hpq _
  have h1 := hker key
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at h1
  have hL : ∀ w : S, L w = ((S.val w) F).1 ℓ := fun _ => rfl
  rw [hL, hL, hcap, hval] at h1
  rw [h1, (capR_commute_capS (n 0) (n 1) τ _ _).eq]
  rfl

theorem cap_levi : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (r s : ℕ) (τ : E →+* ℂ) (u : ℂ)
    (F : Sm E (r + s)), (∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip x * g) = F.1 g) →
    ∀ m : GA E r × GA E s, (cap (a := r + s) τ u F).1 (lev (Ad E) r s m) =
      (capS r s τ (u + (r : ℂ) / 2) (capR r s τ (u - (s : ℂ) / 2) F)).1 (lev (Ad E) r s m) := by
  intro E _ _ _ r s τ u F hF m
  exact capelli_levi_factorization ![r, s] τ u F hF m

end GlobalTheory.CompanionTheory.CTFin.CapFactor

end
end

