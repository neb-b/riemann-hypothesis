module

public import Development.EtaleCohomology.DivisorCycles.OpenCoset
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0010

@[expose] public section

-- bundled from Development.EtaleCohomology.DivisorCycles.CycleCount
section
open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb

def Proj : Prop := ∀ (C : Type) [Field C] (N n : ℕ) (X : Mat C N) (e : Fin n → C), Function.Injective e → Deg n X →
  (∀ i, X.charpoly.IsRoot (e i)) →
  ∃ p : Fin n → Mat C N, Sys p ∧ X = ∑ i, e i • p i ∧ ∀ i, p i ∈ Algebra.adjoin C ({X} : Set (Mat C N))

def Grade : Prop := ∀ (C : Type) [Field C] [CharZero C] (N n : ℕ) (p : Fin n → Mat C N) (e : Fin n → C)
  (g : Submodule C (Mat C N)), Sys p → IsLac e →
  (∀ Y ∈ g, (∑ i, e i • p i) * Y - Y * (∑ i, e i • p i) ∈ g) → ∀ Y ∈ g, ∀ i j, i ≠ j → p i * Y * p j ∈ g

def CycleCount : Prop := ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (N n : ℕ) (p : Fin n → Mat C N)
  (y : Mat C N) (π : Equiv.Perm (Fin n)), Sys p → IsUnit y → (∀ j, y * p j = p (π j) * y) → Deg n y → Disj y π p →
  HasEig n y ∧ ∀ i, π i = i → ∃ c : C, y * p i = c • p i

def DiagScalar : Prop := ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (N n : ℕ) (p : Fin n → Mat C N)
  (e : Fin n → C) (Y : Mat C N), Sys p → Function.Injective e → (∀ i, Y * p i = p i * Y) →
  (∀ s : C, Deg n (s • Y + ∑ i, e i • p i)) → ∀ i, ∃ c : C, Y * p i = c • p i

def AlgStruct : Prop := ∀ (C : Type) [Field C] (N n : ℕ) (p : Fin n → Mat C N) (g : Submodule C (Mat C N)), Sys p →
  (∀ Y ∈ g, ∀ Z ∈ g, Y * Z - Z * Y ∈ g) → (∀ Y ∈ g, ∀ i j, i ≠ j → p i * Y * p j ∈ g) →
  (∀ Y ∈ g, (∀ i, Y * p i = p i * Y) → ∀ i, ∃ c : C, Y * p i = c • p i) →
  ∀ a ∈ Algebra.adjoin C (g : Set (Mat C N)),
    (∀ i j, i ≠ j → p i * a * p j ∈ g) ∧ ∀ i, ∃ c : C, p i * a * p i = c • p i

def Semis : Prop := ∀ (Γ C : Type) [Group Γ] [Field C] (N : ℕ) (ρ : Γ →* GL (Fin N) C) (A : Subalgebra C (Mat C N)),
  IsSSMat ρ → Normd ρ A → Keeps ρ A → NoNil A

def MatrixUnits₂ : Prop := ∀ (C : Type) [Field C] (N n : ℕ) (A : Subalgebra C (Mat C N)) (p : Fin n → Mat C N),
  Sys p → Corner A p → NoNil A → ∃ E, MUnits A p E

def IdemConj : Prop := ∀ (C : Type) [Field C] [CharZero C] (N n : ℕ) (A : Subalgebra C (Mat C N))
  (p q : Fin n → Mat C N), Sys p → Corner A p → Sys q → Corner A q → NoNil A →
  ∃ v ∈ A, IsUnit v ∧ ∃ π : Equiv.Perm (Fin n), (∀ j, v * p j = q (π j) * v) ∧
    ∀ i, (∃ a ∈ A, q i * a * p i ≠ 0) → π i = i

def UnitFactorization : Prop := ∀ (C : Type) [Field C] (N n : ℕ) (A : Subalgebra C (Mat C N)) (p : Fin n → Mat C N)
  (E : Fin n → Fin n → Mat C N), Sys p → MUnits A p E → ∀ v ∈ A, IsUnit v →
  ∃ u ∈ Tv A p, ∃ d : Fin n → C, (∀ j, d j ≠ 0) ∧ v = u * ∑ j, d j • p j

def GenSpec : Prop := ∀ (C : Type) [Field C] (N n : ℕ) (p : Fin n → Mat C N) (x : Mat C N) (π : Equiv.Perm (Fin n)),
  Sys p → IsUnit x → (∀ j, x * p j = p (π j) * x) → ∃ B : Set C, B.Finite ∧ ∀ τ : Fin n → C, (∀ j, τ j ≠ 0) →
    MulLac τ B → Disj (x * ∑ j, τ j • p j) π p

def Struct : Prop := ∀ (Γ C : Type) [Group Γ] [Field C] [IsAlgClosed C] [CharZero C] (N n : ℕ)
  (ρ : Γ →* GL (Fin N) C) (X : Mat C N) (e : Fin n → C), IsSSMat ρ → (∀ g, Deg n (ρ g : Mat C N)) → X ∈ lie ρ →
  IsLac e → (∀ i, X.charpoly.IsRoot (e i)) → ∃ p, Good ρ e p

def Key : Prop := ∀ (Γ C : Type) [Group Γ] [Field C] [IsAlgClosed C] [CharZero C] (N n : ℕ)
  (ρ : Γ →* GL (Fin N) C) (e : Fin n → C) (p : Fin n → Mat C N), (∀ g, Deg n (ρ g : Mat C N)) → IsLac e → Good ρ e p →
  ∀ U : Subgroup Γ, U.Normal → U.FiniteIndex → ∀ g,
    (∃ m ∈ Zcl (img ρ U : Set (Mat C N)), HasEig n ((ρ g : Mat C N) * m)) ∧
    ∀ i, (∃ a ∈ env ρ, p i * a * (ρ g : Mat C N) * p i ≠ 0) → ∃ w ∈ env ρ, p i * (ρ g : Mat C N) = p i * w

def BigCorner : Prop := ∀ (Γ C : Type) [Group Γ] [Field C] (N n : ℕ) (ρ : Γ →* GL (Fin N) C)
  (A : Subalgebra C (Mat C N)) (p : Fin n → Mat C N), Corner A p → Normd ρ A → Keeps ρ A →
  (∀ g i, (∃ a ∈ A, p i * a * (ρ g : Mat C N) * p i ≠ 0) → ∃ w ∈ A, p i * (ρ g : Mat C N) = p i * w) →
  ∃ R : Subalgebra C (Mat C N), (∀ g, (ρ g : Mat C N) ∈ R) ∧ Corner R p ∧ Normd ρ R ∧ Keeps ρ R

def Rep : Prop := ∀ (Γ C : Type) [Group Γ] [Field C] (N n : ℕ) (ρ : Γ →* GL (Fin N) C) (R : Subalgebra C (Mat C N))
  (p : Fin n → Mat C N) (E : Fin n → Fin n → Mat C N), Sys p → MUnits R p E → (∀ g, (ρ g : Mat C N) ∈ R) →
  ∃ r A B, Sub (n := n) ρ r A B

def DenseAlg : Prop := ∀ (Γ C : Type) [Group Γ] [Field C] [CharZero C] (N n : ℕ) (ρ : Γ →* GL (Fin N) C)
  (r : Γ →* GL (Fin n) C) A B, Sub ρ r A B → ∀ (U : Subgroup Γ) (g : Γ), ∀ m ∈ Zcl (img ρ U : Set (Mat C N)),
  HasEig n ((ρ g : Mat C N) * m) → ∃ u ∈ U, (r (g * u) : Mat C n).charpoly.Separable

def DegAll : Prop := ∀ (Γ K : Type) [Group Γ] [TopologicalSpace Γ] [Field K] [TopologicalSpace K]
  [IsTopologicalRing K] [T2Space K] (N n : ℕ) (ρ : Γ →* GL (Fin N) K), Continuous (fun g => (ρ g : Mat K N)) →
  ∀ S : Set Γ, Dense S → (∀ s ∈ S, Deg n (ρ s : Mat K N)) → ∀ g, Deg n (ρ g : Mat K N)

def FinSub : Prop := ∀ (Γ K : Type) [Group Γ] [Field K] (N n : ℕ) (ρ : Γ →* GL (Fin N) K) (r : Γ →* GL (Fin n) K) A B,
  Sub ρ r A B → IsSSMat ρ → IsSSMat r ∧ A.rank = n ∧ (∀ g, (r g : Mat K n) = B * (ρ g : Mat K N) * A) ∧
  ∀ g (q : Polynomial K), Polynomial.aeval (ρ g : Mat K N) q = 0 ↔ Polynomial.aeval (r g : Mat K n) q = 0

def FinEmbed : Prop := ∀ (Γ K : Type) [Group Γ] [Field K] (N n : ℕ) (ρ : Γ →* GL (Fin N) K) (r : Γ →* GL (Fin n) K) A B,
  Sub ρ r A B → IsSSMat ρ → IsSSMat r →
  ∃ (k : ℕ) (T : Fin k → Matrix (Fin n) (Fin N) K) (T' : Fin k → Matrix (Fin N) (Fin n) K),
    (∀ j g, T j * (ρ g : Mat K N) = (r g : Mat K n) * T j) ∧ (∀ j g, (ρ g : Mat K N) * T' j = T' j * (r g : Mat K n)) ∧
    ∑ j, T' j * T j = 1

def FinDense : Prop := ∀ (Γ K : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
  [Field K] [CharZero K] [TopologicalSpace K] [IsTopologicalRing K] [T2Space K] (n : ℕ) (r : Γ →* GL (Fin n) K),
  Continuous (fun g => (r g : Mat K n)) →
  (∀ U : Subgroup Γ, U.Normal → U.FiniteIndex → ∀ g, ∃ u ∈ U, (r (g * u) : Mat K n).charpoly.Separable) →
  IsOpen {g | (r g : Mat K n).charpoly.Separable} ∧ Dense {g | (r g : Mat K n).charpoly.Separable}

def FinPoly : Prop := ∀ (K : Type) [Field K] [IsAlgClosed K] (n : ℕ) (x : Mat K n) (P : Polynomial K), P.Monic →
  P.natDegree = n → Polynomial.aeval x P = 0 → (x.charpoly.Separable → x.charpoly = P) ∧
  (ProdGen n P → x.det = (-1) ^ n * P.coeff 0 → x.charpoly = P)

end LateralTheory.DivDb
end

-- bundled from Development.EtaleCohomology.DivisorCycles.OpenCosetPf
section
open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div

namespace LateralTheory.DivDb.OpenCosetPf
open LateralTheory.DivDb

theorem main (hChain : Chain) : OpenCoset :=
  _root_.UpperTheory.Reformulated.B.Qn18.main hChain

end LateralTheory.DivDb.OpenCosetPf

namespace LateralTheory.DivDb
theorem OpenCoset_of (hChain : Chain) : OpenCoset := OpenCosetPf.main hChain
end LateralTheory.DivDb
end

-- bundled from Development.EtaleCohomology.DivisorCycles.SepPolyProof
section
open Matrix Polynomial
namespace LateralTheory.DivDb.SepPolyProof

noncomputable def disc (C : Type) [Field C] (n : ℕ) : MvPolynomial (Fin n × Fin n) C :=
  resultant (charpoly.univ C (Fin n)) (derivative (charpoly.univ C (Fin n))) n (n - 1)

theorem univ_map_ev {C : Type} [Field C] {n : ℕ} (x : Mat C n) :
    (charpoly.univ C (Fin n)).map (MvPolynomial.eval (fun p : Fin n × Fin n => x p.1 p.2)) = x.charpoly := by
  have h := charpoly.univ_map_eval₂Hom (Fin n) (RingHom.id C) (fun p : Fin n × Fin n => x p.1 p.2)
  have hx : (Matrix.of (fun p : Fin n × Fin n => x p.1 p.2).curry) = x := by ext i j; rfl
  rw [hx] at h
  exact h

theorem ev_disc {C : Type} [Field C] [CharZero C] {n : ℕ} (x : Mat C n) :
    ev x (disc C n) = resultant x.charpoly (derivative x.charpoly) := by
  unfold ev disc
  rw [← resultant_map_map, ← derivative_map, univ_map_ev]
  have h1 : x.charpoly.natDegree = n := by simpa using charpoly_natDegree_eq_dim x
  rw [natDegree_derivative, h1]

end LateralTheory.DivDb.SepPolyProof

namespace LateralTheory.DivDb
open LateralTheory.DivDb.SepPolyProof in
theorem SepPoly_of : SepPoly := by
  intro C _ _ n
  refine ⟨disc C n, fun x => ?_⟩
  rw [ev_disc, Ne, resultant_eq_zero_iff]
  have h0 : x.charpoly ≠ 0 := (charpoly_monic x).ne_zero
  simp only [ne_eq, h0, not_false_eq_true, true_or, true_and, not_not]
  rfl
end LateralTheory.DivDb
end

-- bundled from Development.EtaleCohomology.DivisorCycles.SpecLiePf
section
open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.SpecLiePf
open LateralTheory.DivDb

theorem SpecLie_of (hS : SpecPt) : SpecLie := by
  intro Γ K K' _ _ _ _ _ N n ρ X e hX hL hR
  classical
  let x : (Fin N × Fin N) ⊕ Fin n → K' := Sum.elim (fun p => X p.1 p.2) e
  let gAB : Finset (Fin n) → Finset (Fin n) → MvPolynomial ((Fin N × Fin N) ⊕ Fin n) K := fun A B =>
    MvPolynomial.C (B.card : K) * ∑ i ∈ A, MvPolynomial.X (Sum.inr i) -
      MvPolynomial.C (A.card : K) * ∑ i ∈ B, MvPolynomial.X (Sum.inr i)
  let G : Set (MvPolynomial ((Fin N × Fin N) ⊕ Fin n) K) :=
    {g | ∃ A B : Finset (Fin n), A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧ g = gAB A B}
  have hGf : G.Finite :=
    (Set.finite_range (fun AB : Finset (Fin n) × Finset (Fin n) => gAB AB.1 AB.2)).subset
      (by rintro g ⟨A, B, -, -, -, rfl⟩; exact ⟨(A, B), rfl⟩)
  have haG : ∀ g ∈ G, MvPolynomial.aeval x g ≠ 0 := by
    rintro g ⟨A, B, hA, hB, hAB, rfl⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [gAB, map_sub, map_mul, map_sum, MvPolynomial.aeval_X, x, Sum.elim_inr, map_natCast]
    exact sub_ne_zero.mpr (hL A B hA hB hAB)
  obtain ⟨y, hy, hyG⟩ := hS K K' _ x G hGf haG
  refine ⟨Matrix.of fun a b => y (Sum.inl (a, b)), fun i => y (Sum.inr i), ?_, ?_, ?_⟩
  · change ∀ f ∈ Van (img ρ ⊤ : Set (Mat K N)), dAt f 1 _ = 0
    intro f hf
    have hf' : ∀ g : Γ, MvPolynomial.eval (fun p : Fin N × Fin N => (ρ g : Matrix (Fin N) (Fin N) K) p.1 p.2) f = 0 :=
      fun g => hf _ ⟨g, trivial, rfl⟩
    have h0 := hX f hf'
    let L : MvPolynomial ((Fin N × Fin N) ⊕ Fin n) K := ∑ p : Fin N × Fin N,
      MvPolynomial.C (MvPolynomial.eval (fun q : Fin N × Fin N => (1 : Matrix (Fin N) (Fin N) K) q.1 q.2)
        (MvPolynomial.pderiv p f)) * MvPolynomial.X (Sum.inl p)
    have hxL : MvPolynomial.aeval x L = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        simpa only [L, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, x, Sum.elim_inl] using h0
    have h1 := hy L hxL
    set_option synthInstance.maxHeartbeats 100000 in
      simpa only [L, dAt, ev, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, Matrix.of_apply] using h1
  · intro A B hA hB hAB
    have h1 := hyG _ ⟨A, B, hA, hB, hAB, rfl⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [gAB, map_sub, map_mul, map_sum, MvPolynomial.eval_C, MvPolynomial.eval_X] at h1
    exact sub_ne_zero.mp h1
  · intro i
    let M : Matrix (Fin N) (Fin N) (MvPolynomial ((Fin N × Fin N) ⊕ Fin n) K) :=
      Matrix.scalar (Fin N) (MvPolynomial.X (Sum.inr i)) - Matrix.of (fun a b => MvPolynomial.X (Sum.inl (a, b)))
    have hx : MvPolynomial.aeval x M.det = 0 := by
      have e1 : MvPolynomial.aeval x M.det = ((MvPolynomial.aeval x).toRingHom.mapMatrix M).det := by
        rw [← RingHom.map_det]; rfl
      have e2 : (MvPolynomial.aeval x).toRingHom.mapMatrix M = Matrix.scalar (Fin N) (e i) - X := by
        ext a b
        by_cases h : a = b
        · subst h; simp [M, x]
        · simp [M, x, h]
      rw [e1, e2, ← Matrix.eval_charpoly]; exact hR i
    have h1 := hy _ hx
    have e1 : MvPolynomial.eval y M.det = ((MvPolynomial.eval y).mapMatrix M).det := by
      rw [← RingHom.map_det]
    have e2 : (MvPolynomial.eval y).mapMatrix M =
        Matrix.scalar (Fin N) (y (Sum.inr i)) - Matrix.of (fun a b => y (Sum.inl (a, b))) := by
      ext a b
      by_cases h : a = b
      · subst h; simp [M]
      · simp [M, h]
    rw [e1, e2] at h1
    change Polynomial.eval (y (Sum.inr i)) (Matrix.charpoly (Matrix.of fun a b => y (Sum.inl (a, b)))) = 0
    rw [Matrix.eval_charpoly]; exact h1

end LateralTheory.DivDb.SpecLiePf
end

-- bundled from Development.EtaleCohomology.DivisorCycles.SpecPtPf
section
namespace LateralTheory.DivDb.SpecPtPf

theorem SpecPt_of : LateralTheory.DivDb.SpecPt := by
  intro C R σ _ _ _ _ _ _ x G hG hx
  classical
  let I : Ideal (MvPolynomial σ C) := RingHom.ker (MvPolynomial.aeval (R := C) x)
  have hI : I.IsPrime := RingHom.ker_isPrime _
  let P : MvPolynomial σ C := ∏ g ∈ hG.toFinset, g
  have hP : MvPolynomial.aeval x P ≠ 0 := by
    simp only [P, map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun g hg => hx g (hG.mem_toFinset.mp hg)
  have hPI : P ∉ I.radical := by
    rw [hI.radical]; exact hP
  rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := C), MvPolynomial.mem_vanishingIdeal_iff] at hPI
  push Not at hPI
  obtain ⟨y, hy, hyP⟩ := hPI
  rw [MvPolynomial.mem_zeroLocus_iff] at hy
  refine ⟨y, fun f hf => ?_, fun g hg => ?_⟩
  · have := hy f (RingHom.mem_ker.mpr hf)
    simpa [MvPolynomial.coe_aeval_eq_eval] using this
  · simp only [P, map_prod] at hyP
    exact (Finset.prod_ne_zero_iff.mp hyP) g (hG.mem_toFinset.mpr hg)

end LateralTheory.DivDb.SpecPtPf
end

-- bundled from Development.EtaleCohomology.DivisorCycles.TanLiePf
section
open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.TanLiePf
open LateralTheory.DivDb

theorem DX_X {C : Type} [Field C] {N : ℕ} (Y : Mat C N) (p : Fin N × Fin N) :
    DX Y (MvPolynomial.X p) = ∑ k, MvPolynomial.C (Y p.1 k) * MvPolynomial.X (k, p.2) := by
  simp [DX, MvPolynomial.mkDerivation_X]

theorem DX_comm {C : Type} [Field C] {N : ℕ} (Y Z : Mat C N) :
    ⁅DX Y, DX Z⁆ = DX (Z * Y - Y * Z) := by
  apply MvPolynomial.derivation_ext
  intro p
  rw [Derivation.commutator_apply, DX_X, DX_X, DX_X]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, MvPolynomial.C_mul', map_smul, DX_X, Finset.smul_sum, smul_smul]
  simp only [Matrix.sub_apply, Matrix.mul_apply, ← Finset.sum_sub_distrib]
  simp only [sub_smul, Finset.sum_smul, ← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  rw [Derivation.map_smul, Derivation.map_smul, DX_X, DX_X]
  simp only [MvPolynomial.C_mul', Finset.smul_sum, smul_smul, ← Finset.sum_sub_distrib]

end LateralTheory.DivDb.TanLiePf

namespace LateralTheory.DivDb
open LateralTheory.DivDb.TanLiePf

theorem TanLie_of (hF : TanField) : TanLie := by
  intro C _ N S Y hY Z hZ
  have hY' := (hF C N S Y).1 hY
  have hZ' := (hF C N S Z).1 hZ
  have h : Z * Y - Y * Z ∈ Tan (S : Set (Mat C N)) := by
    rw [hF C N S]
    intro f hf
    rw [← DX_comm, Derivation.commutator_apply]
    intro x hx
    have h1 := hY' _ (hZ' f hf) x hx
    have h2 := hZ' _ (hY' f hf) x hx
    simp only [ev, map_sub] at h1 h2 ⊢
    rw [h1, h2, sub_zero]
  have := (Tan (S : Set (Mat C N))).neg_mem h
  simpa using this

end LateralTheory.DivDb
end

-- bundled from Development.EtaleCohomology.DivisorCycles.TangentFieldExtension
section
open Matrix

namespace LateralTheory.DivDb.TangentFieldExtension
open LateralTheory.DivDb

variable {C : Type} [Field C] {N : ℕ}

theorem ev_DX (Y x : Mat C N) (f : MP C N) : ev x (DX Y f) = dAt f x (Y * x) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [dAt, ev, DX, MvPolynomial.derivation_C]
  | add f g hf hg =>
    rw [map_add (f := _), ev, map_add (f := _), ← ev, ← ev, hf, hg]
    simp only [dAt, map_add (f := _), ev, add_mul, Finset.sum_add_distrib]
  | mul_X f q hf =>
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    simp only [ev, map_add (f := _), map_mul] at hf ⊢
    rw [hf]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [DX, MvPolynomial.mkDerivation_X, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
      dAt, ev, Derivation.leibniz, smul_eq_mul, map_add, map_mul, MvPolynomial.pderiv_X, add_mul,
      Finset.sum_add_distrib, Matrix.mul_apply]
    congr 1
    · simp [Pi.single_apply, apply_ite (MvPolynomial.eval _)]
    · rw [Finset.mul_sum]; simp only [mul_assoc]

theorem TanField_of (hChain : Chain) : TanField := by
  intro C _ N S Y
  constructor
  · intro hY f hf s hs
    obtain ⟨f', hev, hd⟩ := hChain C N N (LinearMap.mulRight C s) f
    have hf' : f' ∈ Van (S : Set (Mat C N)) := fun x hx => by
      rw [hev, LinearMap.mulRight_apply]; exact hf _ (S.mul_mem hx hs)
    have h1 : dAt f' 1 Y = 0 := hY f' hf'
    rw [hd] at h1
    simp only [LinearMap.mulRight_apply, one_mul] at h1
    show ev s (DX Y f) = 0
    rw [ev_DX]; exact h1
  · intro h f hf
    have h1 : ev 1 (DX Y f) = 0 := h f hf 1 S.one_mem
    rw [ev_DX, mul_one] at h1
    exact h1

end LateralTheory.DivDb.TangentFieldExtension
end

-- bundled from Development.EtaleCohomology.DivisorCycles.TorusPtPf
section
open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.TorusPtPf
open LateralTheory.DivDb

variable {C : Type} [Field C] [CharZero C]

noncomputable def E (a : C) : PowerSeries C := PowerSeries.rescale a (PowerSeries.exp C)

lemma coeff_E (a : C) (k : ℕ) : PowerSeries.coeff k (E a) = a ^ k * (k.factorial : C)⁻¹ := by
  simp [E, PowerSeries.coeff_rescale, PowerSeries.coeff_exp]

lemma E_add (a b : C) : E a * E b = E (a + b) := PowerSeries.exp_mul_exp_eq_exp_add a b

lemma E_zero : E (0 : C) = 1 := by
  ext k; rcases k with _ | k <;> simp [coeff_E, PowerSeries.coeff_one]

lemma E_prod {ι : Type} (s : Finset ι) (a : ι → C) : ∏ i ∈ s, E (a i) = E (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [E_zero]
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, E_add]

lemma E_pow (a : C) (m : ℕ) : E a ^ m = E ((m : C) * a) := by
  induction m with
  | zero => simp [E_zero]
  | succ m ih => rw [pow_succ, ih, E_add]; congr 1; push_cast; ring

lemma E_ne (a b c : C) (h : E a - PowerSeries.C b * E c = 0) : b = 1 ∧ a = c := by
  have h0 := congrArg (PowerSeries.coeff 0) h
  have h1 := congrArg (PowerSeries.coeff 1) h
  simp only [map_sub, PowerSeries.coeff_C_mul, coeff_E, map_zero] at h0 h1
  simp at h0 h1
  have hb : b = 1 := by linear_combination -h0
  refine ⟨hb, ?_⟩
  rw [hb] at h1
  linear_combination h1

lemma pow_sys {N n : ℕ} {p : Fin n → Mat C N} (hp : Sys p) (e : Fin n → C) (k : ℕ) :
    (∑ i, e i • p i) ^ k = ∑ i, e i ^ k • p i := by
  induction k with
  | zero => simpa using hp.1.complete.symm
  | succ k ih =>
    rw [pow_succ, ih, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · rw [smul_mul_smul_comm, (hp.1.idem i).eq, pow_succ]
    · intro j _ hji; rw [smul_mul_smul_comm, hp.1.ortho hji.symm, smul_zero]
    · simp

lemma entry_exp {N n : ℕ} {p : Fin n → Mat C N} (hp : Sys p) (e : Fin n → C) (a b : Fin N) :
    (PowerSeries.mk fun k => ((k.factorial : C)⁻¹ • (∑ i, e i • p i) ^ k) a b) =
      ∑ j, PowerSeries.C (p j a b) * E (e j) := by
  ext k
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [PowerSeries.coeff_mk, map_sum, PowerSeries.coeff_C_mul, coeff_E, pow_sys hp, Matrix.smul_apply,
    Matrix.sum_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => by ring

noncomputable def bin {n : ℕ} (q : Finset (Fin n) × Finset (Fin n) × C) : MvPolynomial (Fin n) C :=
  (∏ i ∈ q.1, MvPolynomial.X i) ^ q.2.1.card - MvPolynomial.C q.2.2 * (∏ i ∈ q.2.1, MvPolynomial.X i) ^ q.1.card

theorem TorusPt_of (hE : ExpVan) (hS : SpecPt) : TorusPt := by
  intro C _ _ _ N n S p e hp hlac hX B hB
  classical
  let x : Fin n → PowerSeries C := fun j => E (e j)
  let Q : Set (Finset (Fin n) × Finset (Fin n) × C) :=
    {q | q.1.Nonempty ∧ q.2.1.Nonempty ∧ Disjoint q.1 q.2.1 ∧ q.2.2 ∈ B}
  let G : Set (MvPolynomial (Fin n) C) := Set.range (fun j => MvPolynomial.X j) ∪ bin '' Q
  have hQ : Q.Finite := (Set.finite_univ.prod (Set.finite_univ.prod hB)).subset fun q hq => by
    simp only [Set.mem_prod, Set.mem_univ, true_and]; exact hq.2.2.2
  have hG : G.Finite := (Set.finite_range _).union (hQ.image _)
  have hxg : ∀ g ∈ G, MvPolynomial.aeval x g ≠ 0 := by
    rintro g (⟨j, rfl⟩ | ⟨q, ⟨h1, h2, h3, h4⟩, rfl⟩)
    · intro h0
      have := congrArg (PowerSeries.coeff 0) h0
      simp [x, coeff_E] at this
    · intro h0
      simp only [bin, map_sub, map_mul, map_pow, map_prod, MvPolynomial.aeval_X, MvPolynomial.aeval_C, x, E_prod,
        E_pow] at h0
      have h0' : E ((q.2.1.card : C) * ∑ i ∈ q.1, e i) - PowerSeries.C q.2.2 * E ((q.1.card : C) * ∑ i ∈ q.2.1, e i) = 0 := by
        simpa using h0
      exact hlac _ _ h1 h2 h3 (E_ne _ _ _ h0').2
  obtain ⟨y, hy1, hy2⟩ := hS C (PowerSeries C) (Fin n) x G hG hxg
  refine ⟨y, fun j => ?_, fun f hf => ?_, fun O O' hO hO' hd b hb => ?_⟩
  · have := hy2 _ (Or.inl ⟨j, rfl⟩); simpa using this
  · have h := hE C N S _ hX f hf
    have hent : (fun ab : Fin N × Fin N => PowerSeries.mk fun k =>
          ((k.factorial : C)⁻¹ • (∑ i, e i • p i) ^ k) ab.1 ab.2)
        = fun ab => MvPolynomial.aeval x (∑ j, MvPolynomial.C (p j ab.1 ab.2) * MvPolynomial.X j) := by
      funext ab; rw [entry_exp hp]; simp [x]
    rw [hent, ← MvPolynomial.aeval_bind₁] at h
    have h2 := hy1 _ h
    have h3 : MvPolynomial.aeval y
        ((MvPolynomial.bind₁ fun ab : Fin N × Fin N => ∑ j, MvPolynomial.C (p j ab.1 ab.2) * MvPolynomial.X j) f) = 0 := by
      exact h2
    rw [MvPolynomial.aeval_bind₁] at h3
    unfold ev
    rw [show (fun q : Fin N × Fin N => (∑ j, y j • p j) q.1 q.2) = fun ab =>
        MvPolynomial.aeval y (∑ j, MvPolynomial.C (p j ab.1 ab.2) * MvPolynomial.X j) from
      funext fun ab => by simp [Matrix.sum_apply, mul_comm]]
    exact h3
  · intro h
    apply hy2 _ (Or.inr ⟨(O, O', b), ⟨hO, hO', hd, hb⟩, rfl⟩)
    simp only [bin, map_sub, map_mul, map_pow, map_prod, MvPolynomial.eval_X, MvPolynomial.eval_C]
    rw [h]; ring
end LateralTheory.DivDb.TorusPtPf
end

