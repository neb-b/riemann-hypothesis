module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0004

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial Filter

section Defs

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]

def mConeMap (y : (Σ k, ι k) → Ω) : MRing ι →ₐ[ℤ] MvPolynomial K Ω :=
  aeval fun p => MvPolynomial.C (y p) * MvPolynomial.X p.1

def mCoordIdeal (y : (Σ k, ι k) → Ω) : Ideal (MRing ι) :=
  RingHom.ker (mConeMap y)

def IsSmallH (P : Ideal (MRing ι)) (y : (Σ k, ι k) → Ω) (A : HermLine ι) (τ : ℕ) (s : Ω) : Prop :=
  ∀ (dg dh : K → ℕ) (g h : MRing ι) (z : (Σ k, ι k) → ℂ),
    IsMultiHomog g dg → IsMultiHomog h dh → (∀ k, (dg k : ℤ) = dh k + τ * A.a k) →
    aeval y g = s * aeval y h → z ∈ mcPts P →
    ‖eval z (map (Int.castRingHom ℂ) g)‖ ≤ ‖eval z (map (Int.castRingHom ℂ) h)‖ * A.h z ^ τ

def Birational (y : (Σ k, ι k) → Ω) : Prop :=
  ∀ s : Ω, ∃ (d : K → ℕ) (g h : MRing ι), IsMultiHomog g d ∧ IsMultiHomog h d ∧
    aeval y h ≠ 0 ∧ aeval y g = s * aeval y h

def chartRingZ (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) : Subalgebra ℤ Ω :=
  Algebra.adjoin ℤ (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)

def SmoothGenericFibreM [Algebra ℚ Ω] (y : (Σ k, ι k) → Ω) : Prop :=
  ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
    Algebra.Smooth ℚ (Algebra.adjoin ℚ (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩))

def IsSemipositiveRel (P0 P : Ideal (MRing ι)) (A : HermLine ι) : Prop :=
  IsSmoothHerm A ∧ ∀ z ∈ mcPts P, ∀ w, IsConeTangent (Int.castRingHom ℂ) P0 z w →
    0 ≤ leviForm (fun z => Real.log (A.h z)) z w

def IsSemipositiveH (P : Ideal (MRing ι)) (A : HermLine ι) : Prop :=
  IsSemipositiveRel P P A

def IsConjInvariantH (A : HermLine ι) : Prop :=
  ∀ z : (Σ k, ι k) → ℂ, A.h (fun p => (starRingEnd ℂ) (z p)) = A.h z

def NefOnFibres (P : Ideal (MRing ι)) (a : K → ℤ) : Prop :=
  ∀ W : Ideal (MRing ι), IsMultiProjPrime W → P ≤ W → charOf W ≠ 0 →
    ringKrullDim (MRing ι ⧸ W) = ((1 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    0 ≤ geoNum 1 W (fun _ => a)

def secM (y : (Σ k, ι k) → Ω) (d : K → ℕ) : AddSubgroup Ω :=
  (Submodule.span ℤ {s | ∃ g : MRing ι, IsMultiHomog g d ∧ aeval y g = s}).toAddSubgroup

def chartLat (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) : AddSubgroup Ω where
  carrier := {s | ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
    s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)) ∈ chartRingZ y c}
  zero_mem' := fun c _ => by simp
  add_mem' := fun {s t} hs ht c hc => by rw [add_mul]; exact add_mem (hs c hc) (ht c hc)
  neg_mem' := fun {s} hs c hc => by rw [neg_mul]; exact neg_mem (hs c hc)

def chartLatNm (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) : AddSubgroup Ω where
  carrier := {s | ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
    s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)) ∈ integralClosure (chartRingZ y c) Ω}
  zero_mem' := fun c _ => by simp
  add_mem' := fun {s t} hs ht c hc => by rw [add_mul]; exact add_mem (hs c hc) (ht c hc)
  neg_mem' := fun {s} hs c hc => by rw [neg_mul]; exact neg_mem (hs c hc)

def degC (W : Ideal (MRing ι)) : ℕ :=
  Nat.card (Quot fun z z' : mcPts W =>
    ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ (z' : (Σ k, ι k) → ℂ) = fun p => c p.1 * (z : (Σ k, ι k) → ℂ) p)

def geomDeg (P : Ideal (MRing ι)) (A : HermLine ι) (D : ℕ) : ℝ :=
  ptsIntegral (e := D) P (fun _ z => Real.log (A.h z)) (fun _ => 1)

def MonomialsBounded (P : Ideal (MRing ι)) (A : HermLine ι) (a : K → ℕ) : Prop :=
  ∀ z ∈ mcPts P, ∀ μ : (Σ k, ι k) →₀ ℕ, (∀ k, ∑ i, μ ⟨k, i⟩ = a k) → ‖∏ p, z p ^ μ p‖ ≤ A.h z

def IsZariskiDense (P : Ideal (MRing ι)) (F : Set (Ideal (MRing ι))) : Prop :=
  ∀ f : MRing ι, (∃ a, IsMultiHomog f a) → f ∉ P → ∃ W ∈ F, f ∉ W

end Defs

section Statements

def IntersectionSystem : Type 1 :=
  ∀ (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)],
    Ideal (MRing ι') → (n : ℕ) → (Fin n → HermLine ι') → ℝ

def IsIntersectionSystem (II : IntersectionSystem) : Prop :=
  ∀ (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)], IsIntersectionFamily (II K' ι')

def PackingStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι) (La : ℕ → AddSubgroup Ω),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y → IsSmoothHerm A →
    (∀ τ, La τ ≤ chartLatNm y A.a τ) →
    (∀ τ, {s : La τ | IsSmallH (mCoordIdeal y) y A τ (s : Ω)}.Finite) ∧
      ∃ C : ℝ, ∀ τ, smallSectionCount (IsSmallH (mCoordIdeal y) y A) La τ ≤ C * ((τ : ℝ) + 1) ^ (D + 1)

def ArithmeticVolumeLowerBound : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι)
    (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    SmoothGenericFibreM y → IsSemipositiveH (mCoordIdeal y) A → NefOnFibres (mCoordIdeal y) A.a →
    IsConjInvariantH A →
    II K ι (mCoordIdeal y) (D + 1) (fun _ => A) ≤
      arVolP (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) 1 D

def BirationalPullbackPushforwardFormula : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι) (P0 : Ideal (MRing ι)) (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) A → NefOnFibres (mCoordIdeal y) A.a →
    IsConjInvariantH A →
    II K ι (mCoordIdeal y) (D + 1) (fun _ => A) ≤
      arVolP (IsSmallH (mCoordIdeal y) y A) (chartLatNm y A.a) 1 D

def ArithmeticHilbertSamuelUpperBound : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (a : K → ℕ) (A : HermLine ι) (P0 : Ideal (MRing ι))
    (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    (A.a = fun k => (a k : ℤ)) → P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) A →
    MonomialsBounded (mCoordIdeal y) A a → IsConjInvariantH A →
    limsup (fun τ : ℕ =>
        smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLatNm y A.a) τ /
          ((τ : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))) atTop ≤
      II K ι (mCoordIdeal y) (D + 1) (fun _ => A)

def ArithmeticIntersectionNonneg : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (a : K → ℕ) (A : HermLine ι) (P0 : Ideal (MRing ι))
    (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    (A.a = fun k => (a k : ℤ)) → P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) A →
    MonomialsBounded (mCoordIdeal y) A a → IsConjInvariantH A →
    0 ≤ II K ι (mCoordIdeal y) (D + 1) (fun _ => A)

def SuccessiveMinimaLowerBound : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P P0 : Ideal (MRing ι)) (D : ℕ)
    (A : HermLine ι) (e : ℝ) (II : IntersectionSystem),
    IsIntersectionSystem II → IsArithVar P (D + 1) → P0 ≤ P → IsSemipositiveRel P0 P A →
    NefOnFibres P A.a → IsConjInvariantH A →
    (∀ W, IsArithVar W 1 → P ≤ W → e * degC W ≤ II K ι W 1 ![A]) →
    ((D + 1 : ℕ) : ℝ) * e * geomDeg P A D ≤ II K ι P (D + 1) (fun _ => A)

def SuccessiveMinimaUpperBound : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P P0 : Ideal (MRing ι)) (D : ℕ)
    (A : HermLine ι) (e' : ℝ) (F : Set (Ideal (MRing ι)))
    (II : IntersectionSystem),
    IsIntersectionSystem II → IsArithVar P (D + 1) → P0 ≤ P → IsSemipositiveRel P0 P A →
    NefOnFibres P A.a → IsConjInvariantH A →
    (∀ W ∈ F, IsArithVar W 1 ∧ P ≤ W ∧ II K ι W 1 ![A] ≤ e' * degC W) → IsZariskiDense P F →
    II K ι P (D + 1) (fun _ => A) ≤ ((D + 1 : ℕ) : ℝ) * e' * geomDeg P A D

end Statements

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodC
section
namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

theorem succ_le_ringKrullDim_of_algebraicIndependent {σ : Type} [Finite σ]
    (P : Ideal (MvPolynomial σ ℤ)) (hP : P.IsPrime)
    (hH : P.comap (C : ℤ →+* MvPolynomial σ ℤ) = ⊥) {n : ℕ}
    (x : Fin n → MvPolynomial σ ℚ ⧸ qIdeal P) (hx : AlgebraicIndependent ℚ x) :
    ((n + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial σ ℤ ⧸ P) := by
  have hdom := isDomain_qQuot P hP hH
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg ℚ (MvPolynomial σ ℚ ⧸ qIdeal P)
  have hns : n ≤ s := by
    set S := Algebra.adjoin ℚ (Set.range (g ∘ X))
    have hmem : ∀ y, g y ∈ S := by
      intro y
      show g y ∈ Algebra.adjoin ℚ (Set.range (g ∘ X))
      rw [Algebra.adjoin_range_eq_range_aeval]
      refine ⟨y, ?_⟩
      show aeval (g ∘ X) y = g y
      rw [← MvPolynomial.aeval_unique g]
    let g' : MvPolynomial (Fin s) ℚ →+* S := g.toRingHom.codRestrict S.toSubsemiring hmem
    have hg' : (algebraMap S (MvPolynomial σ ℚ ⧸ qIdeal P)).comp g' = g.toRingHom := by
      ext y <;> rfl
    have halg : Algebra.IsAlgebraic S (MvPolynomial σ ℚ ⧸ qIdeal P) := by
      refine ⟨fun b => ?_⟩
      obtain ⟨p, hpm, hp⟩ := hint b
      refine IsIntegral.isAlgebraic ⟨p.map g', hpm.map g', ?_⟩
      rw [Polynomial.eval₂_map, hg']
      exact hp
    have h1 := hx.cardinalMk_le_trdeg
    have h2 := Algebra.IsAlgebraic.trdeg_le_cardinalMk ℚ (Set.range (g ∘ X))
    have h3 := Cardinal.mk_range_le (f := g ∘ X)
    have := h1.trans (h2.trans h3)
    simpa using this
  have hdim : (s : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial σ ℚ ⧸ qIdeal P) := by
    refine le_ringKrullDim_of_isIntegral g.toRingHom hint hinj s ?_
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  letI := (ratHom P).toAlgebra
  haveI := ratHom_isLocalization P
  refine succ_le_ringKrullDim_of_isLocalization
    (Algebra.algebraMapSubmonoid (MvPolynomial σ ℤ ⧸ P) (nonZeroDivisors ℤ)) ?_ n
    (le_trans (by exact_mod_cast hns) hdim)
  intro p hp hdis
  refine exists_gt_of_comap_int_eq_bot (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective p hp ?_
  ext m
  simp only [Ideal.mem_comap, RingHom.coe_comp, Function.comp_apply, Submodule.mem_bot]
  constructor
  · intro hm
    by_contra hm0
    refine Set.disjoint_left.mp hdis ⟨m, mem_nonZeroDivisors_of_ne_zero hm0, rfl⟩ ?_
    simpa [eq_intCast] using hm
  · rintro rfl
    simp

end ReciprocityTheory.ChartRestriction.G.Geo
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodE
section
namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

noncomputable section

variable {k : Type*} [Field k]

theorem intOver_trans {R : Type*} [CommRing R] [Algebra k R] {r : ℕ} (ℓ : Fin (r + 1) → R)
    (lam : Fin r → k) (h0 : IntOver k (fun i => ℓ i.succ - lam i • ℓ 0) (ℓ 0)) {x : R}
    (hx : IntOver k ℓ x) : IntOver k (fun i => ℓ i.succ - lam i • ℓ 0) x := by
  set ℓ' : Fin r → R := fun i => ℓ i.succ - lam i • ℓ 0 with hℓ'
  let f' : MvPolynomial (Fin r) k →+* R := (aeval ℓ' : MvPolynomial (Fin r) k →ₐ[k] R)
  letI : Algebra (MvPolynomial (Fin r) k) R := f'.toAlgebra
  let Cl := integralClosure (MvPolynomial (Fin r) k) R
  have hmem0 : ℓ 0 ∈ Cl := h0
  have hB : ∀ b, f' b ∈ Cl := fun b => Subalgebra.algebraMap_mem Cl b
  have hmem : ∀ j, ℓ j ∈ Cl := by
    intro j
    refine Fin.cases hmem0 (fun i => ?_) j
    have : ℓ i.succ = f' (X i) + f' (C (lam i)) * ℓ 0 := by
      simp [f', hℓ', Algebra.smul_def]
    rw [this]
    exact Cl.add_mem (hB _) (Cl.mul_mem (hB _) hmem0)
  have hall : ∀ p : MvPolynomial (Fin (r + 1)) k, (aeval ℓ p : R) ∈ Cl := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      have := hB (C a)
      simpa [f'] using this
    | add p q hp hq => rw [map_add (f := _)]; exact Cl.add_mem hp hq
    | mul_X p j hp => rw [map_mul, aeval_X]; exact Cl.mul_mem hp (hmem j)
  obtain ⟨p, hpm, hp⟩ := hx
  let g : MvPolynomial (Fin (r + 1)) k →+* Cl :=
    ((aeval ℓ : MvPolynomial (Fin (r + 1)) k →ₐ[k] R) : MvPolynomial (Fin (r + 1)) k →+* R).codRestrict
      Cl.toSubsemiring hall
  have hxC : IsIntegral Cl x := by
    refine ⟨p.map g, hpm.map g, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hp
  exact isIntegral_trans (R := MvPolynomial (Fin r) k) (A := Cl) x hxC

def forms {R : Type*} [CommRing R] [Algebra k R] {τ : Type*} [Fintype τ] (v : τ → R) {r : ℕ}
    (L : Fin r → τ → k) : Fin r → R :=
  fun j => ∑ t, L j t • v t

theorem exists_linear_normalization [Infinite k] {R : Type*} [CommRing R] [Algebra k R]
    {τ : Type*} [Fintype τ] (v : τ → R) (m : ℕ)
    (hdep : ∀ (r : ℕ) (L : Fin r → τ → k), m < r → ¬ AlgebraicIndependent k (forms v L)) :
    ∃ r ≤ m, ∃ L : Fin r → τ → k, ∀ t, IntOver k (forms v L) (v t) := by
  classical
  let Good : ℕ → Prop := fun r => ∃ L : Fin r → τ → k, ∀ t, IntOver k (forms v L) (v t)
  have hstart : Good (Fintype.card τ) := by
    let e := Fintype.equivFin τ
    refine ⟨fun j s => if s = e.symm j then 1 else 0, fun t => ?_⟩
    have hf : forms v (fun j s => if s = e.symm j then (1 : k) else 0) = fun j => v (e.symm j) := by
      funext j
      simp [forms, ite_smul]
    rw [hf]
    have : v t = (aeval (fun j => v (e.symm j)) : MvPolynomial (Fin _) k →ₐ[k] R) (X (e t)) := by
      simp
    rw [this]
    exact RingHom.isIntegralElem_map _
  have hstep : ∀ r, m < r + 1 → Good (r + 1) → Good r := by
    rintro r hr ⟨L, hL⟩
    have hnot := hdep (r + 1) L hr
    rw [algebraicIndependent_iff] at hnot
    push Not at hnot
    obtain ⟨F, hF, hF0⟩ := hnot
    obtain ⟨lam, h0⟩ := exists_isIntegralElem_linear (forms v L) F hF0 hF
    refine ⟨fun i s => L i.succ s - lam i * L 0 s, fun t => ?_⟩
    have hf : forms v (fun i s => L i.succ s - lam i * L 0 s) =
        fun i => forms v L i.succ - lam i • forms v L 0 := by
      funext i
      simp [forms, sub_smul, mul_smul, Finset.sum_sub_distrib, Finset.smul_sum]
    rw [hf]
    exact intOver_trans (forms v L) lam h0 (hL t)
  have hdesc : ∀ d, Good (m + d) → Good m := by
    intro d
    induction d with
    | zero => exact id
    | succ d ih => exact fun h => ih (hstep (m + d) (by omega) h)
  by_cases hN : Fintype.card τ ≤ m
  · exact ⟨_, hN, hstart⟩
  · refine ⟨m, le_rfl, hdesc (Fintype.card τ - m) ?_⟩
    rw [show m + (Fintype.card τ - m) = Fintype.card τ by omega]
    exact hstart

end

end ReciprocityTheory.ChartRestriction.G.Geo
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodF
section
namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

noncomputable section

attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

def blkWt : (Σ k, ι k) → (K →₀ ℕ) := fun p => Finsupp.single p.1 1

def oneK : K →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun _ => 1)

theorem weight_blkWt_apply (m : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (blkWt (ι := ι)) m k = ∑ i, m ⟨k, i⟩ := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finsupp.finsetSum_apply,
    Fintype.sum_sigma]
  refine (Finset.sum_eq_single k ?_ ?_).trans ?_
  · intro k' _ hk'
    refine Finset.sum_eq_zero fun i _ => ?_
    simp [blkWt, Finsupp.single_apply, hk']
  · simp
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp [blkWt]

theorem isWeightedHomogeneous_qmap (f : MRing ι) (a : K → ℕ) (hf : IsMultiHomog f a) :
    IsWeightedHomogeneous (blkWt (ι := ι)) (qmap f) (Finsupp.equivFunOnFinite.symm a) := by
  intro d hd
  have hd' : d ∈ f.support := by
    rw [MvPolynomial.mem_support_iff]
    intro h
    apply hd
    simp [qmap, MvPolynomial.coeff_map, h]
  ext k
  rw [weight_blkWt_apply, hf d hd' k]
  simp

theorem qIdeal_isHomogeneous (P : Ideal (MRing ι)) (hP : IsMultiHomogIdeal P) :
    (qIdeal P).IsHomogeneous (weightedHomogeneousSubmodule ℚ (blkWt (ι := ι))) := by
  obtain ⟨S, hS, rfl⟩ := hP
  rw [qIdeal, Ideal.map_span]
  apply Ideal.homogeneous_span
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨a, ha⟩ := hS f hf
  exact ⟨_, (mem_weightedHomogeneousSubmodule _ _ _ _).2 (isWeightedHomogeneous_qmap f a ha)⟩

def segMon (i : (k : K) → ι k) : MvPolynomial (Σ k, ι k) ℚ := ∏ k, X ⟨k, i k⟩

theorem segMon_isWeightedHomogeneous (i : (k : K) → ι k) :
    IsWeightedHomogeneous (blkWt (ι := ι)) (segMon i) oneK := by
  have h := IsWeightedHomogeneous.prod Finset.univ
    (fun k => (X ⟨k, i k⟩ : MvPolynomial (Σ k, ι k) ℚ)) (fun k => blkWt (ι := ι) ⟨k, i k⟩)
    (fun k _ => isWeightedHomogeneous_X ℚ _ _)
  have e : (∑ k ∈ Finset.univ, blkWt (ι := ι) ⟨k, i k⟩) = oneK := by
    ext k
    rw [Finsupp.finsetSum_apply]
    simp only [blkWt, oneK, Finsupp.single_apply, Finsupp.coe_equivFunOnFinite_symm]
    simp
  rw [e] at h
  exact h

private theorem aeval_of_isWeightedHomogeneous_blkWt {E : Type*} (w' : E → (K →₀ ℕ))
    (yt : E → MvPolynomial (Σ k, ι k) ℚ)
    (hy : ∀ e, IsWeightedHomogeneous (blkWt (ι := ι)) (yt e) (w' e)) (n : E →₀ ℕ) (c : ℚ) :
    IsWeightedHomogeneous (blkWt (ι := ι)) (aeval yt (monomial n c)) (Finsupp.weight w' n) := by
  classical
  rw [aeval_monomial, Finsupp.weight_apply, Finsupp.sum, Finsupp.prod]
  have h0 : IsWeightedHomogeneous (blkWt (ι := ι))
      (algebraMap ℚ (MvPolynomial (Σ k, ι k) ℚ) c) 0 := by
    rw [MvPolynomial.algebraMap_eq]
    exact isWeightedHomogeneous_C _ _
  have h1 := h0.mul (IsWeightedHomogeneous.prod n.support (fun e => yt e ^ n e)
    (fun e => n e • w' e) (fun e _ => (hy e).pow (n e)))
  simpa using h1

theorem component_aeval {E : Type*} (w' : E → (K →₀ ℕ))
    (yt : E → MvPolynomial (Σ k, ι k) ℚ)
    (hy : ∀ e, IsWeightedHomogeneous (blkWt (ι := ι)) (yt e) (w' e)) (H : MvPolynomial E ℚ)
    (δ : K →₀ ℕ) :
    weightedHomogeneousComponent (blkWt (ι := ι)) δ (aeval yt H) =
      aeval yt (weightedHomogeneousComponent w' δ H) := by
  induction H using MvPolynomial.induction_on' with
  | monomial n c =>
    by_cases h : Finsupp.weight w' n = δ
    · subst h
      rw [(aeval_of_isWeightedHomogeneous_blkWt w' yt hy n c).weightedHomogeneousComponent_same,
        (isWeightedHomogeneous_monomial w' n c rfl).weightedHomogeneousComponent_same]
    · rw [(aeval_of_isWeightedHomogeneous_blkWt w' yt hy n c).weightedHomogeneousComponent_ne δ (Ne.symm h),
        (isWeightedHomogeneous_monomial w' n c rfl).weightedHomogeneousComponent_ne δ (Ne.symm h),
        map_zero]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]

variable (k0 : K)

def sWt (r : ℕ) : Fin r ⊕ {k // k ≠ k0} → (K →₀ ℕ) :=
  Sum.elim (fun _ => oneK) (fun k' => Finsupp.single k'.1 1)

theorem weight_sWt_apply {r : ℕ} (n : (Fin r ⊕ {k // k ≠ k0}) →₀ ℕ) (k : K) :
    Finsupp.weight (sWt k0 r) n k =
      (∑ j, n (Sum.inl j)) + (if h : k = k0 then 0 else n (Sum.inr ⟨k, h⟩)) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finsupp.finsetSum_apply,
    Fintype.sum_sum_type]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    simp [sWt, oneK]
  · by_cases h : k = k0
    · subst h
      rw [dite_eq_left rfl]
      refine Finset.sum_eq_zero fun k' _ => ?_
      simp [sWt, Finsupp.single_apply, k'.2]
    · rw [dite_eq_right h, Finset.sum_eq_single ⟨k, h⟩]
      · simp [sWt]
      · intro k' _ hk'
        have : k'.1 ≠ k := fun e => hk' (Subtype.ext e)
        simp [sWt, Finsupp.single_apply, this]
      · simp

theorem inr_eq_of_weight_eq {r : ℕ} {n n0 : (Fin r ⊕ {k // k ≠ k0}) →₀ ℕ}
    (h : Finsupp.weight (sWt k0 r) n = Finsupp.weight (sWt k0 r) n0) (k' : {k // k ≠ k0}) :
    n (Sum.inr k') = n0 (Sum.inr k') := by
  have h0 : Finsupp.weight (sWt k0 r) n k0 = Finsupp.weight (sWt k0 r) n0 k0 := by rw [h]
  have h1 : Finsupp.weight (sWt k0 r) n k'.1 = Finsupp.weight (sWt k0 r) n0 k'.1 := by rw [h]
  rw [weight_sWt_apply, weight_sWt_apply, dite_eq_left rfl, dite_eq_left rfl] at h0
  rw [weight_sWt_apply, weight_sWt_apply, dite_eq_right k'.2, dite_eq_right k'.2, Subtype.coe_eta] at h1
  omega

theorem aeval_sumElim_factor {S : Type*} [CommRing S] [Algebra ℚ S] {r : ℕ}
    {H : MvPolynomial (Fin r ⊕ {k // k ≠ k0}) ℚ} {δ : K →₀ ℕ}
    (hH : IsWeightedHomogeneous (sWt k0 r) H δ) {n0 : (Fin r ⊕ {k // k ≠ k0}) →₀ ℕ}
    (hn0 : n0 ∈ H.support) (a : Fin r → S) (b : {k // k ≠ k0} → S) :
    aeval (Sum.elim a b) H = (∏ k', b k' ^ n0 (Sum.inr k')) * aeval (Sum.elim a 1) H := by
  classical
  have hw : ∀ n ∈ H.support, ∀ k', n (Sum.inr k') = n0 (Sum.inr k') := fun n hn k' =>
    inr_eq_of_weight_eq k0
      ((hH (mem_support_iff.mp hn)).trans (hH (mem_support_iff.mp hn0)).symm) k'
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  have hp : ∏ k', b k' ^ n (Sum.inr k') = ∏ k', b k' ^ n0 (Sum.inr k') :=
    Finset.prod_congr rfl fun k' _ => by rw [hw n hn k']
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.one_apply, one_pow, Finset.prod_const_one, mul_one, hp]
  ring

end

end ReciprocityTheory.ChartRestriction.G.Geo
end

