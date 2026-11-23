module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
public import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AdelicPairReducedBasis
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open NumberField IsDedekindDomain

namespace GlobalTheory.AdeleFree

section Abstract

variable {A : Type} [CommRing A]

def intClosure (O : Subring A) : Subring A where
  carrier := {r | ∀ M : ℕ, 0 < M → ∃ (z : ℤ) (c : A), c ∈ O ∧ r = (z : A) + (M : A) * c}
  mul_mem' := by
    intro a b ha hb M hM
    obtain ⟨z, c, hc, rfl⟩ := ha M hM
    obtain ⟨z', c', hc', rfl⟩ := hb M hM
    refine ⟨z * z', z * c' + c * z' + M * (c * c'), ?_, by push_cast; ring⟩
    exact add_mem (add_mem (mul_mem (intCast_mem _ _) hc') (mul_mem hc (intCast_mem _ _)))
      (mul_mem (natCast_mem _ _) (mul_mem hc hc'))
  one_mem' := fun M _ => ⟨1, 0, zero_mem _, by simp⟩
  add_mem' := by
    intro a b ha hb M hM
    obtain ⟨z, c, hc, rfl⟩ := ha M hM
    obtain ⟨z', c', hc', rfl⟩ := hb M hM
    exact ⟨z + z', c + c', add_mem hc hc', by push_cast; ring⟩
  zero_mem' := fun M _ => ⟨0, 0, zero_mem _, by simp⟩
  neg_mem' := by
    intro a ha M hM
    obtain ⟨z, c, hc, rfl⟩ := ha M hM
    exact ⟨-z, -c, neg_mem hc, by push_cast; ring⟩

theorem intClosure_le (O : Subring A) {a : A} (ha : a ∈ intClosure O) : a ∈ O := by
  obtain ⟨z, c, hc, rfl⟩ := ha 1 one_pos
  exact add_mem (intCast_mem _ _) (by simpa using hc)

def ratSpan (Z : Subring A) : Subring A where
  carrier := {a | ∃ M : ℕ, 0 < M ∧ (M : A) * a ∈ Z}
  mul_mem' := by
    rintro a b ⟨M, hM, ha⟩ ⟨N, hN, hb⟩
    refine ⟨M * N, Nat.mul_pos hM hN, ?_⟩
    have : ((M * N : ℕ) : A) * (a * b) = (M * a) * (N * b) := by push_cast; ring
    rw [this]; exact mul_mem ha hb
  one_mem' := ⟨1, one_pos, by simp⟩
  add_mem' := by
    rintro a b ⟨M, hM, ha⟩ ⟨N, hN, hb⟩
    refine ⟨M * N, Nat.mul_pos hM hN, ?_⟩
    have : ((M * N : ℕ) : A) * (a + b) = N * (M * a) + M * (N * b) := by push_cast; ring
    rw [this]
    exact add_mem (mul_mem (natCast_mem _ _) ha) (mul_mem (natCast_mem _ _) hb)
  zero_mem' := ⟨1, one_pos, by simp⟩
  neg_mem' := by
    rintro a ⟨M, hM, ha⟩
    exact ⟨M, hM, by rw [mul_neg]; exact neg_mem ha⟩

theorem mem_ratSpan {Z : Subring A} {a : A} (ha : a ∈ Z) : a ∈ ratSpan Z :=
  ⟨1, one_pos, by simpa using ha⟩

theorem den_mul (φ : ℚ →+* A) (q : ℚ) : (q.den : A) * φ q = (q.num : A) := by
  rw [← map_natCast φ q.den, ← map_mul, Rat.den_mul_eq_num, map_intCast]

theorem rat_mem (φ : ℚ →+* A) (Z : Subring A) (q : ℚ) : φ q ∈ ratSpan Z :=
  ⟨q.den, q.den_pos, by rw [den_mul]; exact intCast_mem _ _⟩

theorem inv_mul (φ : ℚ →+* A) {N : ℕ} (hN : 0 < N) : φ (N : ℚ)⁻¹ * (N : A) = 1 := by
  rw [← map_natCast φ N, ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hN.ne'), map_one]

theorem cancel (φ : ℚ →+* A) {N : ℕ} (hN : 0 < N) {a b : A} (h : (N : A) * a = N * b) :
    a = b :=
  calc a = (φ (N : ℚ)⁻¹ * N) * a := by rw [inv_mul φ hN, one_mul]
    _ = φ (N : ℚ)⁻¹ * (N * a) := mul_assoc _ _ _
    _ = φ (N : ℚ)⁻¹ * (N * b) := by rw [h]
    _ = b := by rw [← mul_assoc, inv_mul φ hN, one_mul]

theorem mem_of_mul (φ : ℚ →+* A) (O : Subring A)
    (hint : ∀ (z : ℤ) (N : ℕ), 0 < N → ∀ e ∈ O, (z : A) = N * e → (N : ℤ) ∣ z)
    {N : ℕ} (hN : 0 < N) {c : A} (hc : c ∈ O) (h : (N : A) * c ∈ intClosure O) :
    c ∈ intClosure O := by
  intro M hM
  obtain ⟨z, d, hd, hzd⟩ := h (N * M) (Nat.mul_pos hN hM)
  have hz : (z : A) = N * (c - M * d) := by rw [mul_sub, hzd]; push_cast; ring
  obtain ⟨y, rfl⟩ := hint z N hN (c - M * d) (sub_mem hc (mul_mem (natCast_mem _ _) hd)) hz
  refine ⟨y, d, hd, cancel φ hN ?_⟩
  rw [hzd]; push_cast; ring

theorem exists_basis (φ : ℚ →+* A) (O : Subring A) [IsReduced A] {β : Type} [Fintype β]
    (w : β → A) (hw : ∀ i, w i ∈ O)
    (hint : ∀ (z : ℤ) (N : ℕ), 0 < N → ∀ e ∈ O, (z : A) = N * e → (N : ℤ) ∣ z)
    (h0 : ∀ a : A, (∀ M : ℕ, 0 < M → ∃ c, c ∈ O ∧ a = (M : A) * c) → a = 0)
    (hden : ∀ a : A, ∃ M : ℕ, 0 < M ∧ (M : A) * a ∈ O)
    (hspan : ∀ a ∈ O, ∃ r : β → A, (∀ i, r i ∈ intClosure O) ∧ a = ∑ i, r i * w i)
    (hdiv : ∀ (r : β → A) (N : ℕ), 0 < N → (∀ i, r i ∈ intClosure O) →
      (∃ e, e ∈ O ∧ ∑ i, r i * w i = (N : A) * e) →
        ∀ i, ∃ s, s ∈ intClosure O ∧ r i = (N : A) * s) :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra ℚ R) (R₀ : Subring R) (_ : Algebra R A)
      (b : Module.Basis β R A), AdelicPair R R₀ ∧ IsReduced R ∧ (∀ i, b i = w i) ∧
        ∀ a : A, a ∈ O ↔ ∀ i, b.repr a i ∈ R₀ := by
  classical

  set Z := intClosure O with hZdef
  set R := ratSpan Z with hRdef
  have hZO : ∀ x ∈ Z, x ∈ O := fun x hx => intClosure_le O hx
  have hZR : ∀ x ∈ Z, x ∈ R := fun x hx => mem_ratSpan hx
  let φR : ℚ →+* R := φ.codRestrict R (rat_mem φ Z)
  let _ : Algebra ℚ R := φR.toAlgebra
  let _ : Algebra R A := (Subring.subtype R).toAlgebra
  have hsmul : ∀ (c : R) (x : A), c • x = (c : A) * x := fun _ _ => rfl
  let R₀ : Subring R := Z.comap (Subring.subtype R)
  have hmemR : ∀ c : R, ∃ M : ℕ, 0 < M ∧ (M : A) * c ∈ Z := fun c => c.2

  have hli : LinearIndependent R w := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    choose M hM hMc using fun j => hmemR (c j)
    set K := ∏ j, M j with hKdef
    have hK : 0 < K := Finset.prod_pos fun j _ => hM j
    have hr : ∀ j, (K : A) * c j ∈ Z := by
      intro j
      have hsplit : (K : A) * c j = ((∏ k ∈ Finset.univ.erase j, M k : ℕ) : A) * ((M j : A) * c j) := by
        rw [← mul_assoc, ← Nat.cast_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
      rw [hsplit]
      exact mul_mem (natCast_mem _ _) (hMc j)
    have hc' : ∑ j, (c j : A) * w j = 0 := by simpa only [hsmul] using hc
    have hsum : ∑ j, ((K : A) * c j) * w j = 0 := by
      simp only [mul_assoc]
      rw [← Finset.mul_sum, hc', mul_zero]
    have hzero : (K : A) * c i = 0 := by
      apply h0
      intro N hN
      obtain ⟨s, hs, hrs⟩ := hdiv (fun j => (K : A) * c j) N hN hr
        ⟨0, zero_mem _, by rw [hsum, mul_zero]⟩ i
      exact ⟨s, hZO s hs, hrs⟩
    exact Subtype.ext (cancel φ hK (by rw [hzero]; simp))

  have hsp : ⊤ ≤ Submodule.span R (Set.range w) := by
    rintro a -
    obtain ⟨M, hM, hMa⟩ := hden a
    obtain ⟨r, hr, hra⟩ := hspan _ hMa
    have hmem : ∀ i, φ (M : ℚ)⁻¹ * r i ∈ R := fun i =>
      ⟨M, hM, by rw [← mul_assoc, mul_comm (M : A) (φ _), inv_mul φ hM, one_mul]; exact hr i⟩
    have ha : a = ∑ i, (⟨φ (M : ℚ)⁻¹ * r i, hmem i⟩ : R) • w i := by
      simp only [hsmul]
      apply cancel φ hM
      rw [hra, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← mul_assoc, ← mul_assoc, mul_comm (M : A) (φ _), inv_mul φ hM, one_mul]
    rw [ha]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let b : Module.Basis β R A := Module.Basis.mk hli hsp
  have hb : ∀ i, b i = w i := fun i => Module.Basis.mk_apply hli hsp i
  refine ⟨R, inferInstance, inferInstance, R₀, inferInstance, b, ?_, ?_, hb, ?_⟩
  ·
    refine ⟨?_, ?_⟩
    · intro q hq
      have hq' : φ q ∈ Z := hq
      obtain ⟨z, c, hc, hzc⟩ := hq' q.den q.den_pos
      have h1 : ((q.num - q.den * z : ℤ) : A) = (q.den : A) * ((q.den : A) * c) := by
        push_cast
        rw [← den_mul φ q, hzc]
        ring
      have h2 := hint _ q.den q.den_pos _ (mul_mem (natCast_mem _ _) hc) h1
      have h3 : (q.den : ℤ) ∣ q.num := by
        have h4 := dvd_add h2 (dvd_mul_right (q.den : ℤ) z)
        simpa using h4
      have h5 : q.den = 1 :=
        Nat.eq_one_of_dvd_coprimes q.reduced.symm dvd_rfl (Int.natCast_dvd.mp h3)
      exact ⟨q.num, ((Rat.den_eq_one_iff q).mp h5).symm⟩
    · intro M hM r
      obtain ⟨K, hK, hKr⟩ := hmemR r
      obtain ⟨z, c, hc, hzc⟩ := hKr (K * M) (Nat.mul_pos hK hM)
      have hcZ : c ∈ Z := by
        apply mem_of_mul φ O hint (Nat.mul_pos hK hM) hc
        have hkm : ((K * M : ℕ) : A) * c = (K : A) * r - z := by rw [hzc]; ring
        rw [hkm]
        exact sub_mem hKr (intCast_mem _ _)
      refine ⟨(z : ℚ) / K, ⟨c, hZR c hcZ⟩, hcZ, ?_⟩
      apply Subtype.ext
      have hk : (K : A) * φ ((z : ℚ) / K) = z := by
        rw [← map_natCast φ K, ← map_mul, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hK.ne'),
          map_intCast]
      change (r : A) = φ ((z : ℚ) / K) + (M : A) * c
      apply cancel φ hK
      rw [hzc, mul_add, hk]
      push_cast
      ring
  · exact isReduced_of_injective (Subring.subtype R) Subtype.val_injective
  · intro a
    have hrep : a = ∑ i, (b.repr a i : A) * w i := by
      conv_lhs => rw [← b.sum_repr a]
      simp only [hsmul, hb]
    constructor
    · intro ha i
      obtain ⟨r, hr, hra⟩ := hspan a ha
      let c : β → R := fun j => ⟨r j, hZR _ (hr j)⟩
      have hdiff : ∑ j, (b.repr a j - c j) • b j = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib, b.sum_repr]
        rw [sub_eq_zero]
        simp only [hsmul, hb]
        exact hra
      have h := Fintype.linearIndependent_iff.1 b.linearIndependent _ hdiff i
      rw [sub_eq_zero.1 h]
      exact hr i
    · intro h
      rw [hrep]
      exact Subring.sum_mem _ fun i _ => mul_mem (hZO _ (h i)) (hw i)

end Abstract

theorem finiteAdele_free : ∀ (F : Type) [Field F] [NumberField F] (β : Type) [Fintype β] (ω : Module.Basis β ℤ (𝓞 F)), ∃ (R : Type) (_ : CommRing R) (_ : Algebra ℚ R) (R₀ : Subring R) (_ : Algebra R (FiniteAdeleRing (𝓞 F) F)) (b : Module.Basis β R (FiniteAdeleRing (𝓞 F) F)), AdelicPair R R₀ ∧ IsReduced R ∧ (∀ i, b i = algebraMap F (FiniteAdeleRing (𝓞 F) F) (ω i : 𝓞 F)) ∧ ∀ a : FiniteAdeleRing (𝓞 F) F, (∀ v, (a : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ↔ ∀ i, b.repr a i ∈ R₀ := by
  intro F _ _ β _ ω
  classical
  obtain ⟨-, -, hz0, -, hden, hred⟩ := GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F
  have : IsReduced (FiniteAdeleRing (𝓞 F) F) := hred
  let O : Subring (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.CoordDiv.intAdeles F
  have hint : ∀ (z : ℤ) (N : ℕ), 0 < N → ∀ e ∈ O,
      (z : FiniteAdeleRing (𝓞 F) F) = N * e → (N : ℤ) ∣ z := by
    intro z N hN e he h
    obtain ⟨a, ha⟩ := GlobalTheory.CoordDiv.dvd_of_eq F (z : 𝓞 F) N hN e he (by simpa using h)
    exact GlobalTheory.CoordDiv.int_dvd F z N a ha
  obtain ⟨R, i1, i2, R₀, i3, b, hP, hR, hb, hmem⟩ :=
    exists_basis ((algebraMap F (FiniteAdeleRing (𝓞 F) F)).comp (algebraMap ℚ F)) O
      (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ω i : 𝓞 F))
      (fun i => GlobalTheory.CoordDiv.algebraMap_mem F (ω i)) hint (fun a ha => hz0 a ha) (fun a => hden a)
      (fun a ha => GlobalTheory.ClassFin.exists_sum_integralBasis F β ω a ha)
      (fun r N hN hr he => GlobalTheory.CoordDiv.coord_divisible F β ω r N hN hr he)
  exact ⟨R, i1, i2, R₀, i3, b, hP, hR, hb, fun a => hmem a⟩

end GlobalTheory.AdeleFree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousCharacterFiniteOrderIntegralUnits
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CharFin

theorem finite_order_of_small {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
    [TopologicalSpace R] [TopologicalSpace A] [TopologicalSpace B] [ContinuousAdd B]
    (p : R →+* A) (q : R →+* B) (s : A × B → R) (hs : Continuous s) (hsz : ∀ z, s (p z, q z) = z)
    (S : Subring B) (hsmall : ∀ W ∈ 𝓝 (0 : B), ∃ N : ℕ, 0 < N ∧ ∀ y ∈ S, N • y ∈ W)
    (hfin : ∀ N : ℕ, 0 < N → Finite (S ⧸ Ideal.span {(N : S)}))
    (χ : Rˣ →* Circle) (hχ : Continuous χ) :
    ∃ N : ℕ, 0 < N ∧ (∀ x : Rˣ, (p x = 1 ∧ q x ∈ S ∧ q (x⁻¹ : Rˣ) ∈ S) →
      (∃ y ∈ S, q x - 1 = N • y) → χ x = 1) ∧
      ∃ m : ℕ, 0 < m ∧ ∀ x : Rˣ, (p x = 1 ∧ q x ∈ S ∧ q (x⁻¹ : Rˣ) ∈ S) → χ x ^ m = 1 := by
  have hV : χ ⁻¹' Circle.centeredArc (Real.pi / 2) ∈ 𝓝 (1 : Rˣ) := by
    refine ((Circle.isOpen_centeredArc _).preimage hχ).mem_nhds ?_
    rw [Set.mem_preimage, map_one, Circle.mem_centeredArc (by linarith [Real.pi_pos])]
    simp [Real.pi_pos]
  rw [Units.isInducing_embedProduct.nhds_eq_comap, Filter.mem_comap] at hV
  obtain ⟨T, hT, hTV⟩ := hV
  obtain ⟨T1, hT1, T2, hT2, hTT⟩ := mem_nhds_prod_iff.1 hT
  let f : B → R := fun b => s (1, 1 + b)
  have hf : Continuous f := hs.comp (continuous_const.prodMk (continuous_const.add continuous_id))
  have hf0 : f 0 = 1 := by simpa [f] using hsz 1
  have h1 : f ⁻¹' T1 ∈ 𝓝 (0 : B) := hf.continuousAt.preimage_mem_nhds (by rw [hf0]; exact hT1)
  have h2 : (fun b => MulOpposite.op (f b)) ⁻¹' T2 ∈ 𝓝 (0 : B) :=
    (MulOpposite.continuous_op.comp hf).continuousAt.preimage_mem_nhds
      (by rw [Function.comp_apply, hf0]; exact hT2)
  obtain ⟨N, hN, hNW⟩ := hsmall _ (Filter.inter_mem h1 h2)
  have hpinv : ∀ x : Rˣ, p x = 1 → p (x⁻¹ : Rˣ) = 1 := fun x hx => by
    have := congrArg p x.mul_inv
    rwa [map_mul, hx, one_mul, map_one] at this
  let G : Subgroup Rˣ :=
    { carrier := {x | p x = 1 ∧ q x ∈ S ∧ q (x⁻¹ : Rˣ) ∈ S}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        refine ⟨by simp [hx.1, hy.1], ?_, ?_⟩
        · rw [Units.val_mul, map_mul]; exact mul_mem hx.2.1 hy.2.1
        · rw [mul_inv, Units.val_mul, map_mul]; exact mul_mem hx.2.2 hy.2.2
      inv_mem' := fun {x} hx => ⟨hpinv x hx.1, hx.2.2, by simpa using hx.2.1⟩ }
  let ψ : G →* S :=
    { toFun := fun x => ⟨q (x : Rˣ), x.2.2.1⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp }
  let φ : G →* (S ⧸ Ideal.span {(N : S)})ˣ :=
    ((Ideal.Quotient.mk (Ideal.span {(N : S)})).toMonoidHom.comp ψ).toHomUnits
  have hφ : ∀ x : G, φ x = 1 ↔ ∃ y ∈ S, q (x : Rˣ) - 1 = N • y := by
    intro x
    have : φ x = 1 ↔ Ideal.Quotient.mk (Ideal.span {(N : S)}) (ψ x) = Ideal.Quotient.mk _ 1 := by
      rw [Units.ext_iff]; rfl
    rw [this, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, y.2, by simpa [ψ] using congrArg Subtype.val hy⟩
    · rintro ⟨y, hy, h⟩
      exact ⟨⟨y, hy⟩, Subtype.ext (by simpa [ψ] using h)⟩
  have hfx : ∀ x : G, φ x = 1 → ∃ y ∈ S, ((x : Rˣ) : R) = f (N • y) := by
    intro x hx
    obtain ⟨y, hy, h⟩ := (hφ x).1 hx
    refine ⟨y, hy, ?_⟩
    have := hsz (x : Rˣ)
    rw [x.2.1] at this
    simp only [f, ← h, add_sub_cancel, this]
  have harc : ∀ x : G, φ x = 1 → χ x ∈ Circle.centeredArc (Real.pi / 2) := by
    intro x hx
    obtain ⟨y, hy, h⟩ := hfx x hx
    obtain ⟨y', hy', h'⟩ := hfx x⁻¹ (by rw [map_inv, hx, inv_one])
    refine hTV (hTT ⟨?_, ?_⟩)
    · change ((x : Rˣ) : R) ∈ T1
      rw [h]; exact (hNW y hy).1
    · change MulOpposite.op (((x⁻¹ : G) : Rˣ) : R) ∈ T2
      rw [h']; exact (hNW y' hy').2
  have hker : ∀ x : G, φ x = 1 → χ x = 1 := by
    intro x hx
    refine Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two fun n _ => ?_
    have := harc (x ^ n) (by rw [map_pow, hx, one_pow])
    rwa [Subgroup.coe_pow, map_pow] at this
  haveI := hfin N hN
  refine ⟨N, hN, fun x hx h => hker ⟨x, hx⟩ ((hφ _).2 h),
    Nat.card (S ⧸ Ideal.span {(N : S)})ˣ, Nat.card_pos, fun x hx => ?_⟩
  have := hker ((⟨x, hx⟩ : G) ^ Nat.card (S ⧸ Ideal.span {(N : S)})ˣ)
    (by rw [map_pow, pow_card_eq_one'])
  rwa [Subgroup.coe_pow, map_pow] at this

open GlobalTheory.AdLat

section Integral

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

noncomputable def hatRing : Subring (RA F E) where
  toAddSubgroup := hat1 F (Set.range (algebraMap (𝓞 E) E))
  one_mem' := one_tmul_mem_adelicCompletionOfElementSet F ⟨1, map_one _⟩
  mul_mem' := fun hx hy => mul_mem_adelicCompletionOfElementSet_of_mul_mem F
    (by rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩; exact ⟨x * y, map_mul _ _ _⟩) hx hy

theorem exists_int_add_nsmul (N : ℕ) (hN : 0 < N) (z : RA F E)
    (hz : z ∈ hat1 F (Set.range (algebraMap (𝓞 E) E))) :
    ∃ (x : 𝓞 E), ∃ w ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)),
      z = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (x : E) + N • w := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩ := hz
    obtain ⟨r, b, hb, rfl⟩ := (strong_approximation_mod_nat F N hN).2 a ha
    refine ⟨algebraMap (𝓞 F) (𝓞 E) r * x, _, tmul_mem_adelicCompletion_of_integral F hb ⟨x, rfl⟩, ?_⟩
    rw [TensorProduct.add_tmul, TensorProduct.smul_tmul', Algebra.algebraMap_eq_smul_one (r : F),
      TensorProduct.smul_tmul, Algebra.smul_def]
    rfl
  | zero => exact ⟨0, 0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨x, u, hu, rfl⟩ := hx
    obtain ⟨y, w, hw, rfl⟩ := hy
    refine ⟨x + y, u + w, add_mem hu hw, ?_⟩
    rw [show ((x + y : 𝓞 E) : E) = (x : E) + y from rfl, TensorProduct.tmul_add, smul_add]; abel
  | neg x _ hx =>
    obtain ⟨x, u, hu, rfl⟩ := hx
    refine ⟨-x, -u, neg_mem hu, ?_⟩
    rw [show ((-x : 𝓞 E) : E) = -(x : E) from rfl, TensorProduct.tmul_neg, smul_neg]; abel

theorem finite_quotient_hatRing (N : ℕ) (hN : 0 < N) :
    Finite (hatRing F E ⧸ Ideal.span {(N : hatRing F E)}) := by
  let ι : 𝓞 E →+* hatRing F E :=
    ((Algebra.TensorProduct.includeRight (R := F) (A := FiniteAdeleRing (𝓞 F) F)
      (B := E)).toRingHom.comp (algebraMap (𝓞 E) E)).codRestrict _
      fun x => one_tmul_mem_adelicCompletionOfElementSet F ⟨x, rfl⟩
  haveI : Finite (𝓞 E ⧸ Ideal.span {(N : 𝓞 E)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hN.ne')
  refine Finite.of_surjective (Ideal.quotientMap (I := Ideal.span {(N : 𝓞 E)})
    (Ideal.span {(N : hatRing F E)}) ι ?_) ?_
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    change ι N ∈ Ideal.span {(N : hatRing F E)}
    rw [map_natCast]
    exact Ideal.mem_span_singleton_self _
  · intro z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨x, w, hw, h⟩ := exists_int_add_nsmul F E N hN z z.2
    refine ⟨Ideal.Quotient.mk _ x, ?_⟩
    rw [Ideal.quotientMap_mk, eq_comm, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    refine ⟨⟨w, hw⟩, Subtype.ext ?_⟩
    change (z : RA F E) - (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (x : E) = ((N : hatRing F E) : RA F E) * w
    rw [h, add_sub_cancel_left, nsmul_eq_mul]
    simp

end Integral

theorem integralFiniteAdeles_eq_adelicCompletion_integers (D : D7) :
    intAE D = hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)) := by
  unfold intAE hat1
  congr 1
  ext z
  constructor
  · rintro ⟨a, ha, x, rfl⟩
    exact ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩
  · rintro ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩
    exact ⟨a, ha, x, rfl⟩

theorem char_finUnit_finite_order : ∀ (D : D7) (χ : (AE D)ˣ →* Circle), Continuous χ → ∃ N : ℕ, 0 < N ∧ (∀ x, FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = N • y) → χ x = 1) ∧ ∃ m : ℕ, 0 < m ∧ ∀ x, FinUnit x → χ x ^ m = 1 := by
  intro D χ hχ
  obtain ⟨e, he, -, he'⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  haveI : IsModuleTopology (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (RA D.host.F D.host.E) := ⟨rfl⟩
  haveI : ContinuousAdd (RA D.host.F D.host.E) :=
    IsModuleTopology.toContinuousAdd (FiniteAdeleRing (𝓞 D.host.F) D.host.F) _
  have hsmall := (OpenLat.isOpen_nsmul_hat D.host.F D.host.E 0 ⊤ (by simp)).2
  have := finite_order_of_small (infPart D) (finPart D) e.symm he'
    (fun z => by
      rw [RingEquiv.symm_apply_eq]
      exact Prod.ext (he z).1.symm (he z).2.symm)
    (hatRing D.host.F D.host.E) hsmall (finite_quotient_hatRing D.host.F D.host.E) χ hχ
  unfold FinUnit
  rw [integralFiniteAdeles_eq_adelicCompletion_integers]
  exact this

end GlobalTheory.CharFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ScaledFiniteMatrixMemLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockCompare GlobalTheory.VacUnique

namespace GlobalTheory.VacUnique.Den

theorem exists_nsmul_mem_lattice {E : Type} [Field E] [NumberField E] {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) (h : Submodule.IsFullLattice E Λ) (v : Fin n → E) :
    ∃ N : ℕ, 0 < N ∧ N • v ∈ Λ := by
  exact _root_.GlobalTheory.NatMulIntegralNsmul.exists_nsmul_mem Λ h v

theorem AA_ne_zero (D : D7) : D.host.AA ≠ 0 := by
  refine mul_ne_zero ?_ (inv_ne_zero ?_)
  · rw [FractionalIdeal.coeIdeal_ne_zero]
    intro h
    exact D.host.ccK_ne_bot ((Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.algebraMap.injective _ _)).1 h)
  · rw [FractionalIdeal.coeIdeal_ne_zero]
    intro h
    have h1 := D.host.𝔟_spec.1
    rw [h, Ideal.bot_mul] at h1
    exact differentIdeal_ne_bot h1

theorem exists_nsmul_finRat_mem : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), Submodule.IsFullLattice D.host.E ΛS → Submodule.IsFullLattice D.host.E ΛT → ∀ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ N : ℕ, 0 < N ∧ N • finRat S T γ ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) := by
  intro D S T ΛS ΛT hS hT γ
  obtain ⟨a, ha, ha0⟩ : ∃ a ∈ D.host.AA, a ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact AA_ne_zero D (FractionalIdeal.eq_zero_iff.2 hc)
  rw [Matrix.matrix_eq_sum_single γ]
  simp_rw [← Finset.sum_product']
  refine Finset.sum_induction _ (fun γ => ∃ N : ℕ, 0 < N ∧ N • finRat S T γ ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) ?_ ?_ ?_
  · rintro x y ⟨N, hN, hx⟩ ⟨M, hM, hy⟩
    refine ⟨N * M, mul_pos hN hM, ?_⟩
    rw [AddMonoidHom.map_add (f := _), nsmul_add]
    refine add_mem ?_ ?_
    · rw [mul_nsmul]; exact nsmul_mem hx M
    · rw [mul_nsmul']; exact nsmul_mem hy N
  · exact ⟨1, one_pos, by rw [AddMonoidHom.map_zero, nsmul_zero]; exact zero_mem _⟩
  · rintro ⟨i, j⟩ -
    obtain ⟨N, hN, ht⟩ := exists_nsmul_mem_lattice ΛT hT (Pi.single i (γ i j / a))
    obtain ⟨M, hM, hs⟩ := exists_nsmul_mem_lattice ΛS hS (fun k => star (S.gram⁻¹ j k))
    refine ⟨N * M, mul_pos hN hM, ?_⟩
    refine AddSubgroup.subset_closure ⟨1, fun w => by rw [map_one]; exact one_mem _, fun v hv => absurd trivial hv,
      a, ha, _, hs, _, ht, ?_⟩
    rw [← map_nsmul]
    funext i' j'
    show (pairA D.host.F 0 1) ⊗ₜ[D.host.F] _ = (pairA D.host.F 0 1) ⊗ₜ[D.host.F] _
    congr 1
    have hG : ∑ k, S.gram⁻¹ j k * S.gram k j' = (1 : Matrix _ _ D.host.E) j j' := by
      rw [← Matrix.mul_apply, Matrix.nonsing_inv_mul _ (Formalism.L2.Theta.gram_det_ne S).isUnit]
    have h2 : ∑ k, star ((M • fun k => star (S.gram⁻¹ j k)) k) * S.gram k j' =
        (M : D.host.E) * (1 : Matrix _ _ D.host.E) j j' := by
      rw [← hG, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Pi.smul_apply, star_nsmul, star_star, nsmul_eq_mul, mul_assoc]
    rw [h2]
    simp only [Matrix.smul_apply, Pi.smul_apply, nsmul_eq_mul, Matrix.single_apply, Pi.single_apply, Matrix.one_apply,
      Nat.cast_mul]
    by_cases h1 : i = i' <;> by_cases h3 : j = j'
    · subst h1 h3; simp; field_simp
    · simp [h3]
    · simp [h1, Ne.symm h1]
    · simp [h1, h3]

end GlobalTheory.VacUnique.Den
end

