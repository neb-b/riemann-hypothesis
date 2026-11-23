module

public import Mathlib

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DetAlg
section
namespace ReciprocityTheory.ChartRestriction.G.TB

def DetAlgSt : Prop :=
  ∀ (K : Type) [Field K] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) K)), I.IsRadical →
    ∀ r : MvPolynomial (Fin n) K ⧸ I,
      (∀ (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L]
        (φ : (MvPolynomial (Fin n) K ⧸ I) →ₐ[K] L), φ r = 0) → r = 0

theorem detAlg_holds : DetAlgSt := by
  intro K _ n I hI r hr
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective r
  rw [Ideal.Quotient.eq_zero_iff_mem, ← IsJacobsonRing.out inferInstance hI]
  unfold Ideal.jacobson
  rw [Ideal.mem_sInf]
  rintro J ⟨hIJ, hJ⟩
  haveI := hJ
  letI : Field (MvPolynomial (Fin n) K ⧸ J) := Ideal.Quotient.field J
  haveI : Algebra.FiniteType K (MvPolynomial (Fin n) K ⧸ J) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K J)
      (Ideal.Quotient.mkₐ_surjective K J)
  haveI : FiniteDimensional K (MvPolynomial (Fin n) K ⧸ J) :=
    finite_of_finite_type_of_isJacobsonRing K _
  have h := hr (MvPolynomial (Fin n) K ⧸ J) (Ideal.Quotient.factorₐ K hIJ)
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact h

end ReciprocityTheory.ChartRestriction.G.TB
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.GaugeRatio
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace ReciprocityTheory.ChartRestriction.G.TB

abbrev GLet (T : Type) (rk : T → ℕ) : Type := Σ σ : T, Fin (rk σ)

def scaleBy {O k T : Type} [CommRing O] [CommRing k] {rk : T → ℕ} (χ : T → O →+* k) (a : O) :
    MvPowerSeries (GLet T rk) k →+* MvPowerSeries (GLet T rk) k :=
  MvPowerSeries.rescale (fun l => χ l.1 a)

def GaugeRatioSt : Prop :=
  ∀ (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] (T : Type) [Fintype T]
    (rk : T → ℕ) (χ : T → O →+* k) (cc : T → T),
    (∀ σ a, χ (cc σ) a = χ σ (star a)) →
    (∀ σ τ, σ ≠ τ → ∃ a, IsUnit (χ σ a - χ τ a)) →
    ∀ r : MvPowerSeries (GLet T rk) k, constantCoeff r = 1 →
    (∀ a : O, scaleBy χ (1 + a * star a) r = scaleBy χ a r ^ 2 * r * scaleBy χ (a * star a) r) →
    ∃ q : MvPowerSeries (GLet T rk) k, constantCoeff q = 0 ∧
      (∀ m, coeff m q ≠ 0 → m.degree = 2) ∧
      (∀ l l' : GLet T rk, coeff (Finsupp.single l 1 + Finsupp.single l' 1) q ≠ 0 → l'.1 = cc l.1) ∧
      r = PowerSeries.subst q (PowerSeries.exp k)

end ReciprocityTheory.ChartRestriction.G.TB
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.IdemDen
section
noncomputable section

open NumberField TensorProduct

namespace ReciprocityTheory.ChartRestriction.G.TB

def trDual {E : Type} [Field E] [NumberField E] {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ E) :
    Module.Basis ι ℚ E :=
  (Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) b

def idemOf {E : Type} [Field E] [NumberField E] {C : Type} [Field C] [Algebra ℚ C] {ι : Type} [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι ℚ E) (τ : E →+* C) : E ⊗[ℚ] C :=
  ∑ i, trDual b i ⊗ₜ[ℚ] τ (b i)

def evAt {E : Type} [Field E] {C : Type} [Field C] [Algebra ℚ E] [Algebra ℚ C] (σ : E →+* C) :
    E ⊗[ℚ] C →ₐ[ℚ] C :=
  Algebra.TensorProduct.productMap (σ.toRatAlgHom) (AlgHom.id ℚ C)


open Classical in
def IdemEvalSt : Prop := by
  classical
  exact ∀ (E : Type) [Field E] [NumberField E] (C : Type) [Field C] [CharZero C] [IsAlgClosed C] (ι : Type)
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ E) (τ σ : E →+* C),
    evAt σ (idemOf b τ) = if σ = τ then 1 else 0

def DualDiffSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (ι : Type) [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ E),
    (∀ i, IsIntegral ℤ (b i)) →
    (∀ x : 𝓞 E, ∃ c : ι → ℤ, (x : E) = ∑ i, (c i : ℚ) • b i) →
    ∀ δ ∈ differentIdeal ℤ (𝓞 E), ∀ i, IsIntegral ℤ ((δ : E) * trDual b i)

end ReciprocityTheory.ChartRestriction.G.TB
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.JInjCore
section
namespace ReciprocityTheory.ChartRestriction.G.TB

def IndepDescentSt : Prop :=
  ∀ (K F : Type) [Field K] [Field F] [Algebra K F] [IsGalois K F] (ι : F →+* ℂ)
    (C : Type) [AddCommGroup C] [Module K C] (Pt : Type) (v : C →ₗ[K] (Pt → F))
    (act : (F ≃ₐ[K] F) → Pt → Pt),
    (∀ g, Function.Bijective (act g)) →
    (∀ g f y, v f (act g y) = g (v f y)) →
    Function.Injective v →
    ∀ (n : ℕ) (b : Fin n → C), LinearIndependent K b →
      LinearIndependent ℂ (fun i => (fun y => ι (v (b i) y) : Pt → ℂ))

theorem mem_bot_of_fixed {K F : Type} [Field K] [Field F] [Algebra K F] [IsGalois K F] (a : F)
    (ha : ∀ g : F ≃ₐ[K] F, g a = a) : a ∈ (⊥ : IntermediateField K F) := by
  exact (InfiniteGalois.mem_bot_iff_fixed a).mpr ha

theorem rel_zero {K F C Pt : Type} [Field K] [Field F] [Algebra K F] [IsGalois K F]
    [AddCommGroup C] [Module K C] (v : C →ₗ[K] (Pt → F)) (act : (F ≃ₐ[K] F) → Pt → Pt)
    (hbij : ∀ g, Function.Bijective (act g)) (heq : ∀ g f y, v f (act g y) = g (v f y))
    (hinj : Function.Injective v) {n : ℕ} (b : Fin n → C) (hb : LinearIndependent K b) :
    ∀ (s : Finset (Fin n)) (a : Fin n → F), (∀ y, ∑ i ∈ s, a i * v (b i) y = 0) → ∀ i ∈ s, a i = 0 := by
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
  intro a ha i0 hi0
  by_contra hne
  obtain ⟨a', ha'⟩ : ∃ a' : Fin n → F, ∀ i, a' i = (a i0)⁻¹ * a i := ⟨_, fun _ => rfl⟩
  have ha'rel : ∀ y, ∑ i ∈ s, a' i * v (b i) y = 0 := by
    intro y
    simp only [ha', mul_assoc]
    rw [← Finset.mul_sum, ha y, mul_zero]
  have ha'1 : a' i0 = 1 := by rw [ha']; exact inv_mul_cancel₀ hne
  have hfix : ∀ i ∈ s, ∀ g : F ≃ₐ[K] F, g (a' i) = a' i := by
    intro i hi g
    have hrel_g : ∀ y, ∑ j ∈ s, g (a' j) * v (b j) y = 0 := by
      intro y
      obtain ⟨x, rfl⟩ := (hbij g).2 y
      have h1 := congrArg g (ha'rel x)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_zero] at h1
      simp only [map_mul, ← heq] at h1
      exact h1
    have hdiff : ∀ y, ∑ j ∈ s.erase i0, (g (a' j) - a' j) * v (b j) y = 0 := by
      intro y
      rw [Finset.sum_erase]
      · simp only [sub_mul, Finset.sum_sub_distrib, hrel_g y, ha'rel y, sub_zero]
      · rw [ha'1, map_one, sub_self, zero_mul]
    by_cases hii : i = i0
    · rw [hii, ha'1, map_one]
    · have h2 := ih (s.erase i0) (Finset.erase_ssubset hi0) (fun j => g (a' j) - a' j) hdiff i
        (Finset.mem_erase.mpr ⟨hii, hi⟩)
      exact sub_eq_zero.mp h2
  have hK : ∀ i ∈ s, ∃ c : K, algebraMap K F c = a' i := fun i hi =>
    IntermediateField.mem_bot.mp (mem_bot_of_fixed (a' i) (hfix i hi))
  choose! c hc using hK
  have hv0 : v (∑ i ∈ s, c i • b i) = 0 := by
    funext y
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_apply, Pi.zero_apply, ← ha'rel y]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [map_smul, Pi.smul_apply, Algebra.smul_def, hc i hi]
  have hsum0 : ∑ i ∈ s, c i • b i = 0 := hinj (by rw [hv0, map_zero])
  have hc0 := (linearIndependent_iff'.mp hb) s c hsum0 i0 hi0
  rw [← hc i0 hi0, hc0, map_zero] at ha'1
  exact zero_ne_one ha'1

private theorem exists_finset_linearIndependent_restrict {F Pt : Type} [Field F] {n : ℕ} (w : Fin n → Pt → F)
    (hw : LinearIndependent F w) :
    ∃ S : Finset Pt, LinearIndependent F (fun i (y : S) => w i y) := by
  classical
  let Ker : Finset Pt → Submodule F (Fin n → F) := fun S =>
    LinearMap.ker (Fintype.linearCombination F (fun i (y : S) => w i y))
  have hex : ∃ m, ∃ S : Finset Pt, Module.finrank F (Ker S) = m := ⟨_, ∅, rfl⟩
  obtain ⟨S, hS⟩ := Nat.find_spec hex
  refine ⟨S, ?_⟩
  rw [Fintype.linearIndependent_iff]
  intro c hc
  by_contra hne
  push Not at hne
  obtain ⟨i1, hi1⟩ := hne
  have hsum : (∑ i, c i • w i) ≠ 0 := fun h =>
    hi1 (Fintype.linearIndependent_iff.mp hw c h i1)
  obtain ⟨y, hy⟩ : ∃ y, (∑ i, c i • w i) y ≠ 0 := by
    by_contra h
    push Not at h
    exact hsum (funext h)
  have hcS : c ∈ Ker S := by
    change Fintype.linearCombination F (fun i (y : S) => w i y) c = 0
    rw [Fintype.linearCombination_apply]
    exact hc
  have hle : Ker (insert y S) ≤ Ker S := by
    intro d hd
    change Fintype.linearCombination F (fun i (z : (insert y S : Finset Pt)) => w i z) d = 0 at hd
    change Fintype.linearCombination F (fun i (z : S) => w i z) d = 0
    rw [Fintype.linearCombination_apply] at hd ⊢
    funext z
    have h3 := congrFun hd ⟨z, Finset.mem_insert_of_mem z.2⟩
    simpa [Finset.sum_apply] using h3
  have hnot : c ∉ Ker (insert y S) := by
    intro hc'
    change Fintype.linearCombination F (fun i (z : (insert y S : Finset Pt)) => w i z) c = 0 at hc'
    rw [Fintype.linearCombination_apply] at hc'
    have h3 := congrFun hc' ⟨y, Finset.mem_insert_self y S⟩
    apply hy
    simpa [Finset.sum_apply] using h3
  have hlt : Ker (insert y S) < Ker S := lt_of_le_of_ne hle fun h => hnot (h ▸ hcS)
  have h4 := Submodule.finrank_lt_finrank_of_lt hlt
  have h5 := Nat.find_min' hex ⟨insert y S, rfl⟩
  omega

theorem indepDescent_holds : IndepDescentSt := by
  intro K F _ _ _ _ ι C _ _ Pt v act hbij heq hinj n b hb
  have hwF : LinearIndependent F (fun i => v (b i)) := by
    rw [Fintype.linearIndependent_iff]
    intro a ha i
    refine rel_zero v act hbij heq hinj b hb Finset.univ a (fun y => ?_) i (Finset.mem_univ i)
    have h1 := congrFun ha y
    simpa [Finset.sum_apply] using h1
  obtain ⟨S, hS⟩ := exists_finset_linearIndependent_restrict (fun i => v (b i)) hwF
  let : Algebra F ℂ := ι.toAlgebra
  have hC : LinearIndependent ℂ (fun i => algebraMap F ℂ ∘ (fun (y : S) => v (b i) y)) :=
    linearIndependent_algebraMap_comp_iff.mpr hS
  apply LinearIndependent.of_comp (LinearMap.funLeft ℂ ℂ (fun y : S => (y : Pt)))
  exact hC

end ReciprocityTheory.ChartRestriction.G.TB
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.JetGlue
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace ReciprocityTheory.ChartRestriction.G.TB

abbrev JetRing (S : Type) [CommRing S] (κ : Type) (m : ℕ) : Type :=
  MvPolynomial κ S ⧸ (Ideal.span (Set.range (MvPolynomial.X : κ → MvPolynomial κ S))) ^ (m + 1)

abbrev JetLoc (S : Type) [CommRing S] (κ : Type) (m : ℕ) (𝔭 : Ideal S) [𝔭.IsPrime] : Type :=
  Localization (Algebra.algebraMapSubmonoid (JetRing S κ m) 𝔭.primeCompl)

def JetGlueSt : Prop :=
  ∀ (S : Type) [CommRing S] (κ : Type) [Finite κ] (m : ℕ) (X : Scheme.{0})
    (f g : Spec (CommRingCat.of (JetRing S κ m)) ⟶ X),
    (∀ (𝔭 : Ideal S) [𝔭.IsPrime],
      Spec.map (CommRingCat.ofHom (algebraMap (JetRing S κ m) (JetLoc S κ m 𝔭))) ≫ f =
        Spec.map (CommRingCat.ofHom (algebraMap (JetRing S κ m) (JetLoc S κ m 𝔭))) ≫ g) →
    f = g

end ReciprocityTheory.ChartRestriction.G.TB
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.PerpVecPerpSt
section
namespace ReciprocityTheory.ChartRestriction.G.TB

open MvPolynomial

variable {R : Type} [CommRing R]

noncomputable def xForm {p q n : ℕ} (e : Fin p → Fin n → R) (a b : Fin p) :
    MvPolynomial ((Fin p × Fin n) ⊕ (Fin q × Fin n)) R :=
  ∑ k, X (Sum.inl (a, k)) * C (e b k)

noncomputable def yForm {p q n : ℕ} (f : Fin q → Fin n → R) (a b : Fin q) :
    MvPolynomial ((Fin p × Fin n) ⊕ (Fin q × Fin n)) R :=
  ∑ k, X (Sum.inr (a, k)) * C (f b k)

noncomputable def leadMinor {S : Type} [CommRing S] {m : ℕ} (M : Matrix (Fin m) (Fin m) S) (i : Fin (m + 1)) : S :=
  (M.submatrix (Fin.castLE (Nat.lt_succ_iff.mp i.isLt)) (Fin.castLE (Nat.lt_succ_iff.mp i.isLt)) :
    Matrix (Fin i) (Fin i) S).det

section Perp

variable {V : Type} [AddCommGroup V] [Module R V]

def hMat {p : ℕ} (h : V →ₗ[R] (V → R)) (e e' : Fin p → V) : Matrix (Fin p) (Fin p) R :=
  Matrix.of fun a' a => h (e' a') (e a)

def perpVec {p : ℕ} (h : V →ₗ[R] (V → R)) (e e' : Fin p → V) (g : V) : V :=
  (hMat h e e').det • g - ∑ a, ∑ a', ((hMat h e e').adjugate a a' * h g (e a)) • e' a'

end Perp

def PerpVecSt : Prop :=
  ∀ (R : Type) [CommRing R] (V : Type) [AddCommGroup V] [Module R V] (p : ℕ)
    (h : V →ₗ[R] (V → R)) (e e' : Fin p → V) (g : V) (c : Fin p), h (perpVec h e e' g) (e c) = 0

def PerpVecPerpSt : Prop :=
  ∀ (R : Type) [CommRing R] (V : Type) [AddCommGroup V] [Module R V] (p : ℕ)
    (h : V →ₗ[R] (V → R)) (e e' : Fin p → V) (g : V),
    (∀ a, h g (e a) = 0) → perpVec h e e' g = (hMat h e e').det • g

end ReciprocityTheory.ChartRestriction.G.TB
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.RatIntUnifDiscrete
section
namespace ReciprocityTheory.ChartRestriction.G.TB

open NumberField

structure NormFam (K : Type) [Field K] (V : Type) [AddCommGroup V] [Module K V] where
  N : (K →+* ℂ) → V → ℝ
  nonneg : ∀ σ v, 0 ≤ N σ v
  eq_zero : ∀ σ v, N σ v = 0 → v = 0
  smul : ∀ σ (a : K) v, N σ (a • v) = ‖σ a‖ * N σ v
  add : ∀ σ v w, N σ (v + w) ≤ N σ v + N σ w

section Defs

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V]

def ProdLower (Nf : NormFam K V) (M : Submodule (𝓞 K) V) (A : ℝ) : Prop :=
  ∀ f ∈ M, f ≠ 0 → -A ≤ ∑ σ : K →+* ℂ, Real.log (Nf.N σ f)

def UnifDiscrete (Nf : NormFam K V) (M : Submodule (𝓞 K) V) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ f ∈ M, (∀ σ, Nf.N σ f < ε) → f = 0

end Defs

def DiscOfProdLowerSt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (V : Type) [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] (Nf : NormFam K V) (M : Submodule (𝓞 K) V) (A : ℝ),
    ProdLower Nf M A → UnifDiscrete Nf M

def FGOfDiscSt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (V : Type) [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V]
    (Nf : NormFam K V) (M : Submodule (𝓞 K) V),
    UnifDiscrete Nf M → M.FG

def IsLatticeOfDiscSt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (V : Type) [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V]
    (Nf : NormFam K V) (M : Submodule (𝓞 K) V),
    UnifDiscrete Nf M → Submodule.span K (M : Set V) = ⊤ → Submodule.IsLattice K M

theorem rat_emb_apply (σ : ℚ →+* ℂ) (q : ℚ) : σ q = (q : ℂ) := eq_ratCast σ q

noncomputable def ratNormFam : NormFam ℚ ℚ where
  N σ v := ‖σ v‖
  nonneg _ _ := norm_nonneg _
  eq_zero σ v h := by simpa using h
  smul σ a v := by rw [smul_eq_mul, map_mul, norm_mul]
  add σ v w := by rw [map_add (f := _)]; exact norm_add_le _ _

noncomputable def ratInt : Submodule (𝓞 ℚ) ℚ := Submodule.span (𝓞 ℚ) {1}

theorem mem_ratInt {f : ℚ} (hf : f ∈ ratInt) : ∃ n : ℤ, f = n := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hf
  have hi : IsIntegral ℤ (a : ℚ) := RingOfIntegers.isIntegral_coe a
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
  refine ⟨n, ?_⟩
  rw [Algebra.smul_def, mul_one]
  simpa using hn.symm

theorem ratInt_prodLower : ProdLower ratNormFam ratInt 0 := by
  intro f hf hf0
  obtain ⟨n, rfl⟩ := mem_ratInt hf
  have hn : n ≠ 0 := by exact_mod_cast hf0
  rw [neg_zero]
  refine Finset.sum_nonneg fun σ _ => Real.log_nonneg ?_
  show 1 ≤ ‖σ (n : ℚ)‖
  rw [rat_emb_apply, Rat.cast_intCast, Complex.norm_intCast]
  exact_mod_cast Int.one_le_abs hn

theorem ratInt_unifDiscrete : UnifDiscrete ratNormFam ratInt := by
  refine ⟨1, one_pos, fun f hf hsmall => ?_⟩
  obtain ⟨n, rfl⟩ := mem_ratInt hf
  have h := hsmall (Rat.castHom ℂ)
  change ‖(Rat.castHom ℂ) (n : ℚ)‖ < 1 at h
  rw [rat_emb_apply, Rat.cast_intCast, Complex.norm_intCast] at h
  have h' : |n| < 1 := by exact_mod_cast h
  have : n = 0 := by rwa [Int.abs_lt_one_iff] at h'
  simp [this]

theorem ratInt_span : Submodule.span ℚ (ratInt : Set ℚ) = ⊤ := by
  have h1 : (1 : ℚ) ∈ ratInt := Submodule.subset_span (Set.mem_singleton 1)
  rw [Submodule.eq_top_iff']
  intro x
  have := Submodule.smul_mem (Submodule.span ℚ (ratInt : Set ℚ)) x (Submodule.subset_span h1)
  simpa using this

end ReciprocityTheory.ChartRestriction.G.TB
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ScaledBoundInequalityHypothesesOne
section
namespace ReciprocityTheory.ChartRestriction.G.TB

open ComplexConjugate

def SchwarzBallSt : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (u : E → ℂ) (ρ M : ℝ),
    0 < ρ → DifferentiableOn ℂ u (Metric.ball 0 ρ) → (∀ z ∈ Metric.ball (0 : E) ρ, ‖u z - u 0‖ ≤ M) →
      ∀ z ∈ Metric.ball (0 : E) ρ, ‖u z - u 0‖ ≤ M * ‖z‖ / ρ

def EBasisSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (W : Type) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    [Module ℚ W] [IsScalarTower ℚ E W] (ι : Type) [Fintype ι] (v : ι → W),
    LinearIndependent ℚ v → Fintype.card ι = Module.finrank ℚ E * Module.finrank E W →
      ∃ s : Finset ι, s.card = Module.finrank E W ∧ LinearIndependent E (fun i : s => v i) ∧
        Submodule.span E (Set.range fun i : s => v i) = ⊤

end ReciprocityTheory.ChartRestriction.G.TB
end

