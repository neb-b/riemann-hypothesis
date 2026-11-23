module

public import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.ContravariantIsotypicOrthogonal
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def restrictStableOperators {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V) (W : Submodule K V)
    (h : ∀ a b, ∀ x ∈ W, E a b x ∈ W) : GLOps n K W := fun a b => (E a b).restrict (h a b)

def CompleteReducibilityIsotypic : Prop :=
  ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] (n : ℕ) (E : GLOps n K V),
    IsGLRep E → (⨆ mu : Fin n → ℤ, isoSub E mu) = ⊤

def ContravariantIsotypicOrthogonal : Prop :=
  ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] (n : ℕ) (E : GLOps n K V),
    IsGLRep E → ∀ B : V →ₗ[K] V →ₗ[K] K, (∀ a b x y, B (E a b x) y = B x (E b a y)) →
      ∀ lam mu : Fin n → ℤ, lam ≠ mu → ∀ x ∈ isoSub E lam, ∀ y ∈ isoSub E mu, B x y = 0

def HighestWeightDominant : Prop :=
  ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (n : ℕ)
    (E : GLOps n K V), IsGLRep E → ∀ lam v, IsHWV E lam v → Dominant lam

def SubrepRestrictionRep : Prop :=
  ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] (n : ℕ) (E : GLOps n K V),
    IsGLRep E → ∀ (W : Submodule K V) (h : ∀ a b, ∀ x ∈ W, E a b x ∈ W),
      IsGLRep (restrictStableOperators E W h) ∧
      (∀ (mu : Fin n → ℤ) (x : W), x ∈ weightSp (restrictStableOperators E W h) mu ↔ (x : V) ∈ weightSp E mu) ∧
      (∀ a b k (x : W), ((divPowE (restrictStableOperators E W h) a b k x : W) : V) = divPowE E a b k x) ∧
      (∀ a k (x : W), ((binomE (restrictStableOperators E W h) a k x : W) : V) = binomE E a k x) ∧
      (∀ lam (e : Module.End K V), IsIsoProj E lam e →
        ∃ e' : Module.End K W, IsIsoProj (restrictStableOperators E W h) lam e' ∧ ∀ x : W, ((e' x : W) : V) = e x) ∧
      (∀ lam (e : Module.End K V), IsIsoProj E lam e → (¬ ∃ v : W, IsHWV (restrictStableOperators E W h) lam v) →
        ∀ x ∈ W, e x = 0)

def PolynomialGLRepresentation : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (ι : Type) [Fintype ι] (n : ℕ) (LL : Letters ι),
    (∀ S, IsGLRep (glOps K n LL S)) ∧
    (∀ S S' : Set ι, Disjoint S S' → ∀ a b c d,
      glOps K n LL S a b * glOps K n LL S' c d = glOps K n LL S' c d * glOps K n LL S a b) ∧
    (∀ S S' : Set ι, S ⊆ S' → ∀ a b, glOps K n LL S' a b = glOps K n LL S a b + glOps K n LL (S' \ S) a b) ∧
    (∀ S d a b, ∀ F ∈ Pol K n d, glOps K n LL S a b F ∈ Pol K n d) ∧
    (∀ d : ι → ℕ, FiniteDimensional K (Pol K n d)) ∧
    (∀ S mu F, F ∈ weightSp (glOps K n LL S) mu → ∀ m ∈ F.support, wtS LL S m = mu) ∧
    (∃ B : MvPolynomial (ι × Fin n) K →ₗ[K] MvPolynomial (ι × Fin n) K →ₗ[K] K,
      (∀ F G, B F G = fock F G) ∧ ∀ S a b F G, B (glOps K n LL S a b F) G = B F (glOps K n LL S b a G))

def latticeMultidegreePart {O : Type} [CommRing O] [IsDomain O] {ι : Type} {n : ℕ}
    (L : Submodule O (MvPolynomial (ι × Fin n) (KK O))) (d : ι → ℕ) : Submodule O (Pol (KK O) n d) :=
  L.comap (((Pol (KK O) n d).subtype).restrictScalars O)

def AdmissibleDVRIntegralFormLatticesStable : Prop :=
  ∀ (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (_S : UniformizedDVR p O),
    AdmissibleDVR p n' O → CharZero (KK O) ∧
    ∀ (n : ℕ) (ι : Type) [Fintype ι] (LL : Letters ι),
      (∀ S : Set ι, PolUZStable LL S (IntPol O (ι × Fin n)) ∧
        ∀ u ∈ polUZgens (KK O) LL S, ∀ F : MvPolynomial (ι × Fin n) (KK O),
          InBB (O := O) p F → InBB (O := O) p (u F)) ∧
      (∀ S : Set ι, ∀ u ∈ UZgens (glOps (KK O) n LL S),
        (∀ F ∈ IntPol O (ι × Fin n), u F ∈ IntPol O (ι × Fin n)) ∧
        ∀ F : MvPolynomial (ι × Fin n) (KK O), InBB (O := O) p F → InBB (O := O) p (u F)) ∧
      ∃ BBs : Submodule O (MvPolynomial (ι × Fin n) (KK O)), (∀ F, F ∈ BBs ↔ InBB (O := O) p F) ∧
        ∀ d : ι → ℕ, (latticeMultidegreePart (IntPol O (ι × Fin n)) d).FG ∧ MQ (K := KK O) (latticeMultidegreePart (IntPol O (ι × Fin n)) d) = ⊤ ∧
          (latticeMultidegreePart BBs d).FG ∧ MQ (K := KK O) (latticeMultidegreePart BBs d) = ⊤

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.EBeta
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees


open Classical in
def eBeta {R : Type} [CommRing R] {ι : Type} {r : ℕ} (LL : Letters ι) (S : Set ι) {k1 : Type} [CommRing k1]
    (j : R →+* k1) (g0 g0inv : Matrix (Fin r) (Fin r) k1) :
    MvPolynomial (ι × Fin r) R →+* MvPolynomial (ι × Fin r) k1 :=
  eval₂Hom (C.comp j) fun v =>
    if v.1 ∈ S then
      (if LL.vec v.1 then ∑ a : Fin r, C (g0inv a v.2) * X (v.1, a)
       else ∑ a : Fin r, C (g0 v.2 a) * X (v.1, a))
    else X v


open Classical in
def eWt {ι : Type} {r : ℕ} [NeZero r] (LL : Letters ι) (S : Set ι) (m : ι × Fin r →₀ ℕ) : ℤ :=
  m.sum fun v k => if v.2 = lastIdx r ∧ v.1 ∈ S then (if LL.vec v.1 then (k : ℤ) else -(k : ℤ)) else 0

def HSupp : Prop :=
  ∀ (R : Type) [Field R] (ι : Type) [Fintype ι] (LL : Letters ι) (r : ℕ) [NeZero r] (S : Set ι)
    (k1 : Type) [CommRing k1] (j : R →+* k1) (g0 g0inv : Matrix (Fin r) (Fin r) k1), g0 * g0inv = 1 →
    ∀ (G : MvPolynomial (ι × Fin r) R) (th : ℤ), (th : WithTop ℤ) ≤ valS LL S G →
      ∀ m ∈ (eBeta LL S j g0 g0inv G).support, th ≤ eWt LL S m

def matA (R : Type) [CommRing R] {ι : Type} {r : ℕ} (A : Fin r → ι) :
    Matrix (Fin r) (Fin r) (MvPolynomial (ι × Fin r) R) :=
  Matrix.of fun i j : Fin r => (X (A i, j) : MvPolynomial (ι × Fin r) R)

def HCop : Prop :=
  ∀ (R : Type) [Field R] (ι : Type) (r : ℕ) [NeZero r] (A : Fin r → ι), Function.Injective A →
    (matA R A).adjugate (lastIdx r) (lastIdx r) ≠ 0 ∧
    IsRelPrime (detA (R := R) A) ((matA R A).adjugate (lastIdx r) (lastIdx r))

def E1 : Prop :=
  ∀ (R : Type) [Field R] (ι : Type) [Fintype ι] (LL : Letters ι) (r : ℕ) [NeZero r] (S : Set ι)
    (A : Fin r → ι), Function.Injective A → (∀ l, A l ∈ S ∧ LL.vec (A l) = true) →
    (∀ (d : ι → ℕ) (G : MvPolynomial (ι × Fin r) R), G ∈ Pol R r d →
      ∀ th : ℤ, (th : WithTop ℤ) ≤ valS LL S G → (degOther LL S A d : ℤ) < th →
        (detA (R := R) A) ^ (th - degOther LL S A d).toNat ∣ G)

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.IntegralEnvelopingPreservesSubmodule
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem dvr_fraction_field_char_zero_prime {p : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (S : UniformizedDVR p O) (hp : p.Prime) : CharZero (KK O) := by
  obtain ⟨w, _, p_mem, p_ne, _⟩ := S
  haveI : CharZero O := by
    obtain ⟨q, hq⟩ := CharP.exists O
    rcases CharP.char_is_prime_or_zero O q with hqp | hq0
    · exfalso
      by_cases hdvd : q ∣ p
      · have hqp' : q = p := (Nat.prime_dvd_prime_iff_eq hqp hp).mp hdvd
        subst hqp'
        exact p_ne (CharP.cast_eq_zero O q)
      · have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hqp).mpr (fun h => hdvd (by subst h; exact dvd_rfl))
        have hu : IsUnit (p : ZMod q) := by
          rw [← ZMod.coe_unitOfCoprime p hcop]; exact Units.isUnit _
        have hu' : IsUnit (p : O) := by
          have h5 := hu.map (ZMod.castHom (dvd_refl q) O)
          simpa using h5
        exact (IsLocalRing.mem_maximalIdeal _).mp p_mem hu'
    · subst hq0
      exact CharP.charP_to_charZero O
  unfold KK
  exact charZero_of_injective_algebraMap (IsFractionRing.injective O (FractionRing O))

section field

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem mem_weightSpace_iff_diag_scalar {E : GLOps n K V} {mu : Fin n → ℤ} {x : V} :
    x ∈ weightSp E mu ↔ ∀ a, E a a x = (mu a : K) • x := by
  unfold weightSp
  simp [Submodule.mem_iInf, sub_eq_zero]

theorem inv_factorial_prod_eq_choose [CharZero K] (m : ℤ) (k : ℕ) :
    ((k.factorial : K)⁻¹) * ∏ j ∈ range k, ((m : K) - (j : K)) = ((Ring.choose m k : ℤ) : K) := by
  have h1 := Ring.descPochhammer_eq_factorial_smul_choose m k
  rw [← Polynomial.eval_eq_smeval, descPochhammer_eval_eq_prod_range, nsmul_eq_mul] at h1
  have h2 := congrArg (fun z : ℤ => (z : K)) h1
  push_cast at h2
  rw [h2, ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)), one_mul]

theorem binomial_diagonal_on_weight [CharZero K] {E : GLOps n K V} {mu : Fin n → ℤ} {x : V} (hx : x ∈ weightSp E mu)
    (a : Fin n) (k : ℕ) : binomE E a k x = ((Ring.choose (mu a) k : ℤ) : K) • x := by
  have hx' := (mem_weightSpace_iff_diag_scalar.mp hx) a
  unfold binomE
  rw [LinearMap.smul_apply, ← inv_factorial_prod_eq_choose (mu a) k, mul_smul]
  congr 1
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.prod_append, Finset.prod_range_succ]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, Module.End.mul_apply,
      LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hx']
    rw [← sub_smul, map_smul, ih, smul_smul]
    congr 1
    ring

def shiftedBinomialOperator (E : GLOps n K V) (a : Fin n) (c : ℤ) (d : ℕ) : Module.End K V :=
  ∑ ij ∈ antidiagonal d, ((Ring.choose c ij.2 : ℤ) : K) • binomE E a ij.1

theorem shifted_binomial_on_weight [CharZero K] {E : GLOps n K V} {mu : Fin n → ℤ} {x : V} (hx : x ∈ weightSp E mu)
    (a : Fin n) (c : ℤ) (d : ℕ) : shiftedBinomialOperator E a c d x = ((Ring.choose (mu a + c) d : ℤ) : K) • x := by
  unfold shiftedBinomialOperator
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, binomial_diagonal_on_weight hx, smul_smul, ← Finset.sum_smul]
  congr 1
  rw [Ring.add_choose_eq d (Commute.all _ _)]
  push_cast
  apply Finset.sum_congr rfl
  intro ij _
  ring

end field

section lattice

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

theorem intCast_smul_mem_submodule (M : Submodule O V) (z : ℤ) {x : V} (hx : x ∈ M) : ((z : ℤ) : KK O) • x ∈ M := by
  rw [Int.cast_smul_eq_zsmul]
  exact zsmul_mem hx z

theorem shifted_binomial_preserves_lattice {E : GLOps n (KK O) V} {M : Submodule O V} (hM : UZStable (O := O) E M) (a : Fin n) (c : ℤ)
    (d : ℕ) {x : V} (hx : x ∈ M) : shiftedBinomialOperator E a c d x ∈ M := by
  unfold UZStable at hM
  unfold shiftedBinomialOperator
  rw [LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro ij _
  rw [LinearMap.smul_apply]
  exact intCast_smul_mem_submodule M _ (hM _ (Or.inr ⟨a, ij.1, rfl⟩) x hx)

theorem lattice_stable_weight_separator [CharZero (KK O)] (E : GLOps n (KK O) V) {lam nu : Fin n → ℤ} (h : nu ≠ lam) :
    ∃ (T : Module.End (KK O) V) (g : (Fin n → ℤ) → ℤ), g lam = 1 ∧ g nu = 0 ∧
      (∀ mu, ∀ x ∈ weightSp E mu, T x = ((g mu : ℤ) : KK O) • x) ∧
      ∀ M : Submodule O V, UZStable (O := O) E M → ∀ x ∈ M, T x ∈ M := by
  have hex : ∃ a, nu a ≠ lam a := by
    by_contra hc
    push_neg at hc
    exact h (funext hc)
  obtain ⟨a, ha⟩ := hex
  rcases lt_or_gt_of_ne ha with hlt | hgt
  · obtain ⟨δ, hδ⟩ : ∃ δ : ℕ, lam a - nu a = δ := ⟨(lam a - nu a).toNat, by omega⟩
    refine ⟨shiftedBinomialOperator E a (-nu a) δ, fun mu => Ring.choose (mu a + -nu a) δ, ?_, ?_, ?_, ?_⟩
    · show Ring.choose (lam a + -nu a) δ = 1
      rw [show lam a + -nu a = (δ : ℤ) by omega, Ring.choose_natCast, Nat.choose_self, Nat.cast_one]
    · show Ring.choose (nu a + -nu a) δ = 0
      rw [show nu a + -nu a = ((0 : ℕ) : ℤ) by simp, Ring.choose_natCast,
        Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
    · intro mu x hx
      exact shifted_binomial_on_weight hx a (-nu a) δ
    · exact fun M hM x hx => shifted_binomial_preserves_lattice hM a (-nu a) δ hx
  · obtain ⟨δ, hδ⟩ : ∃ δ : ℕ, nu a - lam a = δ := ⟨(nu a - lam a).toNat, by omega⟩
    refine ⟨1 - shiftedBinomialOperator E a (-lam a) δ, fun mu => 1 - Ring.choose (mu a + -lam a) δ, ?_, ?_, ?_, ?_⟩
    · show 1 - Ring.choose (lam a + -lam a) δ = 1
      rw [show lam a + -lam a = ((0 : ℕ) : ℤ) by simp, Ring.choose_natCast,
        Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, sub_zero]
    · show 1 - Ring.choose (nu a + -lam a) δ = 0
      rw [show nu a + -lam a = (δ : ℤ) by omega, Ring.choose_natCast, Nat.choose_self, Nat.cast_one, sub_self]
    · intro mu x hx
      rw [LinearMap.sub_apply, Module.End.one_apply, shifted_binomial_on_weight hx a (-lam a) δ]
      push_cast
      rw [sub_smul, one_smul]
    · intro M hM x hx
      rw [LinearMap.sub_apply, Module.End.one_apply]
      exact M.sub_mem hx (shifted_binomial_preserves_lattice hM a (-lam a) δ hx)

theorem lattice_weight_components_mem [CharZero (KK O)] (E : GLOps n (KK O) V) (M : Submodule O V) (hM : UZStable (O := O) E M)
    (lam : Fin n → ℤ) (F : Finset (Fin n → ℤ)) : lam ∉ F → ∀ (y0 : V) (f : (Fin n → ℤ) → V),
      y0 ∈ weightSp E lam → (∀ nu ∈ F, f nu ∈ weightSp E nu) → y0 + ∑ nu ∈ F, f nu ∈ M → y0 ∈ M := by
  induction F using Finset.induction_on with
  | empty =>
    intro _ y0 f _ _ hmem
    simpa using hmem
  | @insert a F ha ih =>
    intro hl y0 f hy0 hf hmem
    have hal : a ≠ lam := fun h => hl (h ▸ Finset.mem_insert_self a F)
    obtain ⟨T, g', hg1, hg0, hT, hTM⟩ := lattice_stable_weight_separator E hal
    have hlF : lam ∉ F := fun h => hl (Finset.mem_insert_of_mem h)
    have h2 := hTM M hM _ hmem
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_add (f := _), map_sum, Finset.sum_insert ha] at h2
    rw [hT lam y0 hy0, hg1, hT a (f a) (hf a (Finset.mem_insert_self a F)), hg0] at h2
    have h3 : ∀ nu ∈ F, T (f nu) = ((g' nu : ℤ) : KK O) • f nu :=
      fun nu hnu => hT nu (f nu) (hf nu (Finset.mem_insert_of_mem hnu))
    rw [Finset.sum_congr rfl h3] at h2
    simp only [Int.cast_one, one_smul, Int.cast_zero, zero_smul, zero_add] at h2
    exact ih hlF y0 (fun nu => ((g' nu : ℤ) : KK O) • f nu) hy0
      (fun nu hnu => Submodule.smul_mem _ _ (hf nu (Finset.mem_insert_of_mem hnu))) h2

theorem weight_component_decomposition (E : GLOps n (KK O) V) (hE : (⨆ mu : Fin n → ℤ, weightSp E mu) = ⊤) (lam : Fin n → ℤ) (y : V) :
    ∃ (y0 : V) (F : Finset (Fin n → ℤ)) (f : (Fin n → ℤ) → V), lam ∉ F ∧ y0 ∈ weightSp E lam ∧
      (∀ nu ∈ F, f nu ∈ weightSp E nu) ∧ y = y0 + ∑ nu ∈ F, f nu := by
  have hy : y ∈ ⨆ mu : Fin n → ℤ, weightSp E mu := by
    rw [hE]; exact Submodule.mem_top
  obtain ⟨c, hc, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ y).mp hy
  refine ⟨c lam, c.support.erase lam, c, by simp, hc lam, fun nu _ => hc nu, ?_⟩
  rw [← hsum]
  simp only [Finsupp.sum]
  by_cases h : lam ∈ c.support
  · exact (Finset.add_sum_erase _ _ h).symm
  · have h0 : c lam = 0 := by simpa using h
    rw [Finset.erase_eq_self.mpr h, h0, zero_add]

theorem integral_enveloping_preserves_submodule {E : GLOps n (KK O) V} {M : Submodule O V} (hM : UZStable (O := O) E M)
    {u : Module.End (KK O) V} (hu : u ∈ UZmon E) : ∀ x ∈ M, u x ∈ M := by
  unfold UZmon at hu
  unfold UZStable at hM
  induction hu using Submonoid.closure_induction with
  | mem u hu => exact hM u hu
  | one => intro x hx; exact hx
  | mul u v _ _ hu hv => intro x hx; exact hu _ (hv x hx)

theorem sum_other_weights_mem (E : GLOps n (KK O) V) (lam : Fin n → ℤ) (F : Finset (Fin n → ℤ)) (hl : lam ∉ F)
    (f : (Fin n → ℤ) → V) (hf : ∀ nu ∈ F, f nu ∈ weightSp E nu) : ∑ nu ∈ F, f nu ∈ otherWts E lam := by
  unfold otherWts
  apply Submodule.sum_mem
  intro nu hnu
  have hne : nu ≠ lam := fun h => hl (h ▸ hnu)
  exact (le_iSup₂ (f := fun mu (_ : mu ∈ {mu | mu ≠ lam}) => weightSp E mu) nu hne) (hf nu hnu)

theorem highest_weight_lattice_bounds [CharZero (KK O)] (E : GLOps n (KK O) V) (hE : (⨆ mu : Fin n → ℤ, weightSp E mu) = ⊤)
    (lam : Fin n → ℤ) (v : V) (M : Submodule O V) (hM : UZStable (O := O) E M)
    (hl : ∀ x, (x ∈ M ∧ x ∈ weightSp E lam) ↔ ∃ c : O, x = c • v) :
    Delta (O := O) E v ≤ M ∧ (M : Set V) ⊆ Nabla (O := O) E lam v := by
  unfold Delta Nabla
  have hv : v ∈ M := ((hl v).mpr ⟨1, (one_smul O v).symm⟩).1
  constructor
  · rw [Submodule.span_le]
    rintro x ⟨u, hu, rfl⟩
    exact integral_enveloping_preserves_submodule hM hu v hv
  · intro x hx u hu
    have hux : u x ∈ M := integral_enveloping_preserves_submodule hM hu x hx
    obtain ⟨y0, F, f, hlF, hy0, hf, hdec⟩ := weight_component_decomposition E hE lam (u x)
    have hy0M : y0 ∈ M := lattice_weight_components_mem E M hM lam F hlF y0 f hy0 hf (by rw [← hdec]; exact hux)
    obtain ⟨c, hc⟩ := (hl y0).mp ⟨hy0M, hy0⟩
    refine ⟨c, ?_⟩
    rw [algebraMap_smul, hdec, hc, add_sub_cancel_left]
    exact sum_other_weights_mem E lam F hlF f hf

end lattice

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.InvariantDenominatorLinftyBound
section
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def linf {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V) (W : Submodule K V) : ℕ :=
  sSup {k | ∃ nu ∈ wtsOf E W, (∑ a, nu a = 0) ∧ ∃ a, k = (nu a).natAbs}

def InvariantDenominatorLinftyBound : Prop :=
  ∀ (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (_S : UniformizedDVR p O),
    AdmissibleDVR p n' O →
    ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]
      [FiniteDimensional (KK O) V] (E : GLOps n (KK O) V), IsGLRep E →
      ∀ M : Submodule O V, UZLattice E M → MQ (K := KK O) M = ⊤ →
      ∀ Inv : Module.End (KK O) V, IsInvProj E Inv →
        ∀ x ∈ M, ((p : O) ^ (N0 n * deF p n (linf E (MQ M)))) • Inv x ∈ M

def InvariantProjectionDenominator : Prop :=
  ∀ (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (_S : UniformizedDVR p O),
    AdmissibleDVR p n' O →
    ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]
      [FiniteDimensional (KK O) V] (E : GLOps n (KK O) V), IsGLRep E →
      ∀ M : Submodule O V, UZLattice E M → MQ (K := KK O) M = ⊤ →
      ∀ Inv : Module.End (KK O) V, IsInvProj E Inv →
        ∀ x ∈ M, ((p : O) ^ (N0 n * deF p n (ellOf E (MQ M)))) • Inv x ∈ M

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.IsotypicProjectorFixedMem
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

def highestWeightVectors {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V) (lam : Fin n → ℤ) :
    Submodule K V :=
  weightSp E lam ⊓ ⨅ a : Fin n, ⨅ b : Fin n, ⨅ (_ : a < b), LinearMap.ker (E a b)

def generatedSubrep {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V) (h : V) :
    Submodule K V :=
  Submodule.span K {x | ∃ u ∈ Umon E, x = u h}

def IsotypicProjectorFixedMem : Prop :=
  ∀ (K V : Type) [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (n : ℕ)
    (E : GLOps n K V), IsGLRep E → ∀ (lam : Fin n → ℤ) (e : Module.End K V), IsIsoProj E lam e →
      ∀ Y : V, e Y = Y → Y ∈ isoSub E lam

def GeneratedMultipleOfHWV : Prop :=
  ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] (n : ℕ)
    (E : GLOps n K V), IsGLRep E → ∀ (lam : Fin n → ℤ) (h : V), h ∈ highestWeightVectors E lam →
      generatedSubrep E h ≤ Submodule.span K {h} ⊔ ⨆ mu ∈ {mu : Fin n → ℤ | mu ≠ lam}, (weightSp E mu ⊓ generatedSubrep E h)

def DualLatticeDivisibility : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]
    [FiniteDimensional (KK O) V] (M : Submodule O V), M.FG → MQ (K := KK O) M = ⊤ →
    ∀ (t : KK O) (z : V),
      (∀ f : V →ₗ[KK O] KK O, (∀ x ∈ M, ∃ o : O, f x = algebraMap O (KK O) o) →
        ∃ o : O, f z = t * algebraMap O (KK O) o) →
      ∃ m ∈ M, z = t • m

def LatticeSubspaceBasis : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]
    [FiniteDimensional (KK O) V] (M : Submodule O V), M.FG → MQ (K := KK O) M = ⊤ →
    ∀ H : Submodule (KK O) V, ∃ (k : ℕ) (h : Fin k → V), (∀ j, h j ∈ M ∧ h j ∈ H) ∧
      LinearIndependent (KK O) h ∧ H ≤ Submodule.span (KK O) (Set.range h) ∧
      ∀ x ∈ M, x ∈ H → ∃ o : Fin k → O, x = ∑ j, o j • h j

def GeneratedLatticeCorollary : Prop :=
  ∀ (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (_S : UniformizedDVR p O),
    AdmissibleDVR p n' O →
    ∀ (n : ℕ) [NeZero n] (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V]
      [IsScalarTower O (KK O) V] [FiniteDimensional (KK O) V] (E : GLOps n (KK O) V), IsGLRep E →
      ∀ M : Submodule O V, UZLattice E M →
      ∀ lam : Fin n → ℤ, Dominant lam →
      ∀ π : Module.End (KK O) V, IsWtProj E lam π →
      ∀ h : V, h ∈ M → h ∈ highestWeightVectors E lam → h ≠ 0 →
      ∀ (c : ℤ) (y : V), y ∈ generatedSubrep E h →
        (∀ u ∈ UZmon E, ∃ o : O, π (u y) = ((p : KK O) ^ c * algebraMap O (KK O) o) • h) →
        ∃ m ∈ M, y = ((p : KK O) ^ (c - ((N0 n * deF p n (ellWt lam) : ℕ) : ℤ))) • m

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.NontrivialIsotypicWeightZeroKilled
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def binomialDiagonalSubring (E : GLOps n K V) : Subring (Module.End K V) :=
  Subring.closure {u | ∃ a k, u = binomE E a k}

def OperatorsShiftWeightsByRoots (E : GLOps n K V) : Prop :=
  ∀ a b ν, ∀ x ∈ weightSp E ν, E a b x ∈ weightSp E (ν + rootW a b)

def WeightsBounded (E : GLOps n K V) : Prop :=
  ∃ m : ℕ, ∀ ν, weightSp E ν ≠ ⊥ → ∀ a, |ν a| ≤ (m : ℤ)

def WeightProjectionsIntegralBinomial (E : GLOps n K V) : Prop :=
  ∃ Θ : (Fin n → ℤ) → Module.End K V, (∀ μ, Θ μ ∈ binomialDiagonalSubring E) ∧
    ∀ μ ν, ∀ x ∈ weightSp E ν, Θ μ x = if ν = μ then x else 0

def IsotypicComponentsSpanModule (E : GLOps n K V) : Prop := (⨆ mu : Fin n → ℤ, isoSub E mu) = ⊤

def TrivialIsotypicIsInvariant (E : GLOps n K V) : Prop :=
  ∀ x ∈ isoSub E 0, x ∈ weightSp E 0 ∧ ∀ a b : Fin n, a < b → E a b x = 0

def NontrivialIsotypicWeightZeroKilled (E : GLOps n K V) : Prop :=
  ∀ (P π : Module.End K V), IsWtProj E 0 π → (∀ w ∈ weightSp E 0, w ∈ nMinus E → P w = 0) →
    ∀ mu, mu ≠ 0 → ∀ x ∈ isoSub E mu, P (π x) = 0

end Formalism.MainNotions.G.GLWeightTheory
end
end

