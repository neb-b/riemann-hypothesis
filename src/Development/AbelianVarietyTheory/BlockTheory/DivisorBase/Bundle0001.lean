module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.AdelicScalarMultiplier
section
open scoped TensorProduct NumberField
open IsDedekindDomain

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.AdelicScalarMultiplier

abbrev Af : Type := FiniteAdeleRing ℤ ℚ

def zHat : Subring Af where
  carrier := {a | ∀ v : HeightOneSpectrum ℤ, a v ∈ v.adicCompletionIntegers ℚ}
  mul_mem' ha hb v := mul_mem (ha v) (hb v)
  one_mem' v := one_mem (v.adicCompletionIntegers ℚ)
  add_mem' ha hb v := add_mem (ha v) (hb v)
  zero_mem' v := zero_mem (v.adicCompletionIntegers ℚ)
  neg_mem' ha v := neg_mem (ha v)

def zHatUnits : Subgroup Afˣ := zHat.toSubmonoid.units

abbrev Idele (K : Type) [Field K] [NumberField K] : Type := (Af ⊗[ℚ] K)ˣ

def ideleNorm (K : Type) [Field K] [NumberField K] : Idele K →* Afˣ :=
  Units.map (Algebra.norm Af : Af ⊗[ℚ] K →* Af)

def NormUnitCond {K : Type} [Field K] [NumberField K] (s : Idele K) (q : ℚ) : Prop :=
  ∃ u ∈ zHatUnits, (u : Af) = (((ideleNorm K s)⁻¹ : Afˣ) : Af) * algebraMap ℚ Af q

section Herm

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  {W : Type} [AddCommGroup W] [Module ℚ W] [Module E W]



end Herm

section Groups

variable {E : Type} [Field E] [NumberField E]
  {W : Type} [AddCommGroup W] [Module ℚ W] [Module E W] [IsScalarTower ℚ E W]


variable [Module (𝓞 E) W]



end Groups

end GlobalTheory.IndefiniteRowSideFullHecke.AdelicScalarMultiplier
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.IdeleNormTraceForm
section
open NumberField IsDedekindDomain TensorProduct

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.IdeleNormTraceForm

abbrev Af : Type := FiniteAdeleRing (𝓞 ℚ) ℚ

def Zhat : Subring Af where
  carrier := {a | ∀ v : HeightOneSpectrum (𝓞 ℚ), a v ∈ v.adicCompletionIntegers ℚ}
  mul_mem' := fun {a b} ha hb v => (v.adicCompletionIntegers ℚ).mul_mem _ _ (ha v) (hb v)
  one_mem' := fun v => (v.adicCompletionIntegers ℚ).one_mem
  add_mem' := fun {a b} ha hb v => (v.adicCompletionIntegers ℚ).add_mem _ _ (ha v) (hb v)
  zero_mem' := fun v => (v.adicCompletionIntegers ℚ).zero_mem
  neg_mem' := fun {a} ha v => (v.adicCompletionIntegers ℚ).neg_mem _ (ha v)

def ZhatUnits : Subgroup Afˣ := Zhat.toSubmonoid.units

abbrev Adelic (V : Type) [AddCommGroup V] [Module ℚ V] : Type := Af ⊗[ℚ] V

def ideleNorm (K : Type) [Field K] [NumberField K] : (Adelic K)ˣ →* Afˣ :=
  Units.map (Algebra.norm Af : Adelic K →* Af)

def ratIdele : ℚˣ →* Afˣ := Units.map (algebraMap ℚ Af : ℚ →+* Af).toMonoidHom

def IsNormScale {K : Type} [Field K] [NumberField K] (s : (Adelic K)ˣ) (q : ℚˣ) : Prop :=
  0 < (q : ℚ) ∧ (ideleNorm K s)⁻¹ * ratIdele q ∈ ZhatUnits

section Groups

variable (E : Type) [Field E] [NumberField E]
variable {W : Type} [AddCommGroup W] [Module ℚ W] [Module E W] [IsScalarTower ℚ E W]

def IsHermitian [IsCMField E] (h : W →ₗ[ℚ] W →ₗ[ℚ] E) : Prop :=
  (∀ (a : E) (x y : W), h (a • x) y = a * h x y) ∧
    ∀ x y : W, h y x = IsCMField.complexConj E (h x y)

def traceForm (ξ₀ : E) (h : W →ₗ[ℚ] W →ₗ[ℚ] E) : LinearMap.BilinForm ℚ W :=
  h.compr₂ (Algebra.trace ℚ E ∘ₗ LinearMap.mulLeft ℚ ξ₀)



variable [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]

end Groups

end GlobalTheory.IndefiniteRowSideFullHecke.IdeleNormTraceForm
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.MultiplicationKernelIdentity
section
open Polynomial Module

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity

variable {C : Type} [Field C]

abbrev Int0 (v : AddValuation C (WithTop ℝ)) : Subring C :=
  (AddValuation.toValuation v).integer

theorem mem_addValuationIntegerRing_iff (v : AddValuation C (WithTop ℝ)) (x : C) : x ∈ Int0 v ↔ 0 ≤ v x := Iff.rfl

def RelLen (v : AddValuation C (WithTop ℝ)) {M : Type} [AddCommGroup M] [Module (Int0 v) M]
    (X' X : Submodule (Int0 v) M) (r : ℝ) : Prop :=
  ∃ (n : ℕ) (b : Basis (Fin n) (Int0 v) X) (b' : Basis (Fin n) (Int0 v) X')
    (A : Matrix (Fin n) (Fin n) (Int0 v)),
    (∀ k, (b' k : M) = ∑ i, A i k • (b i : M)) ∧ v (A.det : C) = (r : WithTop ℝ)

section Ring

variable {O : Type} [CommRing O] {S : Type} [Fintype S] [DecidableEq S]

abbrev RS (a : S → O) : Type := AdjoinRoot (∏ s, (X - Polynomial.C (a s)) : O[X])

def lin (a : S → O) (s : S) : RS a := AdjoinRoot.root _ - algebraMap O (RS a) (a s)

def cofac (a : S → O) (τ : S) : RS a := ∏ s ∈ Finset.univ.erase τ, lin a s

def ev (a : S → O) (s : S) : RS a →ₐ[O] O :=
  AdjoinRoot.liftAlgHom _ (AlgHom.id O O) (a s) (by
    rw [Polynomial.eval₂_finsetProd]
    exact Finset.prod_eq_zero (Finset.mem_univ s) (by simp))

def comp (a : S → O) (N : ℕ) (s : S) : (Fin N → RS a) →ₗ[O] (Fin N → O) :=
  (ev a s).toLinearMap.compLeft (Fin N)

def kerMul (a : S → O) (r : RS a) (M : Type) [AddCommGroup M] [Module (RS a) M] [Module O M]
    [IsScalarTower O (RS a) M] : Submodule O M :=
  (LinearMap.ker (LinearMap.lsmul (RS a) M r)).restrictScalars O

def imMul (a : S → O) (r : RS a) (M : Type) [AddCommGroup M] [Module (RS a) M] [Module O M]
    [IsScalarTower O (RS a) M] : Submodule O M :=
  (LinearMap.range (LinearMap.lsmul (RS a) M r)).restrictScalars O

def eigSub (a : S → O) (τ : S) (M : Type) [AddCommGroup M] [Module (RS a) M] [Module O M]
    [IsScalarTower O (RS a) M] : Submodule O M :=
  kerMul a (lin a τ) M

def eigQuot (a : S → O) {N : ℕ} (X : Submodule (RS a) (Fin N → RS a)) (s : S) :
    Submodule O (Fin N → O) :=
  (X.restrictScalars O).map (comp a N s)

def incl (a : S → O) {N : ℕ} (X : Submodule (RS a) (Fin N → RS a)) : X →ₗ[O] (Fin N → RS a) :=
  X.subtype.restrictScalars O

def proj (a : S → O) {N : ℕ} (X : Submodule (RS a) (Fin N → RS a)) :
    (Fin N → RS a) →ₗ[O] ((Fin N → RS a) ⧸ X) :=
  X.mkQ.restrictScalars O

theorem ev_lin (a : S → O) (s t : S) : ev a s (lin a t) = a s - a t := by
  simp [ev, lin]

end Ring

variable {S : Type} [Fintype S] [DecidableEq S]

def eigRank (v : AddValuation C (WithTop ℝ)) (a : S → Int0 v) {N : ℕ}
    (X : Submodule (RS a) (Fin N → RS a)) (s : S) : ℕ :=
  finrank C (Submodule.span C
    ((fun (x : Fin N → Int0 v) (i : Fin N) => (x i : C)) '' (eigQuot a X s : Set (Fin N → Int0 v))))

def vd (v : AddValuation C (WithTop ℝ)) (a : S → Int0 v) (τ : S) : WithTop ℝ :=
  v (∏ s ∈ Finset.univ.erase τ, ((a τ : C) - (a s : C)))

def yExp (v : AddValuation C (WithTop ℝ)) (a : S → Int0 v) {N : ℕ}
    (Fil : Submodule (RS a) (Fin N → RS a)) (τ : S) : WithTop ℝ :=
  ∑ s ∈ Finset.univ.erase τ, eigRank v a Fil s • v ((a s : C) - (a τ : C))

def DetIdentity (v : AddValuation C (WithTop ℝ)) (a : S → Int0 v) {N : ℕ}
    (Fil : Submodule (RS a) (Fin N → RS a)) (τ : S) : Prop :=
  ∃ p : ℕ, p + eigRank v a Fil τ = N ∧
    Nonempty (Basis (Fin N) (Int0 v) (eigSub a τ (Fin N → RS a))) ∧
    Nonempty (Basis (Fin p) (Int0 v) (eigSub a τ ((Fin N → RS a) ⧸ Fil))) ∧
    Nonempty (Basis (Fin (eigRank v a Fil τ)) (Int0 v) (eigQuot a Fil τ)) ∧
    ∀ (h : Basis (Fin N) (Int0 v) (eigSub a τ (Fin N → RS a)))
      (l : Basis (Fin p) (Int0 v) (eigSub a τ ((Fin N → RS a) ⧸ Fil)))
      (x : Fin p → (Fin N → RS a))
      (_ : ∀ i, proj a Fil (x i) = (l i : (Fin N → RS a) ⧸ Fil))
      (f : Basis (Fin (eigRank v a Fil τ)) (Int0 v) (eigQuot a Fil τ))
      (e : Fin N ≃ Fin p ⊕ Fin (eigRank v a Fil τ)),
      ∃ c : C, v c = yExp v a Fil τ ∧
        (Matrix.of fun k : Fin N =>
          Sum.elim (fun i => comp a N τ (x i)) (fun i => (f i : Fin N → Int0 v)) (e k)).det ≠ 0 ∧
        ((Matrix.of fun k : Fin N => comp a N τ (h k : Fin N → RS a)).det : C) =
          c * ((Matrix.of fun k : Fin N =>
            Sum.elim (fun i => comp a N τ (x i)) (fun i => (f i : Fin N → Int0 v)) (e k)).det : C)

def KernelIdentity (v : AddValuation C (WithTop ℝ)) (a : S → Int0 v) {N : ℕ}
    (Fil : Submodule (RS a) (Fin N → RS a)) (τ : S) : Prop :=
  (eigSub a τ (Fin N → RS a)).map (proj a Fil) ≤ eigSub a τ ((Fin N → RS a) ⧸ Fil) ∧
  eigSub a τ (Fin N → RS a) ⊓ LinearMap.ker (proj a Fil) = (eigSub a τ Fil).map (incl a Fil)

def LengthIdentities (v : AddValuation C (WithTop ℝ)) (a : S → Int0 v) {N : ℕ}
    (Fil : Submodule (RS a) (Fin N → RS a)) (τ : S) : Prop :=
  ∃ δ e₂ m : ℝ,
    RelLen v ((eigSub a τ (Fin N → RS a)).map (proj a Fil))
      (eigSub a τ ((Fin N → RS a) ⧸ Fil)) δ ∧
    RelLen v (imMul a (lin a τ) Fil) (kerMul a (cofac a τ) Fil) δ ∧
    RelLen v (imMul a (cofac a τ) Fil) (eigSub a τ Fil) e₂ ∧
    RelLen v ((eigSub a τ Fil).map ((comp a N τ).comp (incl a Fil))) (eigQuot a Fil τ) m ∧
    ((m + e₂ : ℝ) : WithTop ℝ) = eigRank v a Fil τ • vd v a τ ∧
    ((∀ s, eigRank v a Fil s = eigRank v a Fil τ) →
      0 ≤ δ ∧ (δ : WithTop ℝ) ≤ eigRank v a Fil τ • vd v a τ ∧
      0 ≤ m ∧ (m : WithTop ℝ) ≤ eigRank v a Fil τ • vd v a τ)

def HerbrandDet : Prop :=
  ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ))
    (S : Type) [Fintype S] [DecidableEq S] (a : S → Int0 v), Function.Injective a →
    ∀ (N : ℕ) (Fil : Submodule (RS a) (Fin N → RS a)),
      (∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x ∈ Fil → x ∈ Fil) →
      ∀ τ : S, DetIdentity v a Fil τ ∧ KernelIdentity v a Fil τ ∧ LengthIdentities v a Fil τ

theorem v_unit (v : AddValuation C (WithTop ℝ)) {u : Int0 v} (hu : IsUnit u) : v (u : C) = 0 := by
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  have h1 : v (u : C) + v (w : C) = 0 := by
    rw [← v.map_mul, ← Subring.coe_mul, hw]; simp
  have hu0 : 0 ≤ v (u : C) := u.2
  have hw0 : 0 ≤ v (w : C) := w.2
  refine le_antisymm ?_ hu0
  calc v (u : C) ≤ v (u : C) + v (w : C) := le_add_of_nonneg_right hw0
    _ = 0 := h1

theorem RelLen.unique (v : AddValuation C (WithTop ℝ)) {M : Type} [AddCommGroup M]
    [Module (Int0 v) M] {X' X : Submodule (Int0 v) M} {r r' : ℝ}
    (h : RelLen v X' X r) (h' : RelLen v X' X r') : r = r' := by
  obtain ⟨n, b, b', A, hA, hr⟩ := h
  obtain ⟨m, c, c', B, hB, hr'⟩ := h'
  have hnm : n = m := by simpa using Fintype.card_congr (b.indexEquiv c)
  subst hnm
  have hle : X' ≤ X := by
    intro x hx
    have : (x : M) = ∑ k, b'.repr ⟨x, hx⟩ k • (b' k : M) := by
      have := congrArg X'.subtype (b'.sum_repr ⟨x, hx⟩)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at this
      exact this.symm
    rw [this]
    refine X.sum_mem fun k _ => X.smul_mem _ ?_
    rw [hA k]
    exact X.sum_mem fun i _ => X.smul_mem _ (b i).2
  have key : ∀ (b : Basis (Fin n) (Int0 v) X) (b' : Basis (Fin n) (Int0 v) X')
      (A : Matrix (Fin n) (Fin n) (Int0 v)), (∀ k, (b' k : M) = ∑ i, A i k • (b i : M)) →
      LinearMap.toMatrix b' b (Submodule.inclusion hle) = A := by
    intro b b' A hA
    ext i k
    have : Submodule.inclusion hle (b' k) = ∑ i, A i k • b i := by
      apply Subtype.ext
      simpa using hA k
    rw [LinearMap.toMatrix_apply, this]
    simp [Finsupp.single_apply]
  have hAB : A = b.toMatrix c * B * c'.toMatrix b' := by
    rw [← key b b' A hA, ← key c c' B hB, basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix]
  have u1 : IsUnit (b.toMatrix c).det := by
    letI := b.invertibleToMatrix c
    exact Matrix.isUnit_det_of_invertible _
  have u2 : IsUnit (c'.toMatrix b').det := by
    letI := c'.invertibleToMatrix b'
    exact Matrix.isUnit_det_of_invertible _
  have : v (A.det : C) = v (B.det : C) := by
    rw [hAB, Matrix.det_mul, Matrix.det_mul, Subring.coe_mul, Subring.coe_mul, v.map_mul,
      v.map_mul, v_unit v u1, v_unit v u2, zero_add, add_zero]
  rw [hr, hr'] at this
  exact_mod_cast this

end GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TraceDualDifferent
section
noncomputable section

open NumberField nonZeroDivisors

namespace GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent

variable {F : Type} [Field F] [NumberField F]

def traceDual (M : FractionalIdeal (𝓞 F)⁰ F) : Set F :=
  {y | ∀ a ∈ M, ∃ n : ℤ, Algebra.trace ℚ F (y * a) = n}

def covol (M : FractionalIdeal (𝓞 F)⁰ F) : ℝ :=
  Real.sqrt |(discr F : ℝ)| * (FractionalIdeal.absNorm M : ℝ)

def dualCone (M : FractionalIdeal (𝓞 F)⁰ F) (z : (F →+* ℝ) → ℂ) : Set F :=
  {ν | ν ∈ traceDual M ∧ ∀ τ : F →+* ℝ, 0 < (SignType.sign (z τ).im : ℝ) * τ ν}

def lhsTerm (k : ℕ) (z : (F →+* ℝ) → ℂ) (a : F) : ℂ :=
  (∏ τ : F →+* ℝ, (z τ + ((τ a : ℝ) : ℂ))) ^ (-(k : ℤ))

def rhsTerm (k : ℕ) (z : (F →+* ℝ) → ℂ) (ν : F) : ℂ :=
  ((|∏ τ : F →+* ℝ, τ ν| ^ (k - 1) : ℝ) : ℂ) *
    Complex.exp (2 * Real.pi * Complex.I * ∑ τ : F →+* ℝ, ((τ ν : ℝ) : ℂ) * z τ)

def lipConst (k : ℕ) (M : FractionalIdeal (𝓞 F)⁰ F) : ℂ :=
  (2 * Real.pi * Complex.I) ^ (k * Module.finrank ℚ F) /
    ((((k - 1).factorial : ℕ) : ℂ) ^ Module.finrank ℚ F * (covol M : ℂ))

def Lipschitz : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (M : FractionalIdeal (𝓞 F)⁰ F), M ≠ 0 →
    ∀ (k : ℕ), 2 ≤ k → Even k →
    ∀ (z : (F →+* ℝ) → ℂ), (∀ τ, (z τ).im ≠ 0) →
      Summable (fun a : (M : Set F) => lhsTerm k z a) ∧
      Summable (fun ν : dualCone M z => rhsTerm k z ν) ∧
      ∑' a : (M : Set F), lhsTerm k z a = lipConst k M * ∑' ν : dualCone M z, rhsTerm k z ν


open NumberField nonZeroDivisors in
variable {F : Type} [Field F] [NumberField F] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.mem_traceDual_iff {M : FractionalIdeal (𝓞 F)⁰ F} (hM : M ≠ 0) (y : F) :
    y ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.traceDual M ↔ y ∈ FractionalIdeal.dual ℤ ℚ M := by
  change (∀ a ∈ M, ∃ n : ℤ, Algebra.trace ℚ F (y * a) = n) ↔ _
  rw [FractionalIdeal.mem_dual hM]
  refine forall₂_congr fun a _ => ?_
  simp [Algebra.traceForm_apply, eq_comm]


open NumberField nonZeroDivisors in
variable {F : Type} [Field F] [NumberField F] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.covol_pos {M : FractionalIdeal (𝓞 F)⁰ F} (hM : M ≠ 0) :
    0 < _root_.GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.covol M := by
  refine mul_pos (Real.sqrt_pos.2 (abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero F)))) ?_
  exact_mod_cast lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg M)
    (Ne.symm (FractionalIdeal.absNorm_eq_zero_iff.not.2 hM))


open scoped Classical in
open NumberField nonZeroDivisors in
variable {F : Type} [Field F] [NumberField F] in
open Classical in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.covol_eq_covolume [IsTotallyReal F]
    (M : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.covol (M : FractionalIdeal (𝓞 F)⁰ F) =
      ZLattice.covolume (E := mixedEmbedding.mixedSpace F)
        (mixedEmbedding.idealLattice F M) MeasureTheory.volume := by
  rw [mixedEmbedding.covolume_idealLattice, IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero,
    mul_one, mul_comm]
  rfl


open NumberField nonZeroDivisors in
variable {F : Type} [Field F] [NumberField F] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.card_realEmb [IsTotallyReal F] :
    Fintype.card (F →+* ℝ) = Module.finrank ℚ F := by
  classical
  rw [IsTotallyReal.finrank, ← InfinitePlace.card_real_embeddings]
  convert Fintype.card_congr
    { toFun := fun φ => ⟨Complex.ofRealHom.comp φ, ?_⟩
      invFun := fun φ => φ.2.embedding
      left_inv := ?_
      right_inv := ?_ : (F →+* ℝ) ≃ { φ : F →+* ℂ // ComplexEmbedding.IsReal φ } }
  · rw [ComplexEmbedding.isReal_iff]; ext x; simp [ComplexEmbedding.conjugate]
  · intro φ; ext x
    simpa using ComplexEmbedding.IsReal.coe_embedding_apply (φ := Complex.ofRealHom.comp φ) _ x
  · intro φ; ext x; simp [ComplexEmbedding.IsReal.coe_embedding_apply]

end GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
end
end

