module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1077
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1277
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1196
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1276
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1257

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralMatrixIffBoundedPowers
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

namespace GlobalTheory.IntMatBound

variable (K : UQ) {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (e : K.E ≃+* L)

def boundSub (he : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) (n : ℕ) (m : ℤ) :
    Submodule K.O (Matrix (Fin n) (Fin n) K.E) where
  carrier := {X | ∀ i j, Valued.v (e (X i j)) ≤ WithZero.exp m}
  add_mem' := by
    intro X Y hX hY i j
    simp only [Matrix.add_apply, map_add (f := _)]
    exact Valuation.map_add_le _ (hX i j) (hY i j)
  zero_mem' := by
    intro i j
    simp
  smul_mem' := by
    intro c X hX i j
    simp only [Matrix.smul_apply, Algebra.smul_def, map_mul, Valuation.map_mul]
    have h1 : Valued.v (e (algebraMap K.O K.E c)) ≤ 1 := (he _).1 ⟨c, rfl⟩
    calc Valued.v (e (algebraMap K.O K.E c)) * Valued.v (e (X i j)) ≤ 1 * WithZero.exp m :=
          mul_le_mul' h1 (hX i j)
      _ = WithZero.exp m := one_mul _

theorem exists_bound (x : K.E) : ∃ m : ℤ, Valued.v (e x) ≤ WithZero.exp m := by
  by_cases h : Valued.v (e x) = 0
  · exact ⟨0, by rw [h]; exact zero_le'⟩
  · exact ⟨(Valued.v (e x)).log, (WithZero.exp_log h).ge⟩

theorem exists_unif (he : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) :
    ∃ ϖ : K.O, ϖ ≠ 0 ∧ Valued.v (e (algebraMap K.O K.E ϖ)) ≤ WithZero.exp (-1) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  refine ⟨ϖ, hϖ.ne_zero, ?_⟩
  set w := Valued.v (e (algebraMap K.O K.E ϖ)) with hw
  have hE : algebraMap K.O K.E ϖ ≠ 0 := by
    intro h0
    exact hϖ.ne_zero (IsFractionRing.injective K.O K.E (by simpa using h0))
  have w0 : w ≠ 0 := by
    rw [hw, Valuation.ne_zero_iff]
    exact (map_ne_zero e).2 hE
  have w1 : w ≤ 1 := (he _).1 ⟨ϖ, rfl⟩
  have wne : w ≠ 1 := by
    intro h1
    have : Valued.v (e (algebraMap K.O K.E ϖ)⁻¹) ≤ 1 := by
      rw [map_inv₀, map_inv₀, ← hw, h1, inv_one]
    obtain ⟨u, hu⟩ := (he _).2 this
    apply hϖ.not_isUnit
    refine IsUnit.of_mul_eq_one (b := u) (IsFractionRing.injective K.O K.E ?_)
    rw [map_mul, hu, map_one, mul_inv_cancel₀ hE]
  have wlt : w < 1 := lt_of_le_of_ne w1 wne
  have hlog : w.log < 0 := by
    rw [← WithZero.exp_lt_exp, WithZero.exp_log w0, WithZero.exp_zero]
    exact wlt
  rw [← WithZero.exp_log w0, WithZero.exp_le_exp]
  omega

end GlobalTheory.IntMatBound

open GlobalTheory.IntMatBound in
theorem GlobalTheory.IntMatBound.isIntegral_iff_bounded : ∀ (K : UQ) {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (e : K.E ≃+* L), (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) K.E), IsIntegral K.O M ↔ ∃ m : ℤ, ∀ k : ℕ, ∀ i j, Valued.v (e ((M ^ k) i j)) ≤ WithZero.exp m := by
  intro K L _ _ e he n M
  constructor
  · intro hM
    obtain ⟨s, hs⟩ := hM.fg_adjoin_singleton
    have hb : ∀ p : s × Fin n × Fin n, ∃ m : ℤ, Valued.v (e ((p.1 : Matrix (Fin n) (Fin n) K.E) p.2.1 p.2.2)) ≤ WithZero.exp m :=
      fun p => exists_bound K e _
    choose f hf using hb
    obtain ⟨m, hm⟩ := (Set.finite_range f).bddAbove
    refine ⟨m, fun k i j => ?_⟩
    have hle : Submodule.span K.O (s : Set (Matrix (Fin n) (Fin n) K.E)) ≤ boundSub K e he n m := by
      rw [Submodule.span_le]
      intro X hX i j
      exact (hf ⟨⟨X, hX⟩, i, j⟩).trans (WithZero.exp_le_exp.2 (hm ⟨_, rfl⟩))
    have hk : M ^ k ∈ Submodule.span K.O (s : Set (Matrix (Fin n) (Fin n) K.E)) := by
      rw [hs]
      exact Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton K.O M) k
    exact hle hk i j
  · rintro ⟨m, hm⟩
    obtain ⟨ϖ, hϖ0, hϖ⟩ := exists_unif K e he
    have hE : algebraMap K.O K.E ϖ ≠ 0 := by
      intro h0
      exact hϖ0 (IsFractionRing.injective K.O K.E (by simpa using h0))
    set N := m.toNat with hN
    set y : K.E := (algebraMap K.O K.E ϖ)⁻¹ ^ N with hy
    set S : Submodule K.O (Matrix (Fin n) (Fin n) K.E) :=
      Submodule.span K.O (Set.range fun p : Fin n × Fin n => Matrix.single p.1 p.2 y) with hS
    have hmem : ∀ X : Matrix (Fin n) (Fin n) K.E, (∀ i j, Valued.v (e (X i j)) ≤ WithZero.exp m) → X ∈ S := by
      intro X hX
      rw [Matrix.matrix_eq_sum_single X]
      refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
      have hv : Valued.v (e ((algebraMap K.O K.E ϖ) ^ N * X i j)) ≤ 1 := by
        rw [map_mul, map_pow, Valuation.map_mul, Valuation.map_pow]
        calc Valued.v (e (algebraMap K.O K.E ϖ)) ^ N * Valued.v (e (X i j))
            ≤ WithZero.exp (-1) ^ N * WithZero.exp m := mul_le_mul' (pow_le_pow_left' hϖ N) (hX i j)
          _ = WithZero.exp (N • (-1 : ℤ) + m) := by rw [WithZero.exp_add, WithZero.exp_nsmul]
          _ ≤ WithZero.exp 0 := by
              rw [WithZero.exp_le_exp, nsmul_eq_mul, hN]
              omega
          _ = 1 := WithZero.exp_zero
      obtain ⟨c, hc⟩ := (he _).2 hv
      have : Matrix.single i j (X i j) = c • Matrix.single i j y := by
        rw [Matrix.smul_single, Algebra.smul_def, hc, hy, inv_pow, mul_assoc, mul_comm (X i j), ← mul_assoc,
          mul_inv_cancel₀ (pow_ne_zero _ hE), one_mul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, j), rfl⟩)
    have hSfg : S.FG := Submodule.fg_span (Set.finite_range _)
    have hle : Subalgebra.toSubmodule (Algebra.adjoin K.O {M}) ≤ S := by
      rw [Algebra.adjoin_eq_span, Submodule.span_le]
      rintro _ hx
      obtain ⟨k, rfl⟩ := Submonoid.mem_closure_singleton.1 hx
      exact hmem _ (hm k)
    haveI := isNoetherian_of_fg_of_noetherian S hSfg
    haveI := isNoetherian_of_le hle
    have hfg : (Subalgebra.toSubmodule (Algebra.adjoin K.O {M})).FG := Module.Finite.iff_fg.mp inferInstance
    exact IsIntegral.of_mem_of_fg _ hfg M (Algebra.self_mem_adjoin_singleton K.O M)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsometryPullIdComp
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB
open GlobalTheory.QCoh (pullbackSections res_pullbackSections)
open GlobalTheory.Twist (resM app_resM)

namespace GlobalTheory.PullPull

section Sections

variable {X Y Z : Scheme.{0}}

theorem pullbackComp_hom_app (b : Z ⟶ Y) (a : Y ⟶ X) (E : X.Modules) {U : X.Opens} {V : Y.Opens}
    {T : Z.Opens} (h₁ : V ≤ a ⁻¹ᵁ U) (h₂ : T ≤ b ⁻¹ᵁ V) (h : T ≤ (b ≫ a) ⁻¹ᵁ U) (s : Γ(E, U)) :
    ((Scheme.Modules.pullbackComp b a).hom.app E).app T
        (pullbackSections b _ h₂ (pullbackSections a E h₁ s)) =
      pullbackSections (b ≫ a) E h s := by
  rw [← Vert.DivPull.pullbackComp_inv_app b a E h₁ h₂ h s]
  have e : (Scheme.Modules.pullbackComp b a).inv.app E ≫
      (Scheme.Modules.pullbackComp b a).hom.app E = 𝟙 _ := by simp
  exact congr(($e).app T (pullbackSections (b ≫ a) E h s))

end Sections

section Met

variable {k : Type} [CommRing k] {X Y Z : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
  {E E' : X.Modules} {r : ℕ}

end Met

end GlobalTheory.PullPull

namespace GlobalTheory.VMetric

end GlobalTheory.VMetric
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineReps
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open IsDedekindDomain
open GlobalTheory.Doubling (absE absEv absEw)

namespace GlobalTheory.EisMidHt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}


variable (F) in
def adVec (z : Fin n → E) : Fin n → AF F ⊗[F] E := fun i => inclR (F := F) (AF F) (z i)


variable (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)

end GlobalTheory.EisMidHt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulIntSingle
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix

namespace GlobalTheory.ThetaDenom


variable (F : Type) [Field F] [NumberField F] in
def IsMulInt {κ : Type} (M : ℕ) (z : κ → AF F) : Prop :=
  (∀ i, (z i).1 = 0) ∧ ∀ v i, ‖evFin F v (z i)‖ ≤ ‖(M : Fv F v)‖

theorem IsMulInt.mono {F : Type} [Field F] [NumberField F] {κ : Type} {k m : ℕ} {a : κ → AF F}
    (h : IsMulInt F (k * m) a) : IsMulInt F m a := by
  refine ⟨h.1, fun v i => (h.2 v i).trans ?_⟩
  rw [Nat.cast_mul, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (GlobalTheory.SmoothForms.denom_norm_natCast_le_one v k)

def sand {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) (h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)) :
    Matrix (Fin n) (Fin d) (AF F ⊗[F] E) →ₗ[AF F] Matrix (Fin n) (Fin d) (AF F ⊗[F] E) where
  toFun X := g * X * hᵀ
  map_add' X Y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' a X := by rw [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul]

end GlobalTheory.ThetaDenom

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenScaledInt
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.EvAdm

variable (F : Type) [Field F] [NumberField F] (κ : Type)

def scaledInt (a : F) : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F) where
  carrier := {z | ∀ i (v : HeightOneSpectrum (𝓞 F)),
    (algebraMap F (v.adicCompletion F) a)⁻¹ * (z i) v ∈ v.adicCompletionIntegers F}
  zero_mem' := fun i v => by
    change (algebraMap F (v.adicCompletion F) a)⁻¹ * 0 ∈ v.adicCompletionIntegers F
    rw [mul_zero]
    exact zero_mem _
  add_mem' := fun {z w} hz hw i v => by
    show (algebraMap F (v.adicCompletion F) a)⁻¹ * ((z i + w i) v) ∈ _
    have e : (z i + w i) v = (z i) v + (w i) v := rfl
    rw [e, mul_add]
    exact add_mem (hz i v) (hw i v)
  neg_mem' := fun {z} hz i v => by
    show (algebraMap F (v.adicCompletion F) a)⁻¹ * ((-z i) v) ∈ _
    have e : (-z i) v = -((z i) v) := rfl
    rw [e, mul_neg]
    exact neg_mem (hz i v)

variable {F κ}

theorem mem_scaledInt {a : F} {z : κ → FiniteAdeleRing (𝓞 F) F} :
    z ∈ scaledInt F κ a ↔ ∀ i (v : HeightOneSpectrum (𝓞 F)),
      (algebraMap F (v.adicCompletion F) a)⁻¹ * (z i) v ∈ v.adicCompletionIntegers F := Iff.rfl

theorem isOpen_scaledInt [Finite κ] (a : F) : IsOpen (scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)) := by
  have hO : IsOpen {x : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), x v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_mem fun v => Valued.isOpen_valuationSubring _
  have e : (scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)) = ⋂ i, (fun z : κ → FiniteAdeleRing (𝓞 F) F =>
      algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹ * z i) ⁻¹'
      {x : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), x v ∈ v.adicCompletionIntegers F} := by
    ext z
    simp only [SetLike.mem_coe, mem_scaledInt, Set.mem_iInter, Set.mem_preimage, Set.mem_ofPred_eq]
    refine forall_congr' fun i => forall_congr' fun v => ?_
    have h : (algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹ * z i) v =
        (algebraMap F (v.adicCompletion F) a)⁻¹ * (z i) v := by
      have h1 := map_mul (evalV F v) (algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹) (z i)
      rw [AlgHom.commutes, map_inv₀ (algebraMap F (v.adicCompletion F))] at h1
      exact h1
    rw [h]
  rw [e]
  exact isOpen_iInter_of_finite fun i => hO.preimage (continuous_const.mul (continuous_apply i))

end GlobalTheory.EvAdm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairingStdP
section
noncomputable section

open scoped SchwartzMap

namespace GlobalTheory.ArchUniq

section Real

variable {V V₁ : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V₁] [NormedSpace ℝ V₁]

def schrF (P : V → V → ℝ) (w : V × V) (f : V → ℂ) : V → ℂ :=
  fun y => Complex.exp (-(2 * Real.pi * Complex.I) * ((P y w.2 + P w.1 w.2 / 2 : ℝ) : ℂ)) * f (y + w.1)

def omega (P : V → V → ℝ) (w w' : V × V) : ℝ := P w.1 w'.2 - P w'.1 w.2

structure IsPairing (P : V → V → ℝ) : Prop where
  addL : ∀ x x' y, P (x + x') y = P x y + P x' y
  addR : ∀ x y y', P x (y + y') = P x y + P x y'
  smulL : ∀ (c : ℝ) x y, P (c • x) y = c * P x y
  smulR : ∀ (c : ℝ) x y, P x (c • y) = c * P x y
  nondegL : ∀ x, (∀ y, P x y = 0) → x = 0
  nondegR : ∀ y, (∀ x, P x y = 0) → y = 0

structure Setup (P : V → V → ℝ) (P₁ : V₁ → V₁ → ℝ) (j : V₁ × V₁ → V × V) (L : Set (V × V)) : Prop where
  pair : IsPairing P
  pair₁ : IsPairing P₁
  add : ∀ w w', j (w + w') = j w + j w'
  smul : ∀ (c : ℝ) w, j (c • w) = c • j w
  symp : ∀ w w', omega P (j w) (j w') = omega P₁ w w'
  iso : ∀ l ∈ L, ∀ l' ∈ L, omega P l l' = 0
  orth : ∀ l ∈ L, ∀ w, omega P l (j w) = 0
  max : ∀ v, (∀ l ∈ L, omega P v l = 0) → (∀ w, omega P v (j w) = 0) → v ∈ L

def stdP (P₁ : V₁ → V₁ → ℝ) (k : ℕ) (x y : V₁ × (Fin k → ℝ)) : ℝ := P₁ x.1 y.1 + ∑ i, x.2 i * y.2 i

def jStd (k : ℕ) (w : V₁ × V₁) : (V₁ × (Fin k → ℝ)) × (V₁ × (Fin k → ℝ)) := ((w.1, 0), (w.2, 0))


variable (V₁) in
def LStd (k : ℕ) : Set ((V₁ × (Fin k → ℝ)) × (V₁ × (Fin k → ℝ))) :=
  {l | ∃ b : Fin k → ℝ, l = ((0, 0), (0, b))}

theorem isPairing_stdP {P₁ : V₁ → V₁ → ℝ} (h : IsPairing P₁) (k : ℕ) : IsPairing (stdP P₁ k) := by
  exact {
    addL x x' y := by
      simp only [stdP, Prod.fst_add, Prod.snd_add, h.addL, Pi.add_apply, add_mul, Finset.sum_add_distrib]; ring
    addR x y y' := by
      simp only [stdP, Prod.fst_add, Prod.snd_add, h.addR, Pi.add_apply, mul_add, Finset.sum_add_distrib]; ring
    smulL c x y := by
      simp only [stdP, Prod.smul_fst, Prod.smul_snd, h.smulL, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
      ring
    smulR c x y := by
      simp only [stdP, Prod.smul_fst, Prod.smul_snd, h.smulR, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c,
        ← Finset.mul_sum]
      ring
    nondegL x hx := by
      have h1 : x.1 = 0 := h.nondegL _ fun y => by simpa [stdP] using hx (y, 0)
      have h2 : ∑ i, x.2 i * x.2 i = 0 := by
        have := hx (0, x.2)
        simp only [stdP] at this
        rwa [show P₁ x.1 0 = 0 by simpa using h.smulR 0 x.1 0, zero_add] at this
      have h3 : x.2 = 0 := by
        funext i
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_self_nonneg (x.2 i))).1 h2 i (Finset.mem_univ _)
        simpa using this
      exact Prod.ext h1 h3
    nondegR y hy := by
      have h1 : y.1 = 0 := h.nondegR _ fun x => by simpa [stdP] using hy (x, 0)
      have h2 : ∑ i, y.2 i * y.2 i = 0 := by
        have := hy (0, y.2)
        simp only [stdP] at this
        rwa [show P₁ 0 y.1 = 0 by simpa using h.smulL 0 0 y.1, zero_add] at this
      have h3 : y.2 = 0 := by
        funext i
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_self_nonneg (y.2 i))).1 h2 i (Finset.mem_univ _)
        simpa using this
      exact Prod.ext h1 h3
  }

theorem IsPairing.zero_left {P : V → V → ℝ} (h : IsPairing P) (y : V) : P 0 y = 0 := by
  simpa using h.smulL 0 0 y

theorem IsPairing.zero_right {P : V → V → ℝ} (h : IsPairing P) (x : V) : P x 0 = 0 := by
  simpa using h.smulR 0 x 0

theorem setup_std {P₁ : V₁ → V₁ → ℝ} (h : IsPairing P₁) (k : ℕ) : Setup (stdP P₁ k) P₁ (jStd k) (LStd V₁ k) := by
  exact {
    pair := isPairing_stdP h k
    pair₁ := h
    add w w' := by simp [jStd]
    smul c w := by simp [jStd]
    symp w w' := by simp [omega, stdP, jStd]
    iso := by
      rintro _ ⟨b, rfl⟩ _ ⟨b', rfl⟩
      simp [omega, stdP, h.zero_left]
    orth := by
      rintro _ ⟨b, rfl⟩ w
      simp [omega, stdP, jStd, h.zero_left, h.zero_right]
    max := by
      rintro ⟨⟨a₁, a₂⟩, ⟨b₁, b₂⟩⟩ hL hj
      have e2 : a₂ = 0 := by
        have := hL ((0, 0), (0, a₂)) ⟨a₂, rfl⟩
        simp only [omega, stdP, h.zero_right, h.zero_left, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
          zero_add, sub_zero] at this
        funext i
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_self_nonneg (a₂ i))).1 this i (Finset.mem_univ _)
        simpa using this
      have e1 : a₁ = 0 := h.nondegL _ fun y => by
        have := hj (0, y)
        simpa [omega, stdP, jStd, h.zero_left] using this
      have e3 : b₁ = 0 := h.nondegR _ fun x => by
        have := hj (x, 0)
        simpa [omega, stdP, jStd, h.zero_right] using this
      exact ⟨b₂, by simp [e1, e2, e3]⟩
  }

theorem isPairing_mul : IsPairing (fun x y : ℝ => x * y) := by
  exact {
    addL x x' y := add_mul x x' y
    addR x y y' := mul_add x y y'
    smulL c x y := by simp [mul_assoc]
    smulR c x y := by simp only [smul_eq_mul]; ring
    nondegL x hx := by simpa using hx 1
    nondegR y hy := by simpa using hy 1
  }

end Real

section Adelic

open scoped Matrix
open NumberField GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F : Type} [Field F] [NumberField F]


variable (F) in
def trP (κ : Type) [Fintype κ] (y b : κ → mixedEmbedding.mixedSpace F) : ℝ :=
  Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * b i)

def locV {κ : Type} (x : κ → AF F) : κ → mixedEmbedding.mixedSpace F := fun i => evI F (x i)

def liftV {κ : Type} (y : κ → mixedEmbedding.mixedSpace F) : κ → AF F :=
  fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i), 0)

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁}

end Adelic

end GlobalTheory.ArchUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTensorLatticeAtPlaceIffFrameCoordinatesIntegrStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_tensorLatticeAtPlace_iff_frame_coordinates_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl (F := F)) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ι : L →+ _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      Function.Injective ι → (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ↔ ∃ x, ι x = z) → (∀ x y, ι (x * y) = ι x * ι y) →
      (∀ x, x ∈ Formalism.UG.intL L ↔ ι x ∈ AddSubgroup.closure {z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) | ∃ a : AF F, At (evFin F v) a ∧
        evFin F v a ∈ v.adicCompletionIntegers F ∧ ∃ o : 𝓞 E, z = a • inclR (F := F) (AF F) (o : E)}) →
      ∀ (PV : GL (Fin n) L) (PW : GL (Fin d) L), (∀ x : Fin n → L, (∀ i, x i ∈ Formalism.UG.intL L) ↔
        (fun i => ι (((PV : Matrix (Fin n) (Fin n) L) *ᵥ x) i)) ∈ GlobalTheory.InertSph.latAt X v) → (∀ x : Fin d → L, (∀ i, x i ∈ Formalism.UG.intL L) ↔
        (fun i => ι (((PW : Matrix (Fin d) (Fin d) L) *ᵥ x) i)) ∈ GlobalTheory.InertSph.latAt W v) →
      ∀ z, z ∈ latAtV X W v ↔ ∃ u : Matrix (Fin d) (Fin n) L, (∀ i j, u i j ∈ Formalism.UG.intL L) ∧
        GlobalTheory.InertLocFrame.xm ι PV PW u = z := by
  first | exact @GlobalTheory.InertLocFrame.mem_latAtV_iff_xm | exact GlobalTheory.InertLocFrame.mem_latAtV_iff_xm | (intros; apply GlobalTheory.InertLocFrame.mem_latAtV_iff_xm <;> assumption)
end

