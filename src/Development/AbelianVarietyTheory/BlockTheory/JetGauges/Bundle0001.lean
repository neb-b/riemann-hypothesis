module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.JetGauges.BalancedHermitianSpace
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace

open NumberField NumberField.IsCMField TensorProduct

abbrev Bil (Y : Type) [AddCommGroup Y] : Type := Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ

section Forms

variable {Y : Type} [AddCommGroup Y]

def quad (β : Bil Y) (x : Y) : ℝ := β x x / 2

def IsIntegralFn (S : Submodule ℝ (Bil Y)) (l : S →ₗ[ℝ] ℝ) : Prop :=
  ∀ β : S, (∀ a c, ∃ z : ℤ, (β : Bil Y) a c = z) → ∃ z : ℤ, l β = z

def IsPositiveFn (S : Submodule ℝ (Bil Y)) (l : S →ₗ[ℝ] ℝ) : Prop :=
  ∀ β : S, (∀ a, 0 ≤ (β : Bil Y) a a) → β ≠ 0 → 0 < l β

def leastExponent (S : Submodule ℝ (Bil Y)) (b : S) : ℝ :=
  sInf {x | ∃ l : S →ₗ[ℝ] ℝ, IsIntegralFn S l ∧ IsPositiveFn S l ∧ x = l b}

def evalSum (S : Submodule ℝ (Bil Y)) {k : ℕ} (x x' : Fin k → Y) : S →ₗ[ℝ] ℝ where
  toFun β := ∑ i, (β : Bil Y) (x i) (x' i)
  map_add' β γ := by simp [Finset.sum_add_distrib]
  map_smul' r β := by simp [Finset.mul_sum]

end Forms

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

def HasTraceOne : Prop := ∃ w : 𝓞 E, w + ringOfIntegersComplexConj E w = 1

variable {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y]

def IsBalanced (β : Bil Y) : Prop :=
  (∀ x y, β x y = β y x) ∧
    ∀ (a : 𝓞 E) (x y : Y), β (a • x) y = β x (ringOfIntegersComplexConj E a • y)

def IsBalancedSpace (S : Submodule ℝ (Bil Y)) : Prop := ∀ β, β ∈ S ↔ IsBalanced E β



open NumberField NumberField.IsCMField TensorProduct in
variable (E : Type) [Field E] [NumberField E] [IsCMField E] in
variable {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y] in
omit [NumberField E] [IsCMField E] [Module (𝓞 E) Y] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace.isIntegralFn_evalSum (S : Submodule ℝ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace.Bil Y))
    {k : ℕ} (x x' : Fin k → Y) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace.IsIntegralFn S (_root_.GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace.evalSum S x x') := by
  intro β hβ
  choose f hf using hβ
  refine ⟨∑ i, f (x i) (x' i), ?_⟩
  show ∑ i, (β : _root_.GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace.Bil Y) (x i) (x' i) = _
  push_cast
  exact Finset.sum_congr rfl fun i _ => hf _ _

end GlobalTheory.IndefiniteRowSideFullHecke.BalancedHermitianSpace
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.JetGauges.HarishChandraParameters
section
open scoped BigOperators
open Matrix

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.HarishChandraRootData

variable {n : ℕ}

def grpK (ε : Fin n → Bool) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {k | k ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ ∀ a b, ε a ≠ ε b → k a b = 0}

def root (a b : Fin n) : Fin n → ℝ := Pi.single a 1 - Pi.single b 1

def posPairs (n : ℕ) : Finset (Fin n × Fin n) := Finset.univ.filter fun x => x.1 < x.2

def cptPairs (ε : Fin n → Bool) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun x => x.1 < x.2 ∧ ε x.1 = ε x.2

def rho (n : ℕ) : Fin n → ℝ := (1 / 2 : ℝ) • ∑ x ∈ posPairs n, root x.1 x.2

def IsHCParam (μ : Fin n → ℝ) : Prop :=
  StrictAnti μ ∧ ∀ i, ∃ m : ℤ, μ i = (m : ℝ) + ((n : ℝ) - 1) / 2

def torus (θ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun a => Complex.exp (Complex.I * (θ a : ℂ))

def wtChar (ω θ : Fin n → ℝ) : ℂ := Complex.exp (Complex.I * ((∑ a, ω a * θ a : ℝ) : ℂ))

def CptLE (ε : Fin n → Bool) (ω Λ : Fin n → ℝ) : Prop :=
  ∃ c : Fin n × Fin n → ℕ, Λ - ω = ∑ x ∈ cptPairs ε, (c x : ℝ) • root x.1 x.2

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

structure IsUnitaryRepOn (Γ : Set (Matrix (Fin n) (Fin n) ℂ))
    (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H) : Prop where
  map_one : σ 1 = 1
  map_mul : ∀ g ∈ Γ, ∀ g' ∈ Γ, σ (g * g') = σ g * σ g'
  norm_map : ∀ g ∈ Γ, ∀ v, ‖σ g v‖ = ‖v‖
  cont : ∀ v, ContinuousOn (fun g => σ g v) Γ

def weightSpace (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H) (ω : Fin n → ℝ) :
    Submodule ℂ H where
  carrier := {v | ∀ θ : Fin n → ℝ, σ (torus θ) v = wtChar ω θ • v}
  add_mem' := by
    intro a b ha hb θ
    rw [map_add (f := _), ha θ, hb θ, smul_add]
  zero_mem' := by intro θ; simp
  smul_mem' := by
    intro c v hv θ
    rw [map_smul, hv θ, smul_comm]

def IsWeightVector (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H) (ω : Fin n → ℝ) (v : H) : Prop :=
  v ≠ 0 ∧ v ∈ weightSpace σ ω

def KStable (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H)
    (S : Submodule ℂ H) : Prop :=
  ∀ k ∈ grpK ε, ∀ v ∈ S, σ k v ∈ S

structure IsKType (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H)
    (S : Submodule ℂ H) (Λ : Fin n → ℝ) : Prop where
  finDim : FiniteDimensional ℂ S
  stable : KStable ε σ S
  irred : ∀ S' : Submodule ℂ H, S' ≤ S → KStable ε σ S' → S' = ⊥ ∨ S' = S
  exists_highest : ∃ v ∈ S, IsWeightVector σ Λ v
  le_highest : ∀ ω : Fin n → ℝ, ∀ v ∈ S, IsWeightVector σ ω v → CptLE ε ω Λ

end Rep

def rhoU (k : ℕ) : Fin k → ℝ := fun i => ((k : ℝ) - 1) / 2 - (i : ℕ)

structure IsCompactIrrep {k : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : Matrix (Fin k) (Fin k) ℂ → H →L[ℂ] H) (u : Fin k → ℝ) : Prop where
  param : IsHCParam u
  rep : IsUnitaryRepOn (Matrix.unitaryGroup (Fin k) ℂ : Set (Matrix (Fin k) (Fin k) ℂ)) π
  type : IsKType (fun _ => true) π ⊤ (u - rhoU k)

theorem grpK_const (k : ℕ) : grpK (fun _ : Fin k => true) =
    (Matrix.unitaryGroup (Fin k) ℂ : Set (Matrix (Fin k) (Fin k) ℂ)) := by
  ext g
  simp [grpK]

end GlobalTheory.IndefiniteRowSideFullHecke.HarishChandraRootData
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.JetGauges.NodalSeriesPeriods
section
open PowerSeries

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods

abbrev Qbar : Type := ↥(algebraicClosure ℚ ℂ)

abbrev Place (p : ℕ) [Fact p.Prime] : Type := Qbar →+* ℂ_[p]

abbrev incl (p : ℕ) [Fact p.Prime] : 𝓞_ℂ_[p] →+* ℂ_[p] := algebraMap 𝓞_ℂ_[p] ℂ_[p]

def IsModel {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve ℂ_[p]) (W : WeierstrassCurve 𝓞_ℂ_[p])
    (C : WeierstrassCurve.VariableChange ℂ_[p]) : Prop :=
  C • E = W.map (incl p) ∧ IsUnit W.Δ

section Expansion

variable {A : Type} [CommRing A] (W : WeierstrassCurve A)

def step (v : A⟦X⟧) : A⟦X⟧ :=
  1 + C W.a₁ * X * v + C W.a₂ * X ^ 2 * v + C W.a₃ * X ^ 3 * v ^ 2 + C W.a₄ * X ^ 4 * v ^ 2
    + C W.a₆ * X ^ 6 * v ^ 3

def vSer : A⟦X⟧ := mk fun n => coeff n ((step W)^[n + 1] 0)

def wSer : A⟦X⟧ := X ^ 3 * vSer W

open PowerSeries in
variable {A : Type} [CommRing A] (W : WeierstrassCurve A) in
private lemma nodal_map_sub_eq_X_mul_sub_mul (u v : A⟦X⟧) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W u - _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W v =
      X * (u - v) * (C W.a₁ + C W.a₂ * X + C W.a₃ * X ^ 2 * (u + v) + C W.a₄ * X ^ 3 * (u + v)
        + C W.a₆ * X ^ 5 * (u ^ 2 + u * v + v ^ 2)) := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step
  ring

open PowerSeries in
variable {A : Type} [CommRing A] (W : WeierstrassCurve A) in
private lemma X_pow_succ_dvd_sub_of_X_pow_dvd {k : ℕ} {u v : A⟦X⟧} (h : X ^ k ∣ u - v) :
    X ^ (k + 1) ∣
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W u - _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W v := by
  rw [nodal_map_sub_eq_X_mul_sub_mul, pow_succ']
  exact Dvd.dvd.mul_right (mul_dvd_mul_left X h) _

open PowerSeries in
variable {A : Type} [CommRing A] (W : WeierstrassCurve A) in
private lemma X_pow_dvd_iterate_sub_iterate (n m : ℕ) :
    X ^ n ∣ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W)^[n + m] 0
      - (_root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W)^[n] 0 := by
  induction n with
  | zero => rw [pow_zero]; exact one_dvd _
  | succ n ih =>
    have e1 : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W)^[n + 1 + m] 0 =
        _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W
          ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W)^[n + m] 0) := by
      rw [show n + 1 + m = n + m + 1 by omega]
      exact Function.iterate_succ_apply' _ _ _
    have e2 : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W)^[n + 1] 0 =
        _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W
          ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W)^[n] 0) :=
      Function.iterate_succ_apply' _ _ _
    rw [e1, e2]
    exact X_pow_succ_dvd_sub_of_X_pow_dvd W ih

open PowerSeries in
variable {A : Type} [CommRing A] (W : WeierstrassCurve A) in
private lemma vSer_isFixedPt :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.vSer W =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W (_root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.vSer W) := by
  ext k
  have h : X ^ k ∣ _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.vSer W
      - (_root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W)^[k] 0 := by
    rw [X_pow_dvd_iff]
    intro m hm
    have h2 := X_pow_dvd_iterate_sub_iterate W (m + 1) (k - (m + 1))
    rw [show m + 1 + (k - (m + 1)) = k by omega, X_pow_dvd_iff] at h2
    have h3 := h2 m (Nat.lt_succ_self m)
    rw [map_sub, sub_eq_zero] at h3
    rw [map_sub, sub_eq_zero, _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.vSer, coeff_mk]
    exact h3.symm
  have h2 := X_pow_succ_dvd_sub_of_X_pow_dvd W h
  have e : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W)^[k + 1] 0 =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W
        ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step W)^[k] 0) :=
    Function.iterate_succ_apply' _ _ _
  rw [← e, X_pow_dvd_iff] at h2
  have h3 := h2 k (Nat.lt_succ_self k)
  rw [map_sub, sub_eq_zero] at h3
  rw [h3, _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.vSer, coeff_mk]

open PowerSeries in
variable {A : Type} [CommRing A] (W : WeierstrassCurve A) in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.wSer_eq :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.wSer W = X ^ 3 + C W.a₁ * X * _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.wSer W
      + C W.a₂ * X ^ 2 * _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.wSer W
      + C W.a₃ * _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.wSer W ^ 2
      + C W.a₄ * X * _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.wSer W ^ 2
      + C W.a₆ * _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.wSer W ^ 3 := by
  have hv := vSer_isFixedPt W
  simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.wSer]
  conv_lhs => rw [hv, _root_.GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods.step]
  ring

end Expansion

end GlobalTheory.IndefiniteRowSideFullHecke.NodalSeriesPeriods
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.JetGauges.SplitUnramifiedPlaces
section
noncomputable section

open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces

section Ring

variable (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE]

abbrev Op : Type := ℤ_[p] ⊗[ℤ] OE

def bar [StarRing OE] : Op p OE ≃ₐ[ℤ_[p]] Op p OE :=
  Algebra.TensorProduct.congr (AlgEquiv.refl : ℤ_[p] ≃ₐ[ℤ_[p]] ℤ_[p])
    (AlgEquiv.ofRingEquiv (f := (starRingAut : RingAut OE)) (fun n => by simp))

variable {p OE}

def extend {O : Type} [CommRing O] [Algebra ℤ_[p] O] (σ : OE →+* O) : Op p OE →ₐ[ℤ_[p]] O :=
  Algebra.TensorProduct.lift (Algebra.ofId ℤ_[p] O) σ.toIntAlgHom (fun _ _ => Commute.all _ _)

end Ring

@[ext] structure Place (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE] where

  e : Op p OE
  idem : IsIdempotentElem e
  ne_zero : e ≠ 0
  primitive : ∀ f : Op p OE, IsIdempotentElem f → f * e = f → f = 0 ∨ f = e

namespace Place

variable {p : ℕ} [Fact p.Prime] {OE : Type} [CommRing OE]

abbrev Ow (w : Place p OE) : Type := Op p OE ⧸ Ideal.span {1 - w.e}

def toOw (w : Place p OE) : OE →+* w.Ow :=
  (Ideal.Quotient.mk _).comp
    (Algebra.TensorProduct.includeRight : OE →ₐ[ℤ] Op p OE).toRingHom

end Place

section Gauss

variable {p : ℕ} [Fact p.Prime]

end Gauss

end GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.JetGauges.TraceFormDualSystem
section
open NumberField

namespace GlobalTheory.IndefiniteRowSideFullHecke.TraceFormDualSystem

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

noncomputable abbrev bar (a : 𝓞 E) : 𝓞 E := IsCMField.ringOfIntegersComplexConj E a

section Forms

variable (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y]

def balancedForms : Submodule ℝ (Y →+ Y →+ ℝ) where
  carrier := {β | (∀ x x', β x x' = β x' x) ∧
    ∀ (a : 𝓞 E) (x x' : Y), β (a • x) x' = β x (bar E a • x')}
  add_mem' := by
    rintro β γ ⟨h1, h2⟩ ⟨k1, k2⟩
    refine ⟨fun x x' => ?_, fun a x x' => ?_⟩
    · simp only [AddMonoidHom.add_apply]; rw [h1, k1]
    · simp only [AddMonoidHom.add_apply]; rw [h2, k2]
  zero_mem' := ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩
  smul_mem' := by
    rintro c β ⟨h1, h2⟩
    refine ⟨fun x x' => ?_, fun a x x' => ?_⟩
    · simp only [AddMonoidHom.smul_apply]; rw [h1]
    · simp only [AddMonoidHom.smul_apply]; rw [h2]

variable {E Y}

noncomputable def quad (β : balancedForms E Y) (x : Y) : ℝ := β.1 x x / 2

def IsPosSemidef (β : balancedForms E Y) : Prop := ∀ x : Y, 0 ≤ β.1 x x

def IsPosDef (β : balancedForms E Y) : Prop :=
  ∀ (n : ℕ) (x : Fin n → Y), LinearIndependent ℤ x →
    ∀ t : Fin n → ℝ, t ≠ 0 → 0 < ∑ i, ∑ j, t i * t j * β.1 (x i) (x j)

variable (E Y)

structure Exponent where

  form : Module.Dual (𝓞 E) Y →+ Module.Dual (𝓞 E) Y →+ 𝓞 E
  smul_left : ∀ (a : 𝓞 E) y y', form (a • y) y' = a * form y y'
  hermitian : ∀ y y', form y' y = bar E (form y y')
  pos : ∀ (τ : E →+* ℂ) (y : Module.Dual (𝓞 E) Y), y ≠ 0 → 0 < (τ ((form y y : 𝓞 E) : E)).re

variable {E Y}

variable (E Y)

structure DualSystem where

  n : ℕ

  e : Fin n → Y

  y : Fin n → Module.Dual (𝓞 E) Y
  expand : ∀ x, ∑ j, y j x • e j = x

theorem nonempty_dualSystem [Module.Finite (𝓞 E) Y] [Module.Projective (𝓞 E) Y] :
    Nonempty (DualSystem E Y) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' (𝓞 E) Y
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  refine ⟨⟨n, fun j => f (fun k => if j = k then 1 else 0), fun j => LinearMap.proj j ∘ₗ s,
    fun x => ?_⟩⟩
  have hx : f (s x) = x := LinearMap.congr_fun hs x
  calc _ = f (s x) := (LinearMap.pi_apply_eq_sum_univ f (s x)).symm
    _ = x := hx

variable {E Y}

noncomputable def DualSystem.pairing (D : DualSystem E Y) (l : Exponent E Y)
    (β : balancedForms E Y) : ℝ :=
  (∑ j, ∑ k, β.1 (l.form (D.y j) (D.y k) • D.e j) (D.e k)) / 2

variable [Module.Finite (𝓞 E) Y] [Module.Projective (𝓞 E) Y]

noncomputable def pairing (l : Exponent E Y) (β : balancedForms E Y) : ℝ :=
  (Classical.choice (nonempty_dualSystem E Y)).pairing l β

noncomputable def pairingValues (β : balancedForms E Y) : Set ℝ := Set.range fun l : Exponent E Y => pairing l β

def IsPhiC (β : balancedForms E Y) (r : ℝ) : Prop := IsLeast (pairingValues β) r

end Forms

end GlobalTheory.IndefiniteRowSideFullHecke.TraceFormDualSystem
end

