module

public import Formalism.SharpRestriction.CuspSpanNormBounds.LinQRawRange
public import Formalism.FormalDegreeBessel.Bundle0001
public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.DensExact
public import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.AlgebraMapMemO
section
noncomputable section

open ValuativeRel MeasureTheory
open Formalism.MainNotions.S.Loc

namespace PI.LocHerm.SlopeTestRemainingChoices

open Polynomial Topology

section Top

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem mem_O_of_quad (L : LocE F E) (z : E) (t n : 𝒪[F])
    (h : z * z - algebraMap F E t * z + algebraMap F E n = 0) : z ∈ L.O := by
  rw [L.O_def]
  refine ⟨(X ^ 2 + (C (-t) * X + C n) : Polynomial 𝒪[F]), ?_, ?_⟩
  · monicity!
  · have ht : algebraMap 𝒪[F] E t = algebraMap F E t := rfl
    have hn : algebraMap 𝒪[F] E n = algebraMap F E n := rfl
    simp only [eval₂_add, eval₂_mul, eval₂_neg, eval₂_X_pow, eval₂_X, eval₂_C, map_neg, ht, hn]
    linear_combination h

theorem algebraMap_mem_O (L : LocE F E) (a : 𝒪[F]) : algebraMap F E a ∈ L.O :=
  mem_O_of_quad L _ a 0 (by simp)

theorem mem_OF_of_mem_O [Nontrivial E] (L : LocE F E) (a : F) (h : algebraMap F E a ∈ L.O) : a ∈ 𝒪[F] := by
  have hE : Function.Injective (algebraMap F E) := (algebraMap F E).injective
  rw [L.O_def] at h
  have hF : IsIntegral 𝒪[F] a := by
    obtain ⟨p, hp, he⟩ := h
    refine ⟨p, hp, ?_⟩
    apply hE
    have hc : (algebraMap F E).comp (algebraMap 𝒪[F] F) = algebraMap 𝒪[F] E := by
      ext r
      rfl
    rw [Polynomial.hom_eval₂, map_zero, hc, he]
  exact (Valuation.integer.integers _).mem_of_integral hF

theorem cj_mem_O (L : LocE F E) (x : E) (h : x ∈ L.O) : L.cj x ∈ L.O := by
  rw [L.O_def] at h ⊢
  obtain ⟨p, hp, he⟩ := h
  refine ⟨p, hp, ?_⟩
  have hc : L.cj.toRingEquiv.toRingHom.comp (algebraMap 𝒪[F] E) = algebraMap 𝒪[F] E := by
    ext r
    show L.cj (algebraMap F E (r : F)) = algebraMap F E (r : F)
    exact L.cj.commutes _
  have h2 := congrArg L.cj.toRingEquiv.toRingHom he
  rw [Polynomial.hom_eval₂, map_zero, hc] at h2
  exact h2

end Top

section Top2

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem inv_mem_OF (a : F) (h : a ∉ 𝒪[F]) : a⁻¹ ∈ 𝒪[F] := by
  have h' := h
  rw [Valuation.mem_integer_iff] at h'
  rw [Valuation.mem_integer_iff, map_inv₀]
  exact inv_le_one_of_one_le₀ (le_of_lt (not_le.mp h'))

theorem exists_scale (a : F) : ∃ r : 𝒪[F], (r : F) ≠ 0 ∧ (r : F) * a ∈ 𝒪[F] := by
  by_cases ha : a ∈ 𝒪[F]
  · exact ⟨1, by simp, by simpa using ha⟩
  · have ha0 : a ≠ 0 := fun h0 => ha (h0 ▸ zero_mem _)
    refine ⟨⟨a⁻¹, inv_mem_OF a ha⟩, ?_, ?_⟩
    · show a⁻¹ ≠ 0
      exact inv_ne_zero ha0
    · show a⁻¹ * a ∈ 𝒪[F]
      rw [inv_mul_cancel₀ ha0]
      exact one_mem _

variable (L : LocE F E)

theorem tr_ex (x : E) : ∃ a : F, algebraMap F E a = x + L.cj x :=
  (L.cj_fix _).1 (by rw [map_add (f := _), L.cj_cj, add_comm])

theorem nm_ex (x : E) : ∃ a : F, algebraMap F E a = x * L.cj x :=
  (L.cj_fix _).1 (by rw [map_mul, L.cj_cj, mul_comm])

theorem nontrivial_E (L : LocE F E) : Nontrivial E := by
  by_contra hn
  rw [not_nontrivial_iff_subsingleton] at hn
  have h2 := L.rank
  rw [Module.finrank_zero_of_subsingleton] at h2
  omega

theorem exists_theta : ∃ θ ∈ L.O, L.cj θ = -θ ∧ ∃ D : 𝒪[F], (D : F) ≠ 0 ∧ θ * θ = algebraMap F E D := by
  have hx : ∃ x : E, L.cj x ≠ x := by
    by_contra hex
    have hall : ∀ w : E, L.cj w = w := fun w => not_not.mp (not_exists.mp hex w)
    have hle : Module.finrank F E ≤ 1 := by
      have := L.free
      have hw : ∀ w : E, ∃ c : F, c • (1 : E) = w := by
        intro w
        obtain ⟨a, ha⟩ := (L.cj_fix w).1 (hall w)
        exact ⟨a, by rw [Algebra.smul_def, mul_one, ha]⟩
      exact finrank_le_one (1 : E) hw
    have h2 := L.rank
    omega
  obtain ⟨x, hx⟩ := hx
  have hc0 : L.cj (x - L.cj x) = -(x - L.cj x) := by
    rw [map_sub, L.cj_cj]
    ring
  have hθ0ne : x - L.cj x ≠ 0 := by
    intro h0
    apply hx
    exact (sub_eq_zero.mp h0).symm
  obtain ⟨D0, hD0⟩ := (L.cj_fix ((x - L.cj x) * (x - L.cj x))).1 (by rw [map_mul, hc0, neg_mul_neg])
  have hD0ne : D0 ≠ 0 := by
    rintro rfl
    rw [map_zero] at hD0
    have := L.reduced
    exact hθ0ne (IsReduced.eq_zero _ ⟨2, by rw [pow_two]; exact hD0.symm⟩)
  obtain ⟨r, hr0, hrD⟩ := exists_scale D0
  refine ⟨algebraMap F E r * (x - L.cj x), ?_, ?_, ⟨r * ⟨(r : F) * D0, hrD⟩, ?_, ?_⟩⟩
  · apply mem_O_of_quad L _ 0 (-(r * ⟨(r : F) * D0, hrD⟩))
    have e : ((-(r * ⟨(r : F) * D0, hrD⟩) : 𝒪[F]) : F) = -((r : F) * ((r : F) * D0)) := rfl
    have e0 : ((0 : 𝒪[F]) : F) = 0 := rfl
    rw [e, e0, map_zero, map_neg, map_mul, map_mul]
    linear_combination (-(algebraMap F E r) ^ 2) * hD0
  · rw [map_mul, L.cj.commutes, hc0, mul_neg]
  · show (r : F) * ((r : F) * D0) ≠ 0
    exact mul_ne_zero hr0 (mul_ne_zero hr0 hD0ne)
  · show _ = algebraMap F E ((r : F) * ((r : F) * D0))
    rw [map_mul, map_mul, hD0]
    ring

end Top2

section Top3

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem decomp (L : LocE F E) (θ : E) (hθc : L.cj θ = -θ) (D : F) (hD : θ * θ = algebraMap F E D) (x : E) :
    ∃ t c : F, algebraMap F E t = x + L.cj x ∧ algebraMap F E c = (x - L.cj x) * θ ∧
      algebraMap F E (2 * D) * x = algebraMap F E (D * t) + algebraMap F E c * θ := by
  obtain ⟨t, ht⟩ := (L.cj_fix (x + L.cj x)).1 (by rw [map_add (f := _), L.cj_cj, add_comm])
  obtain ⟨c, hc⟩ := (L.cj_fix ((x - L.cj x) * θ)).1 (by rw [map_mul, map_sub, L.cj_cj, hθc]; ring)
  refine ⟨t, c, ht, hc, ?_⟩
  rw [map_mul, map_mul, map_ofNat, ht, hc]
  linear_combination (-(x - L.cj x)) * hD

end Top3

end PI.LocHerm.SlopeTestRemainingChoices
end
end

-- bundled from Formalism.PeriodIntegrals.BordDefs
section
open Matrix

noncomputable section

namespace PI

open Formalism.QuantumDeterminants

def wbPart (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) : Fin (k + 1) → ℂ := fun j => v (wI k r j)

def prW (k : ℕ) (zb : Fin (k + 1) → ℂ) (v : Fin (k + 1) → ℂ) : Fin (k + 1) → ℂ :=
  v - (herm (Hb k) v zb / herm (Hb k) zb zb) • zb

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.HaarDefs
section
open MeasureTheory Matrix

noncomputable section

namespace PI

def IsHaarOn {k r : ℕ} (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))
    (μ : Measure (Formalism.QuantumDeterminants.Mt k r)) : Prop :=
  SigmaFinite μ ∧ μ ≠ 0 ∧ μ {x | Matrix.of x ∉ S} = 0 ∧
    ∀ s ∈ S, μ.map (Formalism.QuantumDeterminants.lmulM s) = μ

def realifyFun {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) : Fin m × Fin m × Bool → ℝ :=
  fun p => if p.2.2 then (X p.1 p.2.1).im else (X p.1 p.2.1).re

def unrealify {m : ℕ} (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) : Matrix (Fin m) (Fin m) ℂ :=
  fun i j => ⟨x (i, j, false), x (i, j, true)⟩

def lieOf {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℂ)) : Set (Matrix (Fin m) (Fin m) ℂ) :=
  {X | ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ S}

def lieE {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℂ)) : Submodule ℝ (EuclideanSpace ℝ (Fin m × Fin m × Bool)) :=
  Submodule.span ℝ ((fun X => (WithLp.equiv 2 _).symm (realifyFun X)) '' lieOf S)

def haarLie {k r : ℕ} (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (κ : ENNReal) :
    Measure (Formalism.QuantumDeterminants.Mt k r) :=
  κ • Measure.map (fun x : lieE S => fun i j => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ _)) i j) volume

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.LocDensCorank
section
open ValuativeRel Classical

noncomputable section

namespace PI.LocDensCorank

open Formalism.MainNotions.S

def LocDensCorank : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E),
    IsNonarchimedeanLocalField F → CharZero F →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (Λ : Submodule M.L.O V),
      H.IsSelfDual Λ → ∀ ϖ : 𝒪[F], Irreducible ϖ →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι E) (a : ι → 𝒪[F]),
        (∀ i j, A i j ∈ M.L.O) → (∃ y ∈ M.L.O, A.det * y = 1) →
        Fintype.card ι ≤ Module.finrank E V →
          H.dens ϖ Λ ((A.map M.L.cj).transpose * Matrix.diagonal (fun i => algebraMap F E (a i : F)) * A) =
            Formalism.L2.SG.DensExact.densProd (Nat.card 𝓀[F]) (if ∀ x : E, x ≠ 0 → IsUnit x then -1 else 1)
              (Module.finrank E V) (Fintype.card ι) (Finset.univ.filter fun i => ϖ ∣ a i).card

end PI.LocDensCorank
end
end

-- bundled from Formalism.PeriodIntegrals.LocDualGen
section
noncomputable section

open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc

namespace PI.LocDualGen

def DualAtL {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : LocAt F E sig p) (δ : A.Fp) : Prop :=
  ∀ x : A.Ep, (∀ y ∈ A.O, A.psiE (-(x * y * algebraMap A.Fp A.Ep δ⁻¹)) = 1) ↔ x ∈ A.O

def UnramL {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : LocAt F E sig p) : Prop :=
  ∀ ϖ : 𝒪[A.Fp], Irreducible ϖ → ∀ x ∈ A.O,
    x * x ∈ Submodule.span A.O {algebraMap A.Fp A.Ep (ϖ : A.Fp)} →
      x ∈ Submodule.span A.O {algebraMap A.Fp A.Ep (ϖ : A.Fp)}

def Stmt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (sig : E →ₐ[F] E) (p : HeightOneSpectrum (𝓞 F)) (A : LocAt F E sig p),
    (IsReduced A.Ep → UnramL A → ∃ δ : A.Fp, δ ≠ 0 ∧ DualAtL A δ) ∧
    (∀ (δ : A.Fp) (u : 𝒪[A.Fp]), IsUnit u → DualAtL A δ → DualAtL A (δ * (u : A.Fp))) ∧
    (IsReduced A.Ep → UnramL A → Irreducible ((resChar p : ℕ) : 𝒪[A.Fp]) → DualAtL A 1)

end PI.LocDualGen
end
end

-- bundled from Formalism.PeriodIntegrals.LocHaarRR
section
noncomputable section

open scoped Classical

open IsDedekindDomain NumberField ValuativeRel MeasureTheory

namespace PI.LocHaarRR

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}

def ordR {A : Formalism.MainNotions.S.Loc.LocAt F E sig p}
    (sg : Formalism.MainNotions.S.Loc.SplitAt A.Fp A.Ep A.cj (Formalism.MainNotions.S.Loc.resChar p)) : Subring A.Ep :=
  let S : Subring (𝒪[A.Fp] × 𝒪[A.Fp]) :=
    RingHom.eqLocus ((Ideal.Quotient.mk (Ideal.span {sg.q})).comp (RingHom.fst _ _))
      ((Ideal.Quotient.mk (Ideal.span {sg.q})).comp (RingHom.snd _ _))
  (S.map ((𝒪[A.Fp]).subtype.prodMap (𝒪[A.Fp]).subtype)).comap sg.e.toRingEquiv.toRingHom

def RR (A : Formalism.MainNotions.S.Loc.LocAt F E sig p) : Set A.Ep :=
  match A.split with
  | none => (A.O : Set A.Ep)
  | some sg => (ordR sg : Set A.Ep)

end

def Target : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (sig : E →ₐ[F] E) (p : HeightOneSpectrum (𝓞 F)) (A : Formalism.MainNotions.S.Loc.LocAt F E sig p),
    IsReduced A.Ep → ∃ μ : Measure A.Ep, μ.IsAddHaarMeasure ∧ SigmaFinite μ ∧ μ (RR A) = 1

end PI.LocHaarRR
end
end

-- bundled from Formalism.PeriodIntegrals.LocHerm
section
noncomputable section

open ValuativeRel MeasureTheory ComplexConjugate ComplexOrder
open Formalism.MainNotions.S.Loc

namespace PI.LocHerm

def AllLoc (P : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E],
    Model F E → Prop) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK → P M

def LocGlue : Prop :=
  AllLoc fun {_F} _ _ _ {E} _ _ _ _ M =>
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V) (abelian₂ : Submodule M.L.O V),
    H.IsSelfDual abelian₂ → ∀ (U : Submodule E V) (hU : IsCompl U (H.perp U)),
    (∀ u : V, u ∈ U → ((∃ x ∈ abelian₂, (Submodule.linearProjOfIsCompl U (H.perp U) hU x : V) = u) ↔
        ∀ y ∈ abelian₂, y ∈ U → H.h u y ∈ M.L.O)) ∧
    (∀ u : V, u ∈ H.perp U → ((∃ x ∈ abelian₂,
        (Submodule.linearProjOfIsCompl (H.perp U) U hU.symm x : V) = u) ↔
        ∀ y ∈ abelian₂, y ∈ H.perp U → H.h u y ∈ M.L.O))

def LocOProj : Prop :=
  AllLoc fun {_F} _ _ _ {E} _ _ _ _ M =>
  ∀ (W : Type) [AddCommGroup W] [Module E W] (P : Submodule M.L.O W), P.FG → Module.Projective M.L.O P

end PI.LocHerm
end
end

-- bundled from Formalism.PeriodIntegrals.LocLatEq
section
noncomputable section

open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc

namespace PI.LocLatEq

def bc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : LocAt F E sig p) {n : ℕ} (x : Fin n → E) :
    Fin n → A.Ep :=
  fun i => A.ιE (x i)

def latL {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : LocAt F E sig p) {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) : Submodule A.O (Fin n → A.Ep) :=
  Submodule.span A.O (bc A '' (Λ : Set (Fin n → E)))

def Stmt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    Module.finrank F E = 2 → ∀ (sig : E →ₐ[F] E) (p : HeightOneSpectrum (𝓞 F)) (A : LocAt F E sig p) (n : ℕ)
    (Λ₁ Λ₂ : Submodule (𝓞 E) (Fin n → E)), Λ₁.FG → Λ₂.FG →
    (latL A Λ₁ = latL A Λ₂ ↔
      ∀ P : HeightOneSpectrum (𝓞 E), P.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = p.asIdeal →
        ∀ x : Fin n → E, (∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • x ∈ Λ₁) ↔ (∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • x ∈ Λ₂))

end PI.LocLatEq
end
end

-- bundled from Formalism.PeriodIntegrals.LocLatSat
section
noncomputable section

open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc

namespace PI.LocLatSat

def bc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : LocAt F E sig p) {n : ℕ} (x : Fin n → E) :
    Fin n → A.Ep :=
  fun i => A.ιE (x i)

def latL {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} (A : LocAt F E sig p) {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) : Submodule A.O (Fin n → A.Ep) :=
  Submodule.span A.O (bc A '' (Λ : Set (Fin n → E)))

def Stmt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (sig : E →ₐ[F] E) (p : HeightOneSpectrum (𝓞 F)) (A : LocAt F E sig p) (n : ℕ)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (W : Submodule E (Fin n → E)), Λ.FG →
    (latL A (Λ ⊓ W.restrictScalars (𝓞 E)) : Set (Fin n → A.Ep)) =
      (latL A Λ : Set (Fin n → A.Ep)) ∩ Submodule.span A.Ep (bc A '' (W : Set (Fin n → E)))

end PI.LocLatSat
end
end

-- bundled from Formalism.PeriodIntegrals.LocProdFormula
section
noncomputable section

open NumberField IsDedekindDomain

namespace PI

def LocProdFormula : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 →
    ∀ (sig : E →ₐ[F] E) (atP : ∀ p : HeightOneSpectrum (𝓞 F), Formalism.MainNotions.S.Loc.LocAt F E sig p)
      (M : ∀ p : HeightOneSpectrum (𝓞 F), Formalism.MainNotions.S.Loc.Model (atP p).Fp (atP p).Ep), (∀ p, (M p).OK) →
      ∀ x : E, x ≠ 0 → ∏ᶠ p, (M p).modK ((atP p).ιE x) = (((|Algebra.norm ℚ x| : ℚ)) : ℝ)⁻¹

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.PinHostLoc
section
noncomputable section

open scoped Classical

open IsDedekindDomain NumberField ValuativeRel MeasureTheory

namespace PI.PinHostLoc

def Target : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (sig : E →ₐ[F] E) (p : HeightOneSpectrum (𝓞 F)) (A : Formalism.MainNotions.S.Loc.LocAt F E sig p)
    (g : Fin 2 → ℕ), (∀ i, (g i).Prime) → g 0 ≠ g 1 →
    ∀ i : Fin 2, ((g i : ℕ) : 𝓞 F) ∈ p.asIdeal → ((g i : ℕ) : 𝓞 F) ∉ p.asIdeal ^ 2 →
      Irreducible ((Formalism.MainNotions.S.Loc.resChar p : ℕ) : 𝒪[A.Fp]) ∧
        ∃ u : 𝒪[A.Fp], IsUnit u ∧
          (u : A.Fp) = A.ιF (((g 0 : ℕ) : F) * ((g 1 : ℕ) : F) / ((g i : ℕ) : F))

end PI.PinHostLoc
end
end

-- bundled from Formalism.PeriodIntegrals.ProdFormulaE
section
noncomputable section

open IsDedekindDomain NumberField

namespace PI.ProdFormulaE

def ProdFormulaE : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (sig : E →ₐ[F] E) (_h2 : Module.finrank F E = 2)
    (L : ∀ p : HeightOneSpectrum (𝓞 F), Formalism.MainNotions.S.Loc.LocAt F E sig p),
  (∀ M : ∀ p, Formalism.MainNotions.S.Loc.Model (L p).Fp (L p).Ep, (∀ p, (M p).OK) →
    ∀ x : E, x ≠ 0 →
      (Function.mulSupport fun p => (M p).modK ((L p).ιE x)).Finite ∧
      ∏ᶠ p, (M p).modK ((L p).ιE x) = |((Algebra.norm ℚ x : ℚ) : ℝ)|⁻¹) ∧
  (∀ x : E,
    (Function.mulSupport fun p => (L p).psiE ((L p).ιE x)).Finite ∧
    ∏ᶠ p, (L p).psiE ((L p).ιE x) =
      Complex.exp (2 * Real.pi * Complex.I * (((Algebra.trace ℚ E x : ℚ) : ℂ))))

end PI.ProdFormulaE
end
end

