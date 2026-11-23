module

public import Mathlib

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitDetRoot
section
noncomputable section
open scoped BigOperators ComplexConjugate

namespace PI

def UnitDetRootDefs.cmTheta (b : ℤ) (d : ℕ) : ℂ := ((b : ℂ) + Complex.I * ((Real.sqrt d : ℝ) : ℂ)) / 2

def UnitDetRootDefs.cmPair (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) : PeriodPair where
  ω₁ := (a : ℂ)
  ω₂ := UnitDetRootDefs.cmTheta b d
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
    have him := congrArg Complex.im h
    have hre := congrArg Complex.re h
    simp [UnitDetRootDefs.cmTheta] at him hre
    have ht : t = 0 := by
      rcases him with h1 | h1
      · exact h1
      · exact absurd h1 (by positivity)
    subst ht
    simp at hre
    refine ⟨?_, rfl⟩
    rcases hre with h1 | h1
    · exact h1
    · exact absurd h1 (by positivity)

def UnitDetRootDefs.scalePair (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) : PeriodPair where
  ω₁ := c * L.ω₁
  ω₂ := c * L.ω₂
  indep := by
    have h := L.indep
    rw [LinearIndependent.pair_iff] at h ⊢
    intro s t hst
    apply h s t
    have : c * (s • L.ω₁ + t • L.ω₂) = 0 := by
      rw [← hst]; simp only [Complex.real_smul]; ring
    exact (mul_eq_zero.mp this).resolve_left hc

def UnitDetRootDefs.area (L : PeriodPair) : ℝ := |(conj L.ω₁ * L.ω₂).im|

section General

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

abbrev UnitDetRootDefs.Sesq (V : Type*) [AddCommGroup V] [Module ℂ V] := V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ

def UnitDetRootDefs.altE (H : UnitDetRootDefs.Sesq V) (x y : V) : ℝ := (H x y).im

def UnitDetRootDefs.dualLat (H : UnitDetRootDefs.Sesq V) (Λ : AddSubgroup V) : AddSubgroup V where
  carrier := {x | ∀ y ∈ Λ, ∃ m : ℤ, UnitDetRootDefs.altE H x y = (m : ℝ)}
  zero_mem' := fun y _ => ⟨0, by simp [UnitDetRootDefs.altE]⟩
  add_mem' := by
    intro a b ha hb y hy
    obtain ⟨m, hm⟩ := ha y hy
    obtain ⟨k, hk⟩ := hb y hy
    exact ⟨m + k, by simp only [UnitDetRootDefs.altE] at hm hk ⊢; simp [hm, hk]⟩
  neg_mem' := by
    intro a ha y hy
    obtain ⟨m, hm⟩ := ha y hy
    exact ⟨-m, by simp only [UnitDetRootDefs.altE] at hm ⊢; simp [hm]⟩

def UnitDetRootDefs.IsSelfDual (H : UnitDetRootDefs.Sesq V) (Λ : AddSubgroup V) : Prop := UnitDetRootDefs.dualLat H Λ = Λ

def UnitDetRootDefs.relIdx (Λ₁ Λ₂ : AddSubgroup V) : ℕ := Λ₁.relIndex Λ₂

def UnitDetRootDefs.IsIsom {W : Type*} [AddCommGroup W] [Module ℂ W] (H : UnitDetRootDefs.Sesq V) (H' : UnitDetRootDefs.Sesq W) (g : V →ₗ[ℂ] W) : Prop :=
  ∀ x y, H' (g x) (g y) = H x y

def UnitDetRootDefs.imgLat {W : Type*} [AddCommGroup W] [Module ℂ W] (g : V →ₗ[ℂ] W) (Λ : AddSubgroup V) : AddSubgroup W :=
  Λ.map g.toAddMonoidHom

end General

section Coordinates

variable {n : Type*} [Fintype n]

def UnitDetRootDefs.matH (h : Matrix n n ℂ) : UnitDetRootDefs.Sesq (n → ℂ) :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun z w => ∑ i, ∑ j, z i * h i j * conj (w j))
    (by intro a b c; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib])
    (by intro c a b; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc])
    (by intro a b c; simp only [Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib])
    (by
      intro c a b
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring)

def UnitDetRootDefs.stdH (L : PeriodPair) (n : Type*) [Fintype n] [DecidableEq n] : UnitDetRootDefs.Sesq (n → ℂ) :=
  UnitDetRootDefs.matH (((UnitDetRootDefs.area L : ℝ) : ℂ)⁻¹ • (1 : Matrix n n ℂ))

def UnitDetRootDefs.stdLat (L : PeriodPair) (n : Type*) : AddSubgroup (n → ℂ) :=
  AddSubgroup.pi Set.univ fun _ => L.lattice.toAddSubgroup

end Coordinates

def UnitDetRootDefs.cmL (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0) : PeriodPair :=
  UnitDetRootDefs.scalePair (UnitDetRootDefs.cmPair a b d ha hd) lam hlam

def UnitDetRootDefs.CmOK (a : ℕ) (b c : ℤ) (d : ℕ) : Prop := 4 * (a : ℤ) * c = b ^ 2 + d ∧ Odd a ∧ d % 8 = 7 ∧ d.Prime

def UnitDetRoot : Prop :=
  ∀ (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0), UnitDetRootDefs.CmOK a b c d →
    ∀ (m : Type) [Fintype m] [DecidableEq m] (Λa : AddSubgroup (m → ℂ)),
      UnitDetRootDefs.IsSelfDual (UnitDetRootDefs.stdH (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) Λa →
      (∀ x ∈ Λa, UnitDetRootDefs.cmTheta b d • x ∈ Λa) →
      UnitDetRootDefs.relIdx (UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) Λa ≠ 0 →
      UnitDetRootDefs.relIdx Λa (UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) ≠ 0 →
      ∃ κ : ℂ, κ ≠ 0 ∧ IsAlgebraic ℚ κ ∧ (∀ σ : ℂ ≃+* ℂ, ‖σ κ‖ = 1) ∧
        ∀ (l : ℕ) [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) (δ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ)),
          UnitDetRootDefs.IsIsom (UnitDetRootDefs.stdH (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) (UnitDetRootDefs.stdH (UnitDetRootDefs.cmL a b d ha hd lam hlam) m)
            (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) →
          UnitDetRootDefs.relIdx (UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) (UnitDetRootDefs.imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) ≠ 0 →
          ¬ l ∣ UnitDetRootDefs.relIdx (UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) (UnitDetRootDefs.imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) →
          UnitDetRootDefs.relIdx (UnitDetRootDefs.imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) (UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m) ≠ 0 →
          ‖ι κ‖ ^ 2 * ‖ι (LinearMap.det (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)))‖ = 1

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryApprox
section
noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace PI

section Group

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

def UnitaryApproxDefs.cT (σ : A →+* A) {m p : Type} (M : Matrix m p A) : Matrix p m A := (M.map σ)ᵀ

def UnitaryApproxDefs.IsHerm (σ : A →+* A) (J : Matrix n n A) : Prop := UnitaryApproxDefs.cT σ J = J

theorem UnitaryApproxDefs.cT_mul (σ : A →+* A) {m p q : Type} [Fintype p] (M : Matrix m p A) (N : Matrix p q A) :
    UnitaryApproxDefs.cT σ (M * N) = UnitaryApproxDefs.cT σ N * UnitaryApproxDefs.cT σ M := by
  simp [UnitaryApproxDefs.cT, Matrix.map_mul, Matrix.transpose_mul]

theorem UnitaryApproxDefs.cT_one (σ : A →+* A) : UnitaryApproxDefs.cT σ (1 : Matrix n n A) = 1 := by
  unfold UnitaryApproxDefs.cT
  rw [Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.transpose_one]

def UnitaryApproxDefs.UJ (σ : A →+* A) (J : Matrix n n A) : Subgroup (GL n A) where
  carrier := {g | UnitaryApproxDefs.cT σ (g : Matrix n n A) * J * (g : Matrix n n A) = J}
  one_mem' := by simp [UnitaryApproxDefs.cT_one]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Units.val_mul] at *
    calc UnitaryApproxDefs.cT σ ((a : Matrix n n A) * (b : Matrix n n A)) * J * ((a : Matrix n n A) * (b : Matrix n n A))
        = UnitaryApproxDefs.cT σ (b : Matrix n n A) * (UnitaryApproxDefs.cT σ (a : Matrix n n A) * J * (a : Matrix n n A)) * (b : Matrix n n A) := by
          rw [UnitaryApproxDefs.cT_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [ha, hb]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_ofPred_eq] at *
    calc UnitaryApproxDefs.cT σ ((g⁻¹ : GL n A) : Matrix n n A) * J * ((g⁻¹ : GL n A) : Matrix n n A)
        = UnitaryApproxDefs.cT σ ((g⁻¹ : GL n A) : Matrix n n A) * (UnitaryApproxDefs.cT σ (g : Matrix n n A) * J * (g : Matrix n n A))
            * ((g⁻¹ : GL n A) : Matrix n n A) := by rw [hg]
      _ = UnitaryApproxDefs.cT σ ((g : Matrix n n A) * ((g⁻¹ : GL n A) : Matrix n n A)) * J
            * ((g : Matrix n n A) * ((g⁻¹ : GL n A) : Matrix n n A)) := by
          rw [UnitaryApproxDefs.cT_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [Units.mul_inv, UnitaryApproxDefs.cT_one, Matrix.one_mul, Matrix.mul_one]
end Group

section Points

variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {n : Type} [Fintype n] [DecidableEq n]

def UnitaryApproxDefs.sigR (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] : E ⊗[F] R →+* E ⊗[F] R :=
  (Algebra.TensorProduct.map σ (AlgHom.id F R)).toRingHom

def UnitaryApproxDefs.inclE (R : Type) [CommRing R] [Algebra F R] : E →+* E ⊗[F] R :=
  Algebra.TensorProduct.includeLeftRingHom

def UnitaryApproxDefs.UPts (σ : E →ₐ[F] E) (J : Matrix n n E) (R : Type) [CommRing R] [Algebra F R] :
    Subgroup (GL n (E ⊗[F] R)) := UnitaryApproxDefs.UJ (UnitaryApproxDefs.sigR σ R) (J.map (UnitaryApproxDefs.inclE (F := F) R))

def UnitaryApproxDefs.tensInt (R : Type) [CommRing R] [Algebra F R] (S₁ : Subring E) (S₂ : Subring R) :
    Subring (E ⊗[F] R) :=
  Subring.closure (Set.range (fun x : S₁ => (x : E) ⊗ₜ[F] (1 : R)) ∪
    Set.range (fun y : S₂ => (1 : E) ⊗ₜ[F] (y : R)))

def UnitaryApproxDefs.intOE (E : Type) [Field E] [NumberField E] : Subring E := (algebraMap (𝓞 E) E).range

end Points

end PI

end
end

-- bundled from Formalism.PeriodIntegrals.VacEntire
section
noncomputable section

namespace PI.VacEntire

variable {ι : Type} [Fintype ι] {N N' : ℕ}

def Hf (A : ℝ) (z w : ι → Fin N' → Fin N → ℂ) : ℂ :=
  (∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j)) / (A : ℂ)

def al (d : ℕ) (A : ℝ) (x : ι → Fin N' → Fin N → ℂ) : ℂ :=
  (-1 : ℂ) ^ (round (Real.sqrt d / 2 * (Hf A x x).re))

def U (A : ℝ) (x : ι → Fin N' → Fin N → ℂ) (G : (ι → Fin N' → Fin N → ℂ) → ℂ) : (ι → Fin N' → Fin N → ℂ) → ℂ :=
  fun z => G (z + x) * Complex.exp (-(Real.pi : ℂ) * Hf A z x - (Real.pi : ℂ) * Hf A x x / 2)

def Iop (d : ℕ) (A : ℝ) (La₁ La₂ : AddSubgroup (ι → Fin N' → Fin N → ℂ))
    (G : (ι → Fin N' → Fin N → ℂ) → ℂ) : (ι → Fin N' → Fin N → ℂ) → ℂ :=
  fun z => ((Real.sqrt ((La₁.addSubgroupOf La₂).index : ℝ))⁻¹ : ℂ) *
    ∑ᶠ q : La₂ ⧸ La₁.addSubgroupOf La₂,
      al d A ((Quotient.out q : La₂) : ι → Fin N' → Fin N → ℂ) * U A ((Quotient.out q : La₂) : ι → Fin N' → Fin N → ℂ) G z

def tensPow {n : Type} [Fintype n] (θ : (n → ℂ) → ℂ) (N N' : ℕ) (z : n → Fin N' → Fin N → ℂ) : ℂ :=
  ∏ i : Fin N', ∏ j : Fin N, θ fun τ => z τ i j

def IopEntire : Prop :=
  ∀ (ι : Type) [Fintype ι] (N N' d : ℕ) (A : ℝ) (La₁ La₂ : AddSubgroup (ι → Fin N' → Fin N → ℂ))
    (G : (ι → Fin N' → Fin N → ℂ) → ℂ), AnalyticOnNhd ℂ G Set.univ → AnalyticOnNhd ℂ (Iop d A La₁ La₂ G) Set.univ

def TensEntire : Prop :=
  ∀ (n : Type) [Fintype n] (θ : (n → ℂ) → ℂ) (N N' : ℕ), AnalyticOnNhd ℂ θ Set.univ →
    AnalyticOnNhd ℂ (tensPow θ N N') Set.univ

def Target : Prop := IopEntire ∧ TensEntire

end PI.VacEntire
end
end

-- bundled from Formalism.PeriodIntegrals.WeilQuotMeas
section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct ENNReal Matrix

namespace PI.WeilQuotMeas

def WeilQuotient : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G), IsClosed (H : Set G) →
    ∀ (μ : Measure G) (ν : Measure H), μ.IsHaarMeasure → μ.IsMulRightInvariant → ν.IsHaarMeasure →
      ν.IsMulRightInvariant →
      ∃ ρ : Measure (G ⧸ H), ρ ≠ 0 ∧ (∀ K : Set (G ⧸ H), IsCompact K → ρ K < ⊤) ∧
        (∀ (g : G) (s : Set (G ⧸ H)), MeasurableSet s → ρ ((fun y => g • y) ⁻¹' s) = ρ s) ∧
        (∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ g, f g ∂μ = ∫⁻ y, (∫⁻ h, f (y.out * h) ∂ν) ∂ρ) ∧
        ∀ ρ' : Measure (G ⧸ H), (∀ K : Set (G ⧸ H), IsCompact K → ρ' K < ⊤) →
          (∀ (g : G) (s : Set (G ⧸ H)), MeasurableSet s → ρ' ((fun y => g • y) ⁻¹' s) = ρ' s) →
          ∃ c : ℝ≥0∞, ρ' = c • ρ

def WqUnique : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (H : Subgroup G), IsClosed (H : Set G) →
    ∀ ρ ρ' : Measure (G ⧸ H), ρ ≠ 0 →
      (∀ K : Set (G ⧸ H), IsCompact K → ρ K < ⊤) →
      (∀ (g : G) (s : Set (G ⧸ H)), MeasurableSet s → ρ ((fun y => g • y) ⁻¹' s) = ρ s) →
      (∀ K : Set (G ⧸ H), IsCompact K → ρ' K < ⊤) →
      (∀ (g : G) (s : Set (G ⧸ H)), MeasurableSet s → ρ' ((fun y => g • y) ⁻¹' s) = ρ' s) →
      ∃ c : ℝ≥0∞, ρ' = c • ρ

end PI.WeilQuotMeas
end
end

-- bundled from Formalism.PeriodIntegrals.WeylProd
section
namespace PI

open Finset

def vandN (x : ℕ → ℝ) (N : ℕ) : ℝ := ∏ i ∈ range N, ∏ j ∈ Ico (i + 1) N, (x i - x j)

noncomputable def dimVN (x : ℕ → ℝ) (N : ℕ) : ℝ := vandN x N / ∏ i ∈ range N, ((i.factorial : ℕ) : ℝ)

def shiftSeq {n : ℕ} (w : Fin n → ℤ) : ℕ → ℝ := fun i => if h : i < n then ((w ⟨i, h⟩ : ℤ) : ℝ) - i else 0

def WeylProd : Prop :=
  ∀ (n : ℕ) (μ w : Fin n → ℤ) (c : ℤ), (∀ t, μ t = w t - c) →
    (((∏ i : Fin n, ∏ j : Fin n,
      if i < j then (((μ i : ℤ) : ℚ) - ((μ j : ℤ) : ℚ) + ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) /
        (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) else 1 : ℚ)) : ℝ) = dimVN (shiftSeq w) n

end PI
end

-- bundled from Formalism.PeriodIntegrals.WittUnram
section
noncomputable section

namespace PI

abbrev WF (p f : ℕ) [Fact p.Prime] := WittVector p (GaloisField p f)

def IsWittIdent {p f : ℕ} [Fact p.Prime] {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] (σ : Qq ≃+* Qq)
    (φ : WF p f ≃+* W) : Prop :=
  ∀ x : WF p f, σ (algebraMap W Qq (φ x)) = algebraMap W Qq (φ (WittVector.frobenius x))

def WittUnram : Prop :=
  ∀ (p f : ℕ) [Fact p.Prime] (W Qq : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] (σ : Qq ≃+* Qq),
    IsFractionRing W Qq → Irreducible (p : W) → Nat.card (W ⧸ Ideal.span {(p : W)}) = p ^ f →
    IsAdicComplete (Ideal.span {(p : W)}) W →
    (∀ x : W, ∃ y : W, σ (algebraMap W Qq x) = algebraMap W Qq (x ^ p + (p : W) * y)) →
    ∃ φ : WF p f ≃+* W, IsWittIdent σ φ

end PI
end
end

-- bundled from Formalism.PeriodIntegrals.WwCauchyBinet
section
noncomputable section

namespace PI.WwCauchyBinet

namespace KM

variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N0 N1 : ℕ)

def ColChoice (nu : Lt → YoungDiagram) : Type :=
  ∀ (s : Lt) (c : Fin ((nu s).rowLen 0)), Fin ((nu s).colLen c) ↪o Fin N1

def nablaX (nu : Lt → YoungDiagram) (J : ColChoice N0 nu) : MvPolynomial (Lt × ℕ × Fin N0) ℤ :=
  ∏ s, ∏ c : Fin ((nu s).rowLen 0), Matrix.det (Matrix.of fun i k : Fin ((nu s).colLen c) =>
    (MvPolynomial.X (s, (i : ℕ), J s c k) : MvPolynomial (Lt × ℕ × Fin N0) ℤ))

end KM

def DeX {Lt k : Type} [Fintype Lt] [CommRing k] (N : ℕ) (nu : Lt → YoungDiagram) (y : Lt → Fin N → ℕ → k) :
    MvPolynomial (Lt × ℕ × Fin N) k :=
  ∏ s, ∏ c : Fin ((nu s).rowLen 0), Matrix.det (Matrix.of fun i j : Fin ((nu s).colLen c) =>
    ∑ a : Fin N, MvPolynomial.C (y s a (j : ℕ)) * MvPolynomial.X (s, (i : ℕ), a))

def minY {Lt k : Type} [Fintype Lt] [CommRing k] (N : ℕ) (nu : Lt → YoungDiagram) (J : KM.ColChoice N nu)
    (y : Lt → Fin N → ℕ → k) : k :=
  ∏ s, ∏ c : Fin ((nu s).rowLen 0), Matrix.det (Matrix.of fun i j : Fin ((nu s).colLen c) => y s (J s c i) (j : ℕ))

def WwCauchyBinet : Prop :=
  ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (k : Type) [CommRing k] (N : ℕ) (nu : Lt → YoungDiagram) (y : Lt → Fin N → ℕ → k),
    DeX N nu y = ∑ᶠ J : KM.ColChoice N nu, MvPolynomial.C (minY N nu J y) *
      MvPolynomial.map (Int.castRingHom k) (KM.nablaX N nu J)

end PI.WwCauchyBinet
end
end

-- bundled from Formalism.PeriodIntegrals.WwInjective
section
noncomputable section

namespace PI.WwInjective

namespace KM

variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N0 N1 : ℕ)

abbrev XZ (Lt : Type) (N0 N1 : ℕ) : Type := (Lt × ℕ × Fin N0) ⊕ (Lt × Fin N0 × Fin N1)

def ColChoice (nu : Lt → YoungDiagram) : Type :=
  ∀ (s : Lt) (c : Fin ((nu s).rowLen 0)), Fin ((nu s).colLen c) ↪o Fin N1

def applyAt0 (l : ℕ) [Fact l.Prime] (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (P : MvPolynomial (XZ Lt N0 N1) ℤ) : MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l] :=
  ∑ μ ∈ P.support, MvPolynomial.monomial (Finsupp.sumFinsuppEquivProdFinsupp μ).1
    (((AddMonoidAlgebra.coeff P μ : ℤ) : ℂ_[l]) *
      ((Finsupp.sumFinsuppEquivProdFinsupp μ).2.prod fun _ n => (n.factorial : ℂ_[l])) *
      MvPowerSeries.coeff (Finsupp.sumFinsuppEquivProdFinsupp μ).2 Th)

def nablaX (nu : Lt → YoungDiagram) (J : ColChoice N0 nu) : MvPolynomial (Lt × ℕ × Fin N0) ℤ :=
  ∏ s, ∏ c : Fin ((nu s).rowLen 0), Matrix.det (Matrix.of fun i k : Fin ((nu s).colLen c) =>
    (MvPolynomial.X (s, (i : ℕ), J s c k) : MvPolynomial (Lt × ℕ × Fin N0) ℤ))

end KM

def DeX {Lt k : Type} [Fintype Lt] [CommRing k] (N : ℕ) (nu : Lt → YoungDiagram) (y : Lt → Fin N → ℕ → k) :
    MvPolynomial (Lt × ℕ × Fin N) k :=
  ∏ s, ∏ c : Fin ((nu s).rowLen 0), Matrix.det (Matrix.of fun i j : Fin ((nu s).colLen c) =>
    ∑ a : Fin N, MvPolynomial.C (y s a (j : ℕ)) * MvPolynomial.X (s, (i : ℕ), a))

def minY {Lt k : Type} [Fintype Lt] [CommRing k] (N : ℕ) (nu : Lt → YoungDiagram) (J : KM.ColChoice N nu)
    (y : Lt → Fin N → ℕ → k) : k :=
  ∏ s, ∏ c : Fin ((nu s).rowLen 0), Matrix.det (Matrix.of fun i j : Fin ((nu s).colLen c) => y s (J s c i) (j : ℕ))

def WwInjective : Prop :=
  ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (l : ℕ) [Fact l.Prime] (N : ℕ) (nu : Lt → YoungDiagram)
    (ph : Module.Dual ℂ_[l] (MvPolynomial (Lt × ℕ × Fin N) ℂ_[l])),
    (∀ y, ph (DeX N nu y) = 0) → ∀ J, ph (MvPolynomial.map (Int.castRingHom _) (KM.nablaX N nu J)) = 0

end PI.WwInjective
end
end

-- bundled from Formalism.PeriodIntegrals.WwMain
section
noncomputable section

namespace PI.WwMain

namespace KM

variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N0 N1 : ℕ)

abbrev XZ (Lt : Type) (N0 N1 : ℕ) : Type := (Lt × ℕ × Fin N0) ⊕ (Lt × Fin N0 × Fin N1)

def minorXZ (s : Lt) (p : ℕ) (I : Fin p ↪o Fin N1) : MvPolynomial (XZ Lt N0 N1) ℤ :=
  Matrix.det (Matrix.of fun i k : Fin p => ∑ a : Fin N0,
    MvPolynomial.X (Sum.inl (s, (i : ℕ), a)) * MvPolynomial.X (Sum.inr (s, a, I k)))

def ColChoice (nu : Lt → YoungDiagram) : Type :=
  ∀ (s : Lt) (c : Fin ((nu s).rowLen 0)), Fin ((nu s).colLen c) ↪o Fin N1

def Gxz (nu : Lt → YoungDiagram) (I : ColChoice N1 nu) : MvPolynomial (XZ Lt N0 N1) ℤ :=
  ∏ s, ∏ c : Fin ((nu s).rowLen 0), minorXZ N0 N1 s ((nu s).colLen c) (I s c)

def applyAt0 (l : ℕ) [Fact l.Prime] (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (P : MvPolynomial (XZ Lt N0 N1) ℤ) : MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l] :=
  ∑ μ ∈ P.support, MvPolynomial.monomial (Finsupp.sumFinsuppEquivProdFinsupp μ).1
    (((AddMonoidAlgebra.coeff P μ : ℤ) : ℂ_[l]) *
      ((Finsupp.sumFinsuppEquivProdFinsupp μ).2.prod fun _ n => (n.factorial : ℂ_[l])) *
      MvPowerSeries.coeff (Finsupp.sumFinsuppEquivProdFinsupp μ).2 Th)

end KM

def DeX {Lt k : Type} [Fintype Lt] [CommRing k] (N : ℕ) (nu : Lt → YoungDiagram) (y : Lt → Fin N → ℕ → k) :
    MvPolynomial (Lt × ℕ × Fin N) k :=
  ∏ s, ∏ c : Fin ((nu s).rowLen 0), Matrix.det (Matrix.of fun i j : Fin ((nu s).colLen c) =>
    ∑ a : Fin N, MvPolynomial.C (y s a (j : ℕ)) * MvPolynomial.X (s, (i : ℕ), a))

def minY {Lt k : Type} [Fintype Lt] [CommRing k] (N : ℕ) (nu : Lt → YoungDiagram) (J : KM.ColChoice N nu)
    (y : Lt → Fin N → ℕ → k) : k :=
  ∏ s, ∏ c : Fin ((nu s).rowLen 0), Matrix.det (Matrix.of fun i j : Fin ((nu s).colLen c) => y s (J s c i) (j : ℕ))

def applyQ {Lt : Type} (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ) (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (Q : MvPolynomial (Lt × Fin N0 × ℕ) ℂ_[l]) (y' : Lt → Fin N1 → ℕ → ℂ_[l]) : ℂ_[l] :=
  let P : MvPolynomial (Lt × Fin N0 × Fin N1) ℂ_[l] :=
    MvPolynomial.aeval (fun v : Lt × Fin N0 × ℕ => ∑ b : Fin N1,
      MvPolynomial.C (y' v.1 b v.2.2) * MvPolynomial.X ((v.1, v.2.1, b) : Lt × Fin N0 × Fin N1)) Q
  ∑ α ∈ P.support, AddMonoidAlgebra.coeff P α * (α.prod fun _ n => (n.factorial : ℂ_[l])) * MvPowerSeries.coeff α Th

def WwMain : Prop :=
  ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (l : ℕ) [Fact l.Prime] (N0 N1 : ℕ) (nu : Lt → YoungDiagram)
    (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (ph : Module.Dual ℂ_[l] (MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l]))
    (Q : MvPolynomial (Lt × Fin N0 × ℕ) ℂ_[l]),
    (∀ y : Lt → Fin N0 → ℕ → ℂ_[l], MvPolynomial.eval (fun v => y v.1 v.2.1 v.2.2) Q = ph (DeX N0 nu y)) →
    ∀ y' : Lt → Fin N1 → ℕ → ℂ_[l],
      applyQ l N0 N1 Th Q y' = ∑ᶠ I : KM.ColChoice N1 nu, minY N1 nu I y' * ph (KM.applyAt0 N0 N1 l Th (KM.Gxz N0 N1 nu I))

end PI.WwMain
end
end

