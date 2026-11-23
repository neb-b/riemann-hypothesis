module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0077
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0076
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0032
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0059
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0022

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreNormPrimeBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def FibreNormPrimeBound.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι) (q : ℕ),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    (∀ k, 1 ≤ e k) → (∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (L j) e) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) →
    ∀ p : ℕ, p.Prime → ∃ C : ℕ,
      ∀ τ : ℕ, ∀ s ∈ chartLatNm y (fun k => ((q * e k : ℕ) : ℤ)) τ, ∀ (j : Fin (D + 1))
        (c : ℕ → MvPolynomial (Fin (D + 1)) ℚ), IsDehomNormForms y L j (q * τ) s c →
          ∀ m : Fin (D + 1) →₀ ℕ,
            -((C * τ : ℕ) : ℤ) ≤ padicValRat p ((c (Module.finrank (pullField y L) Ω)).coeff m)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenNearCover
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def GenNearCover.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (V : Ideal (MRingOver S ι)) (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
    (𝓜 : (K → ℤ) → Submodule S M) (deg : ℕ → K → ℤ),
    IsNoetherianRing S → KH.IsMGraded S ι 𝓜 → V ≤ Module.annihilator (MRingOver S ι) M →
    (∀ P : Ideal (MRingOver S ι), IsClosedMultiPt P → V ≤ P →
      ∃ (f : MRingOver S ι) (δ : K → ℕ) (c₀ : ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f δ ∧ f ∉ P ∧
        ∀ c : ℕ, c₀ ≤ c → GenNear S ι 𝓜 (deg c) f δ) →
    ∃ c₁ : ℕ, ∀ c : ℕ, c₁ ≤ c → GeneratedMod S ι 𝓜 (deg c)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenNearMul
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def GenNearMul.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
    (𝓜 : (K → ℤ) → Submodule S M) (W : Ideal (MRingOver S ι)) (d n : K → ℤ) (f g : MRingOver S ι) (δ γ : K → ℕ),
    KH.IsMGraded S ι 𝓜 → W ≤ Module.annihilator (MRingOver S ι) M → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f δ → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g γ →
    GenNear S ι 𝓜 d f δ → GenNear S ι (KH.quotPart S W) n g γ → GenNear S ι 𝓜 (d + n) (f * g) (δ + γ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGradedSubmodules
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def GradedSubmodules.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
    (𝓜 : (K → ℤ) → Submodule S M),
    KH.IsMGraded S ι 𝓜 →
    IsMultiHomogIdeal (Module.annihilator (MRingOver S ι) M) ∧
      ∀ P : Ideal (MRingOver S ι), IsMultiHomogIdeal P →
        KH.IsMGraded S ι (subGrading 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M)) ∧
          KH.IsMGraded S ι (quotGrading 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNormFormGaussBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

noncomputable section

def NormFormGaussBound.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (D : ℕ) (l : Fin (D + 1) → Ω) (P : IntermediateField ℚ Ω)
    [FiniteDimensional P Ω],
    P = IntermediateField.adjoin ℚ {x | ∃ i k, l k ≠ 0 ∧ x = l i / l k} →
    (∀ (d : ℕ) (F : MvPolynomial (Fin (D + 1)) ℚ), F.IsHomogeneous d → aeval l F = 0 → F = 0) →
    ∀ p : ℕ, p.Prime → ∀ (j : Fin (D + 1)) (K d : ℕ) (x : Ω) (c : ℕ → MvPolynomial (Fin (D + 1)) ℚ),
      (c (Module.finrank P Ω)).IsHomogeneous d →
      (LinearMap.charpoly (Algebra.lmul P Ω x)).map (algebraMap P Ω) =
        ∑ i ∈ Finset.range (Module.finrank P Ω + 1),
          Polynomial.C (aeval (fun i' => l i' / l j) (c i)) * Polynomial.X ^ (Module.finrank P Ω - i) →
      (p : Ω) ^ K * x ∈ integralClosure
        (Subring.closure ({z | ∃ i k, z = l i / l k} ∪ {z | ∃ r : ℕ, ¬ p ∣ r ∧ z = (r : Ω)⁻¹})) Ω →
      ∀ μ : Fin (D + 1) →₀ ℕ,
        -((Module.finrank P Ω * K : ℕ) : ℤ) ≤ padicValRat p ((c (Module.finrank P Ω)).coeff μ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullConeDegree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def PullConeDegree.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι) (N : ℕ),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (L j) e) →
    (∀ c : ∀ k, ι k, (∏ k, (X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) ℚ)) ^ N ∈ coneNullIdeal y L) →
    ∀ (d : K → ℕ) (g : MvPolynomial (Σ k, ι k) ℚ), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g d →
      (∀ k, e k + N * Fintype.card (ι k) ≤ d k) →
      ∃ a : Fin (D + 1) → MvPolynomial (Σ k, ι k) ℚ, (∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (a j) (d - e)) ∧
        aeval y g = ∑ j, aeval y (a j) * aeval y (L j)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionFormsIndependent
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ResolutionFormsIndependent.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ) (n r : ℕ)
    (b : Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis d.x n b → ∀ a : Fin r → ℂ,
    (∀ y : d.R.X, ∑ k, a k * eval (resPt d y) (map (algebraMap ℚ ℂ) (b k)) = 0) → a = 0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsZeroCocycleSection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ZeroCocycleSection.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (a : K → ℤ),
    ∀ v ∈ KH.cechZc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a 0,
      ∃ s ∈ chartLat y a 1, GenOnFibres.secCoch y ℤ s a = v

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.VanishOfVanishNsmul
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem vanish_of_vanish_nsmul {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M]
    [Module S M] [IsScalarTower S (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M) (N : K → ℤ) {q : ℕ}
    (hq : 1 ≤ q)
    (h : ∀ e : K → ℤ, ∃ c₁ : ℕ, ∀ c : ℕ, c₁ ≤ c → Subsingleton (KH.cechHc ι 𝓜 (e + (c * q) • N) 1))
    (e : K → ℤ) : ∃ c₁ : ℕ, ∀ c : ℕ, c₁ ≤ c → Subsingleton (KH.cechHc ι 𝓜 (e + c • N) 1) := by
  choose c₀ hc₀ using fun r : ℕ => h (e + r • N)
  refine ⟨((Finset.range q).sup c₀ + 1) * q, fun c hc => ?_⟩
  have hr : c % q ∈ Finset.range q := Finset.mem_range.mpr (Nat.mod_lt _ (by omega))
  have h1 : c₀ (c % q) ≤ (Finset.range q).sup c₀ := Finset.le_sup (f := c₀) hr
  have h2 : (Finset.range q).sup c₀ + 1 ≤ c / q := (Nat.le_div_iff_mul_le (by omega)).mpr hc
  have h3 := hc₀ (c % q) (c / q) (by omega)
  have e' : e + (c % q) • N + (c / q * q) • N = e + c • N := by
    rw [add_assoc, ← add_smul, Nat.mod_add_div' c q]
  rwa [e'] at h3

theorem KleimanVarietyH1Generation.proof (hK : KH.KAmpStatement) (hDev : H1VanishingDevissage.Statement)
    (hGen : GenerationOfH1Vanishing.Statement) : KleimanVarietyH1Generation.Statement := by
  intro F _ K _ _ ι _ _ I Q α b a hI hQ hN hb ha
  refine hGen F K ι Q _ inferInstance (hDev F K ι Q _ inferInstance fun P hP hQP e => ?_)

  obtain ⟨D, hKD, hD⟩ := Targets.ContractMixedField.exists_dim hP
  have hPd : IsProjVarF P (D - Fintype.card K) := ⟨hP, by rw [hD, Nat.sub_add_cancel hKD]⟩
  have hNP : KH.NefOnF I P α := fun W hW hPW => hN W hW (hQP.trans hPW)

  obtain ⟨q, hq, -, hvan⟩ := hK F K ι I P _ α b a hI hPd hNP hb ha
  exact vanish_of_vanish_nsmul _ _ hq hvan e

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

