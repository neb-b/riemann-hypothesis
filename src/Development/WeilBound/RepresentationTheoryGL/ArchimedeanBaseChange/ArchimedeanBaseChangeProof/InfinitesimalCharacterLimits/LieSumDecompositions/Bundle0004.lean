module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.Bundle0002
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2DecayOfCountEscape
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0016
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0003

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.GrowPHolds
section
noncomputable section

open NumberField MeasureTheory ComplexConjugate
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CuspRep.CuspidalL2GL PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.Leaf2Aux

section Defs

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}

def GrowP (f : GA E N → ℂ) : Prop :=
  Continuous f ∧ (∀ γ ∈ latticeGL E N, ∀ g, f (γ * g) = f g) ∧
    ∀ ε : ℝ, 0 < ε → An.Bnd f fun r => An.rho E N r + ε

def GrowQ (f : GA E N → ℂ) : Prop :=
  Continuous f ∧ (∀ γ ∈ latticeGL E N, ∀ g, f (γ * g) = f g) ∧
    ∃ κ : ℕ → ℝ, (∀ r, 0 < r → r < N → κ r < An.rho E N r) ∧ An.Bnd f κ

def pr (f g : GA E N → ℂ) : ℂ := pet (latticeGL E N) (Measure.haar : Measure (GA E N)) f g

end Defs

def GrowPHolds : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) (χ : Sm E N),
  IsAutForm χ → (∀ (t : ℝ) g, χ.1 (splitCentre E N t * g) = χ.1 g) →
  (∀ r, 0 < r → r < N → ∀ c ∈ Exp r χ.1, pE E N r c ≤ 0) → GrowP χ.1

def GrowQHolds : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) (u : Sm E N),
  IsAutForm u → IsSqInt u.1 → GrowQ u.1

def IntBnd : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) (H : GA E N → ℝ),
  Continuous H → (∀ g, 0 ≤ H g) → (∀ γ ∈ latticeGL E N, ∀ g, H (γ * g) = H g) →
  ∀ m : ℕ → ℝ, (∀ r, 0 < r → r < N → m r < 2 * An.rho E N r) → An.Bnd (fun g => (H g : ℂ)) m →
    ∫⁻ g in stdDom (latticeGL E N), ENNReal.ofReal (H g) ∂(Measure.haar : Measure (GA E N)) < ⊤

def PairLin : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ),
  (∀ (f₁ f₂ g : GA E N → ℂ) (c : ℂ), GrowP f₁ → GrowP f₂ → GrowQ g →
    pr (f₁ + f₂) g = pr f₁ g + pr f₂ g ∧ pr (c • f₁) g = c * pr f₁ g) ∧
  ∀ (f g₁ g₂ : GA E N → ℂ) (c : ℂ), GrowP f → GrowQ g₁ → GrowQ g₂ →
    pr f (g₁ + g₂) = pr f g₁ + pr f g₂ ∧ pr f (c • g₁) = conj c * pr f g₁

def PairRt : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) (x : GA E N)
  (f g : GA E N → ℂ), (∀ γ ∈ latticeGL E N, ∀ y, f (γ * y) = f y) → (∀ γ ∈ latticeGL E N, ∀ y, g (γ * y) = g y) →
    pr (fun y => f (y * x)) g = pr f (fun y => g (y * x⁻¹))

def PairLie : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) (X : Lie E N)
  (χ u : Sm E N), GrowP χ.1 → GrowP (act (.lie X) χ).1 → GrowQ u.1 → GrowQ (act (.lie X) u).1 →
    pr (act (.lie X) χ).1 u.1 = -pr χ.1 (act (.lie X) u).1

def Core : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) (U : Submodule ℂ (Sm E N)),
  _root_.GlobalTheory.CuspRep.IsStable U → (∀ χ ∈ U, IsAutForm χ) → (∀ χ ∈ U, GrowP χ.1) → ∀ φ ∈ U, φ ∈ A2 E N → φ ≠ 0 →
    ∃ (V : Submodule ℂ (Sm E N)) (p : Sm E N →ₗ[ℂ] Sm E N), IsDiscrete V ∧ (∀ χ ∈ U, p χ ∈ V) ∧
      (∀ o, ∀ χ ∈ U, p (act o χ) = act o (p χ)) ∧ p φ ≠ 0

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.Leaf2Aux

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.NodeHolds
section
noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz

open PositivityTheory.Rg.Rs.ParabolicProjection in
theorem node_holds : Node := by
  intro E _ _ _ r s _ _ U W₁ W₂ T hU hW₁ hW₂ hTe hmem hC₁ hC₂ φ₀ hφ₀U hφ₀
  obtain ⟨k₀, g₀, m₀, hm₀⟩ := exists_slice_ne hφ₀ (hmem φ₀ hφ₀U).1
  obtain ⟨n, ψ₁, ψ₂, h₁, h₂, hsum⟩ := tensor_pair_finite_sum ((hmem φ₀ hφ₀U).2 k₀ g₀)
  have hne : ∑ i, (ψ₁ i).1 m₀.1 * (ψ₂ i).1 m₀.2 ≠ 0 := (hsum m₀) ▸ hm₀

  obtain ⟨χ₁, hχ₁, hχ₁e⟩ : ∑ i, (ψ₂ i).1 m₀.2 • ψ₁ i ∈ tw W₁ ((s : ℂ) / 2) :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h₁ i)
  have hχ₁0 : χ₁ ≠ 0 := fun h => sum_left_ne hne (by rw [← hχ₁e, h, map_zero])
  have hc₁ := hC₁ χ₁ hχ₁ hχ₁0
  obtain ⟨t₁, p₁, ht₁, hpos₁, hp₁e, hp₁V, hp₁0⟩ := hc₁
  have hf₁ : twMap r ((s : ℂ) / 2) p₁ (∑ i, (ψ₂ i).1 m₀.2 • ψ₁ i) ≠ 0 := by
    rw [← hχ₁e]
    change twMap r ((s : ℂ) / 2) p₁ (mulChi r (Model.absC E ((s : ℂ) / 2)) χ₁) ≠ 0
    rw [twMap_apply, mulChi_absC_neg, Ne, LinearEquiv.map_eq_zero_iff]
    exact hp₁0
  obtain ⟨b₁, hb₁⟩ := step_left (twMap r ((s : ℂ) / 2) p₁) hf₁

  obtain ⟨χ₂, hχ₂, hχ₂e⟩ : ∑ i, (twMap r ((s : ℂ) / 2) p₁ (ψ₁ i)).1 b₁ • ψ₂ i ∈ tw W₂ (-(r : ℂ) / 2) :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h₂ i)
  have hχ₂0 : χ₂ ≠ 0 := fun h => sum_right_ne hb₁ (by rw [← hχ₂e, h, map_zero])
  have hc₂ := hC₂ χ₂ hχ₂ hχ₂0
  obtain ⟨t₂, p₂, ht₂, hpos₂, hp₂e, hp₂V, hp₂0⟩ := hc₂
  have hf₂ : twMap s (-(r : ℂ) / 2) p₂ (∑ i, (twMap r ((s : ℂ) / 2) p₁ (ψ₁ i)).1 b₁ • ψ₂ i) ≠ 0 := by
    rw [← hχ₂e]
    change twMap s (-(r : ℂ) / 2) p₂ (mulChi s (Model.absC E (-(r : ℂ) / 2)) χ₂) ≠ 0
    rw [twMap_apply, mulChi_absC_neg, Ne, LinearEquiv.map_eq_zero_iff]
    exact hp₂0
  obtain ⟨b₂, hb₂⟩ := step_right (twMap s (-(r : ℂ) / 2) p₂) hf₂

  have hI := indMap_holds E r s U (tw W₁ ((s : ℂ) / 2)) (tw W₂ (-(r : ℂ) / 2)) T (twMap r ((s : ℂ) / 2) p₁)
    (twMap s (-(r : ℂ) / 2) p₂) hU.1 hU.2 (isStable_tw hW₁.1 _) (isStable_tw hW₂.1 _) hTe hmem
    (twMap_equiv hW₁.1 hp₁e) (twMap_equiv hW₂.1 hp₂e)
  obtain ⟨T', hT'e, hT'u, hT's⟩ := hI
  have hT'm : ∀ φ ∈ U, MemInd2 (tw t₁.space ((s : ℂ) / 2)) (tw t₂.space (-(r : ℂ) / 2)) (T' φ) := by
    intro φ hφ
    refine ⟨hT'u φ hφ, fun k g => ?_⟩
    obtain ⟨n', ψ₁', ψ₂', h₁', h₂', hs'⟩ := tensor_pair_finite_sum ((hmem φ hφ).2 k g)
    have e := hT's φ hφ k g n' ψ₁' ψ₂' h₁' h₂' hs'
    rw [show (fun m : GA E r × GA E s => (T' φ).1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) *
      finGL E (r + s) g))) = fun m => ∑ i, (twMap r ((s : ℂ) / 2) p₁ (ψ₁' i)).1 m.1 *
        (twMap s (-(r : ℂ) / 2) p₂ (ψ₂' i)).1 m.2 from funext e]
    exact sum_mem_tens2 (fun i => twMap_mem hp₁V _ (h₁' i)) (fun i => twMap_mem hp₂V _ (h₂' i))
  refine ⟨Tr.node t₁ t₂, T', ⟨ht₁, ht₂⟩, ⟨hpos₁, hpos₂⟩, hT'e, fun φ hφ => ?_, fun h => ?_⟩
  · rw [Tr.space]
    exact Submodule.subset_span ⟨hT'm φ hφ,
      InducedTensorMap.Main.finVec_of_equiv hT'e hφ (hU.2 φ hφ).kfin⟩
  · have e := hT's φ₀ hφ₀U k₀ g₀ n ψ₁ ψ₂ h₁ h₂ hsum (b₁, b₂)
    rw [h] at e
    exact hb₂ e.symm

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksDefs
section
noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockDerivatives

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def yp {a : ℕ} (k : Kinf E a) (g : GL (Fin a) (Af E)) : GA E a := infGL E a (Unitary.toUnits k) * finGL E a g

def lsF (r s : ℕ) (F : Sm E (r + s)) (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) : Set (Sm E r) :=
  {ℓ | ∃ m₂ : GA E s, ∀ m₁, ℓ.1 m₁ = F.1 (lev (Ad E) r s (m₁, m₂) * yp k g)}

def rsF (r s : ℕ) (F : Sm E (r + s)) (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) : Set (Sm E s) :=
  {ℓ | ∃ m₁ : GA E r, ∀ m₂, ℓ.1 m₂ = F.1 (lev (Ad E) r s (m₁, m₂) * yp k g)}

def LS {r s : ℕ} (U : Submodule ℂ (Sm E (r + s))) (T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)) : Submodule ℂ (Sm E r) :=
  Submodule.span ℂ {ℓ | ∃ ψ ∈ U, ∃ k g, ℓ ∈ lsF r s (T ψ) k g}

def RS {r s : ℕ} (U : Submodule ℂ (Sm E (r + s))) (T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)) : Submodule ℂ (Sm E s) :=
  Submodule.span ℂ {ℓ | ∃ ψ ∈ U, ∃ k g, ℓ ∈ rsF r s (T ψ) k g}

theorem lsF_sub_LS {r s : ℕ} {U : Submodule ℂ (Sm E (r + s))} {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)} {ψ : Sm E (r + s)}
    (hψ : ψ ∈ U) (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) : lsF r s (T ψ) k g ⊆ LS U T :=
  fun _ h => Submodule.subset_span ⟨ψ, hψ, k, g, h⟩

theorem rsF_sub_RS {r s : ℕ} {U : Submodule ℂ (Sm E (r + s))} {T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)} {ψ : Sm E (r + s)}
    (hψ : ψ ∈ U) (k : Kinf E (r + s)) (g : GL (Fin (r + s)) (Af E)) : rsF r s (T ψ) k g ⊆ RS U T :=
  fun _ h => Submodule.subset_span ⟨ψ, hψ, k, g, h⟩

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockDerivatives

end
end

