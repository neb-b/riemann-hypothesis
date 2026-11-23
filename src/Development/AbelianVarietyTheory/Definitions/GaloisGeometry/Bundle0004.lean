module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NegOnePowBoundaryTermsCancel
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FirstChernClassMemHodgeFiltration
section
set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace GlobalTheory.LogCris.CupModel

variable {b : Base} {L : b.Fun}

theorem isNilpotent_of_mem (T : Thick L) {x : T.B} (hx : x ∈ T.J) : IsNilpotent x := by
  by_cases hp : b.p = 0
  · obtain ⟨n, hn⟩ := T.adm.2 hp
    refine ⟨n, ?_⟩
    have := Ideal.pow_mem_pow hx n
    rw [hn] at this
    simpa using this
  · obtain ⟨n, hn⟩ := T.adm.1 hp
    refine ⟨b.p ^ n, ?_⟩
    rw [← T.δ.factorial_mul_dpow_eq_pow hx]
    obtain ⟨c, hc⟩ : b.p ^ n ∣ (b.p ^ n).factorial := Nat.dvd_factorial (Nat.pos_of_ne_zero (pow_ne_zero _ hp)) le_rfl
    rw [hc, Nat.cast_mul, Nat.cast_pow, hn, zero_mul, zero_mul]



end GlobalTheory.LogCris.CupModel

namespace GlobalTheory.CatH

end GlobalTheory.CatH
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsParahoricVec
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel
open scoped TensorProduct

namespace GlobalTheory.ThetaGL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {r n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def ThetaPair (μ : kˣ →* ℂˣ) (σ : Representation ℂ (GL (Fin r) k) V) (π : Representation ℂ (GL (Fin n) k) W) :
    Prop :=
  ∃ B : SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] W →ₗ[ℂ] V, B ≠ 0 ∧
    ∀ (g : GL (Fin r) k) (h : GL (Fin n) k) (Φ Φ' : SB (Matrix (Fin n) (Fin r) k)),
      (Φ' : Matrix (Fin n) (Fin r) k → ℂ) = om μ g h Φ → ∀ F : W, B Φ' (π h F) = σ g (B Φ F)

def OmQuot (μ : kˣ →* ℂˣ) (σ : Representation ℂ (GL (Fin r) k) V) (τ : Representation ℂ (GL (Fin n) k) W) :
    Prop :=
  ∃ f : SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] V ⊗[ℂ] W, f ≠ 0 ∧
    ∀ (g : GL (Fin r) k) (h : GL (Fin n) k) (Φ Φ' : SB (Matrix (Fin n) (Fin r) k)),
      (Φ' : Matrix (Fin n) (Fin r) k → ℂ) = om μ g h Φ → f Φ' = TensorProduct.map (σ g) (τ h) (f Φ)

def IsParahoricVec {t : ℕ} (χ : kˣ →* ℂˣ) (π : Representation ℂ (GL (Fin (r + t)) k) W) (v : W) : Prop :=
  ∀ h ∈ KO k (Fin (r + t)),
    (∀ (i : Fin t) (j : Fin r), valuation k (h.val (Fin.natAdd r i) (Fin.castAdd t j)) < 1) →
    ∀ u : kˣ, (u : k) = (h.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det → π h v = (χ u : ℂ) • v

end GlobalTheory.ThetaGL
end
end

