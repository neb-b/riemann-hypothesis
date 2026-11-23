module

public import Mathlib

@[expose] public section

-- bundled from ReciprocityTheory.ThetaSummability.RealCoinvariants.CoinvSubLeComap
section
noncomputable section

namespace ReciprocityTheory.ThetaSummability.Real

variable {M : Type*} [AddCommGroup M] [Module ℂ M] {ι : Type*}

def coinvSub (Y : ι → Module.End ℂ M) (μ : ι → ℂ) : Submodule ℂ M :=
  ⨆ i, LinearMap.range (Y i - μ i • 1)

def jointEig (Y : ι → Module.End ℂ M) (μ : ι → ℂ) : Submodule ℂ M :=
  ⨅ i, LinearMap.ker (Y i - μ i • 1)

abbrev Coinv (Y : ι → Module.End ℂ M) (μ : ι → ℂ) := M ⧸ coinvSub Y μ

theorem coinvSub_le_comap {Y : ι → Module.End ℂ M} (μ : ι → ℂ) {T : Module.End ℂ M}
    (hT : ∀ i, Commute T (Y i)) : coinvSub Y μ ≤ (coinvSub Y μ).comap T := by
  unfold coinvSub
  apply iSup_le
  intro i
  rintro x ⟨y, rfl⟩
  rw [Submodule.mem_comap]
  apply Submodule.mem_iSup_of_mem i
  refine ⟨T y, ?_⟩
  have hc : T (Y i y) = Y i (T y) := by
    rw [← Module.End.mul_apply, (hT i).eq, Module.End.mul_apply]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul, hc]

def coinvOp {Y : ι → Module.End ℂ M} (μ : ι → ℂ) (T : Module.End ℂ M)
    (hT : ∀ i, Commute T (Y i)) : Module.End ℂ (Coinv Y μ) :=
  (coinvSub Y μ).mapQ (coinvSub Y μ) T (coinvSub_le_comap μ hT)

end ReciprocityTheory.ThetaSummability.Real
end
end

-- bundled from ReciprocityTheory.ThetaSummability.RealCoinvariants.Numbers
section
noncomputable section

namespace ReciprocityTheory.ThetaSummability.Real

structure RealData where
  a : ℕ
  a' : ℕ
  p : ℕ
  q : ℕ
  κ : ℕ

structure RealData.Hyp (D : RealData) : Prop where
  a_gt : D.a' < D.a
  a'_pos : 1 ≤ D.a'
  even_im_hermitian_sub : (D.a - D.a') % 2 = 0
  h1a : 2 * D.p + 1 ≤ D.a
  h1b : 2 * D.q + 1 ≤ D.a'
  h2 : D.a + D.a' < D.κ
  h3 : D.κ % 2 = 0
  h5 : 2 * (D.p + D.q) < D.a'
  h4 : 2 * D.p + D.a' < D.a

namespace RealData

variable (D : RealData)

def d : ℕ := D.a + D.a'
def y : ℕ := D.p + D.q
def R : ℕ := D.d - D.y
def S : ℕ := D.y
def P : ℕ := D.a - D.p
def Q : ℕ := D.p
def P' : ℕ := D.q
def Q' : ℕ := D.a' - D.q

end RealData

end ReciprocityTheory.ThetaSummability.Real
end
end

