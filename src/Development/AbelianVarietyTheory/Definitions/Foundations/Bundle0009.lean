module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.PsType

section Abstract

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

def IsEig (π : Representation ℂ G V) (H : Set G) (θ : G → ℂ) (v : V) : Prop := ∀ h ∈ H, π h v = θ h • v

def aug (π : Representation ℂ G V) (H : Set G) (θ : G → ℂ) : Submodule ℂ V :=
  Submodule.span ℂ {x | ∃ h ∈ H, ∃ w : V, x = π h w - θ h • w}

structure Datum [TopologicalSpace G] (H : Set G) (θ : G → ℂ) : Prop where
  one : (1 : G) ∈ H
  mul : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H
  inv : ∀ a ∈ H, a⁻¹ ∈ H
  compact : IsCompact H
  val_one : θ 1 = 1
  val_mul : ∀ a ∈ H, ∀ b ∈ H, θ (a * b) = θ a * θ b
  near : ∃ U ∈ nhds (1 : G), ∀ g ∈ U, g ∈ H → θ g = 1

end Abstract

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def Triv (χ : kˣ →* ℂˣ) (x : k) : Prop :=
  ∀ u : kˣ, valuation k (u : k) = 1 → valuation k ((u : k) - 1) ≤ valuation k x → χ u = 1

def Ordered (ψ : Fin n → kˣ →* ℂˣ) : Prop :=
  ∀ i a b j : Fin n, i ≤ a → a ≤ b → b ≤ j → ∀ x : k, Triv (ψ i / ψ j) x → Triv (ψ a / ψ b) x

def grp (ψ : Fin n → kˣ →* ℂˣ) : Set (GL (Fin n) k) :=
  {g | g ∈ KO k (Fin n) ∧ ∀ i j : Fin n, i < j → Triv (ψ i / ψ j) (g.val i j)}


open Classical in
def ev (χ : kˣ →* ℂˣ) (x : k) : ℂ :=
  if h : valuation k x = 1 then (χ (Units.mk0 x fun h0 => by simp [h0] at h) : ℂ) else 1

def nxt (ψ : Fin n → kˣ →* ℂˣ) (m : Fin n) : kˣ →* ℂˣ :=
  if h : (m : ℕ) + 1 < n then ψ ⟨(m : ℕ) + 1, h⟩ else 1

def minor (g : GL (Fin n) k) (m : Fin n) : k := (g.val.toSquareBlockProp fun i => i ≤ m).det

def theta (ψ : Fin n → kˣ →* ℂˣ) (g : GL (Fin n) k) : ℂ := ∏ m, ev (ψ m / nxt ψ m) (minor g m)

def HasVec {V : Type} [AddCommGroup V] [Module ℂ V] (ψ : Fin n → kˣ →* ℂˣ) (π : Representation ℂ (GL (Fin n) k) V) : Prop :=
  ∃ v : V, v ≠ 0 ∧ IsEig π (grp ψ) (theta ψ) v

def Agree (ψ ω : Fin n → kˣ →* ℂˣ) : Prop := ∀ i (u : kˣ), valuation k (u : k) = 1 → ψ i u = ω i u

def strip (ψ : Fin n → kˣ →* ℂˣ) (r : ℕ) (ϖ : k) (m : ℕ) : Set (GL (Fin n) k) :=
  {g | ∀ i j : Fin n, if (i : ℕ) < r ∧ r ≤ (j : ℕ) then
      valuation k (ϖ ^ m * g.val i j) ≤ 1 ∧ Triv (ψ i / ψ j) (ϖ ^ m * g.val i j)
    else g.val i j = (1 : Matrix (Fin n) (Fin n) k) i j}

def Cut (ψ : Fin n → kˣ →* ℂˣ) (r : ℕ) : Prop := ∀ i j : Fin n, (i : ℕ) < r → r ≤ (j : ℕ) → ¬ Triv (ψ i / ψ j) 1

end GlobalTheory.PsType
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.SiegelNeZeroIff
section
noncomputable section

open scoped UpperHalfPlane MatrixGroups

namespace GlobalTheory.KZ.SiegelModel

open GlobalTheory.Sieg GlobalTheory.Sieg.Model

theorem isOpen_Hs : IsOpen Hs :=
  isOpen_lt continuous_const Complex.continuous_im

theorem neBot_Hs : (Filter.codiscreteWithin Hs).NeBot := by
  have hI : Complex.I ∈ Hs := by simp [Hs]
  have hloc : nhdsWithin Complex.I (Hs \ {Complex.I}) = nhdsWithin Complex.I {Complex.I}ᶜ := by
    rw [Set.sdiff_eq]
    exact nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds (isOpen_Hs.mem_nhds hI))
  have hne : (nhdsWithin Complex.I (Hs \ {Complex.I})).NeBot := by
    rw [hloc]
    infer_instance
  refine hne.mono ?_
  unfold Filter.codiscreteWithin
  exact le_iSup₂ (f := fun x (_ : x ∈ Hs) => nhdsWithin x (Hs \ {x})) Complex.I hI

theorem germ_eq_of_eqOn {φ ψ : ℂ → ℂ} (h : ∀ z ∈ Hs, φ z = ψ z) : (φ : Mero) = (ψ : Mero) :=
  Filter.Germ.coe_eq.2 (Filter.mem_of_superset (Filter.self_mem_codiscreteWithin Hs) fun z hz => h z hz)

theorem sgC_coe (c : ℕ) (x : Fin 2 → ℚ) (τ : ℍ) : sgC c x τ = sg c x τ := by
  unfold sgC
  rw [UpperHalfPlane.ofComplex_apply]

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (T : Tower Ω ε)

theorem an_injective : Function.Injective T.an := by
  have := neBot_Hs
  exact T.an.injective

theorem siegel_eq {c : ℕ} {x : Fin 2 → ℚ} {f : T.K} (hf : T.an f = ((sgC c x : ℂ → ℂ) : Mero)) :
    siegel T c x = f := by
  have hex : ∃ f : T.K, T.an f = ((sgC c x : ℂ → ℂ) : Mero) := ⟨f, hf⟩
  unfold siegel
  rw [dite_eq_left hex]
  exact an_injective T (hex.choose_spec.trans hf.symm)

theorem mob_ofSL (γ : SL(2, ℤ)) (τ : ℍ) : mob (ofSL γ) τ = ((γ • τ : ℍ) : ℂ) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [mob, ent, ofSL]

theorem an_siegel {c : ℕ} {x : Fin 2 → ℚ} (M : ℕ) (hM : 0 < M) (hd : DifferentiableOn ℂ (sgC c x) Hs)
    (hmod : ∀ (γ : SL(2, ℤ)) (τ : ℍ), sg c x (γ • τ) = sg c (act x γ) τ)
    (hlev : ∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, sg c (act x γ) τ = sg c x τ)
    (hexp : ∀ γ : SL(2, ℤ), ∃ (a : ℤ → Ω) (n0 : ℤ), (∀ n < n0, a n = 0) ∧ ∀ τ : ℍ,
      HasSum (fun n : ℤ => ε (a n) * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * τ / M)) (sg c (act x γ) τ)) :
    T.an (siegel T c x) = ((sgC c x : ℂ → ℂ) : Mero) := by

  have hγz : ∀ (γ : SL(2, ℤ)) (z : ℂ) (hz : z ∈ Hs), sgC c x (mob (ofSL γ) z) = sg c (act x γ) ⟨z, hz⟩ := by
    intro γ z hz
    rw [mob_ofSL γ ⟨z, hz⟩, sgC_coe, hmod]
  have hlev' : ∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ z ∈ Hs, sgC c x (mob (ofSL γ) z) = sgC c x z := by
    intro γ hγ z hz
    rw [hγz γ z hz, hlev γ hγ, ← sgC_coe]
  have hexp' : ∀ γ : SL(2, ℤ), ∃ (a : ℤ → Ω) (n0 : ℤ), (∀ n < n0, a n = 0) ∧ ∀ z ∈ Hs,
      HasSum (fun n : ℤ => ε (a n) * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * z / M))
        (sgC c x (mob (ofSL γ) z)) := by
    intro γ
    obtain ⟨a, n0, ha, hs⟩ := hexp γ
    refine ⟨a, n0, ha, fun z hz => ?_⟩
    rw [hγz γ z hz]
    exact hs ⟨z, hz⟩
  obtain ⟨f, hf⟩ := T.mem_q (sgC c x) M hM hd hlev' hexp'
  rw [siegel_eq T hf]
  exact hf

end GlobalTheory.KZ.SiegelModel
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Foundations.SumMulCoPtSbEqSumInv
section
noncomputable section

namespace GlobalTheory.LambdaValuationPowers

variable {K : Type*} [Field K] [CharZero K]

def coPtSb (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) (c d a b : ℤ) (s : ℕ) : K :=
  (c : K) ^ 2 * (d : K) ^ 2 * GlobalTheory.KummerEisensteinGalois.coPtMu N p m k ψ a b s
    - (c : K) ^ ((3 : ℤ) - k) * ψ⁻¹ (c : ZMod (p ^ m)) * (d : K) ^ 2 * GlobalTheory.KummerEisensteinGalois.coPtMu N p m k ψ (c * a) b s
    - (c : K) ^ 2 * (d : K) * ψ⁻¹ (d : ZMod (p ^ m)) * GlobalTheory.KummerEisensteinGalois.coPtMu N p m k ψ a (d * b) s
    + (c : K) ^ ((3 : ℤ) - k) * ψ⁻¹ (c : ZMod (p ^ m)) * (d : K) * ψ⁻¹ (d : ZMod (p ^ m)) *
        GlobalTheory.KummerEisensteinGalois.coPtMu N p m k ψ (c * a) (d * b) s

theorem coPtSb_one (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) (c d x : ℤ) (s : ℕ) :
    coPtSb N p m k ψ c d x 1 s = GlobalTheory.KummerEisensteinGalois.coPtS N p m k ψ c d x s := by
  simp [coPtSb, GlobalTheory.KummerEisensteinGalois.coPtS]

def chiAvg (N p m k : ℕ) [NeZero N] (ψ : DirichletCharacter K (p ^ m)) (χ : ℕ → K) (c d x : ℤ) (s : ℕ) : K :=
  ∑ δ : (ZMod N)ˣ, (χ (δ : ZMod N).val)⁻¹ * coPtSb N p m k ψ c d (x * ((δ : ZMod N).val : ℤ)) ((δ : ZMod N).val : ℤ) s


omit [CharZero K] in
theorem ffMu_congr (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) {a a' : ℤ} (h : a ≡ a' [ZMOD N]) :
    GlobalTheory.KummerEisensteinGalois.ffMu N p m k ψ a = GlobalTheory.KummerEisensteinGalois.ffMu N p m k ψ a' := by
  funext s
  have h' : ∀ z : ℤ, z ≡ a [ZMOD N] ↔ z ≡ a' [ZMOD N] := fun z => ⟨fun hz => hz.trans h, fun hz => hz.trans h.symm⟩
  simp only [GlobalTheory.KummerEisensteinGalois.ffMu, h']


omit [CharZero K] in
theorem eeMu_congr (N p m : ℕ) (ψ : DirichletCharacter K (p ^ m)) {b b' : ℤ} (h : b ≡ b' [ZMOD N]) :
    GlobalTheory.KummerEisensteinGalois.eeMu N p m ψ b = GlobalTheory.KummerEisensteinGalois.eeMu N p m ψ b' := by
  funext s
  have h' : ∀ z : ℤ, z ≡ b [ZMOD N] ↔ z ≡ b' [ZMOD N] := fun z => ⟨fun hz => hz.trans h, fun hz => hz.trans h.symm⟩
  simp only [GlobalTheory.KummerEisensteinGalois.eeMu, h']


omit [CharZero K] in
theorem coPtMu_congr (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) {a a' b b' : ℤ} (ha : a ≡ a' [ZMOD N])
    (hb : b ≡ b' [ZMOD N]) : GlobalTheory.KummerEisensteinGalois.coPtMu N p m k ψ a b = GlobalTheory.KummerEisensteinGalois.coPtMu N p m k ψ a' b' := by
  simp only [GlobalTheory.KummerEisensteinGalois.coPtMu, ffMu_congr N p m k ψ ha, eeMu_congr N p m ψ hb]


omit [CharZero K] in
theorem coPtSb_congr (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) (c d : ℤ) {a a' b b' : ℤ} (ha : a ≡ a' [ZMOD N])
    (hb : b ≡ b' [ZMOD N]) : coPtSb N p m k ψ c d a b = coPtSb N p m k ψ c d a' b' := by
  funext s
  simp only [coPtSb, coPtMu_congr N p m k ψ ha hb, coPtMu_congr N p m k ψ (ha.mul_left c) hb,
    coPtMu_congr N p m k ψ ha (hb.mul_left d), coPtMu_congr N p m k ψ (ha.mul_left c) (hb.mul_left d)]






end GlobalTheory.LambdaValuationPowers
end
end

