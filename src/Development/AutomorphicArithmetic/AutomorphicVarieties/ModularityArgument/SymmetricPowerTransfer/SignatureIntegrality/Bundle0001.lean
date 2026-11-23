module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.UnitaryDoubleCosetIndicator

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.LevelTorusLeTorus
section
noncomputable section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

namespace UpperTheory.V.Z.Sym.Sig

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem val_ord (x : kˣ) : valuation k (x : k) = uniformizer k ^ ord k x := by
  have h := GlAx.val_div_ord x
  rw [Units.val_div_eq_div_val, map_div₀, GlAx.val_zpow] at h
  exact (div_eq_one_iff_eq (zpow_pos GlAx.unif_pos _).ne').1 h

theorem mem_Uc {c : ℕ} {u : kˣ} : u ∈ Uc k c ↔ valuation k (u : k) = 1 ∧ valuation k ((u : k) - 1) ≤ uniformizer k ^ (c : ℤ) := by
  constructor
  · intro h
    refine ⟨Uc_le_Uo k c h, ?_⟩
    obtain ⟨v, hv, rfl⟩ := h
    have h1 : Ideal.Quotient.mk _ (v : 𝒪[k]) = 1 := congrArg Units.val hv
    rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq, GlAx.mem_pow] at h1
    exact h1
  · rintro ⟨h1, h2⟩
    obtain ⟨v, hv⟩ := (Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.integer.integers (valuation k))
      (x := (⟨u, h1.le⟩ : 𝒪[k]))).2 h1
    refine ⟨v, Units.ext ?_, Units.ext (congrArg Subtype.val hv)⟩
    change Ideal.Quotient.mk _ (v : 𝒪[k]) = Ideal.Quotient.mk _ 1
    rw [Ideal.Quotient.eq, GlAx.mem_pow, hv]
    exact h2

theorem mem_Kc_of {c : ℕ} {g : GL (Fin n) k} (h : g ∈ KO k (Fin n)) (h' : GlAx.Bd c g) : g ∈ Kc k n c := by
  obtain ⟨y, rfl⟩ := h
  exact ⟨y, (GlAx.map_eq_one c y).2 h', rfl⟩

theorem Kc_conj {c : ℕ} {g x : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) (hx : x ∈ Kc k n c) : g * x * g⁻¹ ∈ Kc k n c := by
  obtain ⟨y, rfl⟩ := hg
  obtain ⟨z, hz, rfl⟩ := hx
  exact ⟨y * z * y⁻¹, (MonoidHom.normal_ker _).conj_mem z hz y, by simp⟩

theorem dg_mem_KO {s : Fin n → kˣ} (h : ∀ i, s i ∈ Uo k) : dg s ∈ KO k (Fin n) := by
  have H : ∀ s : Fin n → kˣ, (∀ i, s i ∈ Uo k) → GlAx.Bd 0 (dg s) := fun s h => GlAx.bd_zero.2 fun i j => by
    rw [dg, val_diagT, diagonal_apply]
    split_ifs
    exacts [(show valuation k (s i : k) = 1 from h i).le, zero_mem _]
  exact GlAx.mem_KO.2 ⟨H s h, by rw [dg, ← map_inv]; exact H _ fun i => inv_mem (h i)⟩

theorem dg_mem_Kc {c : ℕ} {s : Fin n → kˣ} : dg s ∈ Kc k n c ↔ ∀ i, s i ∈ Uc k c := by
  constructor
  · intro h i
    have a := (GlAx.mem_Kc.1 h).1 i i
    have b := GlAx.bd_zero.1 (GlAx.mem_KO.1 (GlAx.Kc_le c h)).1 i i
    have b' := GlAx.bd_zero.1 (GlAx.mem_KO.1 (GlAx.Kc_le c h)).2 i i
    rw [dg, ← map_inv] at b'
    simp only [dg, Matrix.sub_apply, val_diagT, diagonal_apply_eq, one_apply_eq] at a b b'
    refine mem_Uc.2 ⟨le_antisymm b ?_, a⟩
    have b2 : valuation k ((s i : k)⁻¹) ≤ 1 := by rw [← Units.val_inv_eq_inv_val]; exact b'
    rw [map_inv₀] at b2
    exact (inv_le_one₀ (zero_lt_iff.2 (by simp))).1 b2
  · intro h
    refine mem_Kc_of (dg_mem_KO fun i => Uc_le_Uo k c (h i)) fun i j => ?_
    rw [dg, Matrix.sub_apply, val_diagT, diagonal_apply, Matrix.one_apply]
    split_ifs
    exacts [(mem_Uc.1 (h i)).2, by simp]

namespace Lev

variable (V : Lev k)

theorem levelTorus_le_torus : V.TH n ≤ (glIwa k n).T := by
  rintro _ ⟨s, hs, rfl⟩
  exact ⟨s, fun i => V.H_le (hs i trivial), rfl⟩

theorem Tc_le_TH : (glIwa k n).Tc V.c ≤ V.TH n := by
  rintro _ ⟨⟨s, -, rfl⟩, h⟩
  exact ⟨s, fun i _ => V.le (dg_mem_Kc.1 h i), rfl⟩

theorem N_le : (glIwa k n).N ≤ V.J n := le_sup_left.trans le_sup_left

theorem TH_le : V.TH n ≤ V.J n := le_sup_right.trans le_sup_left

theorem Nm_le : (glIwa k n).Nm V.c ≤ V.J n := le_sup_right

theorem dg_mem {s : Fin n → kˣ} (h : ∀ i, s i ∈ V.H) : dg s ∈ V.J n := V.TH_le ⟨s, fun i _ => h i, rfl⟩

theorem J_le_KO : V.J n ≤ KO k (Fin n) := by
  refine sup_le (sup_le (fun _ h => h.2) ?_) fun _ h => GlAx.Kc_le _ h.2
  rintro _ ⟨s, hs, rfl⟩
  exact dg_mem_KO fun i => V.H_le (hs i trivial)

end Lev

end UpperTheory.V.Z.Sym.Sig

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.UnitaryHyperbolicOrbitCount
section
noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

namespace UpperTheory.V.Z.Sym.Sig

open Classical

def MemJ : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (V : Lev k) (n : ℕ) (g : GL (Fin n) k), g ∈ V.J n ↔
    (∀ i j, valuation k (g i j) ≤ 1) ∧ (∀ i j, j < i → valuation k (g i j) ≤ valuation k (unif k : k) ^ (V.c + 1)) ∧
      ∀ i, ∃ u ∈ V.H, (u : k) = g i i

def FactJ : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (V : Lev k) (n : ℕ), (∀ g ∈ V.J n, ∃ a ∈ (glIwa k n).N, ∃ s ∈ V.TH n, ∃ b ∈ (glIwa k n).Nm V.c, g = a * s * b) ∧
    ∀ (m : ℕ), ∀ a ∈ (glIwa k n).N, ∀ a' ∈ (glIwa k n).N, ∀ s ∈ V.TH n, ∀ s' ∈ V.TH n, ∀ b ∈ (glIwa k n).Nm V.c,
      ∀ b' ∈ (glIwa k n).Nm V.c, (a * s * b)⁻¹ * (a' * s' * b') ∈ Kc k n m → a⁻¹ * a' ∈ Kc k n m

def Shrink : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (d : Fin n → kˣ), SDom d → ∀ m : ℕ,
    (∀ a ∈ (glIwa k n).N, a ∈ Kc k n m → dg d * a * (dg d)⁻¹ ∈ (glIwa k n).N ⊓ Kc k n (m + 1)) ∧
      ∀ c, ∀ b ∈ (glIwa k n).Nm c, b ∈ Kc k n m → (dg d)⁻¹ * b * dg d ∈ (glIwa k n).Nm c ⊓ Kc k n (m + 1)

def FixPt : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (P : Subgroup (GL (Fin n) k)),
    (P = (glIwa k n).N ∨ ∃ c, P = (glIwa k n).Nm c) → ∀ Ψ : P → P,
    (∀ (m : ℕ) (a b : P), (a : GL (Fin n) k)⁻¹ * b ∈ Kc k n m → (Ψ a : GL (Fin n) k)⁻¹ * Ψ b ∈ Kc k n (m + 1)) → ∃ a, Ψ a = a

def Contract : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (V : Lev k) (n : ℕ) (σ : GL (Fin n) k →* GL (Fin n) k), Pres V σ → ∀ d : Fin n → kˣ, SDom d →
    ∀ g ∈ V.DC d, ∃ j ∈ V.J n, ∃ s ∈ V.TH n, j⁻¹ * g * σ j = s * dg d

def DiagDC : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (V : Lev k) (n : ℕ) (d s : Fin n → kˣ), Dom d → (dg s ∈ V.DC d ↔ ∀ i, s i / d i ∈ V.H)

def ThFacts : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (V : Lev k), Pres V (th' k) ∧ (∀ g ∈ V.J 3, th' k g ∈ V.J 3) ∧ (∀ x y z : kˣ, th' k (dg ![x, y, z]) = dg ![z⁻¹, y⁻¹, x⁻¹]) ∧
    (∀ (n : ℕ) (g : GL (Fin n) k), th k n (th k n g) = g) ∧ th k 3 (Phi k) = (Phi k)⁻¹ ∧ (Phi k)⁻¹ = Phi k ∧
    ∀ g, th' k g * Phi k = Phi k * th k 3 g

def ConjDiag : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (s s' : Fin n → kˣ), SDom s → SDom s' →
    ∀ y : GL (Fin n) k, y⁻¹ * dg s * y = dg s' → s = s' ∧ ∃ u, y = dg u

def FinFacts : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (V : Lev k), V.H.relIndex (Uo k) ≠ 0 ∧ V.H2 ≤ Uo k ∧ V.H ≤ V.H2 ∧ (∃ R, V.IsSigns R) ∧ (∃ R, V.IsSqReps R) ∧
    ∀ n : ℕ, HeckePair (V.J n) ∧ IsOpen (V.J n : Set (GL (Fin n) k)) ∧ IsCompact (V.J n : Set (GL (Fin n) k)) ∧ V.J n ≤ KO k (Fin n)

def Link : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ),
    (Lev.iw k).J n = iwC k n ⊤ ∧ (Lev.iw k).J n = (glIwa k n).Iw 0 ∧ ∀ c, (Lev.deep k c).J n = (glIwa k n).I1 c

def HkMul : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (V : Lev k) (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ (GL (Fin n) k) M),
    (∀ d d' : Fin n → kˣ, Dom d → Dom d' → hk ρ (V.J n) (dg d) * hk ρ (V.J n) (dg d') = hk ρ (V.J n) (dg (d * d'))) ∧
    ∀ d : Fin n → kˣ, Dom d → ∀ v : fixd ρ (V.J n), (hk ρ (V.J n) (dg d) v : M) = (glIwa k n).uOp ρ (dg d) v

def DCMul : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (V : Lev k) (n : ℕ) (d d' : Fin n → kˣ), Dom d → Dom d' → ∀ g : GL (Fin n) k,
    (g ∈ V.DC (d * d') → ∃! y : GL (Fin n) k ⧸ V.J n, y.out ∈ V.DC d ∧ y.out⁻¹ * g ∈ V.DC d') ∧
      ∀ y ∈ V.DC d, y⁻¹ * g ∈ V.DC d' → g ∈ V.DC (d * d')

def EqG : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (V : Lev k) (ω : kˣ →* ℂˣ) (Rs Ry : Finset kˣ) (x z : kˣ) (d : Fin 3 → kˣ),
    (∀ u ∈ V.J 3, ∀ u' ∈ V.J 3, ∀ g, V.unitaryDoubleCosetIndicator d (u * g * th k 3 u') = V.unitaryDoubleCosetIndicator d g ∧
      V.fG ω Rs Ry x z (u * g * th k 3 u') = V.fG ω Rs Ry x z g) ∧
    {y : GL (Fin 3) k ⧸ (V.J 3).map (th k 3) | V.unitaryDoubleCosetIndicator d y.out ≠ 0}.Finite ∧
    {y : GL (Fin 3) k ⧸ (V.J 3).map (th k 3) | V.fG ω Rs Ry x z y.out ≠ 0}.Finite

def EqZ : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (V : Lev k) (ω : kˣ →* ℂˣ), (∀ u ∈ V.H, ω u = 1) → ∀ (n : ℕ), 0 < n →
    (∃ Ω : V.ZJ n →* ℂˣ, ∀ (z : kˣ) (j : GL (Fin n) k) (u : V.ZJ n), j ∈ V.J n →
      (u : GL (Fin n) k) = GeneralLinearGroup.scalar (Fin n) z * j → Ω u = ω z) ∧
    (∀ u, u ∈ V.ZJ n ↔ ∃ z : kˣ, ∃ j ∈ V.J n, u = GeneralLinearGroup.scalar (Fin n) z * j) ∧
    ∀ d : Fin n → kˣ, SDom d →
      (∀ (z : kˣ), ∀ g ∈ V.DC d, V.fZ ω d (GeneralLinearGroup.scalar (Fin n) z * g) = (((ω z)⁻¹ : ℂˣ) : ℂ)) ∧
      (∀ (z : kˣ) g, V.fZ ω d (GeneralLinearGroup.scalar (Fin n) z * g) = (((ω z)⁻¹ : ℂˣ) : ℂ) * V.fZ ω d g) ∧
      (∀ u ∈ V.J n, ∀ u' ∈ V.J n, ∀ g, V.fZ ω d (u * g * u') = V.fZ ω d g) ∧
      {y : GL (Fin n) k ⧸ V.ZJ n | V.fZ ω d y.out ≠ 0}.Finite

def SuppZ : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (V : Lev k) (ω : kˣ →* ℂˣ) (d : Fin 2 → kˣ), SDom d → ∀ g, V.fZ ω d g ≠ 0 →
    ∃ (g₀ : GL (Fin 2) k) (a b : kˣ), g = g₀ * dg ![a, b] * g₀⁻¹ ∧ a / b / (d 0 / d 1) ∈ V.H

def NormalG : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    (∀ (g₀ : GL (Fin 3) k) (x y z : kˣ), (g₀ * dg ![x, y, z] * Phi k * (th k 3 g₀)⁻¹) * th k 3 (g₀ * dg ![x, y, z] * Phi k * (th k 3 g₀)⁻¹) =
      g₀ * dg ![x / z, 1, z / x] * g₀⁻¹) ∧
    ∀ (δ : GL (Fin 3) k) (a : kˣ), valuation k (a : k) < 1 →
      ((δ * th k 3 δ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k).charpoly = (X - C 1) * (X - C (a : k)) * (X - C ((a⁻¹ : kˣ) : k)) →
      ∃ (g₀ : GL (Fin 3) k) (x y z : kˣ), δ = g₀ * dg ![x, y, z] * Phi k * (th k 3 g₀)⁻¹ ∧ x / z = a

def NormalD : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (γ : GL (Fin 2) k) (a b : kˣ), a ≠ b →
    (γ : Matrix (Fin 2) (Fin 2) k).charpoly = (X - C (a : k)) * (X - C (b : k)) → ∃ g₀ : GL (Fin 2) k, γ = g₀ * dg ![a, b] * g₀⁻¹

def FixG : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (V : Lev k) (d : Fin 3 → kˣ), SDom d → ∀ x₁ y₁ z₁ : kˣ, valuation k ((x₁ / z₁ : kˣ) : k) < 1 → ∀ y : GL (Fin 3) k,
    (y⁻¹ * (dg ![x₁, y₁, z₁] * Phi k) * th k 3 y * (Phi k)⁻¹ ∈ V.DC d ↔ ∃ u : Fin 3 → kˣ, ∃ j ∈ V.J 3, y = dg u * j ∧
      x₁ / (u 0 * u 2) / d 0 ∈ V.H ∧ y₁ / u 1 ^ 2 / d 1 ∈ V.H ∧ z₁ / (u 0 * u 2) / d 2 ∈ V.H)

def UnitaryHyperbolicOrbitCount : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (V : Lev k) (T : Type) [Group T] (r : T →* kˣ), Function.Surjective r → ∀ (g₀ : GL (Fin 3) k) (ι : T →* GL (Fin 3) k),
    (∀ s, ι s = g₀ * dg ![r s, 1, (r s)⁻¹] * g₀⁻¹) → ∀ d : Fin 3 → kˣ, SDom d → ∀ x₁ y₁ z₁ : kˣ, valuation k ((x₁ / z₁ : kˣ) : k) < 1 →
    (letI : MulAction T (GL (Fin 3) k ⧸ V.J 3) := MulAction.compHom _ ι
     {o : MulAction.orbitRel.Quotient T (GL (Fin 3) k ⧸ V.J 3) |
       V.unitaryDoubleCosetIndicator d (o.out.out⁻¹ * (g₀ * dg ![x₁, y₁, z₁] * Phi k * (th k 3 g₀)⁻¹) * th k 3 o.out.out) ≠ 0}.Finite) ∧
    orb ι ((Uo k).comap r) (th k 3) (V.J 3) (V.unitaryDoubleCosetIndicator d) (g₀ * dg ![x₁, y₁, z₁] * Phi k * (th k 3 g₀)⁻¹) =
      if x₁ / z₁ / (d 0 / d 2) ∈ V.H ∧ ∃ s : kˣ, y₁ / (d 1 * s ^ 2) ∈ V.H then (V.H.relIndex (Uo k) : ℂ) * (V.H.relIndex V.H2 : ℂ) else 0

def OrbZ : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (V : Lev k) (ω : kˣ →* ℂˣ), (∀ u ∈ V.H, ω u = 1) → ∀ d : Fin 2 → kˣ, SDom d →
    ∀ (T : Type) [Group T] (p q : T →* kˣ), Function.Surjective (p / q) → ∀ (g₀ : GL (Fin 2) k) (ι : T →* GL (Fin 2) k),
    (∀ s, ι s = g₀ * dg ![p s, q s] * g₀⁻¹) → ∀ a b : kˣ, valuation k (a : k) < valuation k (b : k) →
    (letI : MulAction T (GL (Fin 2) k ⧸ V.ZJ 2) := MulAction.compHom _ ι
     {o : MulAction.orbitRel.Quotient T (GL (Fin 2) k ⧸ V.ZJ 2) | V.fZ ω d (o.out.out⁻¹ * (g₀ * dg ![a, b] * g₀⁻¹) * o.out.out) ≠ 0}.Finite) ∧
    orb ι ((Uo k).comap (p / q)) (MonoidHom.id _) (V.ZJ 2) (V.fZ ω d) (g₀ * dg ![a, b] * g₀⁻¹) =
      if a / b / (d 0 / d 1) ∈ V.H then (V.H.relIndex (Uo k) : ℂ) * (ω (d 1 / b) : ℂ) else 0

end UpperTheory.V.Z.Sym.Sig

end
end

