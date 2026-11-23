module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum
section
open MeasureTheory ValuativeRel Matrix
open scoped ENNReal

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

section Defs
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

def deltaR (c : ℕ) (g : GL n k) : ℝ := nabs k (Matrix.GeneralLinearGroup.det g) ^ ((c : ℤ) - 1)

def IsCosetFn (J : Subgroup (GL (n ⊕ Fin c) k)) (h : GL (n ⊕ Fin c) k) (f : GL (n ⊕ Fin c) k → ℂ) : Prop :=
  (∀ u ∈ N k n c 1, ∀ (g : GL n k) (x : GL (n ⊕ Fin c) k), f (u * embX c g * x) = (deltaR c g : ℂ) * f x) ∧
    (∀ x, ∀ j ∈ J, f (x * j) = f x) ∧
    ∀ x, DoubleCoset.mk (R k n c 1) J x ≠ DoubleCoset.mk (R k n c 1) J h → f x = 0

def IsCO {G : Type} [Group G] [TopologicalSpace G] (J : Subgroup G) : Prop :=
  IsOpen (J : Set G) ∧ IsCompact (J : Set G)

def IsUnif (ϖ : kˣ) : Prop := ∀ x : k, valuation k x < 1 ↔ valuation k x ≤ valuation k (ϖ : k)

variable [MeasurableSpace k] [BorelSpace k]

def volR (ν : Measure k) (m : Measure (GL n k)) (S : Subgroup (GL (n ⊕ Fin c) k)) : ℝ≥0∞ :=
  ∫⁻ g, volN ν n c 1 {u : N k n c 1 | embX c g * (u : GL (n ⊕ Fin c) k) ∈ S} ∂m

def rescale (ν : Measure k) (b : GL (n ⊕ Fin c) k) (m : Measure (GL n k)) : Measure (GL n k) :=
  (volN ν n c 1 ((stabLat b).subgroupOf (N k n c 1)))⁻¹ • m

end Defs

section Levels
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def Reduces {a : Type} [Fintype a] [DecidableEq a] (g : GL a k) (gb : GL a 𝓀[k]) : Prop :=
  ∃ g₀ : GL a 𝒪[k], Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) g₀ = g ∧
    Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k]) g₀ = gb

def IsUpperUnip {F a : Type} [Field F] [DecidableEq a] (pos : a → ℕ) (M : Matrix a a F) : Prop :=
  ∀ r s, pos s ≤ pos r → M r s = (1 : Matrix a a F) r s

def superSum {F a : Type} [Field F] [Fintype a] (pos : a → ℕ) (M : Matrix a a F) : F :=
  ∑ r, ∑ s, if pos s = pos r + 1 then M r s else 0

def framePos (κ l : ℕ) : Fin κ ⊕ Fin l → ℕ := Sum.elim (fun i => i.val) (fun i => κ + i.val)

def IsGenericLevel (ψ : AddChar k Circle) (ϖ : kˣ) {κ l : ℕ} (P : TypeDatum k (Fin κ ⊕ Fin l)) : Prop :=
  (∀ g, g ∈ P.J ↔ ∃ gb, Reduces g gb ∧ IsUpperUnip (framePos κ l) gb.val) ∧
    ∀ g : P.J, (P.lam g : ℂ) = ψ ((ϖ⁻¹ : kˣ) * superSum (framePos κ l) (g : GL (Fin κ ⊕ Fin l) k).val)

def IsSymLevel (ψ : AddChar k Circle) (ϖ : kˣ) (ρ : ℕ) {κ l : ℕ} (P : TypeDatum k (Fin κ ⊕ Fin l)) : Prop :=
  (∀ g, g ∈ P.J ↔ ∃ u ∈ N 𝓀[k] (Fin κ) l (ρ + 1), ∃ γ : GL (Fin κ) 𝓀[k],
      IsUpperUnip Fin.val γ.val ∧ Reduces g (u * embX l γ)) ∧
    ∀ g : P.J, (P.lam g : ℂ) = ψ ((ϖ⁻¹ : kˣ) * simpleSum (g : GL (Fin κ ⊕ Fin l) k)) *
      ψ ((ϖ⁻¹ : kˣ) * superSum Fin.val (g : GL (Fin κ ⊕ Fin l) k).val.toBlocks₁₁)

def colPos (κ : ℕ) (t : Type) : XIx (Fin κ) t 0 → ℕ :=
  Sum.elim (Sum.elim (fun i => i.val) (fun i => i.elim0)) (fun p => p.1.elim0)

variable (k) in
def colGroup (κ : ℕ) (t : Type) [Fintype t] [DecidableEq t] : Set (GL (XIx (Fin κ) t 0) k) :=
  {γ | ∃ gb, Reduces γ gb ∧ IsUpperUnip (colPos κ t) gb.val}

def colChar (ψ : AddChar k Circle) (ϖ : kˣ) {κ : ℕ} {t : Type} [Fintype t] [DecidableEq t]
    (γ : GL (XIx (Fin κ) t 0) k) : ℂ :=
  ψ ((ϖ⁻¹ : kˣ) * superSum (colPos κ t) γ.val)

end Levels

section Props
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k)

def StepWellDefined : Prop :=
  ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ), 1 ≤ c →
  ∀ (μ : kˣ →* ℂˣ) (P' : Level (GL (n' ⊕ Fin (c + 1)) k)) (P : Level (GL (n ⊕ Fin c) k))
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ), Φ ∈ SB _ → IsCO P'.J → IsCO P.J → HasTypes μ P' P Φ →
    (∀ h' h, flat ψ ν μ Φ h' h ∈ SB (Matrix n n' k)) ∧
    (∀ h', (idxAt ψ ν μ Φ P.J h').Finite) ∧
    (∀ u' ∈ N k n' (c + 1) 1, ∀ (g' : GL n' k) (j' : P'.J) h' h,
      flat ψ ν μ Φ (u' * embX (c + 1) g' * h' * (j' : GL (n' ⊕ Fin (c + 1)) k)) h =
        ((P'.lam j' : ℂ) * (ψ (simpleSum u') : ℂ) *
          ((nabs k (Matrix.GeneralLinearGroup.det g') ^ ((c : ℝ) / 2) : ℝ) : ℂ)) • om μ g' 1 (flat ψ ν μ Φ h' h)) ∧
    (∀ u ∈ N k n c 1, ∀ (g : GL n k) (j : P.J) h' h,
      flat ψ ν μ Φ h' (u * embX c g * h * (j : GL (n ⊕ Fin c) k)) =
        ((((P.lam j)⁻¹ : ℂˣ) : ℂ) * (ψ (-simpleSum u) : ℂ) *
          ((nabs k (Matrix.GeneralLinearGroup.det g) ^ (((c : ℝ) + 1) / 2 - 1) : ℝ) : ℂ)) •
            om μ 1 g (flat ψ ν μ Φ h' h)) ∧
    (∀ h₁' h₂' h₁ h₂, DoubleCoset.mk (R k n' (c + 1) 1) P'.J h₁' = DoubleCoset.mk (R k n' (c + 1) 1) P'.J h₂' →
      DoubleCoset.mk (R k n c 1) P.J h₁ = DoubleCoset.mk (R k n c 1) P.J h₂ →
      (flat ψ ν μ Φ h₁' h₁ ≠ 0 ↔ flat ψ ν μ Φ h₂' h₂ ≠ 0)) ∧
    (∀ h₁' h₂', DoubleCoset.mk (R k n' (c + 1) 1) P'.J h₁' = DoubleCoset.mk (R k n' (c + 1) 1) P'.J h₂' →
      idxAt ψ ν μ Φ P.J h₁' = idxAt ψ ν μ Φ P.J h₂') ∧
    ∀ b h' h, xi ψ ν μ Φ P.J b h' h ≠ 0 ↔ DoubleCoset.mk (R k n c 1) P.J h ∈ idxAt ψ ν μ Φ P.J h'

def ChainFinite : Prop :=
  ∀ (s : ℕ) (X : ℕ → Type) [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] (Z : Type) [Fintype Z] [DecidableEq Z]
    (T : Chain k s X Z), T.Regular → T.Laws →
    (∀ j c (h : j + 1 + c = s) g g', T.entry ψ ν j c h g g' ≠ 0 ↔
      DoubleCoset.mk (R k (X (j + 1)) (c + 1) 1) (T.lev (j + 1) (c + 1) (congrArg (· + 1) h)).J g' ∈ T.idx ψ ν j c h g) ∧
    ∀ A : RepFam k s X, T.IsRepSystem A ψ ν →
      (∀ j c h, (A j c h).Finite) ∧
      (∀ A' : RepFam k s X, T.IsRepSystem A' ψ ν → ∀ j c (h : j + c = s),
        DoubleCoset.mk (R k (X j) (c + 1) 1) (T.lev j (c + 1) (by omega)).J '' A j c h =
          DoubleCoset.mk (R k (X j) (c + 1) 1) (T.lev j (c + 1) (by omega)).J '' A' j c h) ∧
      (∀ ϖ : kˣ, IsUnif ϖ → ∃ e : ℕ, 1 ≤ e ∧ T.Adapted A (box _ (ϖ ^ e)⁻¹) (box _ (ϖ ^ e))) ∧
      ∀ c₁ c₂ : kˣ, (T.coupIdx A (box _ c₁) (box _ c₂)).Finite

def CosetMeasure : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n] (c : ℕ), 1 ≤ c →
  ∀ (J : Subgroup (GL (n ⊕ Fin c) k)), IsCO J → ∀ h : GL (n ⊕ Fin c) k,
    IsCO (prX (Cgrp J h)) ∧
    (∀ g ∈ prX (Cgrp J h), valuation k ((Matrix.GeneralLinearGroup.det g : kˣ) : k) = 1 ∧ deltaR c g = 1) ∧
    (∃ f, IsCosetFn J h f ∧ f h = 1) ∧
    ((resCard k).Prime → ∀ b, ∃ z : ℤ, volNat ν b (Cgrp J h) = (resCard k : ℝ) ^ z) ∧
    ∀ (m : Measure (GL n k)), m.IsHaarMeasure →
      volR ν m (Cgrp J h) = volN ν n c 1 ((Cgrp J h).subgroupOf (N k n c 1)) * m (prX (Cgrp J h)) ∧
      volR ν m (Cgrp J h) ≠ 0 ∧ volR ν m (Cgrp J h) ≠ ⊤ ∧
      (∀ b, (volR ν (rescale ν b m) (Cgrp J h)).toReal = volNat ν b (Cgrp J h) * (m (prX (Cgrp J h))).toReal) ∧
      ∀ (μG : Measure (GL (n ⊕ Fin c) k)), μG.IsHaarMeasure → ∀ f, IsCosetFn J h f → ∀ z : ℂ,
        IsQuotInt ν m μG 1 f z ↔ z = (((μG J).toReal / (volR ν m (Cgrp J h)).toReal : ℝ) : ℂ) * f h

def VolumeCancels : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n] (c : ℕ), 1 ≤ c →
  ∀ (J : Subgroup (GL (n ⊕ Fin c) k)), IsCO J → ∀ (b h : GL (n ⊕ Fin c) k)
    (m : Measure (GL n k)), m.IsHaarMeasure → ∀ (μG : Measure (GL (n ⊕ Fin c) k)), μG.IsHaarMeasure → μG J = 1 →
    ∀ f, IsCosetFn J h f → ∃ z : ℂ, IsQuotInt ν (rescale ν b m) μG 1 f z ∧
      (∀ z', IsQuotInt ν (rescale ν b m) μG 1 f z' → z' = z) ∧
      (((m (prX (Cgrp J h))).toReal : ℝ) : ℂ) * z = (((volNat ν b (Cgrp J h))⁻¹ : ℝ) : ℂ) * f h

def TargetLaw : Prop :=
  ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ), 1 ≤ c →
  ∀ (μ : kˣ →* ℂˣ) (P' : Level (GL (n' ⊕ Fin (c + 1)) k)) (P : Level (GL (n ⊕ Fin c) k))
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ), Φ ∈ SB _ → IsCO P'.J → IsCO P.J → HasTypes μ P' P Φ →
  ∀ h' h,
    (∀ u ∈ N k n c 1, ∀ (g : GL n k) (hm : h⁻¹ * (u * embX c g) * h ∈ P.J),
      om μ 1 g (flat ψ ν μ Φ h' h) =
        ((ψ (simpleSum u) : ℂ) * (((P.lam ⟨_, hm⟩)⁻¹ : ℂˣ) : ℂ)) • flat ψ ν μ Φ h' h) ∧
    (flat ψ ν μ Φ h' h ≠ 0 → ∃ χ : prX (Cgrp P.J h) →* ℂˣ, IsColChar ψ P h χ ∧ ∀ g : prX (Cgrp P.J h),
      om μ 1 (g : GL n k) (flat ψ ν μ Φ h' h) = (χ g : ℂ) • flat ψ ν μ Φ h' h ∧
      (∀ b, om μ 1 (g : GL n k) (xi ψ ν μ Φ P.J b h' h) = (χ g : ℂ) • xi ψ ν μ Φ P.J b h' h) ∧
      ∀ (V' V : Type) [AddCommGroup V'] [Module ℂ V'] [AddCommGroup V] [Module ℂ V]
        (π' : Representation ℂ (GL n' k) V') (π : Representation ℂ (GL n k) V)
        (θ : V' →ₗ[ℂ] (Matrix n n' k → ℂ) →ₗ[ℂ] V),
        (∀ γ' γ φ, ∀ Ξ ∈ SB (Matrix n n' k), θ (π' γ' φ) (om μ γ' γ Ξ) = π γ (θ φ Ξ)) →
        ∀ φ, π g (θ φ (flat ψ ν μ Φ h' h)) = (χ g : ℂ) • θ φ (flat ψ ν μ Φ h' h))

def SourceLaw : Prop :=
  ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ), 1 ≤ c →
  ∀ (μ : kˣ →* ℂˣ) (P' : Level (GL (n' ⊕ Fin (c + 1)) k)) (P : Level (GL (n ⊕ Fin c) k))
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ), Φ ∈ SB _ → IsCO P'.J → IsCO P.J → HasTypes μ P' P Φ →
  ∀ h' h, ∀ u ∈ N k n' (c + 1) 1, ∀ (g : GL n' k) (hm : h'⁻¹ * (u * embX (c + 1) g) * h' ∈ P'.J),
    om μ g 1 (flat ψ ν μ Φ h' h) = ((ψ (simpleSum u) : ℂ)⁻¹ * (P'.lam ⟨_, hm⟩ : ℂ)) • flat ψ ν μ Φ h' h

def ChainInvariant : Prop :=
  ∀ (s : ℕ) (X : ℕ → Type) [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] (Z : Type) [Fintype Z] [DecidableEq Z]
    (T : Chain k s X Z), T.Regular → T.Laws →
    (∀ j c (H : j + 1 + 1 + c = s) h' h h'', ∀ g ∈ prX (Cgrp (T.lev (j + 1) (c + 1 + 1) (by omega)).J h), ∀ x x',
      om (T.mu (j + 1)) 1 g (T.entry ψ ν j (c + 1) (by omega) h' h) x *
          om (T.mu (j + 1 + 1)) g 1 (T.entry ψ ν (j + 1) c H h h'') x' =
        T.entry ψ ν j (c + 1) (by omega) h' h x * T.entry ψ ν (j + 1) c H h h'' x') ∧
    ∀ h, ∀ u ∈ N k (X s) (0 + 1) 1, ∀ (g : GL (X s) k)
      (hm : h⁻¹ * (u * embX (0 + 1) g) * h ∈ (T.lev s (0 + 1) rfl).J) (y : X (s + 1) → k),
      om (T.mu (s + 1)) g 1 (fun x₀ => T.Psi h x₀ y) =
        ((ψ (simpleSum u) : ℂ)⁻¹ * ((T.lev s (0 + 1) rfl).lam ⟨_, hm⟩ : ℂ)) • fun x₀ => T.Psi h x₀ y

def ChainInvariantLast : Prop :=
  ∀ (j : ℕ) (X : ℕ → Type) [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] (Z : Type) [Fintype Z] [DecidableEq Z]
    (T : Chain k (j + 1) X Z), T.Regular → T.Laws →
    ∀ h' h, ∀ g ∈ prX (Cgrp (T.lev (j + 1) (0 + 1) rfl).J h), ∀ x x' y,
      om (T.mu (j + 1)) 1 g (T.entry ψ ν j 0 rfl h' h) x * om (T.mu (j + 1 + 1)) g 1 (fun x₀ => T.Psi h x₀ y) x' =
        T.entry ψ ν j 0 rfl h' h x * T.Psi h x' y

def FirstVertex {s : ℕ} {X : ℕ → Type} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] {Z : Type} [Fintype Z]
    [DecidableEq Z] (T : Chain k s X Z) (K₀ : Set (GL (X 0) k)) (lam : GL (X 0) k → ℂ) : Prop :=
  (∀ c (H : 0 + c = s + 1),
    (prX (Cgrp (T.lev 0 c H).J 1) : Set (GL (X 0) k)) = K₀ ∧
    (∀ γ ∈ K₀, ∃ hm : embX c γ ∈ (T.lev 0 c H).J, ((T.lev 0 c H).lam ⟨_, hm⟩ : ℂ) = lam γ) ∧
    ∃ χ : prX (Cgrp (T.lev 0 c H).J 1) →* ℂˣ, IsColChar ψ (T.lev 0 c H) 1 χ ∧
      ∀ γ, (χ γ : ℂ) * lam (γ : GL (X 0) k) = 1) ∧
  ∀ c (H : 0 + (c + 1) = s) h, ∀ γ ∈ K₀,
    om (T.mu (0 + 1)) γ 1 (flat ψ ν (T.mu (0 + 1)) (T.Phi 0 (c + 1) H) 1 h) =
      lam γ • flat ψ ν (T.mu (0 + 1)) (T.Phi 0 (c + 1) H) 1 h

def FirstVertexChains : Prop :=
  ∀ (s : ℕ) (t : Type) [Fintype t] [DecidableEq t],
    (∀ (κ : ℕ) (ϖ : kˣ), IsUnif ϖ →
      (∃ P : TypeDatum k (Fin κ ⊕ Fin (s + 1)), IsGenericLevel ψ ϖ P) ∧
      (∀ ρ, s + 1 = 2 * ρ + 1 → ∃ P : TypeDatum k (Fin κ ⊕ Fin (s + 1)), IsSymLevel ψ ϖ ρ P) ∧
      ∀ (P : TypeDatum k (Fin κ ⊕ Fin (s + 1))),
        (IsGenericLevel ψ ϖ P ∨ ∃ ρ, s + 1 = 2 * ρ + 1 ∧ IsSymLevel ψ ϖ ρ P) →
        ∀ (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)),
          FirstVertex ψ ν (typeChain t ϖ P μ hμ) (colGroup k κ t) (colChar ψ ϖ)) ∧
    ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (η : ℕ → kˣ →* ℂˣ),
      (∀ j, IsUnram (η j)) → FirstVertex ψ ν (twistChain s t κ δ hδ η) (KO k (XIx κ t 0)) fun _ => 1

end Props

def Statement : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), HasConductor ψ 1 → IsUnitVol ν →
    StepWellDefined ψ ν ∧ ChainFinite ψ ν ∧ CosetMeasure ν ∧ VolumeCancels ν ∧ TargetLaw ψ ν ∧ SourceLaw ψ ν ∧
      ChainInvariant ψ ν ∧ ChainInvariantLast ψ ν ∧ FirstVertexChains ψ ν

end GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NormalRepresentationLattice
section
open MeasureTheory ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

section Plain
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}

def nfBasis (ϖ : kˣ) (g : GL n k) (e : Fin c → ℤ) (z : n → k) : GL (n ⊕ Fin c) k :=
  colE c 1 z * embX c g * embA n (SplitFlip.diagGL fun i => ϖ ^ e i)

theorem nfBasis_val (ϖ : kˣ) (g : GL n k) (e : Fin c → ℤ) (z : n → k) : (nfBasis ϖ g e z).val =
    fromBlocks g.val (Matrix.of fun r i => if i.val = 0 then z r * (ϖ : k) ^ e i else 0) 0
      (diagonal fun i => (ϖ : k) ^ e i) := by
  change fromBlocks 1 _ 0 1 * fromBlocks g.val 0 0 1 * fromBlocks 1 0 0 (diagonal _) = _
  rw [fromBlocks_multiply, fromBlocks_multiply]
  ext (r | r) (i | i) <;> simp

theorem nfBasis_one (ϖ : kˣ) (e : Fin c → ℤ) (z : n → k) : nfBasis ϖ 1 e z = normalBasis ϖ e z := by
  simp [nfBasis, normalBasis]

variable [ValuativeRel k]

def powInt (ϖ : kˣ) (e : ℤ) : Set k := {s | valuation k s ≤ valuation k ((ϖ ^ e : kˣ) : k)}

def topCoord (Λ : Submodule 𝒪[k] (n ⊕ Fin c → k)) (i : Fin c) : Set k :=
  {s | ∃ y ∈ Λ, (∀ l, i < l → y (Sum.inr l) = 0) ∧ y (Sum.inr i) = s}

def MeetsIn (Λ : Submodule 𝒪[k] (n ⊕ Fin c → k)) (L : Submodule 𝒪[k] (n → k)) : Prop :=
  ∀ y : n → k, Sum.elim y 0 ∈ Λ ↔ y ∈ L

def MapsLat {ι ι' : Type*} [Fintype ι'] (x : Matrix ι ι' k) (Λ' : Submodule 𝒪[k] (ι' → k))
    (Λ : Submodule 𝒪[k] (ι → k)) : Prop := ∀ v ∈ Λ', x *ᵥ v ∈ Λ

end Plain

variable (k : Type*) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def NormalFormModN : Prop :=
  ∀ ϖ : kˣ, valuation k (ϖ : k) = uniformizer k →
  ∀ (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (h : GL (n ⊕ Fin c) k),
    ∃ u ∈ N k n c 1, ∃ (g : GL n k) (e : Fin c → ℤ) (z : n → k),
      latOf (u * h) = latOf (nfBasis ϖ g e z) ∧ MeetsIn (latOf h) (latOf g)

variable [MeasurableSpace k] [BorelSpace k]

variable {k}
variable {s : ℕ} {X : ℕ → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] {Z : Type*} [Fintype Z] [DecidableEq Z]
  (T : Chain k s X Z) (ϖ : kˣ) (ψ : AddChar k Circle) (ν : Measure k)

def IsNormalRep (j c : ℕ) (h : j + c = s) (g : GL (X j ⊕ Fin (c + 1)) k) : Prop :=
  ∃ (e : Fin (c + 1) → ℤ) (z : X j → k), (∀ i, -(j : ℤ) ≤ e i ∧ e i ≤ 0) ∧ (∀ i, z i ∈ 𝒪[k]) ∧
    latOf (g * T.bas j (c + 1) (by omega)) = latOf (normalBasis ϖ e z)

def NormalReps : Prop :=
  (∀ A, T.IsRepSystem A ψ ν → ∀ j c h, ∀ g ∈ A j c h, ∃ g₁,
    DoubleCoset.mk (R k (X j) (c + 1) 1) (T.lev j (c + 1) (by omega)).J g₁ =
      DoubleCoset.mk (R k (X j) (c + 1) 1) (T.lev j (c + 1) (by omega)).J g ∧ IsNormalRep T ϖ j c h g₁) ∧
  (∃ A, T.IsRepSystem A ψ ν ∧ T.RepsNormal A ϖ) ∧
  ∀ A, T.IsRepSystem A ψ ν → T.RepsNormal A ϖ → T.RepsMeet A ∧ ∀ j c h, ∀ g ∈ A j c h,
    ∀ κ ∈ stabLat (T.bas j (c + 1) (by omega)),
      latOf (T.bas j (c + 1) (by omega)) ≤ latOf (g * κ * T.bas j (c + 1) (by omega)) ∧
      ∀ y ∈ latOf (g * κ * T.bas j (c + 1) (by omega)), ((ϖ ^ j : kˣ) : k) • y ∈ latOf (T.bas j (c + 1) (by omega))

def DepthOne : Prop :=
  ∀ A, T.IsRepSystem A ψ ν → T.RepsNormal A ϖ → ∀ j c (h : j + 1 + c = s),
    ∀ g ∈ A j (c + 1) (by omega), ∀ g' ∈ A (j + 1) c h,
    DoubleCoset.mk (R k (X (j + 1)) (c + 1) 1) (T.lev (j + 1) (c + 1) (congrArg Nat.succ h)).J g' ∈ T.idx ψ ν j c h g →
      (∀ x₀ y, om (T.mu (j + 1)) g g' (T.Phi j (c + 1) (by omega)) (affPt 1 x₀ y) ≠ 0 →
        (∀ i : Fin (c + 1), affPt 1 x₀ y (Sum.inr i) (Sum.inr i.succ) ∈ powInt ϖ (-1)) ∧
          ch (affPt 1 x₀ y) ∈ powInt ϖ (-1)) ∧
      (∀ (e : Fin (c + 1) → ℤ) (z : X (j + 1) → k),
        latOf (g' * T.bas (j + 1) (c + 1) (by omega)) = latOf (normalBasis ϖ e z) →
          ∀ i : Fin c, e i.succ - 1 ≤ e i.castSucc) ∧
      ∀ u ∈ N k (X (j + 1)) (c + 1) 1, ∀ γ : GL (X (j + 1)) k,
        u * embX (c + 1) γ ∈ Cgrp (T.lev (j + 1) (c + 1) (by omega)).J g' →
          (∀ i : Fin c, u.val (Sum.inr i.castSucc) (Sum.inr i.succ) ∈ powInt ϖ (-1)) ∧ simpleSum u ∈ powInt ϖ (-1)

def LastSteps : Prop :=
  ∀ A, T.IsRepSystem A ψ ν → T.RepsMeet A →
    (∀ g ∈ A s 0 rfl, IsNormalRep T ϖ s 0 rfl g) ∧
    (∀ g ∈ A s 0 rfl, ∀ x₀ y, T.Psi g x₀ y ≠ 0 → ∀ i, y i ∈ 𝒪[k]) ∧
    (∀ M : ℕ, 1 ≤ M → ∀ yb ∈ T.coupIdx A (box _ (ϖ ^ M)⁻¹) (box _ (ϖ ^ M)),
      ∀ y, Submodule.Quotient.mk y = yb → ∀ i, y i ∈ 𝒪[k]) ∧
    T.Adapted A (box _ (ϖ ^ (s + 1))⁻¹) (box _ (ϖ ^ (s + 1))) ∧
    ∀ ε : k, valuation k ε = 1 → ∀ yb ∈ T.coupIdx A (box _ (ϖ ^ (s + 1))⁻¹) (box _ (ϖ ^ (s + 1))),
      ∀ η, hat ψ ν ε (cosetInd _ yb) η ≠ 0 →
        ∀ y, Submodule.Quotient.mk y = yb → ε * (η ⬝ᵥ y) ∈ powInt ϖ (-((s : ℤ) + 1))


variable (k) in
def ChainSizes : Prop :=
  ∀ ϖ : kˣ, valuation k (ϖ : k) = uniformizer k →
  ∀ ψ : AddChar k Circle, HasConductor ψ 1 → ∀ ν : Measure k, ν.IsAddHaarMeasure →
  ∀ (s : ℕ) (r t Z : Type) [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] [Fintype Z] [DecidableEq Z]
    (X : ℕ → Type) [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]
    (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (μ₀ : ℕ → kˣ →* ℂˣ), (∀ j, IsUnram (μ₀ j)) →
  ∀ (F : ∀ j c, j + c = s + 1 → LatFrame k (Ix r t j) (X j ⊕ Fin c)) (Ftop : LatFrame k (Ix r t (s + 2)) Z),
    (∀ j c h, latOf (F j c h).bas = latOf 1) →
      NormalReps (Chain.ofTwist δ hδ μ₀ F Ftop) ϖ ψ ν ∧ DepthOne (Chain.ofTwist δ hδ μ₀ F Ftop) ϖ ψ ν ∧
        LastSteps (Chain.ofTwist δ hδ μ₀ F Ftop) ϖ ψ ν


end GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.OmegaColumnSlices
section
open MeasureTheory ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.OmegaColumnSlices
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

section Lattices
variable {k : Type} [Field k] [ValuativeRel k] {a b : Type} [Fintype a]

def Maps (Λ' : Submodule 𝒪[k] (a → k)) (Λ : Submodule 𝒪[k] (b → k)) (x : Matrix b a k) : Prop :=
  ∀ v ∈ Λ', x *ᵥ v ∈ Λ

def dualStd (k : Type) [Field k] [ValuativeRel k] (a : Type) [Fintype a] : Set (a → k) :=
  {η | ∀ y ∈ box a (1 : kˣ), η ⬝ᵥ y ∈ 𝒪[k]}

def srcLat (a : Type) (ϖ : kˣ) : Submodule 𝒪[k] (a ⊕ Fin (0 + 1) → k) :=
  (box a (1 : kˣ)).comap (LinearMap.funLeft 𝒪[k] k Sum.inl) ⊓
    (box (Fin (0 + 1)) ϖ).comap (LinearMap.funLeft 𝒪[k] k Sum.inr)

end Lattices

section Line
variable {k : Type} [Field k] {n n' : Type}

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype n] [DecidableEq n]

def omCol (μz : kˣ →* ℂˣ) (h : GL n k) (φ : (n → k) → ℂ) : (n → k) → ℂ := fun y =>
  (((μz (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ) : ℂ) *
    ((nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) * φ ((h⁻¹).val *ᵥ y)

def omRow (μz : kˣ →* ℂˣ) (h : GL n k) (φ' : (n → k) → ℂ) : (n → k) → ℂ := fun η =>
  (((μz (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ) : ℂ) *
    ((nabs k (Matrix.GeneralLinearGroup.det h) ^ ((1 : ℝ) / 2) : ℝ) : ℂ) * φ' (η ᵥ* h.val)

end Line

section Pen
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']


end Pen

section Top
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
variable {s : ℕ} {X : ℕ → Type} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] {Z : Type} [Fintype Z] [DecidableEq Z]

end Top

section Checks
variable {k : Type} [Field k] [ValuativeRel k] {ι n : Type} [Fintype n] [DecidableEq n]

end Checks

end GlobalTheory.IndefiniteRowSideFullHecke.OmegaColumnSlices
end
end

