module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryDeterminantRoot
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TransvectionEq
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0028

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SignatureEmbeddingCoverComp
section
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false

noncomputable section

namespace GlobalTheory.XiDetCompare

open Formalism.L2.Pj Formalism.L2.PjFree NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.IndefiniteRowSideFullHecke.ComplexResidueRing GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDeterminantRoot GlobalTheory.CoefChangeCompare
open scoped TensorProduct

section Lattices

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [IsCMField E] [Algebra F E] {r : ℕ}

def latHat0 (L0 : Submodule (𝓞 E) (Fin r → E)) : AddSubgroup (Fin r → AdE F E) :=
  AddSubgroup.closure {z | ∃ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧
    ∃ x ∈ L0, z = fun i => a ⊗ₜ x i}

def finVec (v : Fin r → E) : Fin r → AdE F E := fun i => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ v i

variable {F}

def gLat (L0 : Submodule (𝓞 E) (Fin r → E)) (g : Matrix (Fin r) (Fin r) (AdE F E)) : Set (Fin r → AdE F E) :=
  g.mulVec '' (latHat0 F L0 : Set (Fin r → AdE F E))

def latG (L0 : Submodule (𝓞 E) (Fin r → E)) (AA : Set E) (g : Matrix (Fin r) (Fin r) (AdE F E)) :
    Submodule (𝓞 E) (Fin r → E) :=
  Submodule.span (𝓞 E) {w | ∃ a : E, a ∈ AA ∧ ∃ v, finVec F v ∈ gLat L0 g ∧ w = a • v}

def latGHat (L0 : Submodule (𝓞 E) (Fin r → E)) (AA : Set E) (g : Matrix (Fin r) (Fin r) (AdE F E)) :
    AddSubgroup (Fin r → AdE F E) :=
  AddSubgroup.closure {w | ∃ a : E, a ∈ AA ∧ ∃ z ∈ gLat L0 g, w = fun i => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ a) * z i}

variable (L0 : Submodule (𝓞 E) (Fin r → E)) (AA : Set E)

variable {La : Type} [AddCommGroup La] [Module (𝓞 E) La]

end Lattices

section Reading

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [IsCMField E] [Algebra F E]
  [Fact (IsRealIn F E)] {r : ℕ}

def Reads (xi : (AdE F E)ˣ →* ℂˣ) (ξ : (AdE F E)ˣ →* Circle) : Prop :=
  ∀ x u : (AdE F E)ˣ, (x : AdE F E) = u * conjA F (x : AdE F E) → ((xi u : ℂˣ) : ℂ) = ((ξ x : Circle) : ℂ)

def TrivFix (ξ : (AdE F E)ˣ →* Circle) : Prop := ∀ x : (AdE F E)ˣ, conjA F (x : AdE F E) = x → ξ x = 1

def TrivRat (ξ : (AdE F E)ˣ →* Circle) : Prop := ∀ (x : (AdE F E)ˣ) (z : E), (x : AdE F E) = diagE F z → ξ x = 1

end Reading

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [IsCMField E] [Algebra F E]
variable {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {n r rk : ℕ}
variable {𝔾 : Type} [Group 𝔾]

section First

variable (Γ : Subgroup 𝔾) (fin : 𝔾 →* GL (Fin rk) (AdE F E)) (L0 : Submodule (𝓞 E) (Fin rk → E)) (AA : Set E)

def MarkedBy {c : Coeff l} {σ : c.F →+* ℂ} (U : Formalism.L2.PjFree.Unf Xo c σ r) (hr : rk = r)
    (dict : 𝔾 → Σ k, Frame (U.X k).Ψ r) (ι : Dw.La →ₗ[𝓞 E] (Fin rk → E)) {g : ℕ}
    {lab : Fin g → E →+* ℂ} (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) lab)
    (ik : U.Comp → Fin Fu.n) (φ : ∀ k, (Fu.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ) (h γ : 𝔾) : Prop :=
  γ ∈ Γ ∧
    ((U.X (dict h).1).Λ : Set (Fin r → E)) =
      (fun v : Fin rk → E => v ∘ Fin.cast hr.symm) '' (latG L0 AA (fin (γ * h)).1 : Set _) ∧
    ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
      ∃ w ∈ latGHat L0 AA (fin (γ * h)).1,
        finVec F ((φ (dict h).1 (Fu.t (ik (dict h).1) a) : Fin r → E) ∘ Fin.cast hr) -
          (fin (γ * h)).1.mulVec (finVec F (ι a)) = (l.M : ℕ) • w

variable {Th : Type} (arch : Th → 𝔾 → Matrix (Fin rk) (Fin rk) ℂ)


variable (gram : Matrix (Fin rk) (Fin rk) E) (xi0 : E) (IsInf : (E →+* ℂ) → Th → Prop)

end First

section Mark

variable (Γ : Subgroup 𝔾) (fin : 𝔾 →* GL (Fin r) (AdE F E)) (L0 : Submodule (𝓞 E) (Fin r → E)) (AA : Set E)
variable {c : Coeff l} {σ : c.F →+* ℂ} (U : Formalism.L2.PjFree.Unf Xo c σ r) (dict : 𝔾 → Σ k, Frame (U.X k).Ψ r)
  (ι : Dw.La →ₗ[𝓞 E] (Fin r → E)) {g : ℕ} {lab : Fin g → E →+* ℂ}
  (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) lab)
  (ik : U.Comp → Fin Fu.n) (φ : ∀ k, (Fu.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ)

def embOf (k : U.Comp) : (Fu.Di (ik k)).La →ₗ[𝓞 E] (Fin r → E) := (U.X k).Λ.subtype ∘ₗ (φ k).toLinearMap

variable {L0 AA ι}

end Mark

section Value

variable [Fact (IsRealIn F E)]

def XiValAtC {c : Coeff l} (c0 : ℂ) (Gm : Matrix (Fin r) (Fin r) E) (ι : Dw.La →ₗ[𝓞 E] (Fin r → E))
    (ξ : (AdE F E)ˣ →* Circle) (σ : c.F →+* ℂ) {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty)
    (φ : ∀ i, (Fu.Di i).La →ₗ[𝓞 E] (Fin r → E)) (f : Rul Xo c) : Prop :=
  ∀ (i : Fin Fu.n) (h : Matrix (Fin r) (Fin r) (AdE F E)) (x : (AdE F E)ˣ),
    IsUnitaryA Gm h → AtClass l Gm ι (φ i) (Fu.t i) h → IsDetRootA h x →
    ∀ P : (Fu.Di i).La →+ (Fin g → ℂ), IsPeriod (Fu.Di i) ty P →
      ∀ y : FrPt Xo c (CAt σ), y.x = Fu.u i P → Formalism.L2.PjFree.toC (evR Xo c f y) = c0 * ((ξ x : Circle) : ℂ)


variable (Xo) in
def XiValC (c : Coeff l) (c0 : ℂ) (Gm : Matrix (Fin r) (Fin r) E) (ξ0 : E) (ι : Dw.La →ₗ[𝓞 E] (Fin r → E))
    (ξ : (AdE F E)ˣ →* Circle) (σ : c.F →+* ℂ) (f : Rul Xo c) : Prop :=
  r = Dw.p + Dw.q ∧ ∃ (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1))
    (φ : ∀ i, (Fu.Di i).La →ₗ[𝓞 E] (Fin r → E)),
    AllMarked F Gm ξ0 ι Fu φ ∧ XiValAtC c0 Gm ι ξ σ Fu φ f

variable (Γ : Subgroup 𝔾) (fin : 𝔾 →* GL (Fin r) (AdE F E)) {L0 : Submodule (𝓞 E) (Fin r → E)} {AA : Set E}
variable {c : Coeff l} {σ : c.F →+* ℂ} (U : Formalism.L2.PjFree.Unf Xo c σ r) (dict : 𝔾 → Σ k, Frame (U.X k).Ψ r)
  {ι : Dw.La →ₗ[𝓞 E] (Fin r → E)} {g : ℕ} {lab : Fin g → E →+* ℂ}
  (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) lab)
  (ik : U.Comp → Fin Fu.n) (φ : ∀ k, (Fu.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ)
  (ψ : ∀ i, (Fu.Di i).La →ₗ[𝓞 E] (Fin r → E))

def Reaches (Gm : Matrix (Fin r) (Fin r) E) (ι : Dw.La →ₗ[𝓞 E] (Fin r → E)) : Prop :=
  ∀ (i : Fin Fu.n) (gm : Matrix (Fin r) (Fin r) (AdE F E)), IsUnitaryA Gm gm → LatAt ι (ψ i) gm →
    MarkAt l ι (ψ i) (Fu.t i) gm → ∀ P : (Fu.Di i).La →+ (Fin g → ℂ), IsPeriod (Fu.Di i) lab P →
      ∀ y : FrPt Xo c (CAt σ), y.x = Fu.u i P → ∃ h : 𝔾, (fin h).1 = gm ∧ ik (dict h).1 = i ∧
        ∃ (hx : (dict h).2 ∈ (U.X (dict h).1).dom) (t : Ix Dw → (CAt σ)ˣ), FrBor t (U.un (dict h).1 ⟨(dict h).2, hx⟩) y

variable {Γ fin U dict Fu ik φ ψ} {Gm : Matrix (Fin r) (Fin r) E} {xi : (AdE F E)ˣ →* ℂˣ} {ξ : (AdE F E)ˣ →* Circle}
  {c0 : ℂ} {f : Rul Xo c}

end Value

section Covers

variable [Fact (IsRealIn F E)] (Γ : Subgroup 𝔾) (fin : 𝔾 →* GL (Fin r) (AdE F E)) (L0 : Submodule (𝓞 E) (Fin r → E))
  (AA : Set E) {Th : Type} (arch : Th → 𝔾 → Matrix (Fin r) (Fin r) ℂ) (IsInf : (E →+* ℂ) → Th → Prop)

variable {Γ fin L0 AA arch IsInf} {gram : Matrix (Fin r) (Fin r) E} {xi0 : E}

section One

variable {c : Coeff l} {σ : c.F →+* ℂ} {U : Formalism.L2.PjFree.Unf Xo c σ r} {dict : 𝔾 → Σ k, Frame (U.X k).Ψ r}
  {ι : Dw.La →ₗ[𝓞 E] (Fin r → E)} {x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ}
  {g : ℕ} {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
  {Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)}
  {ik : U.Comp → Fin Fu.n} {φ : ∀ k, (Fu.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ} {th : ∀ k, (U.X k).Ψ → Th}

end One

variable {c : Coeff l} {σ0 : c.F →+* ℂ} {Tup : Type*} {dδ : Tup → DeltaDat Xo c n}
  {U₂ : ∀ t, Formalism.L2.PjFree.Unf (dδ t).Xo₂ (dδ t).c₂ (σ0.comp ((dδ t).eF.symm : (dδ t).c₂.F →+* c.F)) r}
  {dict₂ : ∀ t, 𝔾 → Σ k, Frame ((U₂ t).X k).Ψ r} {ι : Dw.La →ₗ[𝓞 E] (Fin r → E)}
  {x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ} {xi : Tup → (AdE F E)ˣ →* ℂˣ} {ξ : Tup → (AdE F E)ˣ →* Circle} {c0 : ℂ}

end Covers

section Comparison₂

section Act

variable (c : Coeff l) {G : Type} [Group G] (lev : G → (Dw.La →ₗ[𝓞 E] Dw.La) × (Dw.La →ₗ[𝓞 E] Dw.La))

variable {c} {c' : Coeff l} (hle : c.F ≤ c'.F)

end Act

variable (Γ : Subgroup 𝔾)



variable {c c' : Coeff l} (hle : c.F ≤ c'.F) {Vs : Type} [AddCommGroup Vs] [Module c'.F Vs]

variable (LL : IntermediateField ℚ ℂ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r)
  (dict : 𝔾 → Σ k, Frame ((U (sig0 c)).X k).Ψ r) (mu : 𝔾 → ℂ) (xr : ℝ) (a : (E →+* ℂ) × ℕ → ℕ) {G : Type} [Group G]
  (lev : G → (Dw.La →ₗ[𝓞 E] Dw.La) × (Dw.La →ₗ[𝓞 E] Dw.La)) {Tup : Type*} (dδ : Tup → DeltaDat Xo c' n)
  (Cl' : Tup → Type) [∀ t, Fintype (Cl' t)] (w : ∀ t, Cl' t → (Fin n → LevQ Dw (dδ t).l₂) → c'.F)
  (La : ∀ t, Cl' t → GenLat E n) (Nc gam : ∀ t, Cl' t → ℕ) (vol : Tup → c'.F) (ep : ∀ t, Cl' t → c'.F)
  (io : Vs →ₗ[c'.F] MvPolynomial (LtN Dw n) c'.F)
  (thAd : ∀ t, (Cl' t → Vs) → (Quotient (QuotientGroup.rightRel Γ) → ℂ)) (Pl : ∀ t, (Cl' t → Vs) → Prop)
  (cst : (U (sig0 c)).Comp → ℂ) (ph : ℂ)

end Comparison₂

section Whole

variable [Fact (IsRealIn F E)] {Γ : Subgroup 𝔾} {fin : 𝔾 →* GL (Fin r) (AdE F E)} {L0 : Submodule (𝓞 E) (Fin r → E)}
  {AA : Set E} {Th : Type} {arch : Th → 𝔾 → Matrix (Fin r) (Fin r) ℂ} {IsInf : (E →+* ℂ) → Th → Prop}
  {gram : Matrix (Fin r) (Fin r) E} {xi0 : E} {c c' : Coeff l} {hle : c.F ≤ c'.F} {Vs : Type} [AddCommGroup Vs]
  [Module c'.F Vs] {LL : IntermediateField ℚ ℂ} {U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r}
  {dict : 𝔾 → Σ k, Frame ((U (sig0 c)).X k).Ψ r} {mu : 𝔾 → ℂ} {xr : ℝ} {a : (E →+* ℂ) × ℕ → ℕ} {G : Type} [Group G]
  {lev : G → (Dw.La →ₗ[𝓞 E] Dw.La) × (Dw.La →ₗ[𝓞 E] Dw.La)} {Tup : Type*} {dδ : Tup → DeltaDat Xo c' n}
  {Cl' : Tup → Type} [∀ t, Fintype (Cl' t)] {w : ∀ t, Cl' t → (Fin n → LevQ Dw (dδ t).l₂) → c'.F}
  {La : ∀ t, Cl' t → GenLat E n} {Nc gam : ∀ t, Cl' t → ℕ} {vol : Tup → c'.F} {ep : ∀ t, Cl' t → c'.F}
  {io : Vs →ₗ[c'.F] MvPolynomial (LtN Dw n) c'.F}
  {thAd : ∀ t, (Cl' t → Vs) → (Quotient (QuotientGroup.rightRel Γ) → ℂ)} {Pl : ∀ t, (Cl' t → Vs) → Prop}
  {cst : (U (sig0 c)).Comp → ℂ} {ph : ℂ}
  {U₂ : ∀ t, Formalism.L2.PjFree.Unf (dδ t).Xo₂ (dδ t).c₂ ((sig0 c').comp ((dδ t).eF.symm : (dδ t).c₂.F →+* c'.F)) r}
  {dict₂ : ∀ t, 𝔾 → Σ k, Frame ((U₂ t).X k).Ψ r} {ι : Dw.La →ₗ[𝓞 E] (Fin r → E)}
  {x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ} {xi : Tup → (AdE F E)ˣ →* ℂˣ} {ξ : Tup → (AdE F E)ˣ →* Circle}

end Whole

end GlobalTheory.XiDetCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.WeightZeroSectionValueConjPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.WeightZeroValue

open GlobalTheory.Frames GlobalTheory.NonDominant Polynomial

theorem poly_const (P Q : ℂ[X]) (h : ∀ c : ℂ, c ≠ 0 → P.eval c = Q.eval c⁻¹) (s : ℂ) : P.eval s = P.eval 0 := by
  have h0 : P - C (Q.coeff 0) = 0 := by
    refine poly_eq_zero _ Q.divX 1 one_pos 1 fun c hc => ?_
    have e := congrArg (eval c⁻¹) (Polynomial.X_mul_divX_add Q)
    rw [eval_add, eval_mul, eval_X, eval_C] at e
    rw [eval_sub, eval_C, h c hc, ← e]
    field_simp
    ring
  rw [sub_eq_zero.1 h0, eval_C, eval_C]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ}

def Keeps (σ : c.F →+* ℂ) (f : Rul Xo c) (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ) : Prop :=
  ∀ y y' : FrPt Xo c (CAt σ), FrChg (S := CAt σ) g 1 y y' → evR Xo c f y' = evR Xo c f y

theorem Keeps.mul {f : Rul Xo c} {g g' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ}
    (hg : Keeps σ f g) (hg' : Keeps σ f g') (hu : ∀ τ, IsUnit (g τ).det) (hu' : ∀ τ, IsUnit (g' τ).det) :
    Keeps σ f fun τ => g τ * g' τ := fun y y' h => by
  obtain ⟨y₁, h₁, -⟩ := existsUnique_frChg E H Dw l Xo c (CAt σ) y g' 1 hu'
  obtain ⟨y₂, h₂, -⟩ := existsUnique_frChg E H Dw l Xo c (CAt σ) y₁ g 1 hu
  have h₃ := (frChg_refl_and_comp E H Dw l Xo c _ y y₁ y₂).2 _ _ _ _ h₁ h₂
  rw [Units.val_one, _root_.mul_one] at h₃
  have e : y₂ = y' := (existsUnique_frChg E H Dw l Xo c (CAt σ) y (fun τ => (g τ * g' τ : Matrix _ _ ℂ)) 1
    (fun τ => show IsUnit (g τ * g' τ).det by rw [Matrix.det_mul]; exact (hu τ).mul (hu' τ))).unique h₃ h
  rw [← e, hg _ _ h₂, hg' _ _ h₁]

theorem evR_bor {f : Rul Xo c} (hf : f ∈ sec Xo c 0 0) {t : Ix Dw → (CAt σ)ˣ} {y y' : FrPt Xo c (CAt σ)}
    (h : FrBor t y y') : evR Xo c f y' = evR Xo c f y := by
  have e : ex Dw 0 0 = 0 := funext fun i => by cases i <;> rfl
  rw [evR_weight hf h, e]
  simp [wchar]

theorem keeps_lower {f : Rul Xo c} (hf : f ∈ sec Xo c 0 0)
    {g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ} (h0 : ∀ τ i j, i < j → g τ i j = 0)
    (hd : ∀ τ i, g τ i i ≠ 0) : Keeps σ f g := fun y y' h => by
  let t : Ix Dw → ℂˣ := fun i => match i with
    | none => 1
    | some p => Units.mk0 _ (hd p.1 p.2)
  exact evR_bor (t := t) hf (((frBor_calculus E H Dw l Xo c _ y y' y').1 t).2 ⟨g, h0, fun _ _ => rfl, h⟩)


open Classical in
def only {R : Type} [CommRing R] (τ : E →+* ℂ) (M : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R) :
    ∀ ρ : E →+* ℂ, Matrix (Fin (Dw.mult ρ)) (Fin (Dw.mult ρ)) R := Function.update (fun _ => 1) τ M

section Only

variable {R : Type} [CommRing R] {τ : E →+* ℂ}

theorem only_self (M : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R) : only τ M τ = M := by simp [only]

theorem only_of_ne (M : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R) {ρ : E →+* ℂ} (h : ρ ≠ τ) :
    only τ M ρ = 1 := by
  unfold only
  exact @Function.update_of_ne _ _ (fun a b => Classical.propDecidable (a = b)) _ _ h _ _

theorem only_det {M : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R} (hM : IsUnit M.det) (ρ : E →+* ℂ) :
    IsUnit (only τ M ρ).det := by
  by_cases h : ρ = τ
  · subst h; rwa [only_self]
  · simp [only_of_ne _ h]

theorem only_mul (M N : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R) :
    (fun ρ => only τ M ρ * only τ N ρ) = only τ (M * N) := funext fun ρ => by
  by_cases h : ρ = τ
  · subst h; simp [only_self]
  · simp [only_of_ne _ h]

theorem only_map (M : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R[X]) (s : R) :
    (fun ρ => (only τ M ρ).map (eval s)) = only τ (M.map (eval s)) := funext fun ρ => by
  by_cases h : ρ = τ
  · subst h; simp [only_self]
  · simp [only_of_ne _ h]

end Only

theorem keeps_only_lower {f : Rul Xo c} (hf : f ∈ sec Xo c 0 0) {τ : E →+* ℂ}
    {M : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ} (h0 : ∀ i j, i < j → M i j = 0) (hd : ∀ i, M i i ≠ 0) :
    Keeps σ f (only τ M) := by
  refine keeps_lower hf (fun ρ i j hij => ?_) fun ρ i => ?_
  · by_cases h : ρ = τ
    · subst h; rw [only_self]; exact h0 i j hij
    · rw [only_of_ne _ h, Matrix.one_apply_ne hij.ne]
  · by_cases h : ρ = τ
    · subst h; rw [only_self]; exact hd i
    · simp [only_of_ne _ h]

theorem keeps_upper {f : Rul Xo c} (hf : f ∈ sec Xo c 0 0) {τ : E →+* ℂ} {i j : Fin (Dw.mult τ)} (hij : i < j)
    (r : ℂ) : Keeps σ f (only τ (Matrix.transvection i j r)) := fun y y' hy' => by
  have hT : ∀ s : CAt σ, (Matrix.transvection i j (X : (CAt σ)[X])).map (eval s) = Matrix.transvection i j s :=
    fun s => by
      ext k m
      simp only [Matrix.transvection, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
        eval_add]
      split_ifs <;> simp
  have hsw : ∀ {R : Type} [CommRing R], IsUnit (Matrix.swap R i j).det := fun {R} _ =>
    (Matrix.isUnit_iff_isUnit_det _).1 (IsUnit.of_mul_eq_one _ (Matrix.swap_mul_self i j))
  have hTd : ∀ {R : Type} [CommRing R] (s : R), IsUnit (Matrix.transvection i j s).det := fun s => by
    rw [Matrix.det_transvection_of_ne _ _ hij.ne]; exact isUnit_one
  obtain ⟨P, hP⟩ := exists_poly hf y (only τ (Matrix.transvection i j X)) (only_det (hTd _))
  obtain ⟨w, hw, -⟩ := existsUnique_frChg E H Dw l Xo c _ y (only τ (Matrix.swap _ i j)) 1 (only_det hsw)
  obtain ⟨Q, hQ⟩ := exists_poly hf w (only τ (Matrix.transvection i j X)) (only_det (hTd _))
  simp only [only_map, hT] at hP hQ
  have hc := poly_const P Q (fun s hs => by
    obtain ⟨B, hB, hBd, hBe⟩ := transvection_eq hij s hs
    obtain ⟨y₁, hy₁, -⟩ := existsUnique_frChg E H Dw l Xo c (CAt σ) w
      (only τ (Matrix.transvection i j (s⁻¹ : ℂ))) 1 (only_det (hTd _))
    have hBu : IsUnit B.det := by
      have := hTd s
      rw [← hBe, Matrix.det_mul] at this
      exact isUnit_of_mul_isUnit_left this
    obtain ⟨y₂, hy₂, -⟩ := existsUnique_frChg E H Dw l Xo c (CAt σ) y₁ (only (R := CAt σ) τ B) 1 (only_det hBu)
    have e3 := keeps_only_lower (σ := σ) hf hB (fun k => by
      rw [hBd k]; split_ifs <;> simp [hs]) y₁ y₂ hy₂
    have h1 := (frChg_refl_and_comp E H Dw l Xo c _ y w y₁).2 _ _ _ _ hw hy₁
    rw [only_mul (R := CAt σ) (Matrix.transvection i j (s⁻¹ : ℂ))] at h1
    have h2 := (frChg_refl_and_comp E H Dw l Xo c _ y y₁ y₂).2 _ _ _ _ h1 hy₂
    rw [only_mul (R := CAt σ) B, Units.val_one, _root_.mul_one, _root_.mul_one] at h2
    have e1 : evR Xo c f y₂ = P.eval s :=
      hP s y₂ ((congrArg (fun M => FrChg (only (R := CAt σ) τ M) 1 y y₂) hBe).mp h2)
    have e2 : evR Xo c f y₁ = Q.eval (s⁻¹ : ℂ) := hQ _ y₁ hy₁
    exact e1.symm.trans (e3.trans e2)) r
  have h0 := hP 0 y (by
    have : only τ (Matrix.transvection i j (0 : CAt σ)) = fun _ => 1 := by simp [only]
    rw [this]
    exact (frChg_refl_and_comp E H Dw l Xo c _ y y y).1)
  exact (hP r y' hy').trans (hc.trans h0.symm)

theorem keeps_only {f : Rul Xo c} (hf : f ∈ sec Xo c 0 0) {τ : E →+* ℂ}
    (M : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ) (hM : M.det ≠ 0) : Keeps σ f (only τ M) := by
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero (fun M => Keeps σ f (only τ M)) M hM
    (fun d hd => ?_) (fun t => ?_) fun A B hA hB kA kB => ?_
  · rw [Matrix.det_diagonal] at hd
    exact keeps_only_lower hf (fun i j hij => Matrix.diagonal_apply_ne _ hij.ne) fun i => by
      rw [Matrix.diagonal_apply_eq]; exact Finset.prod_ne_zero_iff.1 hd i (Finset.mem_univ i)
  · rcases lt_or_gt_of_ne t.hij with h | h
    · exact keeps_upper hf h t.c
    · refine keeps_only_lower hf (fun k m hkm => ?_) fun k => ?_
      · rw [Matrix.TransvectionStruct.toMatrix, Matrix.transvection, Matrix.add_apply, Matrix.one_apply_ne hkm.ne,
          Matrix.single_apply_of_ne, add_zero]
        rintro ⟨rfl, rfl⟩
        exact absurd h (not_lt.2 hkm.le)
      · rw [Matrix.TransvectionStruct.toMatrix, Matrix.transvection, Matrix.add_apply, Matrix.one_apply_eq,
          Matrix.single_apply_of_ne, add_zero]
        · exact one_ne_zero
        · rintro ⟨h1, h2⟩
          exact t.hij (h1.trans h2.symm)
  · rw [← only_mul]
    exact kA.mul kB (only_det hA.isUnit) (only_det hB.isUnit)

theorem keeps_all {f : Rul Xo c} (hf : f ∈ sec Xo c 0 0)
    (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ) (hg : ∀ τ, IsUnit (g τ).det) :
    Keeps σ f g := by
  classical
  have key : ∀ s : Finset (E →+* ℂ), Keeps σ f fun ρ => if ρ ∈ s then g ρ else 1 := fun s => by
    induction s using Finset.induction_on with
    | empty => exact keeps_lower hf (fun τ i j hij => by simp [Matrix.one_apply_ne hij.ne]) fun τ i => by simp
    | insert τ s hτ ih =>
      have := (keeps_only (σ := σ) hf (g τ) (hg τ).ne_zero).mul ih (only_det (hg τ)) fun ρ => by
        split_ifs
        · exact hg ρ
        · simp
      convert this using 2 with ρ
      by_cases h : ρ = τ
      · subst h; simp [only_self, hτ]
      · simp [only_of_ne _ h, h]
  simpa using key Finset.univ

theorem evR_eq_of_same_point {f : Rul Xo c} (hf : f ∈ sec Xo c 0 0) {y y' : FrPt Xo c (CAt σ)} (h : y'.x = y.x) :
    evR Xo c f y' = evR Xo c f y := by
  obtain ⟨g, s, hg, hzw⟩ := (frChg_exists_unique E H Dw l Xo c _ y y').1 h
  obtain ⟨z1, h1, -⟩ := existsUnique_frChg E H Dw l Xo c _ y g 1 hg
  obtain ⟨z2, h2, -⟩ := existsUnique_frChg E H Dw l Xo c _ z1 (fun _ => 1) s (fun _ => by simp)
  have h3 := (frChg_refl_and_comp E H Dw l Xo c _ y z1 z2).2 _ _ _ _ h1 h2
  simp only [Units.val_one, _root_.mul_one, _root_.one_mul] at h1 h3
  have e : z2 = y' := (existsUnique_frChg E H Dw l Xo c _ y g s hg).unique h3 hzw
  let t : Ix Dw → (CAt σ)ˣ := fun i => match i with
    | none => s
    | some _ => 1
  rw [← e, evR_bor (t := t) hf (((frBor_calculus E H Dw l Xo c _ z1 z2 z2).1 t).2
    ⟨fun _ => 1, fun τ i j hij => Matrix.one_apply_ne hij.ne, fun τ i => Matrix.one_apply_eq i, h2⟩)]
  exact keeps_all hf g hg y z1 h1

theorem evR_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (σ : c.F →+* ℂ) (τ : ℂ ≃+* ℂ), ∀ f ∈ sec Xo c 0 0, ∀ (y : FrPt Xo c (CAt σ)) (y' : FrPt Xo c (CAt ((τ : ℂ →+* ℂ).comp σ))), y'.x = spMap (τ : ℂ →+* ℂ) ≫ y.x → Formalism.L2.PjFree.toC (evR Xo c f y') = τ (Formalism.L2.PjFree.toC (evR Xo c f y)) := by
  intro E _ _ _ H D l Xo c σ τ f hf y y' h
  let φ : CAt σ →ₐ[c.F] CAt ((τ : ℂ →+* ℂ).comp σ) := { (τ : ℂ →+* ℂ) with commutes' := fun _ => rfl }
  obtain ⟨z, hz⟩ := _root_.GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H D l Xo c _ _ φ y
  rw [evR_eq_of_same_point hf (h.trans hz.1.symm), evR_map hf φ hz]
  rfl

end GlobalTheory.WeightZeroValue
end
end

