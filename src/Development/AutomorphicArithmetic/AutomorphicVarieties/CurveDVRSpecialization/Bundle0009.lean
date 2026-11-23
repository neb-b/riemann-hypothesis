module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.RatTorsionFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.GfResZpow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.MatIrrOpenGd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.WeightZeroAlgebraLeEntryAlgebra
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0013
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0009
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0044
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ContinuousCoboundaries2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.SlopeTestRemainingChoices

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.GdMain
section
open NumberField IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr UpperTheory.V

open Matrix Formalism.MainNotions.N in
private theorem ss_conj {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {ρ ρ' : Γ →* GL (Fin n) k} (h : GL (Fin n) k)
    (hh : ∀ g, ρ' g = h * ρ g * h⁻¹) (hρ : IsSSRep ρ) : IsSSRep ρ' := by
  let e : (Fin n → k) ≃ₗ[k] (Fin n → k) := Matrix.toLin'OfInv (M := (h : Matrix (Fin n) (Fin n) k))
    (M' := ((h⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) (Units.mul_inv h) (Units.inv_mul h)
  have he : ∀ v, e v = ((h⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ v := fun v => rfl
  have key : ∀ g v, e ((ρ' g : Matrix (Fin n) (Fin n) k) *ᵥ v) = (ρ g : Matrix (Fin n) (Fin n) k) *ᵥ e v := by
    intro g v
    rw [he, he, hh, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
    congr 2
    group
  intro W hW
  obtain ⟨W', hW', hc⟩ := hρ (W.map (e : (Fin n → k) →ₗ[k] (Fin n → k))) (by
    rintro g _ ⟨v, hv, rfl⟩
    exact ⟨_, hW g v hv, key g v⟩)
  refine ⟨W'.comap (e : (Fin n → k) →ₗ[k] (Fin n → k)), fun g v hv => ?_, ?_⟩
  · show e _ ∈ W'
    rw [key]
    exact hW' g _ hv
  · have := (Submodule.orderIsoMapComap e).symm.isCompl hc
    have h2 : IsCompl ((W.map (e : (Fin n → k) →ₗ[k] (Fin n → k))).comap (e : (Fin n → k) →ₗ[k] (Fin n → k)))
      (W'.comap (e : (Fin n → k) →ₗ[k] (Fin n → k))) := this
    rwa [Submodule.comap_map_eq_of_injective e.injective] at h2

private theorem autCsd_iso {F Ω : Type} [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] {l : ℕ}
    [Fact l.Prime] {n : ℕ} {ι : Qbar l ≃+* ℂ} {r r' : G F Ω →* GL (Fin n) (Qbar l)} (h : Af.RepIso r r')
    (H : Af.IsAutCsd ι r) : Af.IsAutCsd ι r' := by
  obtain ⟨π, h1, h2, h3, h4⟩ := H
  refine ⟨π, h1, h2, ss_conj h.choose h.choose_spec h3, h4.mono fun w ⟨B, hB, hB'⟩ => ⟨B, hB, hB'.of_iso h⟩⟩

private theorem tw_iso {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k} (χ : Γ →* kˣ)
    (h : Af.RepIso r r') : Af.RepIso (Af.tw r χ) (Af.tw r' χ) := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g, fun s => Units.ext ?_⟩
  rw [Units.val_mul, Units.val_mul, Af.tw_val, Af.tw_val, hg, Units.val_mul, Units.val_mul, Matrix.mul_smul,
    Matrix.smul_mul]

private theorem conj_left {G R : Type} [Group G] [CommRing R] (r : G →* GG (m := 3) (R := R)) (h : GL (Fin 3) R) (g : G)
    (hg : (r g).right = 1) : (conjBy h r g).left = h * (r g).left * h⁻¹ := by
  have e : conjBy h r g = GG.ofGL h * r g * GG.ofGL h⁻¹ := by
    rw [map_inv]; rfl
  rw [e, SemidirectProduct.mul_left, SemidirectProduct.mul_left, SemidirectProduct.left_inl,
    SemidirectProduct.left_inl, SemidirectProduct.right_inl, sgnAct_one, SemidirectProduct.mul_right,
    SemidirectProduct.right_inl, hg, mul_one, sgnAct_one]

open Matrix in
private theorem matIrr_conj {G R : Type} [Group G] [CommRing R] {m : ℕ} {U : Subgroup G}
    {a a' : G → Matrix (Fin m) (Fin m) R} (h : GL (Fin m) R)
    (e : ∀ g ∈ U, a g = ((h⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) * a' g * h) (H : MatIrr U a) :
    MatIrr U a' :=
  _root_.UpperTheory.Reformulated.B.Qf5.matIrr_conj h e H

private theorem att_iso {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] {k : ℕ} {ι : Qbar l ≃+* ℂ}
    {f : Af.Newform k} {r r' : G ℚ Ω →* GL (Fin 2) (Qbar l)} (h : Af.RepIso r r') (H : f.Att ι r) : f.Att ι r' := by
  obtain ⟨g, hg⟩ := h
  refine ⟨ss_conj g hg H.1, H.2.mono fun w hw A hA => ⟨fun s hs => ?_, fun σ hσ => ?_⟩⟩
  · rw [hg, (hw A hA).1 s hs, mul_one, mul_inv_cancel]
  · rw [← (hw A hA).2 σ hσ, hg, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]

private def dg {R : Type} [CommRing R] (t : Rˣ) : GL (Fin 2) R where
  val := Matrix.diagonal ![(t : R), ((t⁻¹ : Rˣ) : R)]
  inv := Matrix.diagonal ![((t⁻¹ : Rˣ) : R), (t : R)]
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; fin_cases i <;> simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; fin_cases i <;> simp

private theorem corner_conj {G R : Type} [Group G] [CommRing R] (r : G →* GG (m := 3) (R := R)) (t : Rˣ) (g : G) :
    corner (conjBy (tor R t) r g).mat =
      (dg t : Matrix (Fin 2) (Fin 2) R) * corner (r g).mat * (((dg t)⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) := by
  ext a b
  show _ = (Matrix.diagonal ![(t : R), ((t⁻¹ : Rˣ) : R)] * corner (r g).mat *
    Matrix.diagonal ![((t⁻¹ : Rˣ) : R), (t : R)] : Matrix (Fin 2) (Fin 2) R) a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, corner, corner, Matrix.submatrix_apply, Matrix.submatrix_apply,
    (conjBy_tor r t).1, wt, zpow_sub, Units.val_mul, mul_right_comm]
  congr 1
  · congr 1
    fin_cases a <;> simp [wt1]
  · fin_cases b <;> simp [wt1]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.HostFrameEx
section
noncomputable section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Aut
open scoped Pointwise

namespace UpperTheory.V.Pr

variable (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]

def upl (L : Type) [Field L] [NumberField L] [Algebra L Ω] : Subgroup (G ℚ Ω) where
  carrier := {s | ∀ x ∈ maximalRealSubfield L, s (algebraMap L Ω x) = algebraMap L Ω x}
  one_mem' _ _ := rfl
  mul_mem' {a b} ha hb x hx := by rw [AlgEquiv.mul_apply, hb x hx, ha x hx]
  inv_mem' {a} ha x hx := a.symm_apply_eq.2 (ha x hx).symm

variable {Ω} {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O]

structure GalLink (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ)
    (L : Type) [Field L] [NumberField L] [Algebra L Ω] (Φ : Fr.Frame l (ResidueField O)) where
  ab : IsAbelianGalois ℚ L
  gal : galOf ℚ L Ω = upl Ω L ⊓ η.ker
  unr : ∀ B' : ValuationSubring Ω, Ine (F := ℚ) B' ⊓ upl Ω L ≤ η.ker
  split : ∀ B' : ValuationSubring Ω, B'.valuation (M : Ω) < 1 → Dec (F := ℚ) B' ⊓ upl Ω L ≤ η.ker
  teich : ∀ B' : ValuationSubring Ω, ¬ B'.valuation (l : Ω) < 1 → ∀ s ∈ Ine (F := ℚ) B' ⊓ upl Ω L,
    barChar O Ψ s = 1 → Ψ s = 1
  p : upl Ω L →* Φ.Γ
  p_cont : Continuous p
  p_surj : Function.Surjective p
  p_ker : p.ker = (Subgroup.normalClosure {s : upl Ω L | ∃ B' : ValuationSubring Ω, ¬ B'.valuation (l : Ω) < 1 ∧
    s.1 ∈ Ine (F := ℚ) B' ∧ η s = 1 ∧ barChar O Ψ s = 1}).topologicalClosure
  del : ∀ s, Φ.del (p s) = η s
  eps : ∀ s, Φ.eps (p s) = cycZ ℚ Ω l s
  psi : ∀ s, Φ.Ψ (p s) = barChar O Ψ s
  c : ∃ h : σ ∈ upl Ω L, p ⟨σ, h⟩ = Φ.c
  g0 : ∃ h : g₁ ∈ upl Ω L, p ⟨g₁, h⟩ = Φ.g0
  pl : Φ.V → ValuationSubring Ω
  pl_conj : ∀ v, ∃ γ : G ℚ Ω, η γ = 1 ∧ pl v = γ • B
  pl_all : ∀ B' : ValuationSubring Ω, B'.valuation (l : Ω) < 1 → ∃! v, ∃ u ∈ upl Ω L, B' = u • pl v
  j : ∀ v, Φ.Gv v →* upl Ω L
  j_cont : ∀ v, Continuous (j v)
  j_inj : ∀ v, Function.Injective (j v)
  j_range : ∀ v (s : upl Ω L), s ∈ (j v).range ↔ s.1 ∈ Dec (F := ℚ) (pl v)
  j_loc : ∀ v g, Φ.loc v g = p (j v g)
  j_ine : ∀ v g, g ∈ Φ.Iv v ↔ (j v g).1 ∈ Ine (F := ℚ) (pl v)
  dv : ∀ v, Φ.dv v = (upl Ω L).relIndex (Dec (F := ℚ) (pl v))
  mu : ∀ v, ∃ g, cycMod ℚ Ω l 1 (j v g) ≠ 1

def GalLink.p0 {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
    {L : Type} [Field L] [NumberField L] [Algebra L Ω] {Φ : Fr.Frame l (ResidueField O)} (k : GalLink η Ψ σ g₁ B M L Φ)
    (s : G L Ω) : Φ.G0 :=
  have h : galEmb ℚ L Ω s ∈ upl Ω L ⊓ η.ker := k.gal ▸ galEmb_mem ℚ L Ω s
  ⟨k.p ⟨galEmb ℚ L Ω s, h.1⟩, (k.del _).trans h.2⟩

def SeedClause (c : Coef l) (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* c.Oˣ) (σ : G ℚ Ω) (L : Type) [Field L] [NumberField L] [Algebra L Ω] : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : Algebra K Ω) (N w : ℕ) (χ' η' θ : G ℚ Ω →* (Qbar l)ˣ) (j : ℕ),
    Sd.FieldPairCharacterTripleConditions K L σ N w χ' η' θ j ∧ χ' ≠ η' ∧ ¬ l ∣ orderOf χ' ∧ (∀ s, (η' s).val = (((η s).val : ℤ) : Qbar l)) ∧
    (∀ s, ‖((cycBar ℚ Ω l ^ j * χ') s).val - (Ψ s).val.1‖ < 1) ∧ ¬ (l : ℤ) ∣ discr K

def HasFrame (c : Coef l) [CharP (ResidueField c.O) l] (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* c.Oˣ) (σ : G ℚ Ω) (B : ValuationSubring Ω)
    (M : ℕ) : Prop :=
  ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : IsCMField L) (_ : Algebra L Ω) (g₁ : G ℚ Ω)
    (Φ : Fr.Frame l (ResidueField c.O)) (C₀ : ℕ), Nonempty (GalLink η Ψ σ g₁ B M L Φ) ∧ Φ.Ok C₀ ∧ Φ.Big C₀ ∧
      SeedClause c η Ψ σ L

def HostFrameEx : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) [CharP (ResidueField c.O) l]
    (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), UnitaryThreeInertia.HostData l e ψ o₁ →
  ∀ σ : G ℚ Ω, IsCC σ → ∀ B : ValuationSubring Ω, B.valuation (l : Ω) < 1 →
    HasFrame c (UnitaryThreeInertia.eta4 Ω) (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ B (l * N)

def GdFrameEx : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω]
    (l : ℕ) [Fact l.Prime] (c : Coef l) [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ)
    (ψ : DirichletCharacter c.O N) (D : Dat Ω K c e ψ) (B : ValuationSubring Ω), B.valuation (l : Ω) < 1 →
    HasFrame c D.η D.Ψ D.cc B (l * N * (discr K).natAbs)

end UpperTheory.V.Pr

end
end

