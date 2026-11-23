module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HasConductorMulShift
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0025

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointOperatorIdentities
section
open ValuativeRel Matrix IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.AdjointOperatorIdentities

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Notions
variable {n : Type}

def KeepsFinite (A : Module.End ℂ (Form k n ℂ)) : Prop :=
  ∀ φ : Form k n ℂ, (Function.support φ).Finite → (Function.support (A φ)).Finite

def IsScaledUnitaryOn (W : Submodule ℂ (Form k n ℂ)) (a : ℂ) (A : Module.End ℂ (Form k n ℂ)) : Prop :=
  Set.BijOn A {φ | φ ∈ W ∧ (Function.support φ).Finite} {φ | φ ∈ W ∧ (Function.support φ).Finite} ∧
    ∀ φ ∈ W, ∀ φ' ∈ W, (Function.support φ).Finite → (Function.support φ').Finite →
      cntIp (A φ) (A φ') = a * cntIp φ φ'

def IsUnitStable {V : Type} [AddCommGroup V] [Module 𝓀[k] V] (S : Finset {x : V // x ≠ 0}) : Prop :=
  ∀ (c : 𝓀[k]ˣ) (x y : {x : V // x ≠ 0}), x ∈ S → y.1 = (c : 𝓀[k]) • x.1 → y ∈ S

end Notions


variable (k) in
structure Vanishing (n : Type) [Fintype n] [DecidableEq n] (M : Type) [AddCommGroup M] [Module ℂ M] (ϖ : Unif k) :
    Prop where

  trLat_eq_zero : ∀ φ ∈ Mram k n M, ∀ (L : Submodule 𝒪[k] (n → k)) [L.IsFullLattice k], trLat L φ = 0

  trKer_eq_zero : ∀ φ ∈ Mram k n M, ∀ (L : Submodule 𝒪[k] (n → k)) [L.IsFullLattice k], trKer L φ = 0

  partial_lat : ∀ φ ∈ Mram k n M, ∀ (L : Submodule 𝒪[k] (n → k)) [L.IsFullLattice k]
    (S : Finset {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}), IsUnitStable (k := k) S → ∑ f ∈ S, φ (ofDual L f) = 0

  partial_ker : ∀ φ ∈ Mram k n M, ∀ (L : Submodule 𝒪[k] (n → k)) [L.IsFullLattice k]
    (S : Finset {x : Red L // x ≠ 0}), IsUnitStable (k := k) S → ∑ x ∈ S, φ (up L ϖ x) = 0

  invariant_eq_zero : ∀ (π : Representation ℂ (GL n k) M) (P : Pair k n) (v : levelVec π P),
    formOf π P v ∈ Mram k n M → ∀ (M' : Type) [AddCommGroup M'] [Module ℂ M'] (θ : M →ₗ[ℂ] M'),
    ((∀ g ∈ latStab P.lat, ∀ w, θ (π g w) = θ w) ∨ (∀ g ∈ latStab P.ker, ∀ w, θ (π g w) = θ w)) → θ v = 0


variable (k) in
structure OperatorIdentities (n : Type) [Fintype n] (M : Type) [AddCommGroup M] [Module ℂ M] (ϖ : Unif k)
    (χ : AddChar 𝓀[k] ℂ) : Prop where

  FFStar_formula : ∀ (φ : Form k n M) (L : Submodule 𝒪[k] (n → k)) [L.IsFullLattice k]
    [Fintype {x : Red L // x ≠ 0}]
    (f : {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}),
    FFStar ϖ χ φ (ofDual L f) = ∑ x : {x : Red L // x ≠ 0}, χ (-f.1 x.1) • φ (up L ϖ x)

  FFStar_mul_FF : (FFStar ϖ χ * FF ϖ χ : Module.End ℂ (Form k n M)) = ((resCard k : ℂ) ^ Fintype.card n) • 1 - tr

  FF_mul_FFStar : (FF ϖ χ * FFStar ϖ χ : Module.End ℂ (Form k n M)) = ((resCard k : ℂ) ^ Fintype.card n) • 1 - tr'

  FFStar_FF_ram : ∀ φ ∈ Mram k n M, FFStar ϖ χ (FF ϖ χ φ) = ((resCard k : ℂ) ^ Fintype.card n) • φ

  FF_FFStar_ram : ∀ φ ∈ Mram k n M, FF ϖ χ (FFStar ϖ χ φ) = ((resCard k : ℂ) ^ Fintype.card n) • φ

  FF_mem_ram : ∀ φ ∈ Mram k n M, FF ϖ χ φ ∈ Mram k n M

  FFStar_mem_ram : ∀ φ ∈ Mram k n M, FFStar ϖ χ φ ∈ Mram k n M

  D_dia : ∀ c : 𝓀[k]ˣ, (D ϖ * dia c : Module.End ℂ (Form k n M)) = dia c * D ϖ

  FF_dia : ∀ c : 𝓀[k]ˣ, (FF ϖ χ * dia c : Module.End ℂ (Form k n M)) = dia c * FF ϖ χ

  FF_eq_D_Gs : ∀ φ ∈ Mram k n M, FF ϖ χ φ = D ϖ (Gs χ φ)

  Gs_mul_GsStar : (Gs χ * GsStar χ : Module.End ℂ (Form k n M)) = (resCard k : ℂ) • 1 - Nm

  D_U_ram : ∀ φ ∈ Mram k n M, D ϖ (U ϖ φ) = ((resCard k : ℂ) ^ ((Fintype.card n : ℤ) - 1)) • φ

  U_D_ram : ∀ φ ∈ Mram k n M, U ϖ (D ϖ φ) = ((resCard k : ℂ) ^ ((Fintype.card n : ℤ) - 1)) • φ

  FFStar_dia : ∀ c : 𝓀[k]ˣ, (FFStar ϖ χ * dia c : Module.End ℂ (Form k n M)) = dia c * FFStar ϖ χ

  U_dia : ∀ c : 𝓀[k]ˣ, (U ϖ * dia c : Module.End ℂ (Form k n M)) = dia c * U ϖ

  dia_mem_ram : ∀ c : 𝓀[k]ˣ, ∀ φ ∈ Mram k n M, dia c φ ∈ Mram k n M

  phiOne_dia : ∀ (c : 𝓀[k]ˣ) (m : Type) [Fintype m] (P : Pair k n) (Q : Pair k m),
    phiOne (c • P) (c • Q) = phiOne P Q

  twisted_class_sum : ∀ (ε : 𝓀[k]ˣ) (φ : Form k n M) (L : Submodule 𝒪[k] (n → k)) [L.IsFullLattice k]
    [Fintype {x : Red L // x ≠ 0}] (f : {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}),
    ∑ x : {x : Red L // x ≠ 0}, χ (-((ε : 𝓀[k]) * f.1 x.1)) • φ (up L ϖ x) = dia ε (FFStar ϖ χ φ) (ofDual L f)

  sign_FFStar_sign_FF : (dia (-1) * FFStar ϖ χ * (dia (-1) * FF ϖ χ) : Module.End ℂ (Form k n M)) =
    FFStar ϖ χ * FF ϖ χ

  sign_ram : ∀ φ ∈ Mram k n M,
    dia (-1) (FFStar ϖ χ (dia (-1) (FF ϖ χ φ))) = ((resCard k : ℂ) ^ Fintype.card n) • φ

  unit_ram : ∀ c : 𝓀[k]ˣ, ∀ φ ∈ Mram k n M,
    dia c (FFStar ϖ χ (dia c⁻¹ (FF ϖ χ φ))) = ((resCard k : ℂ) ^ Fintype.card n) • φ


variable (k) in
structure AdjointIdentities (n : Type) [Fintype n] (ϖ : Unif k) (χ : AddChar 𝓀[k] ℂ) : Prop where

  FF_finite : KeepsFinite (n := n) (FF ϖ χ) ∧ KeepsFinite (n := n) (FFStar ϖ χ)

  D_finite : KeepsFinite (n := n) (D ϖ) ∧ KeepsFinite (n := n) (U ϖ)

  FF_adj : IsAdj (n := n) (FF ϖ χ) (FFStar ϖ χ)

  FF_unitary : IsScaledUnitaryOn (Mram k n ℂ) ((resCard k : ℂ) ^ Fintype.card n) (FF ϖ χ)

  Gs_adj : IsAdj (n := n) (Gs χ) (GsStar χ)

  U_adj : IsAdj (n := n) (U ϖ) (D ϖ)

  dia_adj : ∀ c : 𝓀[k]ˣ, IsAdj (n := n) (dia c) (dia c⁻¹)

  dia_unitary : ∀ c : 𝓀[k]ˣ, IsScaledUnitaryOn (n := n) ⊤ 1 (dia c) ∧ IsScaledUnitaryOn (Mram k n ℂ) 1 (dia c)

  sign_adj : IsAdj (n := n) (dia (-1) * FF ϖ χ) (dia (-1) * FFStar ϖ χ)

  sign_unitary : IsScaledUnitaryOn (Mram k n ℂ) ((resCard k : ℂ) ^ Fintype.card n) (dia (-1) * FF ϖ χ)

  unit_unitary : ∀ c : 𝓀[k]ˣ, IsAdj (n := n) (dia c⁻¹ * FF ϖ χ) (dia c * FFStar ϖ χ) ∧
    IsScaledUnitaryOn (Mram k n ℂ) ((resCard k : ℂ) ^ Fintype.card n) (dia c⁻¹ * FF ϖ χ)

def PairOperatorStatement : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ϖ : Unif k) (ψ : AddChar k Circle) (hψ : HasConductor ψ 1) (n : Type) [Fintype n] [DecidableEq n],
    (∀ (M : Type) [AddCommGroup M] [Module ℂ M],
      Vanishing k n M ϖ ∧ OperatorIdentities k n M ϖ (resChar ψ hψ ϖ)) ∧
    AdjointIdentities k n ϖ (resChar ψ hψ ϖ)

section Examples

end Examples

end GlobalTheory.IndefiniteRowSideFullHecke.AdjointOperatorIdentities
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FlagVolumeFiltration
section
open MeasureTheory ValuativeRel Matrix IsLocalRing
open scoped Pointwise NNReal ENNReal

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.FlagVolumeFiltration
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LatPair

section Objects
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} {c : ℕ}


variable (k n) in
def flagSub (c i : ℕ) : Submodule 𝒪[k] (n ⊕ Fin c → k) where
  carrier := {y | ∀ l : Fin c, i ≤ l.val → y (Sum.inr l) = 0}
  zero_mem' _ _ := rfl
  add_mem' h h' l hl := by simp [h l hl, h' l hl]
  smul_mem' s y h l hl := by simp [h l hl]

def latStep (L : Submodule 𝒪[k] (n ⊕ Fin c → k)) (i : ℕ) : Submodule 𝒪[k] (n ⊕ Fin c → k) :=
  L ⊓ flagSub k n c i

def interX (L : Submodule 𝒪[k] (n ⊕ Fin c → k)) : Submodule 𝒪[k] (n → k) :=
  L.comap (GlobalTheory.LatPair.inX k n c)

def flagIn (c i : ℕ) (y : n ⊕ Fin i → k) : n ⊕ Fin c → k :=
  Sum.elim (fun r => y (Sum.inl r)) fun l => if h : l.val < i then y (Sum.inr ⟨l.val, h⟩) else 0

variable [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

def InCoset (L₀ : Submodule 𝒪[k] (n ⊕ Fin c → k)) (h₀ h : GL (n ⊕ Fin c) k) : Prop :=
  ∃ r ∈ R k n c 1, ∃ κ ∈ latStab L₀, h = r * h₀ * κ

variable [MeasurableSpace k] [BorelSpace k]

end Objects

section Statements
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (q : Unif k)

def DatumTranslate : Prop :=
  ∀ (μ : kˣ →* ℂˣ) (P : Pair k n') (L'₀ : Submodule 𝒪[k] (n' ⊕ Fin (c + 1) → k)) [L'₀.IsLattice k]
    (L₀ L : Submodule 𝒪[k] (n ⊕ Fin c → k)) [L₀.IsLattice k] (h' : GL (n' ⊕ Fin (c + 1)) k) (h : GL (n ⊕ Fin c) k),
    h' • L'₀ = GlobalTheory.LatPair.gluedS q (c + 1) P.ker P.vec → h • L₀ = L → ∀ x,
      GlobalTheory.LatPair.latInd (GlobalTheory.LatPair.gluedS q (c + 1) P.ker P.vec) L x =
        (((μ (GeneralLinearGroup.det h'))⁻¹ : ℂˣ) : ℂ) * (μ (GeneralLinearGroup.det h) : ℂ) *
          ((nabs k (GeneralLinearGroup.det h') ^ (-((Fintype.card n : ℝ) + c) / 2) : ℝ) : ℂ) *
          ((nabs k (GeneralLinearGroup.det h) ^ (((Fintype.card n' : ℝ) + c + 1) / 2) : ℝ) : ℂ) *
          om μ h' h (GlobalTheory.LatPair.latInd L'₀ L₀) x

def OneOrbit : Prop :=
  (∀ (L₁ L₂ : Submodule 𝒪[k] (n → k)) (f₁ f₂ : n → k), IsGlue L₁ f₁ → IsGlue L₂ f₂ →
    ∃ g : GL n k, g • L₁ = L₂ ∧ g • f₁ - f₂ ∈ L₂) ∧
  ∀ (L₀ : Submodule 𝒪[k] (n ⊕ Fin c → k)) [L₀.IsLattice k] (Q : Pair k n) (h₀ : GL (n ⊕ Fin c) k),
    h₀ • L₀ = GlobalTheory.LatPair.gluedS q c Q.ker Q.vec → ∀ h : GL (n ⊕ Fin c) k,
      (∃ u ∈ N k n c 1, ∃ (L'' : Submodule 𝒪[k] (n → k)) (f'' : n → k), IsGlue L'' f'' ∧
        h • L₀ = u • GlobalTheory.LatPair.gluedS q c L'' f'') ↔ InCoset L₀ h₀ h

variable [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k)


end Statements

section Examples
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type} {c : ℕ}

end Examples

end GlobalTheory.IndefiniteRowSideFullHecke.FlagVolumeFiltration
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IndicatorFunctionIdentity
section
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity
open GlobalTheory.SplitWeil GlobalTheory.LatPair

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

private lemma isOpen_stdLat : IsOpen (stdLat k n : Set (n → k)) := by
  have e : (stdLat k n : Set (n → k)) = Set.univ.pi fun _ => (𝒪[k] : Set k) := by
    ext x
    simp [mem_stdLat]
  rw [e]
  exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_int k

theorem isOpen_lat (L : Submodule 𝒪[k] (n → k)) [L.IsFullLattice k] : IsOpen (L : Set (n → k)) := by
  obtain ⟨g, rfl⟩ := exists_smul_lat (stdLat k n) L
  have e : ((g • stdLat k n : Submodule 𝒪[k] (n → k)) : Set (n → k)) =
      (fun x => (g⁻¹ : GL n k).val *ᵥ x) ⁻¹' (stdLat k n : Set (n → k)) := by
    ext x
    exact mem_smul_iff
  rw [e]
  exact isOpen_stdLat.preimage (Continuous.matrix_mulVec continuous_const continuous_id)

theorem maps_std_iff (x : Matrix n n' k) :
    (∀ y ∈ stdLat k n', x *ᵥ y ∈ stdLat k n) ↔ ∀ i j, x i j ∈ 𝒪[k] := by
  constructor
  · intro H i j
    have h1 : (Pi.single j 1 : n' → k) ∈ stdLat k n' := by
      rw [mem_stdLat]
      intro l
      rw [Pi.single_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    have h2 := mem_stdLat.1 (H _ h1) i
    simpa [Matrix.mulVec_single_one] using h2
  · intro H y hy
    rw [mem_stdLat] at hy ⊢
    intro i
    simp only [Matrix.mulVec, dotProduct]
    exact sum_mem fun j _ => mul_mem (H i j) (hy j)

theorem maps_smul_iff (g : GL n' k) (h : GL n k) (S : Submodule 𝒪[k] (n' → k)) (L : Submodule 𝒪[k] (n → k))
    (x : Matrix n n' k) :
    (∀ y ∈ g • S, x *ᵥ y ∈ h • L) ↔ ∀ y ∈ S, ((h⁻¹ : GL n k).val * x * g.val) *ᵥ y ∈ L := by
  have key : ∀ y : n' → k, ((h⁻¹ : GL n k).val * x * g.val) *ᵥ y = (h⁻¹ : GL n k) • (x *ᵥ (g • y)) := by
    intro y
    simp only [Units.smul_def, Matrix.smul_eq_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  constructor
  · intro H y hy
    rw [key, ← mem_smul_iff]
    exact H _ (Submodule.smul_mem_pointwise_smul y g S hy)
  · intro H y hy
    rw [mem_smul_iff] at hy ⊢
    have h1 := H _ hy
    rw [key, smul_inv_smul] at h1
    exact h1

private lemma isCompact_isOpen_isClosed_integral_matrices : IsCompact {x : Matrix n n' k | ∀ i j, x i j ∈ 𝒪[k]} ∧
    IsOpen {x : Matrix n n' k | ∀ i j, x i j ∈ 𝒪[k]} ∧ IsClosed {x : Matrix n n' k | ∀ i j, x i j ∈ 𝒪[k]} := by
  have e : {x : Matrix n n' k | ∀ i j, x i j ∈ 𝒪[k]} =
      Set.univ.pi fun _ : n => Set.univ.pi fun _ : n' => (𝒪[k] : Set k) := by
    ext x
    exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩
  have hc : IsClosed (𝒪[k] : Set k) := (𝒪[k]).toAddSubgroup.isClosed_of_isOpen (isOpen_int k)
  rw [e]
  exact ⟨isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_int k,
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => isOpen_int k,
    isClosed_set_pi fun _ _ => isClosed_set_pi fun _ _ => hc⟩

private lemma exists_sideMul_preimage_integral (S : Submodule 𝒪[k] (n' → k)) (L : Submodule 𝒪[k] (n → k))
    [S.IsFullLattice k] [L.IsFullLattice k] : ∃ (g : GL n' k) (h : GL n k), {x : Matrix n n' k | ∀ y ∈ S, x *ᵥ y ∈ L} =
      (sideMul g h) ⁻¹' {x : Matrix n n' k | ∀ i j, x i j ∈ 𝒪[k]} := by
  obtain ⟨g, rfl⟩ := exists_smul_lat (stdLat k n') S
  obtain ⟨h, rfl⟩ := exists_smul_lat (stdLat k n) L
  refine ⟨g, h, ?_⟩
  ext x
  change (∀ y ∈ g • stdLat k n', x *ᵥ y ∈ h • stdLat k n) ↔
    ∀ i j, ((h⁻¹ : GL n k).val * x * g.val) i j ∈ 𝒪[k]
  rw [maps_smul_iff, maps_std_iff]

theorem hom_lat (S : Submodule 𝒪[k] (n' → k)) (L : Submodule 𝒪[k] (n → k)) [S.IsFullLattice k] [L.IsFullLattice k] :
    IsCompact {x : Matrix n n' k | ∀ y ∈ S, x *ᵥ y ∈ L} ∧ IsOpen {x : Matrix n n' k | ∀ y ∈ S, x *ᵥ y ∈ L} := by
  obtain ⟨g, h, e⟩ := exists_sideMul_preimage_integral S L
  rw [e]
  exact ⟨(sideMul g h).isCompact_preimage.2 isCompact_isOpen_isClosed_integral_matrices.1, isCompact_isOpen_isClosed_integral_matrices.2.1.preimage (sideMul g h).continuous⟩

private lemma phiOne_congr_of_sub_mulVec_mem_ker {P : Pair k n'} {Q : Pair k n} {x z : Matrix n n' k}
    (hz : ∀ y ∈ P.lat, (z - x) *ᵥ y ∈ Q.ker) : phiOne P Q z = phiOne P Q x := by
  have key : Maps P Q z ↔ Maps P Q x := by
    rw [maps_iff_hasVal, maps_iff_hasVal]
    refine forall_congr' fun y => forall_congr' fun a => imp_congr_right fun hy => ?_
    have hd : Q.HasVal ((z - x) *ᵥ y) 0 := Pair.mem_ker.1 (hz y hy.mem)
    rw [Matrix.sub_mulVec] at hd
    constructor
    · intro h1
      simpa using h1.sub hd
    · intro h1
      simpa using h1.add hd
  unfold phiOne
  by_cases hx : Maps P Q x
  · rw [if_pos (key.2 hx), if_pos hx]
  · rw [if_neg (mt key.1 hx), if_neg hx]

private lemma isClosed_setOf_mulVec_mem (S : Submodule 𝒪[k] (n' → k)) (L : Submodule 𝒪[k] (n → k))
    [S.IsFullLattice k] [L.IsFullLattice k] : IsClosed {x : Matrix n n' k | ∀ y ∈ S, x *ᵥ y ∈ L} := by
  obtain ⟨g, h, e⟩ := exists_sideMul_preimage_integral S L
  rw [e]
  exact isCompact_isOpen_isClosed_integral_matrices.2.2.preimage (sideMul g h).continuous

theorem phiOne_mem (P : Pair k n') (Q : Pair k n) : phiOne P Q ∈ SB (Matrix n n' k) := by
  change IsLocallyConstant (phiOne P Q) ∧ HasCompactSupport (phiOne P Q)
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hH0 : {d : Matrix n n' k | ∀ y ∈ P.lat, d *ᵥ y ∈ Q.ker} ∈ nhds (0 : Matrix n n' k) := by
      refine (hom_lat P.lat Q.ker).2.mem_nhds ?_
      intro y _
      rw [Matrix.zero_mulVec]
      exact zero_mem _
    have ht : Filter.Tendsto (fun z : Matrix n n' k => z - x) (nhds x) (nhds 0) := by
      simpa using (continuous_sub_right x).tendsto x
    filter_upwards [ht hH0] with z hz
    exact phiOne_congr_of_sub_mulVec_mem_ker hz
  · refine HasCompactSupport.intro' (hom_lat P.lat Q.lat).1 (isClosed_setOf_mulVec_mem P.lat Q.lat) fun x hx => ?_
    unfold phiOne
    rw [if_neg]
    rintro ⟨hm, -⟩
    exact hx hm

def phiOneSB (P : Pair k n') (Q : Pair k n) : SB (Matrix n n' k) := ⟨phiOne P Q, phiOne_mem P Q⟩

private lemma det_mem_of_integral_entries {u : GL n k} (hu : ∀ i j, u.val i j ∈ 𝒪[k]) : u.val.det ∈ 𝒪[k] := by
  let M : Matrix n n 𝒪[k] := fun i j => ⟨u.val i j, hu i j⟩
  have e : u.val = (𝒪[k]).subtype.mapMatrix M := by
    ext i j
    rfl
  rw [e, ← RingHom.map_det]
  exact (M.det).2

theorem valuation_det_of_fix (L : Submodule 𝒪[k] (n → k)) [L.IsFullLattice k] {h : GL n k} (hh : h • L = L) :
    valuation k ((Matrix.GeneralLinearGroup.det h : kˣ) : k) = 1 := by
  obtain ⟨g, rfl⟩ := exists_smul_lat (stdLat k n) L
  obtain ⟨u, hu⟩ : ∃ u : GL n k, u = g⁻¹ * h * g := ⟨_, rfl⟩
  have hfix : u • stdLat k n = stdLat k n := by
    rw [hu, mul_smul, mul_smul, hh, inv_smul_smul]
  have hint : ∀ w : GL n k, w • stdLat k n = stdLat k n → ∀ i j, w.val i j ∈ 𝒪[k] := by
    intro w hw
    refine (maps_std_iff w.val).1 ?_
    intro y hy
    have h1 : w • y ∈ w • stdLat k n := Submodule.smul_mem_pointwise_smul y w _ hy
    rw [hw] at h1
    exact h1
  have h1 := det_mem_of_integral_entries (hint u hfix)
  have h2 := det_mem_of_integral_entries (hint u⁻¹ (by rw [inv_smul_eq_iff, hfix]))
  have hdet : Matrix.GeneralLinearGroup.det u = Matrix.GeneralLinearGroup.det h := by
    rw [hu, map_mul, map_mul, map_inv, mul_comm _ (Matrix.GeneralLinearGroup.det g), mul_inv_cancel_left]
  rw [← hdet, Matrix.GeneralLinearGroup.val_det_apply]
  have hp : u.val.det * (u⁻¹ : GL n k).val.det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have v1 := (Valuation.mem_integer_iff _ _).1 h1
  have v2 := (Valuation.mem_integer_iff _ _).1 h2
  have v3 : valuation k u.val.det * valuation k (u⁻¹ : GL n k).val.det = 1 := by
    rw [← map_mul, hp, map_one]
  refine le_antisymm v1 ?_
  calc (1 : ValueGroupWithZero k) = valuation k u.val.det * valuation k (u⁻¹ : GL n k).val.det := v3.symm
    _ ≤ valuation k u.val.det * 1 := by gcongr
    _ = valuation k u.val.det := mul_one _

variable {V' V : Type} [AddCommGroup V'] [Module ℂ V'] [AddCommGroup V] [Module ℂ V]

def IsEquivTheta (μ : kˣ →* ℂˣ) (π' : Representation ℂ (GL n' k) V') (π : Representation ℂ (GL n k) V)
    (θ : V' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] V) : Prop :=
  ∀ (g : GL n' k) (h : GL n k) (v : V') (Ψ Ψ' : SB (Matrix n n' k)),
    Ψ'.1 = om μ g h Ψ.1 → θ (π' g v) Ψ' = π h (θ v Ψ)

variable {μ : kˣ →* ℂˣ} {π' : Representation ℂ (GL n' k) V'} {π : Representation ℂ (GL n k) V}
  {θ : V' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] V}

theorem theta_mem (hμ : IsUnram μ) (hθ : IsEquivTheta μ π' π θ) (P₀ : Pair k n') (Q₀ : Pair k n) (v : V') :
    θ v (phiOneSB P₀ Q₀) ∈ levelVec π Q₀ := by
  change ∀ h : GL n k, h • Q₀ = Q₀ → π h (θ v (phiOneSB P₀ Q₀)) = θ v (phiOneSB P₀ Q₀)
  intro h hh
  have hv : valuation k ((Matrix.GeneralLinearGroup.det h : kˣ) : k) = 1 :=
    valuation_det_of_fix Q₀.lat (by rw [← Pair.smul_lat, hh])
  have hfun : (phiOneSB P₀ Q₀).1 = om μ 1 h (phiOneSB P₀ Q₀).1 := by
    funext x
    have e1 : phiOne P₀ Q₀ x = phiOne P₀ Q₀ ((h⁻¹ : GL n k).val * x * (1 : GL n' k).val) := by
      rw [← phiOne_smul (1 : GL n' k) h, one_smul, hh]
    change phiOne P₀ Q₀ x = om μ 1 h (phiOne P₀ Q₀) x
    rw [e1]
    simp only [om, map_one, Units.val_one, hμ _ hv, inv_one, nabs_one, nabs_eq_one_of_valuation_eq_one hv,
      Real.one_rpow, Complex.ofReal_one, one_mul]
  have h1 := hθ 1 h v _ _ hfun
  simpa using h1.symm

def kerVec (hμ : IsUnram μ) (hθ : IsEquivTheta μ π' π θ) (P₀ : Pair k n') (Q₀ : Pair k n) :
    levelVec π' P₀ →ₗ[ℂ] levelVec π Q₀ :=
  LinearMap.codRestrict _ (θ.flip (phiOneSB P₀ Q₀) ∘ₗ (levelVec π' P₀).subtype)
    fun v => theta_mem hμ hθ P₀ Q₀ v.1

def K (hμ : IsUnram μ) (hθ : IsEquivTheta μ π' π θ) (P₀ : Pair k n') (Q₀ : Pair k n) :
    EqForm π' →ₗ[ℂ] EqForm π :=
  (evalEquiv π Q₀).symm.toLinearMap ∘ₗ kerVec hμ hθ P₀ Q₀ ∘ₗ (evalEquiv π' P₀).toLinearMap

theorem K_apply (hμ : IsUnram μ) (hθ : IsEquivTheta μ π' π θ) (P₀ : Pair k n') (Q₀ : Pair k n) (φ : EqForm π')
    (h : GL n k) : (K hμ hθ P₀ Q₀ φ).1 (h • Q₀) = π h (θ (φ.1 P₀) (phiOneSB P₀ Q₀)) := by
  change formOf π Q₀ (kerVec hμ hθ P₀ Q₀ (evalEquiv π' P₀ φ)) (h • Q₀) = _
  rw [formOf_smul]
  rfl


open Classical in
def midInd (q : Unif k) (L : Submodule 𝒪[k] (n' → k)) (e₁ : n' → k) (Q : Pair k n) (x : Matrix n n' k) : ℂ :=
  if (∀ y ∈ L, x *ᵥ y ∈ Q.lat) ∧ Q.HasVal (x *ᵥ (q.1 • e₁)) 1 then 1 else 0


def scal (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) : ℂ :=
  (((resCard k : ℝ) ^ (((t : ℝ) + 1) / 2) : ℝ) : ℂ)

end GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity
end
end

