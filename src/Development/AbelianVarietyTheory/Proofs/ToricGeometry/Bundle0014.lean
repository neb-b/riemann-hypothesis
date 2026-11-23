module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsAppellHumbertFrameIsRig
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory

namespace OriginFrame

def ValRules : Prop :=
  ∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)

theorem rigVal_ne_zero (hv : ValRules) {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (s : Γ(X, U)ˣ) : valAt' x U s.val ≠ 0 := by
  intro h0
  obtain ⟨e, he⟩ := (hv X x).2.1 U h
  have key := congrArg e s.val_inv
  rw [map_mul, map_one, ← he, h0, zero_mul] at key
  exact zero_ne_one key

theorem rigChart_iff {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (L : LB X) (j : (L.pull x).ι) :
    ⊤ ≤ (L.pull x).U j ↔ ⊤ ≤ x ⁻¹ᵁ L.U (j PUnit.unit) := by
  delta LB.pull LB.LinComb LB.wchart
  constructor
  · intro h p _
    exact Set.mem_iInter.mp (h trivial) PUnit.unit
  · intro h p hp
    exact Set.mem_iInter.mpr (fun k => by cases k; exact h hp)

theorem rigVal_compat (hv : ValRules) {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (L : LB X)
    (rig : LB.Gen (L.pull x)) (hr : rig.IsGen) (j j' : (L.pull x).ι)
    (hj : ⊤ ≤ (L.pull x).U j) (hj' : ⊤ ≤ (L.pull x).U j') :
    valAt' (𝟙 (Sp ℂ)) ((L.pull x).U j) (rig.s j).val =
      valAt' x (L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit)) (L.g (j PUnit.unit) (j' PUnit.unit)).val *
        valAt' (𝟙 (Sp ℂ)) ((L.pull x).U j') (rig.s j').val := by
  unfold LB.Gen.IsGen at hr
  obtain ⟨hle, hg⟩ : ∃ hle : (L.pull x).U j ⊓ (L.pull x).U j' ≤ x ⁻¹ᵁ (L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit)),
      (L.pull x).g j j' = res hle (pullU x _ (L.g (j PUnit.unit) (j' PUnit.unit))) := by
    delta LB.pull LB.LinComb
    dsimp only
    rw [Fintype.prod_unique, zpow_one]
    exact ⟨_, rfl⟩
  have hJ : ⊤ ≤ (𝟙 (Sp ℂ)) ⁻¹ᵁ ((L.pull x).U j ⊓ (L.pull x).U j') := by
    exact le_inf hj hj'
  obtain ⟨e, he⟩ := (hv (Sp ℂ) (𝟙 _)).2.1 _ hJ
  have hrj := congrArg (fun u => e (Units.val u)) (hr j j')
  rw [hg] at hrj
  rw [Units.val_mul, map_mul] at hrj
  simp only [← he] at hrj
  have eres : ∀ {U W : (Sp ℂ).Opens} (hh : W ≤ U) (u : (Γ(Sp ℂ, U))ˣ),
      ((res hh u : (Γ(Sp ℂ, W))ˣ) : Γ(Sp ℂ, W)) = resG (Sp ℂ) hh (u : Γ(Sp ℂ, U)) := fun _ _ => rfl
  have epu : ∀ (W : X.Opens) (u : (Γ(X, W))ˣ),
      ((pullU x W u : (Γ(Sp ℂ, x ⁻¹ᵁ W))ˣ) : Γ(Sp ℂ, x ⁻¹ᵁ W)) = (x.app W).hom (u : Γ(X, W)) := fun _ _ => rfl
  have r3 := fun U h f => (hv (Sp ℂ) (𝟙 (Sp ℂ))).2.2.1 U ((L.pull x).U j ⊓ (L.pull x).U j') h f hJ
  simp only [eres, epu, r3] at hrj
  rw [(hv (Sp ℂ) (𝟙 _)).2.2.2.1 X x, Category.id_comp] at hrj
  exact hrj

end OriginFrame


open OriginFrame in
theorem exists_appellHumbert_frame_isRig :
    Out.CubeSt → (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default
        : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X,
        U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X,
        U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ
        : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫
        φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X,
        U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U
        : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) → (∀ (A : Over (Sp
        ℂ)) [GrpObj A] [IsCommMonObj A] (L₀ L : LB A.left) (g : ℕ) (u
        : HolUnif A L₀ g), L.IsLB → ∀ t : LB.Gen (Theta A L), t.IsGen → ∀ (W : L.ι → Set (Fin g →
        ℂ)) (c : L.ι → L.ι → (Fin g → ℂ) → ℂ), W = (fun (i : L.ι) => {z : Fin g → ℂ | ⊤ ≤ (u.ex
        z).left ⁻¹ᵁ L.U i}) → c = (fun (i j : L.ι) (z : Fin g → ℂ) => valAt' (u.ex z).left (L.U i ⊓
        L.U j) (L.g i j).val) → ((∀ i, IsOpen (W i)) ∧ (∀ z, ∃ i, z ∈ W i) ∧
        (∀ i j, DifferentiableOn ℂ (c i j) (W i ∩ W j)) ∧ (∀ i j z, z ∈ W i → z ∈ W j → c i j z ≠ 0)
        ∧ (∀ i j k z, z ∈ W i → z ∈ W j → z ∈ W k → c i j z * c j k z = c i k z) ∧
        (∀ i z, ∀ l ∈ u.Λ, z + l ∈ W i ↔ z ∈ W i) ∧ (∀ i j z, ∀ l ∈ u.Λ, c i j (z +
        l) = c i j z)) ∧ ∃ T : (Finset (Fin 3) → L.ι) → (Fin 3 → Fin g →
        ℂ) → ℂ, (∀ j, DifferentiableOn ℂ (T j) {x | (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j
        I))}) ∧ (∀ j x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j
        I)) → T j x ≠ 0) ∧ (∀ j j' x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j
        I)) → (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j' I)) → T j x = (∏ I : Finset (Fin 3), c (j
        I) (j' I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) * T j' x) ∧ (∀ j x (l
        : Fin 3 → Fin g → ℂ), (∀ a, l a ∈ u.Λ) → T j (x + l) = T j x)) → (∀ (g : ℕ) {J : Type} (W
        : J → Set (Fin g → ℂ)) (c : J → J → (Fin g → ℂ) → ℂ), (∀ i, IsOpen (W
        i)) → (∀ z, ∃ i, z ∈ W i) → (∀ i j, DifferentiableOn ℂ (c i j) (W i ∩ W
        j)) → (∀ i j z, z ∈ W i → z ∈ W j → c i j z ≠ 0) → (∀ i j k z, z ∈ W i → z ∈ W j → z ∈ W k → c i j z * c j k z = c i k z) → ∀ (T
        : (Finset (Fin 3) → J) → (Fin 3 → Fin g → ℂ) → ℂ), (∀ j, DifferentiableOn ℂ (T j) {x
        | (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I))}) → (∀ j x, (∀ I : Finset (Fin
        3), ∑ a ∈ I, x a ∈ W (j I)) → T j x ≠ 0) → (∀ j j' x, (∀ I : Finset (Fin
        3), ∑ a ∈ I, x a ∈ W (j I)) → (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j'
        I)) → T j x = (∏ I : Finset (Fin 3), c (j I) (j' I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 -
        I.card))) * T j' x) → ∀ (Λ : Submodule ℤ (Fin g →
        ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g →
        ℂ)) = ⊤ → (∀ i z, ∀ l ∈ Λ, z + l ∈ W i ↔ z ∈ W i) → (∀ i j z, ∀ l ∈ Λ, c i j (z +
        l) = c i j z) → (∀ j x (l : Fin 3 → Fin g → ℂ), (∀ a, l a ∈ Λ) → T j (x + l) = T j x) → ∃ (r
        : ℝ) (fr : J → (Fin g → ℂ) → ℂ) (κ : ℂ), 0 < r ∧ ((∀ i, DifferentiableOn ℂ (fr i) (W i ∩
        Metric.ball 0 r)) ∧ (∀ i z, z ∈ W i → z ∈ Metric.ball 0 r → fr i z ≠ 0) ∧
        (∀ i j z, z ∈ W i → z ∈ W j → z ∈ Metric.ball 0 r → fr i z = c i j z * fr j z)) ∧ ∀ᶠ x in 𝓝 (0
        : Fin 3 → Fin g → ℂ), ∀ j, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j
        I)) → T j x = κ * ∏ I : Finset (Fin 3), fr (j I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 -
        I.card))) → (∀ (g : ℕ) {J : Type} (W : J → Set (Fin g → ℂ)) (c : J → J → (Fin g →
        ℂ) → ℂ), (∀ i, IsOpen (W i)) → (∀ z, ∃ i, z ∈ W i) → (∀ i j, DifferentiableOn ℂ (c i j) (W i
        ∩ W
        j)) → (∀ i j z, z ∈ W i → z ∈ W j → c i j z ≠ 0) → (∀ i j k z, z ∈ W i → z ∈ W j → z ∈ W k → c i j z * c j k z = c i k z) → ∀ (T
        : (Finset (Fin 3) → J) → (Fin 3 → Fin g → ℂ) → ℂ), (∀ j, DifferentiableOn ℂ (T j) {x
        | (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I))}) → (∀ j x, (∀ I : Finset (Fin
        3), ∑ a ∈ I, x a ∈ W (j I)) → T j x ≠ 0) → (∀ j j' x, (∀ I : Finset (Fin
        3), ∑ a ∈ I, x a ∈ W (j I)) → (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j'
        I)) → T j x = (∏ I : Finset (Fin 3), c (j I) (j' I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 -
        I.card))) * T j' x) → (∃ (r : ℝ) (fr : J → (Fin g → ℂ) → ℂ) (κ
        : ℂ), 0 < r ∧ ((∀ i, DifferentiableOn ℂ (fr i) (W i ∩ Metric.ball 0 r)) ∧
        (∀ i z, z ∈ W i → z ∈ Metric.ball 0 r → fr i z ≠ 0) ∧
        (∀ i j z, z ∈ W i → z ∈ W j → z ∈ Metric.ball 0 r → fr i z = c i j z * fr j z)) ∧ ∀ᶠ x in 𝓝 (0
        : Fin 3 → Fin g → ℂ), ∀ j, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j
        I)) → T j x = κ * ∏ I : Finset (Fin 3), fr (j I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 -
        I.card))) → ∃ (fr : J → (Fin g → ℂ) → ℂ) (κ : ℂ), ((∀ i, DifferentiableOn ℂ (fr i) (W i ∩
        Set.univ)) ∧ (∀ i z, z ∈ W i → z ∈ Set.univ → fr i z ≠ 0) ∧
        (∀ i j z, z ∈ W i → z ∈ W j → z ∈ Set.univ → fr i z = c i j z * fr j z)) ∧ ∀ j x, (∀ I : Finset (Fin
        3), ∑ a ∈ I, x a ∈ W (j I)) → T j x = κ * ∏ I : Finset (Fin 3), fr (j
        I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) → (∀ (g : ℕ) {J : Type} (W : J → Set (Fin g →
        ℂ)) (c : J → J → (Fin g → ℂ) → ℂ), (∀ i, IsOpen (W
        i)) → (∀ z, ∃ i, z ∈ W i) → (∀ i j, DifferentiableOn ℂ (c i j) (W i ∩ W
        j)) → (∀ i j z, z ∈ W i → z ∈ W j → c i j z ≠ 0) → (∀ i j k z, z ∈ W i → z ∈ W j → z ∈ W k → c i j z * c j k z = c i k z) → ∀ (T
        : (Finset (Fin 3) → J) → (Fin 3 → Fin g → ℂ) → ℂ), (∀ j, DifferentiableOn ℂ (T j) {x
        | (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I))}) → (∀ j x, (∀ I : Finset (Fin
        3), ∑ a ∈ I, x a ∈ W (j I)) → T j x ≠ 0) → (∀ j j' x, (∀ I : Finset (Fin
        3), ∑ a ∈ I, x a ∈ W (j I)) → (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j'
        I)) → T j x = (∏ I : Finset (Fin 3), c (j I) (j' I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 -
        I.card))) * T j' x) → ∀ (Λ : Submodule ℤ (Fin g →
        ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g →
        ℂ)) = ⊤ → (∀ i z, ∀ l ∈ Λ, z + l ∈ W i ↔ z ∈ W i) → (∀ i j z, ∀ l ∈ Λ, c i j (z +
        l) = c i j z) → (∀ j x (l : Fin 3 → Fin g → ℂ), (∀ a, l a ∈ Λ) → T j (x +
        l) = T j x) → ∀ (fr : J → (Fin g → ℂ) → ℂ) (κ : ℂ), ((∀ i, DifferentiableOn ℂ (fr i) (W i ∩
        Set.univ)) ∧ (∀ i z, z ∈ W i → z ∈ Set.univ → fr i z ≠ 0) ∧
        (∀ i j z, z ∈ W i → z ∈ W j → z ∈ Set.univ → fr i z = c i j z * fr j z)) → (∀ j x, (∀ I : Finset (Fin
        3), ∑ a ∈ I, x a ∈ W (j I)) → T j x = κ * ∏ I : Finset (Fin 3), fr (j
        I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) → ∃ (a : Λ → ℂ) (B : Λ →+ ((Fin g → ℂ) →ₗ[ℂ]
        ℂ)), (∀ l, a l ≠ 0) ∧ (∀ l m : Λ, a (l + m) = a l * a m * cexp (B l m)) ∧ ∀ (l
        : Λ) i z, z ∈ W i → fr i z = a l * cexp (B l z) * fr i (z + l)) → (∀ (g : ℕ) (Λ
        : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g →
        ℂ)) = ⊤ → ∀ (a : Λ → ℂ) (B : Λ →+ ((Fin g → ℂ) →ₗ[ℂ] ℂ)), (∀ l, a l ≠ 0) → (∀ l m : Λ, a (l
        + m) = a l * a m * cexp (B l m)) → ∃ (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ) (Ef
        : LinearMap.BilinForm ℤ Λ) (Q : (Fin g →
        ℂ) → ℂ), Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : Λ, (Ef l m : ℝ) = ((l : Fin g → ℂ) ⬝ᵥ
        Hm.mulVec (star (m : Fin g → ℂ))).im) ∧ Differentiable ℂ Q ∧ Q 0 = 0 ∧ ∀ (l
        : Λ) z, a l * cexp (B l z) * cexp (Q z - Q (z + l)) = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec
        (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l
        : Fin g → ℂ)))))) → (∀ (P : Out.PolAV (Sp ℂ)) (rig : LB.Gen (P.L.pull (eSec
        P.A))), rig.IsGen → ∀ u₀ : HolUnif P.A (⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩
        : LB P.A.left) P.g, ∃ (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ
        : u.Λ → ℂ) (Ef
        : LinearMap.BilinForm ℤ u.Λ), u.ex = u₀.ex ∧ u.IsRig rig ∧ Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ (∀ l m : u.Λ, (Ef
        l m : ℝ) = ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin P.g → ℂ))).im) ∧ ∀ (l
        : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U i → u.fr i z = (χ l * cexp (Real.pi * (z ⬝ᵥ
        Hm.mulVec (star (l : Fin P.g → ℂ))) + Real.pi / 2 * ((l : Fin P.g → ℂ) ⬝ᵥ Hm.mulVec (star (l
        : Fin P.g → ℂ))))) * u.fr i (z + l)) := by
  intro hCube hV hFrame hLoc hGlob hFact hNorm P rig hrig u₀
  have hLB : P.L.IsLB := P.7
  obtain ⟨cs⟩ := (hCube (Sp ℂ) P ⟨P.L, rig, hLB, hrig⟩ rfl).1
  obtain ⟨W, hW⟩ : ∃ W : P.L.ι → Set (Fin P.g → ℂ),
      W = fun i => {z | ⊤ ≤ (u₀.ex z).left ⁻¹ᵁ P.L.U i} := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : P.L.ι → P.L.ι → (Fin P.g → ℂ) → ℂ,
      c = fun i j z => valAt' (u₀.ex z).left (P.L.U i ⊓ P.L.U j) (P.L.g i j).val := ⟨_, rfl⟩
  have memW : ∀ i z, z ∈ W i ↔ ⊤ ≤ (u₀.ex z).left ⁻¹ᵁ P.L.U i := by
    intro i z
    rw [hW]
    exact Iff.rfl
  obtain ⟨⟨hWo, hWc, hcd, hcn, hcc, hWp, hcp⟩, T, hT1, hT2, hT3, hT4⟩ :=
    hFrame P.A _ P.L P.g u₀ hLB cs.t cs.2 W c hW hc
  have hloc := hLoc P.g W c hWo hWc hcd hcn hcc T hT1 hT2 hT3 u₀.Λ u₀.discrete u₀.full hWp hcp hT4
  obtain ⟨fr, κ, ⟨hfrd, hfrn, hfrc⟩, hTfr⟩ := hGlob P.g W c hWo hWc hcd hcn hcc T hT1 hT2 hT3 hloc
  obtain ⟨a, B, ha, hab, hfa⟩ :=
    hFact P.g W c hWo hWc hcd hcn hcc T hT1 hT2 hT3 u₀.Λ u₀.discrete u₀.full hWp hcp hT4 fr κ
      ⟨hfrd, hfrn, hfrc⟩ hTfr
  obtain ⟨Hm, χ, Ef, Q, hH, hχ, hEf, hQd, _, hQ⟩ := hNorm P.g u₀.Λ u₀.discrete u₀.full a B ha hab

  have hex0 : u₀.ex 0 = 1 := (u₀.ker 0).2 (Submodule.zero_mem _)
  have he0 : (u₀.ex 0).left = eSec P.A := by
    simp only [hex0, CategoryTheory.Hom.one_def, toUnit_unit, Category.id_comp]
    rfl
  obtain ⟨i₀, h₀⟩ := hWc 0
  have hjj : ⊤ ≤ (P.L.pull (eSec P.A)).U (fun _ => i₀ : PUnit.{1} → P.L.ι) :=
    (OriginFrame.rigChart_iff (eSec P.A) P.L (fun _ => i₀ : PUnit.{1} → P.L.ι)).2 (by rw [← he0]; exact (memW _ _).1 h₀)
  have hjj' : ⊤ ≤ (𝟙 (Sp ℂ)) ⁻¹ᵁ (P.L.pull (eSec P.A)).U (fun _ => i₀ : PUnit.{1} → P.L.ι) := by
    exact hjj
  have hvne := OriginFrame.rigVal_ne_zero hV (𝟙 (Sp ℂ)) _ hjj' (rig.s (fun _ => i₀ : PUnit.{1} → P.L.ι))
  clear hFrame hLoc hGlob hFact hNorm hCube hT1 hT2 hT3 hT4 hloc hTfr hcd hcn hcc hWp hcp hWo hWc hab
  have hF : fr i₀ 0 * Complex.exp (Q 0) ≠ 0 := mul_ne_zero (hfrn i₀ 0 h₀ trivial) (Complex.exp_ne_zero _)
  have hlam : valAt' (𝟙 (Sp ℂ)) ((P.L.pull (eSec P.A)).U (fun _ => i₀ : PUnit.{1} → P.L.ι)) (rig.s (fun _ => i₀ : PUnit.{1} → P.L.ι)).val /
      (fr i₀ 0 * Complex.exp (Q 0)) ≠ 0 := div_ne_zero hvne hF
  refine ⟨{
      ex := u₀.ex
      ex_add := u₀.ex_add
      ex_onto := u₀.ex_onto
      Λ := u₀.Λ
      ker := u₀.ker
      discrete := u₀.discrete
      full := u₀.full
      hol := u₀.hol
      fr := fun i z => valAt' (𝟙 (Sp ℂ)) ((P.L.pull (eSec P.A)).U (fun _ => i₀ : PUnit.{1} → P.L.ι)) (rig.s (fun _ => i₀ : PUnit.{1} → P.L.ι)).val /
        (fr i₀ 0 * Complex.exp (Q 0)) * (fr i z * Complex.exp (Q z))
      fr_hol := ?_
      fr_ne := ?_
      fr_compat := ?_ }, Hm, χ, Ef, rfl, ?_, hH, hχ, hEf, ?_⟩
  · intro i
    refine (((hfrd i).mono fun z hz => ⟨(memW i z).2 hz, trivial⟩).mul
      hQd.cexp.differentiableOn).const_mul _
  · intro i z hz
    exact mul_ne_zero hlam (mul_ne_zero (hfrn i z ((memW i z).2 hz) trivial) (Complex.exp_ne_zero _))
  · intro i j z hz
    have hp := ((hV _ (u₀.ex z).left).1 _).1 hz
    have hzi : z ∈ W i := (memW i z).2 (((hV _ _).1 _).2 hp.1)
    have hzj : z ∈ W j := (memW j z).2 (((hV _ _).1 _).2 hp.2)
    have h1 := hfrc i j z hzi hzj trivial
    rw [hc] at h1
    dsimp only at h1 ⊢
    rw [h1]
    ring
  · intro j hj
    have hj0 : 0 ∈ W (j PUnit.unit) :=
      (memW _ _).2 (by rw [he0]; exact (OriginFrame.rigChart_iff (eSec P.A) P.L j).1 hj)
    have hcomp := OriginFrame.rigVal_compat hV (eSec P.A) P.L rig hrig j (fun _ => i₀ : PUnit.{1} → P.L.ι) hj hjj
    have hfc := hfrc (j PUnit.unit) i₀ 0 hj0 h₀ trivial
    rw [hc] at hfc
    dsimp only at hfc ⊢
    rw [hcomp, hfc, he0, div_mul_eq_mul_div, div_eq_iff hF]
    ring
  · intro l i z hz
    have hzW : z ∈ W i := (memW i z).2 hz
    dsimp only at hz ⊢
    have hE := Complex.exp_ne_zero (Q (z + l))
    rw [← hQ l z, hfa l i z hzW, Complex.exp_sub]
    field_simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEtaleCoordsVanishing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

noncomputable section

namespace GlobalTheory.HolChart

theorem exists_etale_coords_vanishing {g : ℕ} {A : Type} [CommRing A] (c : ℂ →+* A)
    (hc : c.IsStandardSmoothOfRelativeDimension g) (e : A →+* ℂ) (he : ∀ a, e (c a) = a) :
    ∃ φ : MvPolynomial (Fin g) ℂ →+* A, φ.comp MvPolynomial.C = c ∧ φ.Etale ∧
      ∀ i, e (φ (MvPolynomial.X i)) = 0 := by
  obtain ⟨φ, h1, h2⟩ := hc.exists_etale_mvPolynomial
  let a : Fin g → ℂ := fun i => e (φ (MvPolynomial.X i))
  let T : MvPolynomial (Fin g) ℂ ≃ₐ[ℂ] MvPolynomial (Fin g) ℂ :=
    AlgEquiv.ofAlgHom (MvPolynomial.aeval fun i => MvPolynomial.X i - MvPolynomial.C (a i))
      (MvPolynomial.aeval fun i => MvPolynomial.X i + MvPolynomial.C (a i))
      (by ext i; simp) (by ext i; simp)
  have hC : ∀ x, φ (MvPolynomial.C x) = c x := fun x => by rw [← h1]; rfl
  refine ⟨φ.comp T.toRingEquiv.toRingHom, ?_, ?_, ?_⟩
  · ext x
    simp [T, hC]
  · exact RingHom.Etale.respectsIso.2 φ T.toRingEquiv h2
  · intro i
    simp [T, hC, he, a]

theorem derivation_eq_zero {g : ℕ} {A : Type} [CommRing A] (φ : MvPolynomial (Fin g) ℂ →+* A)
    (hφ : φ.Etale) (e : A →+* ℂ) (D : A →+ ℂ) (h0 : ∀ a, D (φ (MvPolynomial.C a)) = 0)
    (hm : ∀ f f', D (f * f') = e f * D f' + e f' * D f)
    (hX : ∀ i, D (φ (MvPolynomial.X i)) = 0) : D = 0 := by
  have h1 : D 1 = 0 := by simpa using h0 1
  have hP : ∀ p, D (φ p) = 0 := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => exact h0 a
    | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, add_zero]
    | mul_X p i hp => rw [map_mul, hm, hp, hX]; simp
  let F : A →+* DualNumber ℂ :=
    { toFun := fun f => TrivSqZeroExt.inl (e f) + TrivSqZeroExt.inr (D f)
      map_one' := by ext <;> simp [h1]
      map_mul' := fun f f' => by ext <;> simp [hm, mul_comm]
      map_zero' := by ext <;> simp
      map_add' := fun f f' => by ext <;> simp }
  let F₀ : A →+* DualNumber ℂ := (algebraMap ℂ (DualNumber ℂ)).comp e
  have hFF : ∀ p, F (φ p) = F₀ (φ p) := fun p => by
    ext <;> simp [F, F₀, hP, TrivSqZeroExt.algebraMap_eq_inl]
  let _ := φ.toAlgebra
  let _ : Algebra (MvPolynomial (Fin g) ℂ) (DualNumber ℂ) := (F₀.comp φ).toAlgebra
  have _ : Algebra.Etale (MvPolynomial (Fin g) ℂ) A := hφ
  let G : A →ₐ[MvPolynomial (Fin g) ℂ] DualNumber ℂ :=
    { F with commutes' := hFF }
  let G₀ : A →ₐ[MvPolynomial (Fin g) ℂ] DualNumber ℂ := { F₀ with commutes' := fun p => rfl }
  have hnil : IsNilpotent (RingHom.ker (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) := by
    refine ⟨2, ?_⟩
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    rw [RingHom.mem_ker] at hx hy
    have hx' : x.fst = 0 := hx
    have hy' : y.fst = 0 := hy
    rw [Ideal.mem_bot]
    ext <;> simp [hx', hy']
  have hG : G = G₀ := Algebra.FormallyUnramified.ext' (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom hnil G G₀
    (fun x => by simp [G, G₀, F, F₀])
  ext f
  have := congrArg (fun H : A →ₐ[MvPolynomial (Fin g) ℂ] DualNumber ℂ => (H f).snd) hG
  simpa [G, G₀, F, F₀, TrivSqZeroExt.algebraMap_eq_inl] using this

theorem hol_of_affine
    (hval : (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)))
    {g : ℕ} {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) {W : Set (Fin g → ℂ)} (hW : IsOpen W)
    (s : (Fin g → ℂ) → (Sp ℂ ⟶ X)) (hs : ∀ w ∈ W, ⊤ ≤ s w ⁻¹ᵁ U)
    (hd : ∀ a : Γ(X, U), DifferentiableOn ℂ (fun w => valAt' (s w) U a) W)
    (V : X.Opens) (f : Γ(X, V)) :
    IsOpen {w | w ∈ W ∧ ⊤ ≤ s w ⁻¹ᵁ V} ∧
      DifferentiableOn ℂ (fun w => valAt' (s w) V f) {w | w ∈ W ∧ ⊤ ≤ s w ⁻¹ᵁ V} := by
  have key : ∀ w₀ ∈ {w | w ∈ W ∧ ⊤ ≤ s w ⁻¹ᵁ V}, {w | w ∈ W ∧ ⊤ ≤ s w ⁻¹ᵁ V} ∈ 𝓝 w₀ ∧
      DifferentiableAt ℂ (fun w => valAt' (s w) V f) w₀ := by
    rintro w₀ ⟨hw₀, hV⟩
    obtain ⟨h, hhV, hh⟩ := hU.exists_basicOpen_le (V := V) ⟨_, ((hval X (s w₀)).1 V).1 hV⟩
      (((hval X (s w₀)).1 U).1 (hs w₀ hw₀))
    have hB₀ : ⊤ ≤ s w₀ ⁻¹ᵁ X.basicOpen h := ((hval X (s w₀)).1 _).2 hh
    have hne₀ : valAt' (s w₀) U h ≠ 0 := ((hval X (s w₀)).2.2.2.2.1 U h).1 hB₀
    have hWn : W ∈ 𝓝 w₀ := hW.mem_nhds hw₀
    have hda : ∀ a : Γ(X, U), DifferentiableAt ℂ (fun w => valAt' (s w) U a) w₀ := fun a =>
      (hd a w₀ hw₀).differentiableAt hWn
    have hN : ∀ᶠ w in 𝓝 w₀, w ∈ W ∧ valAt' (s w) U h ≠ 0 :=
      Filter.Eventually.and hWn ((hda h).continuousAt.eventually_ne hne₀)
    have _ := hU.isLocalization_basicOpen h
    obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj h (resG X hhV f)
    refine ⟨hN.mono fun w hw => ⟨hw.1, ?_⟩, ?_⟩
    · exact ((hval X (s w)).1 V).2
        (hhV (((hval X (s w)).1 _).1 (((hval X (s w)).2.2.2.2.1 U h).2 hw.2)))
    · have hq : DifferentiableAt ℂ (fun w => valAt' (s w) U a * (valAt' (s w) U h ^ n)⁻¹) w₀ :=
        (hda a).mul (((hda h).pow n).inv (pow_ne_zero n hne₀))
      refine DifferentiableAt.congr_of_eventuallyEq hq (hN.mono fun w hw => ?_)
      have hB : ⊤ ≤ s w ⁻¹ᵁ X.basicOpen h := ((hval X (s w)).2.2.2.2.1 U h).2 hw.2
      obtain ⟨ev, hev⟩ := (hval X (s w)).2.1 _ hB
      have r1 := (hval X (s w)).2.2.1 V _ hhV f hB
      have r2 := (hval X (s w)).2.2.1 U _ (X.basicOpen_le h) a hB
      have r3 := (hval X (s w)).2.2.1 U _ (X.basicOpen_le h) h hB
      have ha' : resG X hhV f * resG X (X.basicOpen_le h) h ^ n = resG X (X.basicOpen_le h) a := ha
      have := congrArg ev ha'
      rw [map_mul, map_pow, ← hev, ← hev, ← hev, r1, r2, r3] at this
      show valAt' (s w) V f = valAt' (s w) U a * (valAt' (s w) U h ^ n)⁻¹
      rw [← this, mul_inv_cancel_right₀ (pow_ne_zero n hw.2)]
  exact ⟨isOpen_iff_mem_nhds.2 fun w hw => (key w hw).1,
    fun w hw => (key w hw).2.differentiableWithinAt⟩

theorem exists_holomorphic_chart :
    (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) → (∀ (X : Over (Sp ℂ)) (U : X.left.Opens), IsAffineOpen U → ∀ e : Γ(X.left, U) →+* ℂ, (∀ a, e (constFn X.hom U a) = a) → ∃! x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U ∧ ∀ f, valAt' x.left U f = e f) → (∀ (g : ℕ) (A : Type) [CommRing A] [Algebra ℂ A] [Algebra (MvPolynomial (Fin g) ℂ) A] [IsScalarTower ℂ (MvPolynomial (Fin g) ℂ) A] [Algebra.Etale (MvPolynomial (Fin g) ℂ) A] (e : A →ₐ[ℂ] ℂ), (∀ i, e (algebraMap (MvPolynomial (Fin g) ℂ) A (MvPolynomial.X i)) = 0) → ∃ (W : Set (Fin g → ℂ)) (σ : (Fin g → ℂ) → (A →ₐ[ℂ] ℂ)) (n : ℕ) (f : Fin n → A) (ε : ℝ), IsOpen W ∧ 0 ∈ W ∧ σ 0 = e ∧ 0 < ε ∧ (∀ a, DifferentiableOn ℂ (fun w => σ w a) W) ∧ (∀ w ∈ W, ∀ i, σ w (algebraMap (MvPolynomial (Fin g) ℂ) A (MvPolynomial.X i)) = w i) ∧ ∀ x : A →ₐ[ℂ] ℂ, (∀ k, ‖x (f k) - e (f k)‖ < ε) → ∃ w ∈ W, x = σ w) → (∀ (X : Over (Sp ℂ)) (g : ℕ), SmoothOfRelativeDimension g X.hom → ∀ e : (𝟙_ (Over (Sp ℂ)) ⟶ X), ∃ (W : Set (Fin g → ℂ)) (σ : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (U : X.left.Opens) (t : Fin g → Γ(X.left, U)), IsOpen W ∧ 0 ∈ W ∧ σ 0 = e ∧ IsAffineOpen U ∧ (∀ (U : (X).left.Opens) (f : Γ((X).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ (σ w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (σ w).left U f) {w | w ∈ W ∧ ⊤ ≤ (σ w).left ⁻¹ᵁ U}) ∧ (∀ w ∈ W, ⊤ ≤ (σ w).left ⁻¹ᵁ U ∧ ∀ i, valAt' (σ w).left U (t i) = w i) ∧ IsOpen[(TopologicalSpace.generateFrom {S : Set (𝟙_ (Over (Sp ℂ)) ⟶ X) | ∃ (U : X.left.Opens) (f : Γ(X.left, U)) (O : Set ℂ), IsOpen O ∧ S = {x | ⊤ ≤ (x).left ⁻¹ᵁ U ∧ valAt' x.left U f ∈ O}})] (σ '' W) ∧ (∀ D : Γ(X.left, U) →+ ℂ, (∀ a, D (constFn X.hom U a) = 0) → (∀ f f', D (f * f') = valAt' e.left U f * D f' + valAt' e.left U f' * D f) → (∀ i, D (t i) = 0) → D = 0)) := by
  intro hval haff hring X g hX e
  let e' : Sp ℂ ⟶ X.left := e.left
  obtain ⟨U₀, -, U, hU, hp, hle, hsm⟩ :=
    hX.exists_isStandardSmoothOfRelativeDimension (e' (default : PrimeSpectrum ℂ))
  have hU₀ : U₀ = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    have h1 : X.hom (e' (default : PrimeSpectrum ℂ)) ∈ U₀ := hle hp
    have h2 : y = X.hom (e' (default : PrimeSpectrum ℂ)) :=
      Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    rw [h2]; exact h1
  subst hU₀
  let c : ℂ →+* Γ(X.left, U) :=
    (X.hom.appLE ⊤ U hle).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  have hcc : ∀ a, constFn X.hom U a = c a := fun a => rfl
  have hc : c.IsStandardSmoothOfRelativeDimension g :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 (X.hom.appLE ⊤ U hle).hom
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv hsm
  have hpts : ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ X, ⊤ ≤ x.left ⁻¹ᵁ U →
      ∃ ev : Γ(X.left, U) →+* ℂ, (∀ f, valAt' x.left U f = ev f) ∧ ∀ a, ev (c a) = a := by
    intro x hx
    obtain ⟨ev, hev⟩ := (hval X.left x.left).2.1 U hx
    refine ⟨ev, hev, fun a => ?_⟩
    rw [← hev, ← hcc]
    exact (hval X.left x.left).2.2.2.2.2 X.hom (Over.w x) U a hx
  have heU : ⊤ ≤ e.left ⁻¹ᵁ U := ((hval X.left e').1 U).2 hp
  obtain ⟨ev, hev, hevc⟩ := hpts e heU
  obtain ⟨φ, hφc, hφ, hφ0⟩ := exists_etale_coords_vanishing c hc ev hevc
  have hφc' : ∀ a, φ (MvPolynomial.C a) = c a := fun a => by rw [← hφc]; rfl
  let _ : Algebra ℂ Γ(X.left, U) := c.toAlgebra
  let _ : Algebra (MvPolynomial (Fin g) ℂ) Γ(X.left, U) := φ.toAlgebra
  have _ : IsScalarTower ℂ (MvPolynomial (Fin g) ℂ) Γ(X.left, U) :=
    IsScalarTower.of_algebraMap_eq' hφc.symm
  have _ : Algebra.Etale (MvPolynomial (Fin g) ℂ) Γ(X.left, U) := hφ
  let eA : Γ(X.left, U) →ₐ[ℂ] ℂ := { ev with commutes' := hevc }
  obtain ⟨W, σ, n, f, ε, hW, hW0, hσ0, hε, hσd, hσt, hσs⟩ := hring g Γ(X.left, U) eA hφ0
  have hex : ∀ x : Γ(X.left, U) →ₐ[ℂ] ℂ, ∃! y : (𝟙_ (Over (Sp ℂ)) ⟶ X),
      ⊤ ≤ y.left ⁻¹ᵁ U ∧ ∀ f, valAt' y.left U f = x f := fun x =>
    haff X U hU x.toRingHom (fun a => x.commutes a)
  choose pt hpt hptu using hex
  let W' : Set (Fin g → ℂ) := W ∩ ⋂ k, (W ∩ (fun w => σ w (f k)) ⁻¹' Metric.ball (eA (f k)) ε)
  have hW' : IsOpen W' := hW.inter (isOpen_iInter_of_finite fun k =>
    (hσd (f k)).continuousOn.isOpen_inter_preimage hW Metric.isOpen_ball)
  have hmem : ∀ w, w ∈ W' ↔ w ∈ W ∧ ∀ k, ‖σ w (f k) - eA (f k)‖ < ε := by
    intro w
    simp only [W', Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Metric.mem_ball, dist_eq_norm]
    exact ⟨fun h => ⟨h.1, fun k => (h.2 k).2⟩, fun h => ⟨h.1, fun k => ⟨h.1, h.2 k⟩⟩⟩
  refine ⟨W', fun w => pt (σ w), U, fun i => φ (MvPolynomial.X i), hW', ?_, ?_, hU, ?_, ?_, ?_, ?_⟩
  · exact (hmem 0).2 ⟨hW0, fun k => by rw [hσ0, sub_self, norm_zero]; exact hε⟩
  · show pt (σ 0) = e
    rw [hσ0]
    exact (hptu eA e ⟨heU, hev⟩).symm
  · intro V a
    refine hol_of_affine hval hU hW' (fun w => (pt (σ w)).left) (fun w _ => (hpt (σ w)).1)
      (fun b => ?_) V a
    exact ((hσd b).mono Set.inter_subset_left).congr fun w _ => (hpt (σ w)).2 b
  · intro w hw
    exact ⟨(hpt (σ w)).1, fun i => ((hpt (σ w)).2 _).trans (hσt w hw.1 i)⟩
  · have himg : (fun w => pt (σ w)) '' W' =
        {x : 𝟙_ (Over (Sp ℂ)) ⟶ X | ⊤ ≤ x.left ⁻¹ᵁ U ∧ valAt' x.left U 0 ∈ (Set.univ : Set ℂ)} ∩
          ⋂ k, {x : 𝟙_ (Over (Sp ℂ)) ⟶ X | ⊤ ≤ x.left ⁻¹ᵁ U ∧
            valAt' x.left U (f k) ∈ Metric.ball (eA (f k)) ε} := by
      ext x
      simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_univ,
        and_true, Metric.mem_ball, dist_eq_norm]
      constructor
      · rintro ⟨w, hw, rfl⟩
        refine ⟨(hpt (σ w)).1, fun k => ⟨(hpt (σ w)).1, ?_⟩⟩
        rw [(hpt (σ w)).2]
        exact ((hmem w).1 hw).2 k
      · rintro ⟨hx, hk⟩
        obtain ⟨ex, hex, hexc⟩ := hpts x hx
        let xA : Γ(X.left, U) →ₐ[ℂ] ℂ := { ex with commutes' := hexc }
        have hk' : ∀ k, ‖xA (f k) - eA (f k)‖ < ε := fun k => by
          have := (hk k).2
          rw [hex] at this
          exact this
        obtain ⟨w, hw, hxw⟩ := hσs xA hk'
        refine ⟨w, (hmem w).2 ⟨hw, hxw ▸ hk'⟩, ?_⟩
        rw [← hxw]
        exact (hptu xA x ⟨hx, hex⟩).symm
    rw [himg]
    let _ := TopologicalSpace.generateFrom {S : Set (𝟙_ (Over (Sp ℂ)) ⟶ X) |
      ∃ (U : X.left.Opens) (f : Γ(X.left, U)) (O : Set ℂ), IsOpen O ∧
        S = {x | ⊤ ≤ (x).left ⁻¹ᵁ U ∧ valAt' x.left U f ∈ O}}
    refine IsOpen.inter ?_ (isOpen_iInter_of_finite fun k => ?_)
    · exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨U, 0, Set.univ, isOpen_univ, rfl⟩
    · exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨U, f k, _, Metric.isOpen_ball, rfl⟩
  · intro D h0 hm hX
    refine derivation_eq_zero φ hφ ev D (fun a => ?_) (fun a b => ?_) hX
    · rw [hφc', ← hcc]; exact h0 a
    · rw [← hev, ← hev]; exact hm a b

end GlobalTheory.HolChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsReducedSchemeOfSmoothOfIsIntegrallyClosed
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory

theorem isReduced_scheme_of_smooth_of_isIntegrallyClosed (T : Type) [CommRing T] [IsDomain T]
    [IsIntegrallyClosed T] {X : Scheme.{0}} (f : X ⟶ Sp T) [Smooth f] :
    AlgebraicGeometry.IsReduced X := by
  have hT : GlobalTheory.IsNormalScheme (Sp T) := inferInstance
  have hX : GlobalTheory.IsNormalScheme X := (isNormalScheme_iff X).mpr
    (forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth f ((isNormalScheme_iff _).mp hT))
  infer_instance

theorem isReduced_of_smooth_complex :
    (∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ), Smooth p → IsReduced X) :=
  fun _ p _ ↦ isReduced_scheme_of_smooth_of_isIntegrallyClosed ℂ p

end GlobalTheory
end

