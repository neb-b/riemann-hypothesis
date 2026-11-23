module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.CubeTrivialisationOnUniformisingSpace
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0151
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0147
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0025
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0018

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbIsoLinCombLamOfAppellHumbert
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory

namespace SharpBundle

def IsFrameAlong {g : ℕ} {X : Scheme.{0}} (e : (Fin g → ℂ) → (Sp ℂ ⟶ X)) (L : LB X)
    (fr : L.ι → (Fin g → ℂ) → ℂ) : Prop :=
  (∀ i, DifferentiableOn ℂ (fr i) {z | ⊤ ≤ e z ⁻¹ᵁ L.U i}) ∧ (∀ i z, ⊤ ≤ e z ⁻¹ᵁ L.U i → fr i z ≠ 0) ∧
    ∀ i j z, ⊤ ≤ e z ⁻¹ᵁ (L.U i ⊓ L.U j) → fr i z = valAt' (e z) (L.U i ⊓ L.U j) (L.g i j).val * fr j z

theorem differentiableOn_finset_prod {E κ : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {S : Set E}
    (s : Finset κ) (φ : κ → E → ℂ) (h : ∀ k, DifferentiableOn ℂ (φ k) S) :
    DifferentiableOn ℂ (fun z => ∏ k ∈ s, φ k z) S := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using differentiableOn_const (1 : ℂ)
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a).mul ih

theorem IsFrameAlong.linComb {g : ℕ} {X Y : Scheme.{0}} (e : (Fin g → ℂ) → (Sp ℂ ⟶ X)) (L : LB Y) {K : Type}
    [Fintype K] (φ : K → (X ⟶ Y)) (ε : K → ℤ) (fr : K → L.ι → (Fin g → ℂ) → ℂ)
    (h : ∀ k, IsFrameAlong (fun z => e z ≫ φ k) L (fr k)) :
    IsFrameAlong e (LB.LinComb L φ ε) (fun (j : K → L.ι) z => ∏ k, fr k (j k) z ^ ε k) := by
  have hc : ∀ (j : K → L.ι) z, ⊤ ≤ e z ⁻¹ᵁ LB.wchart L φ j → ∀ k, ⊤ ≤ (e z ≫ φ k) ⁻¹ᵁ L.U (j k) :=
    fun j z hz => (CubeValues.le_preimage_wchart (e z) L φ j).1 hz
  refine ⟨fun j => ?_, fun j z hz => ?_, fun j j' z hz => ?_⟩
  · refine differentiableOn_finset_prod Finset.univ (fun k (z : Fin g → ℂ) => fr k (j k) z ^ ε k) fun k => ?_
    refine DifferentiableOn.zpow ?_ (Or.inl fun z hz => (h k).2.1 _ _ (hc j z hz k))
    exact ((h k).1 (j k)).mono fun z hz => hc j z hz k
  · exact Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ ((h k).2.1 _ _ (hc j z hz k))
  · obtain ⟨h1, h2⟩ := (top_le_preimage_inf (e z) _ _).1 hz
    have e1 := CubeValues.val_linComb (e z) valAt'_rules L φ ε j j' h1 h2
    refine Eq.trans ?_ (congrArg (· * ∏ k, fr k (j' k) z ^ ε k) e1.symm)
    show _ = (∏ k, _) * _
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← mul_zpow]
    exact congrArg (· ^ ε k) ((h k).2.2 (j k) (j' k) z
      ((top_le_preimage_inf _ _ _).2 ⟨hc j z h1 k, hc j' z h2 k⟩))

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem isFrameAlong_comp {n : ℕ} (F : (Fin n → ℂ) →ₗ[ℂ] (Fin g → ℂ)) :
    IsFrameAlong (fun z => (u.ex (F z)).left) L (fun i z => u.fr i (F z)) :=
  ⟨fun i => (u.fr_hol i).comp (LinearMap.toContinuousLinearMap F).differentiable.differentiableOn fun _ hz => hz,
    fun i z hz => u.fr_ne i (F z) hz, fun i j z hz => u.fr_compat i j (F z) hz⟩

def withFrame {M : LB A.left} (fr : M.ι → (Fin g → ℂ) → ℂ) (h : IsFrameAlong (fun z => (u.ex z).left) M fr) :
    HolUnif A M g where
  ex := u.ex
  ex_add := u.ex_add
  ex_onto := u.ex_onto
  Λ := u.Λ
  ker := u.ker
  discrete := u.discrete
  full := u.full
  hol := u.hol
  fr := fr
  fr_hol := h.1
  fr_ne := h.2.1
  fr_compat := h.2.2

theorem hermForm_add_left (Hm : Matrix (Fin g) (Fin g) ℂ) (z z' w : Fin g → ℂ) :
    hermForm Hm (z + z') w = hermForm Hm z w + hermForm Hm z' w := by
  simp [hermForm, add_dotProduct]

theorem hermForm_swap {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (z w : Fin g → ℂ) :
    hermForm Hm w z = hermForm Hm z w - 2 * Complex.I * ((hermForm Hm z w).im : ℂ) := by
  have h : hermForm Hm w z = starRingEnd ℂ (hermForm Hm z w) := by
    change _ = star (hermForm Hm z w)
    unfold hermForm
    rw [← Matrix.star_dotProduct_star, Matrix.star_mulVec, star_star, hH.eq, Matrix.dotProduct_mulVec]
  rw [h]
  apply Complex.ext <;> simp
  ring

variable {u} {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}

theorem ah_step (h : u.IsAH Hm χ) (l : u.Λ) (i : L.ι) (z : Fin g → ℂ) (hz : ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i) :
    u.fr i z = χ l * Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l) * u.fr i (z + l) :=
  h.2.2.2 l i z hz

theorem ah_step_add (h : u.IsAH Hm χ) (l m : u.Λ) (i : L.ι) (z : Fin g → ℂ) (hz : ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i) :
    u.fr i z = χ l * χ m * Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l +
      (Real.pi * hermForm Hm (z + l) m + Real.pi / 2 * hermForm Hm m m)) * u.fr i (z + l + m) := by
  have h2 := ah_step h m i (z + l) (by rw [CubeValues.ex_add_period u z l l.2]; exact hz)
  rw [ah_step h l i z hz, h2, Complex.exp_add _ (_ + _)]
  ring

theorem prod_finset_fin_two' (f : Finset (Fin 2) → ℂ) :
    ∏ I : ULift.{0} (Finset (Fin 2)), f I.down = f ∅ * f {0} * f {1} * f {0, 1} := by
  rw [Fintype.prod_equiv Equiv.ulift (fun I : ULift.{0} (Finset (Fin 2)) => f I.down) f fun I => rfl]
  have : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  rw [this, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]
  ring

theorem lam_step (h : u.IsAH Hm χ) (j : ULift.{0} (Finset (Fin 2)) → L.ι) (x x' : Fin 2 → Fin g → ℂ) (l : Fin 2 → u.Λ)
    (hx' : ∀ a, x' a = x a + l a)
    (hx : ∀ I, ⊤ ≤ (u.ex (∑ a ∈ I.down, x a)).left ⁻¹ᵁ L.U (j I)) :
    ∏ I : ULift.{0} (Finset (Fin 2)), u.fr (j I) (∑ a ∈ I.down, x a) ^ ((-1 : ℤ) ^ (2 - I.down.card)) =
      Complex.exp (Real.pi * Complex.I * ((hermForm Hm (l 0) (l 1)).im : ℂ) +
        (Real.pi * (hermForm Hm (x 0) (l 1) + hermForm Hm (x 1) (l 0)) +
          Real.pi / 2 * (hermForm Hm (l 0) (l 1) + hermForm Hm (l 1) (l 0)))) *
      ∏ I : ULift.{0} (Finset (Fin 2)), u.fr (j I) (∑ a ∈ I.down, x' a) ^ ((-1 : ℤ) ^ (2 - I.down.card)) := by
  rw [prod_finset_fin_two' fun I => u.fr (j ⟨I⟩) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (2 - I.card)),
    prod_finset_fin_two' fun I => u.fr (j ⟨I⟩) (∑ a ∈ I, x' a) ^ ((-1 : ℤ) ^ (2 - I.card))]
  have c01 : ({0, 1} : Finset (Fin 2)).card = 2 := rfl
  have s01 : ∀ y : Fin 2 → Fin g → ℂ, ∑ a ∈ ({0, 1} : Finset (Fin 2)), y a = y 0 + y 1 := fun y =>
    Finset.sum_pair (by decide)
  have h0 := hx ⟨{0}⟩
  have h1 := hx ⟨{1}⟩
  have h01 := hx ⟨{0, 1}⟩
  simp only [Finset.sum_singleton, s01] at h0 h1 h01
  have e0 := ah_step h (l 0) _ _ h0
  have e1 := ah_step h (l 1) _ _ h1
  have e01 := ah_step_add h (l 0) (l 1) _ _ h01
  have n0 : χ (l 0) ≠ 0 := fun e => by simpa [e] using h.2.2.1 (l 0)
  have n1 : χ (l 1) ≠ 0 := fun e => by simpa [e] using h.2.2.1 (l 1)
  have hs : x 0 + l 0 + (x 1 + l 1) = x 0 + x 1 + l 0 + l 1 := by abel
  simp only [Finset.sum_singleton, s01, Finset.sum_empty, Finset.card_empty, Finset.card_singleton, c01, hx', hs]
  norm_num
  rw [e0, e1, e01]
  have key : Complex.exp (Real.pi * hermForm Hm (x 0 + x 1) (l 0) + Real.pi / 2 * hermForm Hm (l 0) (l 0) +
      (Real.pi * hermForm Hm (x 0 + x 1 + l 0) (l 1) + Real.pi / 2 * hermForm Hm (l 1) (l 1))) =
      Complex.exp (Real.pi * Complex.I * ((hermForm Hm (l 0) (l 1)).im : ℂ) +
        (Real.pi * (hermForm Hm (x 0) (l 1) + hermForm Hm (x 1) (l 0)) +
          Real.pi / 2 * (hermForm Hm (l 0) (l 1) + hermForm Hm (l 1) (l 0)))) *
      Complex.exp (Real.pi * hermForm Hm (x 0) (l 0) + Real.pi / 2 * hermForm Hm (l 0) (l 0)) *
      Complex.exp (Real.pi * hermForm Hm (x 1) (l 1) + Real.pi / 2 * hermForm Hm (l 1) (l 1)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [hermForm_add_left]
    rw [hermForm_swap h.1 (l 0) (l 1)]
    ring
  rw [key]
  have := Complex.exp_ne_zero (Real.pi * hermForm Hm (x 0) (l 0) + Real.pi / 2 * hermForm Hm (l 0) (l 0))
  have := Complex.exp_ne_zero (Real.pi * hermForm Hm (x 1) (l 1) + Real.pi / 2 * hermForm Hm (l 1) (l 1))
  simp only [mul_inv]
  field_simp

theorem sum_symmetrise {n : ℕ} (W : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → Fin n → ℂ) :
    ∑ uv : Fin n × Fin n, (W uv.1 uv.2 : ℂ) * (b uv.1 uv.2 + b uv.2 uv.1) =
      ∑ i, ∑ j, ((W + W.transpose) i j : ℂ) * b i j := by
  simp only [Fintype.sum_prod_type, Matrix.add_apply, Matrix.transpose_apply, Int.cast_add, mul_add, add_mul,
    Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_comm

end SharpBundle


open SharpBundle in
theorem lbIso_linComb_lam_of_appellHumbert : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (P₀ : Out.PolAV (Sp ℂ)) (u₀ : HolUnif P₀.A P₀.L P₀.g) (H₀ : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ₀ : u₀.Λ → ℂ) (pr : Fin 8 → (P.A ⟶ P₀.A)) (R : Fin 8 → ((Fin P.g → ℂ) →ₗ[ℂ] (Fin P₀.g → ℂ))), u.IsAH Hm χ → u₀.IsAH H₀ χ₀ → (∀ i z, u₀.ex (R i z) = u.ex z ≫ pr i) → (∀ z w, hermForm Hm z w = ∑ i, ∑ j, ((W + W.transpose) i j : ℂ) * hermForm H₀ (R i z) (R j w)) → (∀ l : u.Λ, χ l = Complex.exp (Real.pi * Complex.I * ∑ i, ∑ j, (W i j : ℂ) * ((hermForm H₀ (R i l) (R j l)).im : ℂ))) → LBIso P.L (LB.LinComb (abelian₂ P₀.A P₀.L) (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) := by
  intro h1 h2 h3 h4 W P u Hm χ P₀ u₀ H₀ χ₀ pr R hu hu₀ hR hH hχ
  let r : Fin 8 × Fin 8 → Fin 2 → Fin 8 := fun uv => ![uv.1, uv.2]
  have hpt : ∀ (uv : Fin 8 × Fin 8) (I : Finset (Fin 2)) z,
      ((u.ex z).left ≫ (lift (pr uv.1) (pr uv.2)).left) ≫ (psum P₀.A (x2 P₀.A) I).left =
        (u₀.ex (∑ a ∈ I, R (r uv a) z)).left := fun uv I z => by
    rw [← Over.comp_left, ← Over.comp_left,
      CubeValues.comp_psum u₀ (u.ex z ≫ lift (pr uv.1) (pr uv.2)) (x2 P₀.A) fun a => R (r uv a) z]
    intro k
    fin_cases k <;> simp [x2, r, hR]
  have hin : ∀ uv : Fin 8 × Fin 8, IsFrameAlong (fun z => (u.ex z).left ≫ (lift (pr uv.1) (pr uv.2)).left)
      (abelian₂ P₀.A P₀.L) (fun (j : ULift.{0} (Finset (Fin 2)) → P₀.L.ι) z =>
        ∏ I : ULift.{0} (Finset (Fin 2)), u₀.fr (j I) (∑ a ∈ I.down, R (r uv a) z) ^ ((-1 : ℤ) ^ (2 - I.down.card))) :=
    fun uv => IsFrameAlong.linComb _ P₀.L (K := ULift.{0} (Finset (Fin 2))) _ _
      (fun I i z => u₀.fr i (∑ a ∈ I.down, R (r uv a) z)) fun I => by
        simp only [hpt]
        simpa only [LinearMap.sum_apply] using isFrameAlong_comp u₀ (∑ a ∈ I.down, R (r uv a))
  have hout := IsFrameAlong.linComb (fun z => (u.ex z).left) (abelian₂ P₀.A P₀.L) (K := Fin 8 × Fin 8)
    (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2) _ hin
  have hΛ : ∀ i (l : u.Λ), R i l ∈ u₀.Λ := fun i l => by
    rw [← u₀.ker, hR, (u.ker _).2 l.2, ← CubeValues.ex_zero u, ← hR, map_zero, CubeValues.ex_zero]
  refine GlobalTheory.lbIso_of_same_factor h1 h2 h3 h4 P _ _ u (withFrame u _ hout) P.isLB
    (LB.isLB_linComb (LB.isLB_linComb P₀.isLB _ _) _ _) rfl fun l i j z hi hj => ?_
  have hj' := (CubeValues.le_preimage_wchart (u.ex z).left (abelian₂ P₀.A P₀.L) _ j).1 hj
  have hst := fun uv : Fin 8 × Fin 8 => lam_step hu₀ (j uv) (fun a => R (r uv a) z) (fun a => R (r uv a) (z + l))
    (fun a => ⟨R (r uv a) l, hΛ _ l⟩) (fun a => map_add _ _ _) fun I => by
      rw [← hpt]
      exact (CubeValues.le_preimage_wchart _ P₀.L _ (j uv)).1 (hj' uv) I
  dsimp only [withFrame]
  change u.fr i z * ∏ uv : Fin 8 × Fin 8, _ = u.fr i (z + l) * ∏ uv : Fin 8 × Fin 8, _
  simp only [hst, mul_zpow, Finset.prod_mul_distrib, ← Complex.exp_int_mul, ← Complex.exp_sum]
  rw [ah_step hu l i z hi, hχ, ← Complex.exp_add, hH, hH, ← sum_symmetrise W fun a b => hermForm H₀ (R a z) (R b l),
    ← sum_symmetrise W fun a b => hermForm H₀ (R a l) (R b l), ← Fintype.sum_prod_type' fun a b =>
      (W a b : ℂ) * ((hermForm H₀ (R a l) (R b l)).im : ℂ), Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, mul_comm _ (u.fr i (z + l)), _root_.mul_assoc]
  congr 3
  refine Finset.sum_congr rfl fun uv _ => ?_
  simp only [r, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalOfFieldExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.SiegelDescent

variable {S S' : Scheme.{0}} {A : Over S} {A' : Over S'}

private theorem hom_ext_tensor_left_of_fst_snd {B Z : Scheme.{0}} {X : Over B} (g k : Z ⟶ (X ⊗ X).left)
    (h1 : g ≫ (fst X X).left = k ≫ (fst X X).left) (h2 : g ≫ (snd X X).left = k ≫ (snd X X).left) : g = k := by
  have hw : k ≫ (X ⊗ X).hom = g ≫ (X ⊗ X).hom := by
    rw [← Over.w (fst X X), ← Category.assoc, ← h1, Category.assoc]
  have key := CartesianMonoidalCategory.hom_ext (Over.homMk g rfl : Over.mk (g ≫ (X ⊗ X).hom) ⟶ X ⊗ X)
    (Over.homMk k hw) (by ext; simpa using h1) (by ext; simpa using h2)
  exact congrArg CommaMorphism.left key

private theorem pGen_of_isGen_iso_pull {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : L'.Iso (L.pull F))
    (hw : w.IsGen) : PGen w := by
  intro Y f y j j' k k' hj hj' hk hk'
  obtain ⟨J, hJ⟩ : ∃ J : (L.pull F).ι, J = fun _ => j := ⟨_, rfl⟩
  obtain ⟨J', hJ'⟩ : ∃ J' : (L.pull F).ι, J' = fun _ => j' := ⟨_, rfl⟩
  have m1 : f y ∈ (L.pull F).U J := by rw [hJ]; exact mem_pull.2 hj
  have m2 : f y ∈ (L.pull F).U J' := by rw [hJ']; exact mem_pull.2 hj'
  have hy : f y ∈ ((L.pull F).div L').U (J, k) ⊓ ((L.pull F).div L').U (J', k') := ⟨⟨m1, hk⟩, ⟨m2, hk'⟩⟩
  have e := congrArg (gm f y _) (hw (J, k) (J', k'))
  rw [gm_res f y _ hy, map_mul, gm_res f y _ hy] at e
  have eg : gm f y (((L.pull F).div L').U (J, k) ⊓ ((L.pull F).div L').U (J', k'))
      (((L.pull F).div L').g (J, k) (J', k')) =
      gm (f ≫ F) y (L.U j ⊓ L.U j') (L.g j j') * (gm f y (L'.U k ⊓ L'.U k') (L'.g k k'))⁻¹ := by
    have hy' : f y ∈ (L.pull F).U J ⊓ L'.U k ⊓ ((L.pull F).U J' ⊓ L'.U k') := ⟨⟨m1, hk⟩, ⟨m2, hk'⟩⟩
    show gm f y ((L.pull F).U J ⊓ L'.U k ⊓ ((L.pull F).U J' ⊓ L'.U k'))
      (res _ ((L.pull F).g J J') * (res _ (L'.g k k'))⁻¹) = _
    rw [map_mul, map_inv, gm_res f y _ hy', gm_res f y _ hy', gm_pull_g L F f y J J' m1 m2]
    subst hJ hJ'
    rfl
  rw [eg] at e
  unfold gw
  subst hJ hJ'
  exact e

private theorem flat_spMap_of_field_hom' {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K) : Flat (spMap i) := by
  unfold spMap
  infer_instance

private theorem surjective_spMap_of_field_hom {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K) : Surjective (spMap i) := by
  constructor
  intro x
  exact ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K), Subsingleton.elim (α := PrimeSpectrum K₀) _ _⟩

theorem lift_comp_square {φ : A'.left ⟶ A.left} {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left} (hs : IsSquare φ φ₂)
    {T : Over S} {T' : Over S'} (u : T'.left ⟶ T.left) (a b : T ⟶ A) (a' b' : T' ⟶ A')
    (ha : a'.left ≫ φ = u ≫ a.left) (hb : b'.left ≫ φ = u ≫ b.left) :
    (lift a' b').left ≫ φ₂ = u ≫ (lift a b).left := by
  have e1 : (lift a' b').left ≫ (fst A' A').left = a'.left := by rw [← Over.comp_left, lift_fst]
  have e2 : (lift a b).left ≫ (fst A A).left = a.left := by rw [← Over.comp_left, lift_fst]
  have e3 : (lift a' b').left ≫ (snd A' A').left = b'.left := by rw [← Over.comp_left, lift_snd]
  have e4 : (lift a b).left ≫ (snd A A).left = b.left := by rw [← Over.comp_left, lift_snd]
  apply hom_ext_tensor_left_of_fst_snd
  · rw [Category.assoc, hs.1, ← Category.assoc, e1, ha, Category.assoc, e2]
  · rw [Category.assoc, hs.2, ← Category.assoc, e3, hb, Category.assoc, e4]

theorem eq_one_of_pull {f : S' ⟶ S} [Flat f] [Surjective f] [GrpObj A] [GrpObj A'] {φ : A'.left ⟶ A.left}
    {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left} {P : LB (A ⊗ A).left} {P' : LB (A' ⊗ A').left}
    (h : IsGrpPullback A' A f φ) (hs : IsSquare φ φ₂) (hP : P.IsLB) (hP' : P'.IsLB) (hw : LBIso P' (P.pull φ₂))
    (hK : ∀ (T : Over S') (x : T ⟶ A'), (∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) → x = 1)
    (T : Over S) (x : T ⟶ A) (hx : ∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) : x = 1 := by
  obtain ⟨w, hwg⟩ := hw
  obtain ⟨t, ht⟩ := hx
  let T' : Over S' := Over.mk (pullback.snd T.hom f)
  let p : T'.left ⟶ T.left := pullback.fst T.hom f
  have hp : p ≫ T.hom = T'.hom ≫ f := pullback.condition
  have hxl : (p ≫ x.left) ≫ A.hom = T'.hom ≫ f := by rw [Category.assoc, Over.w x]; exact hp
  let xl : T'.left ⟶ A'.left := h.1.lift (p ≫ x.left) T'.hom hxl
  have hxl1 : xl ≫ φ = p ≫ x.left := h.1.lift_fst _ _ _
  have hxl2 : xl ≫ A'.hom = T'.hom := h.1.lift_snd _ _ _
  let x' : T' ⟶ A' := Over.homMk xl hxl2
  have hA : φ ≫ A.hom = A'.hom ≫ f := h.1.w
  let Z : Over S := Over.mk ((A' ⊗ T').hom ≫ f)
  let a0 : Z ⟶ A := Over.homMk ((fst A' T').left ≫ φ) (by
    rw [Category.assoc, hA, ← Category.assoc, Over.w (fst A' T')]; rfl)
  let b0 : Z ⟶ T := Over.homMk ((snd A' T').left ≫ p) (by
    rw [Category.assoc, hp, ← Category.assoc, Over.w (snd A' T')]; rfl)
  let q : (A' ⊗ T').left ⟶ (A ⊗ T).left := (lift a0 b0).left
  have hq1 : q ≫ (fst A T).left = (fst A' T').left ≫ φ := by
    rw [← Over.comp_left, lift_fst]; rfl
  have hq2 : q ≫ (snd A T).left = (snd A' T').left ≫ p := by
    rw [← Over.comp_left, lift_snd]; rfl
  have hc : (lift (snd A' T' ≫ x') (fst A' T')).left ≫ φ₂ = q ≫ (lift (snd A T ≫ x) (fst A T)).left := by
    refine lift_comp_square hs q _ _ _ _ ?_ hq1.symm
    rw [Over.comp_left, Over.comp_left, Category.assoc, ← Category.assoc q, hq2, Category.assoc]
    exact congrArg ((snd A' T').left ≫ ·) hxl1
  obtain ⟨a, ha, -⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_gen_move hP hP' w (pGen_of_isGen_iso_pull w hwg) (K := PUnit)
    (fun _ => (lift (snd A T ≫ x) (fst A T)).left) (fun _ => (lift (snd A' T' ≫ x') (fst A' T')).left)
    (fun _ => 1) q (fun _ => hc) t ht
  have hx' : x' = 1 := hK T' x' ⟨a, ha⟩
  let Zp : Over S := Over.mk (T'.hom ≫ f)
  let z : Zp ⟶ A := Over.homMk (p ≫ x.left) hxl
  have hz : z.left = (1 : T' ⟶ A').left ≫ φ := by
    show p ≫ x.left = _
    rw [← hxl1, ← hx']
    rfl
  have hzz := h.2 T' 1 1 z z hz hz
  rw [_root_.mul_one] at hzz
  have hz1 : z = 1 := by
    have e : z * z = z * 1 := by
      rw [_root_.mul_one]
      exact Over.OverMorphism.ext (hzz.trans hz.symm)
    exact mul_left_cancel e
  have hfl : Flat p := inferInstanceAs (Flat (pullback.fst T.hom f))
  have hsu : Surjective p := inferInstanceAs (Surjective (pullback.fst T.hom f))
  have hpe : Epi p := Flat.epi_of_flat_of_surjective p
  let pO : Zp ⟶ T := Over.homMk p hp
  have e1 : pO ≫ x = z := Over.OverMorphism.ext rfl
  have e2 : pO ≫ (1 : T ⟶ A) = 1 := by
    simp
  have hfin : p ≫ x.left = p ≫ (1 : T ⟶ A).left := by
    have e3 := congrArg CommaMorphism.left ((e1.trans hz1).trans e2.symm)
    exact e3
  exact Over.OverMorphism.ext ((cancel_epi p).1 hfin)

theorem principal_of_fieldExtension : ∀ (h M : ℕ) (o : Type) [CommRing o] (ζ : o) (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (s₀ : Sp K₀ ⟶ Sp o) (s : Sp K ⟶ Sp o) (c₀ : SiegPre h M ζ s₀) (c : SiegPre h M ζ s), SiegPB c c₀ (spMap i) → c.Principal → c₀.Principal := by
  intro h M o _ ζ K₀ K _ _ i s₀ s c₀ c hpb hc
  obtain ⟨φ, φ₂, hg, hs, hw, -⟩ := hpb
  have hfl : Flat (spMap i) := flat_spMap_of_field_hom' i
  have hsu : Surjective (spMap i) := surjective_spMap_of_field_hom i
  refine ⟨?_, fun T x hx => eq_one_of_pull hg hs c₀.isLB c.isLB hw hc.2 T x hx⟩
  obtain ⟨w, hwg⟩ := hw
  have hΔ : (lift (𝟙 c.A) (𝟙 c.A)).left ≫ φ₂ = φ ≫ (lift (𝟙 c₀.A) (𝟙 c₀.A)).left :=
    lift_comp_square hs φ _ _ _ _ (by simp) (by simp)
  have i1 : LBIso c.diag (c₀.P.pull (φ ≫ (lift (𝟙 c₀.A) (𝟙 c₀.A)).left)) := by
    have := iso_linComb (pGen_of_isGen_iso_pull w hwg) (K := PUnit) (fun _ => (lift (𝟙 c.A) (𝟙 c.A)).left) (fun _ => 1)
    rw [hΔ] at this
    exact this
  obtain ⟨w₀, hw₀⟩ := exists_iso_linComb c₀.isLB (K := PUnit) (F := (lift (𝟙 c₀.A) (𝟙 c₀.A)).left)
    (fun _ => (lift (𝟙 c₀.A) (𝟙 c₀.A)).left) (fun _ => 1) (fun _ _ _ => rfl)
  have i2 : LBIso (c₀.diag.pull φ) (c₀.P.pull (φ ≫ (lift (𝟙 c₀.A) (𝟙 c₀.A)).left)) :=
    iso_linComb (pGen_of_isGen_iso_pull w₀ hw₀) (K := PUnit) (fun _ => φ) (fun _ => 1)
  have hd : LBIso c.diag (c₀.diag.pull φ) :=
    LBIso.trans (pull_isLB c.isLB _) (pull_isLB c₀.isLB _) (pull_isLB (pull_isLB c₀.isLB _) _) i1 i2.symm
  exact GlobalTheory.AmpleDescent.relAmple_of_fieldExtension K₀ K i c₀.A c.A φ c₀.diag c.diag c₀.ab hg
    (pull_isLB c₀.isLB _) (pull_isLB c.isLB _) hd hc.1

end GlobalTheory.SiegelDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TrivLocallyOfDense
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.AbLaw

noncomputable section
namespace GlobalTheory.SeesawReduced

theorem triv_locally_of_dense : ∀ (R : Type) [CommRing R] [IsReduced R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (M : LB X), M.IsLB → Smooth f → IsProper f → GeometricallyIntegral f → IsProjBy f → Dense {p : PrimeSpectrum R | ∃ (K : Type) (_ : Field K) (g : R →+* K) (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of K)), RingHom.ker g = p.asIdeal ∧ IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) ∧ Triv (M.pull π)} → ∀ p : PrimeSpectrum R, ∃ r : R, r ∉ p.asIdeal ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) → IsUnit (g r) → Triv (M.pull π) := by
  intro R _ _ X f M hM hSm hPr hGI hPB hD p
  haveI := hPr
  haveI := hGI

  have hP : Nonempty (Perf f M) := _root_.GlobalTheory.AbLaw.nonempty_perf_of_smooth_isProjBy R X f hSm hPB M hM
  have hQ : Nonempty (Perf f (pw M (-1))) := _root_.GlobalTheory.AbLaw.nonempty_perf_of_smooth_isProjBy R X f hSm hPB _ (isLB_pw hM (-1))

  have hC := GlobalTheory.TrivLocus.isClosed_trivLocus R X f M hM hP hQ hPr hGI
  have hAll := hD.closure_eq.symm.trans hC.closure_eq
  have hmem : ∀ q : PrimeSpectrum R, q ∈ {p : PrimeSpectrum R | ∃ (K : Type) (_ : Field K) (g : R →+* K)
      (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of K)), RingHom.ker g = p.asIdeal ∧
      IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) ∧ Triv (M.pull π)} := by
    intro q; rw [← hAll]; exact Set.mem_univ q

  obtain ⟨K, _, g, X₁, π₁, f₁, hk, hpb, htr⟩ := hmem p
  obtain ⟨K₀, _, g₀, X₀, π₀, f₀, hk₀, hpb₀, hbij, htr₀⟩ :=
    GlobalTheory.GeomFibre.exists_field_pullback_appTop_bijective_and_triv R X f M hM hPr hGI K g X₁ π₁ f₁ hpb htr
  obtain ⟨r, I, hr, -, hI⟩ := GlobalTheory.AbLaw.Seesaw.seesaw R X f M hM hP inferInstance inferInstance
    K₀ g₀ X₀ π₀ f₀ hpb₀ hbij htr₀
  refine ⟨r, ?_, ?_⟩
  · intro hrp
    apply hr
    have hrk : r ∈ RingHom.ker g₀ := by rw [hk₀, hk]; exact hrp
    exact RingHom.mem_ker.1 hrk

  have hvan : ∀ x ∈ I, x * r = 0 := by
    intro x hx
    apply IsReduced.eq_zero
    rw [← mem_nilradical, nilradical_eq_sInf, Ideal.mem_sInf]
    intro J hJ
    let q : PrimeSpectrum R := ⟨J, hJ⟩
    by_cases hrJ : r ∈ J
    · exact J.mul_mem_left x hrJ
    · apply J.mul_mem_right r
      obtain ⟨L, _, gq, Xq, πq, fq, hkq, hpbq, htrq⟩ := hmem q
      have hu : IsUnit (gq r) := by
        rw [isUnit_iff_ne_zero]
        intro h0
        have hrk : r ∈ RingHom.ker gq := RingHom.mem_ker.2 h0
        rw [hkq] at hrk
        exact hrJ hrk
      have := ((hI L gq Xq πq fq hpbq hu).1 htrq) hx
      rw [RingHom.mem_ker] at this
      show x ∈ q.asIdeal
      rw [← hkq]; exact this
  intro R' _ g' X' π f' hpb' hu'
  refine (hI R' g' X' π f' hpb' hu').2 ?_
  intro x hx
  rw [RingHom.mem_ker]
  have h0 : g' x * g' r = 0 := by rw [← map_mul, hvan x hx, map_zero]
  exact (hu'.mul_left_eq_zero).1 h0

end GlobalTheory.SeesawReduced
end
end

