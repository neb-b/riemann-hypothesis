module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.OmAUnipFourierInv
section
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
open scoped Classical

noncomputable section
namespace GlobalTheory.SplitFlip.Model
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model GlobalTheory.SplitFlip

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section NonZero
variable {A A' D : Type*} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]


omit [DecidableEq A] in
theorem isPrimFrame_mul {Λ Λ' : Submodule 𝒪[k] (D → k)} {X : Matrix A D k} (hX : IsPrimFrame Λ X) (g : GL D k)
    (hg : ∀ x, x ᵥ* g.val ∈ Λ' ↔ x ∈ Λ) : IsPrimFrame Λ' (X * g.val) := by
  have hr : ∀ i, (X * g.val).row i = X.row i ᵥ* g.val := fun i => by
    funext j; simp [Matrix.row, Matrix.mul_apply, vecMul, dotProduct]
  refine ⟨?_, fun i => ?_, le_antisymm ?_ ?_⟩
  · rw [rank_mul_eq_left_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit)]; exact hX.1
  · rw [hr, hg]; exact hX.2.1 i
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨Submodule.subset_span ⟨i, rfl⟩, by rw [SetLike.mem_coe, hr, hg]; exact hX.2.1 i⟩
  · rintro x ⟨hx, hx'⟩
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun k).1 hx
    have e1 : ∑ i, c i • (X * g.val).row i = (∑ i, c i • X.row i) ᵥ* g.val := by
      simp only [hr, sum_vecMul, smul_vecMul]
    rw [e1] at hx' ⊢
    have h2 : (∑ i, c i • X.row i) ∈ Submodule.span 𝒪[k] (Set.range X.row) := by
      rw [hX.2.2]
      exact ⟨Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i)), (hg _).1 hx'⟩
    obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun 𝒪[k]).1 h2
    rw [← hd, sum_vecMul]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [smul_vecMul, ← hr]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem val_le_iff_mem {ϖ : kˣ} (hϖ : IsUnif ϖ) (e : ℕ) (r : 𝒪[k]) :
    r ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ e ↔ valuation k (r : k) ≤ valuation k ((ϖ ^ e : kˣ) : k) := by
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    ← (Valuation.integer.integers (valuation k)).le_iff_dvd]
  rfl


open Classical in
theorem sum_psi {ϖ : kˣ} (hϖ : IsUnif ϖ) {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (e : ℕ) (s s' : Res (k := k) e) :
    ∑ t : Res (k := k) e, (ψ (((Quotient.out t : 𝒪[k]) : k) *
      ((((ϖ ^ e)⁻¹ : kˣ) : k) * (((Quotient.out s : 𝒪[k]) : k) - ((Quotient.out s' : 𝒪[k]) : k)))) : ℂ) =
      if s = s' then (Fintype.card (Res (k := k) e) : ℂ) else 0 := by
  split_ifs with h
  · subst h; simp
  set x : k := (((ϖ ^ e)⁻¹ : kˣ) : k) * (((Quotient.out s : 𝒪[k]) : k) - ((Quotient.out s' : 𝒪[k]) : k)) with hx
  have h0 : 0 < valuation k ((ϖ ^ e : kˣ) : k) := zero_lt_iff.2 (by simp)
  have hvx : valuation k x = (valuation k ((ϖ ^ e : kˣ) : k))⁻¹ *
      valuation k ((Quotient.out s - Quotient.out s' : 𝒪[k]) : k) := by
    rw [hx, map_mul, Units.val_inv_eq_inv_val, map_inv₀]; rfl
  have triv : ∀ y : k, valuation k y ≤ 1 → ψ y = 1 := fun y hy => (hψ 1).2 le_rfl y (by simpa using hy)
  have hx1 : ¬ valuation k x ≤ valuation k ((1 : kˣ) : k) := by
    intro H
    rw [hvx, Units.val_one, map_one, inv_mul_le_iff₀ h0, mul_one, ← val_le_iff_mem hϖ, ← Ideal.Quotient.eq] at H
    exact h (by simpa using H)
  rw [← hψ x] at hx1
  push Not at hx1
  obtain ⟨y, hy, hy'⟩ := hx1
  have hx0 : x ≠ 0 := by
    rintro H
    rw [H, map_zero, le_zero_iff, map_eq_zero] at hy
    exact hy' (by simp [hy])
  have hr : y / x ∈ 𝒪[k] := by
    rw [Valuation.mem_integer_iff, map_div₀]; exact div_le_one_of_le₀ hy zero_le
  have key : ∀ a b : 𝒪[k], Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ e) a = Ideal.Quotient.mk _ b →
      ψ ((a : k) * x) = ψ ((b : k) * x) := fun a b hab => by
    rw [Ideal.Quotient.eq, val_le_iff_mem hϖ] at hab
    rw [show (a : k) * x = b * x + ((a - b : 𝒪[k]) : k) * x by push_cast; ring, AddChar.map_add_eq_mul,
      triv (((a - b : 𝒪[k]) : k) * x), mul_one]
    rw [map_mul, hvx, ← mul_assoc]
    exact mul_le_one' (by rw [mul_inv_le_iff₀ h0, one_mul]; exact hab) (Quotient.out s - Quotient.out s' : 𝒪[k]).2
  set S := ∑ t : Res (k := k) e, (ψ (((Quotient.out t : 𝒪[k]) : k) * x) : ℂ) with hS
  have hshift : S = ψ y * S := by
    rw [hS, Finset.mul_sum, ← Equiv.sum_comp (Equiv.addRight (Ideal.Quotient.mk _ (⟨_, hr⟩ : 𝒪[k]) : Res (k := k) e))]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [key _ (Quotient.out t + ⟨_, hr⟩) (by simp), ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
    congr 2
    push_cast
    field_simp
    ring
  by_contra hne
  exact hy' (Circle.ext (by simpa using (mul_left_eq_self₀.1 hshift.symm).resolve_right hne))

theorem sum_invFourierSum {ϖ : kˣ} (hϖ : IsUnif ϖ) {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (e : ℕ)
    (P : Finset D) (Ψ : Matrix A D k → ℂ) (X : Matrix A D k) (S₀ : A → P → Res (k := k) e) :
    ∑ T : A → P → Res (k := k) e, GlobalTheory.SplitFlip.invFourierSum ψ ϖ e P Ψ (setCols P X (liftRes T)) *
      (ψ (pairCols P (setCols P X ((ϖ ^ e)⁻¹ • liftRes S₀)) (liftRes T)) : ℂ) =
      (Fintype.card (Res (k := k) e) : ℂ) ^ (Fintype.card A * P.card) * Ψ (setCols P X ((ϖ ^ e)⁻¹ • liftRes S₀)) := by
  classical
  have h1 : ∀ T S, setCols P (setCols P X T) S = setCols P X S := fun T S => by
    ext i j; by_cases h : j ∈ P <;> simp [setCols, h]
  have h2 : ∀ T : A → P → Res (k := k) e, ∀ i, ∀ j ∈ P, setCols P X (liftRes T) i j ∈ 𝒪[k] := fun T i j h => by
    simpa [setCols, h] using liftRes_mem T i ⟨j, h⟩
  simp only [GlobalTheory.SplitFlip.invFourierSum_apply, if_pos (h2 _), h1, Finset.sum_mul]
  rw [Finset.sum_comm]
  have h3 : ∀ S T : A → P → Res (k := k) e,
      (ψ (-pairCols P (setCols P X (liftRes T)) ((ϖ ^ e)⁻¹ • liftRes S)) : ℂ) *
        (ψ (pairCols P (setCols P X ((ϖ ^ e)⁻¹ • liftRes S₀)) (liftRes T)) : ℂ) =
      ∏ i, ∏ j, (ψ (((Quotient.out (T i j) : 𝒪[k]) : k) * ((((ϖ ^ e)⁻¹ : kˣ) : k) *
        (((Quotient.out (S₀ i j) : 𝒪[k]) : k) - ((Quotient.out (S i j) : 𝒪[k]) : k)))) : ℂ) := fun S T => by
    have hp : ∀ {ι : Type _} (s : Finset ι) (f : ι → k), (ψ (∑ i ∈ s, f i) : ℂ) = ∏ i ∈ s, (ψ (f i) : ℂ) :=
      fun s f => by
        induction s using Finset.induction_on with
        | empty => simp
        | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul,
            Circle.coe_mul, ih]
    rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, ← Finset.prod_product', ← hp, Finset.sum_product]
    congr 2
    simp only [pairCols, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp [setCols, liftRes, Units.smul_def]
    ring
  have h4 : ∀ S : A → P → Res (k := k) e, ∑ T : A → P → Res (k := k) e,
      ∏ i, ∏ j, (ψ (((Quotient.out (T i j) : 𝒪[k]) : k) * ((((ϖ ^ e)⁻¹ : kˣ) : k) *
        (((Quotient.out (S₀ i j) : 𝒪[k]) : k) - ((Quotient.out (S i j) : 𝒪[k]) : k)))) : ℂ) =
      if S₀ = S then (Fintype.card (Res (k := k) e) : ℂ) ^ (Fintype.card A * P.card) else 0 := fun S => by
    rw [← Fintype.prod_sum (fun i (t : P → Res (k := k) e) => ∏ j, (ψ (((Quotient.out (t j) : 𝒪[k]) : k) *
      ((((ϖ ^ e)⁻¹ : kˣ) : k) *
        (((Quotient.out (S₀ i j) : 𝒪[k]) : k) - ((Quotient.out (S i j) : 𝒪[k]) : k)))) : ℂ))]
    have h5 : ∀ i, ∑ t : P → Res (k := k) e, ∏ j, (ψ (((Quotient.out (t j) : 𝒪[k]) : k) * ((((ϖ ^ e)⁻¹ : kˣ) : k) *
        (((Quotient.out (S₀ i j) : 𝒪[k]) : k) - ((Quotient.out (S i j) : 𝒪[k]) : k)))) : ℂ) =
        ∏ j, if S₀ i j = S i j then (Fintype.card (Res (k := k) e) : ℂ) else 0 := fun i => by
      rw [← Fintype.prod_sum (fun (j : P) (t : Res (k := k) e) => (ψ (((Quotient.out t : 𝒪[k]) : k) *
        ((((ϖ ^ e)⁻¹ : kˣ) : k) *
        (((Quotient.out (S₀ i j) : 𝒪[k]) : k) - ((Quotient.out (S i j) : 𝒪[k]) : k)))) : ℂ))]
      exact Finset.prod_congr rfl fun j _ => by convert sum_psi hϖ hψ e (S₀ i j) (S i j)
    rw [Finset.prod_congr rfl fun i _ => h5 i]
    split_ifs with h
    · subst h; simp [← pow_mul, mul_comm]
    · obtain ⟨i, hi⟩ := Function.ne_iff.1 h
      obtain ⟨j, hj⟩ := Function.ne_iff.1 hi
      exact Finset.prod_eq_zero (Finset.mem_univ i) (Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj))
  simp only [mul_assoc, h3, ← Finset.mul_sum, h4]
  simp [mul_comm]

variable [MeasurableSpace k] [BorelSpace k]

end NonZero

variable {A D₁ D₂ : Type*} [Fintype A] [DecidableEq A] [Fintype D₁] [DecidableEq D₁] [Fintype D₂] [DecidableEq D₂]





variable [MeasurableSpace k] [BorelSpace k]

end GlobalTheory.SplitFlip.Model
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex
open scoped DirectSum TensorProduct

namespace GlobalTheory.EtC

variable {R : Type} [CommRing R]

def Loc (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) : Prop :=
  ∃ S : Sieve U, S ∈ Scheme.etaleTopology U ∧ ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → P V g

abbrev sgl (F : Shv R) : Cx R := (CochainComplex.singleFunctor (Shv R) 0).obj F

def sglι (F : Shv R) : F ⟶ (sgl F).X 0 := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv

def resAug (F : Shv R) : sgl F ⟶ res R F := (injectiveResolution F).ι'

abbrev cpull {K L : Cx R} (f : K ⟶ L) (I : Cx R) (n : ℤ) : CohomologyClass L I n →+ CohomologyClass K I n :=
  cpre (Cocycle.ofHom f) I n n (zero_add n)

abbrev cpush (K : Cx R) {I J : Cx R} (f : I ⟶ J) (n : ℤ) : CohomologyClass K I n →+ CohomologyClass K J n :=
  cpost K (Cocycle.ofHom f) n n (add_zero n)

def Sx.face {E : Spc} {p : ℕ} {U : Scheme.{0}} (x : Sx E (p + 1) U) (i : Fin (p + 2)) : Sx E p U := (E.δ i).app (op U) x

def Sx.along {E : Spc} {p N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (θ : SimplexCategory.mk p ⟶ SimplexCategory.mk N) : Sx E p U :=
  (E.map θ.op).app (op U) x

def Sx.res {E : Spc} {p : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E p U) : Sx E p V := (E.obj (op (SimplexCategory.mk p))).map g.op x

def Sx.map {E E' : Spc} (f : E ⟶ E') {p : ℕ} {U : Scheme.{0}} (x : Sx E p U) : Sx E' p U :=
  (f.app (op (SimplexCategory.mk p))).app (op U) x

abbrev Tens (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : Type 1 :=
  ⨁ p : {p : ℤ × ℤ // p.1 + p.2 = w}, (Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U)

def Tens.res {I J : Cx R} {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) : Tens I J U w →ₗ[ULift.{1} R] Tens I J V w :=
  DirectSum.lmap fun p => TensorProduct.map ((I.X p.1.1).obj.map g.op).hom ((J.X p.1.2).obj.map g.op).hom

def Pair.lift {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) (w : ℤ) : Tens I J U w →ₗ[ULift.{1} R] Sec (K.X w) U := by
  classical
  exact DirectSum.toModule _ _ _ fun p => TensorProduct.lift (μ.mul U p.1.1 p.1.2 w p.2)

def Pair.IsTensor {I J K : Cx R} (μ : Pair I J K) : Prop :=
  (∀ (U : Scheme.{0}) (w : ℤ) (y : Sec (K.X w) U), Loc U fun V g => ∃ x, μ.lift V w x = Sec.res g y) ∧
  ∀ (U : Scheme.{0}) (w : ℤ) (x : Tens I J U w), μ.lift U w x = 0 → Loc U fun _ g => Tens.res g w x = 0

def Pair.Compat {I J K I' J' K' : Cx R} (μ : Pair I J K) (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J') (m : K ⟶ K') : Prop :=
  ∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
    Sec.map (m.f w) (μ.mul U s t w h a b) = ν.mul U s t w h (Sec.map (f.f s) a) (Sec.map (g.f t) b)

def Pair.IsFlip {I J K : Cx R} (μ : Pair I J K) (ν : Pair J I K) : Prop :=
  ∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
    ν.mul U t s w (by omega) b a = (s * t).negOnePow • μ.mul U s t w h a b

def FlatS (M : Shv R) : Prop :=
  ∃ (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (φ : P ⟶ M.obj),
    (∀ (U : Scheme.{0}) (y : Sec M U), Loc U fun V g => ∃ x, (φ.app (op V)).hom x = Sec.res g y) ∧
    (∀ (U : Scheme.{0}) (x : P.obj (op U)), (φ.app (op U)).hom x = 0 → Loc U fun _ g => (P.map g.op).hom x = 0) ∧
    ∀ U : Scheme.{0}, Nonempty U → Module.Flat (ULift.{1} R) (P.obj (op U))

def IsTwRes (q : ℕ) (i : ℤ) (T : Cx (ZMod q)) (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (T.X 0) U) : Prop :=
  T.IsStrictlyGE 0 ∧ ∃ ε : sgl (tw q i) ⟶ T, QuasiIso ε ∧
    ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), Sec.map (ε.f 0) (Sec.map (sglι (tw q i)) (twGen i ζ)) = e U ζ

def unitSec {U : Scheme.{0}} (u : (Γ(U, ⊤))ˣ) : Sec Gm U := ofRings.sec unitsF U (ULift.up (Additive.ofMul u))

def secClass (F : Shv R) {X : Scheme.{0}} (s : Sec F X) : H R (sch.obj X) F 0 :=
  pick fun c => ∃ α : Cocycle _ _ 0, CohomologyClass.mk α = c ∧ ev (R := R) α.1 0 0 (by simp) X (𝟙 X) = Sec.map (resι R F) s

def picClass {E : Spc} (L : E ⟶ ofCat (glCat 1)) : H ℤ E Gm 1 :=
  pick fun c => ∃ γ : Cocycle _ _ 1, CohomologyClass.mk γ = c ∧
    (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev (R := ℤ) γ.1 0 1 (by simp) U x = 0) ∧
    ∀ (U : Scheme.{0}) (x : Sx E 1 U), ev (R := ℤ) γ.1 1 0 (by simp) U x = Sec.map (resι ℤ Gm) (unitSec (lineUnit L x))

def SemiMap.IsImage {S : Type} [CommRing S] {I : Cx S} {J : Cx R} (ρ : SemiMap I J) {E : Spc} {n : ℤ}
    (α : Cochain ((chains S).obj E) I n) (β : Cochain ((chains R).obj E) J n) : Prop :=
    ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U), ev (R := R) β p s h U x = ρ.app U s (ev (R := S) α p s h U x)

abbrev Pr (N : ℕ) : Type := Σ p r : ℕ, (SimplexCategory.mk p ⟶ SimplexCategory.mk N) × (SimplexCategory.mk r ⟶ SimplexCategory.mk N)

def Pr.push {N M : ℕ} (θ : SimplexCategory.mk N ⟶ SimplexCategory.mk M) : (Pr N →₀ ℤ) →ₗ[ℤ] (Pr M →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ fun z => ⟨z.1, z.2.1, z.2.2.1 ≫ θ, z.2.2.2 ≫ θ⟩

def Pr.d₁ {N : ℕ} (z : Pr N) : Pr N →₀ ℤ :=
  Nat.casesOn (motive := fun p => (SimplexCategory.mk p ⟶ SimplexCategory.mk N) → (Pr N →₀ ℤ)) z.1 (fun _ => 0)
    (fun p a => ∑ i : Fin (p + 2), Finsupp.single ⟨p, z.2.1, SimplexCategory.δ i ≫ a, z.2.2.2⟩ ((-1) ^ (i : ℕ))) z.2.2.1

def Pr.d₂ {N : ℕ} (z : Pr N) : Pr N →₀ ℤ :=
  Nat.casesOn (motive := fun r => (SimplexCategory.mk r ⟶ SimplexCategory.mk N) → (Pr N →₀ ℤ)) z.2.1 (fun _ => 0)
    (fun r b => ∑ j : Fin (r + 2), Finsupp.single ⟨z.1, r, z.2.2.1, SimplexCategory.δ j ≫ b⟩ ((-1) ^ (j : ℕ))) z.2.2.2

def Pr.d (N : ℕ) : (Pr N →₀ ℤ) →ₗ[ℤ] (Pr N →₀ ℤ) := Finsupp.linearCombination ℤ fun z => z.d₁ + (-1 : ℤ) ^ z.1 • z.d₂

def Pr.aw (N : ℕ) : Pr N →₀ ℤ := ∑ p : Fin (N + 1), Finsupp.single
  ⟨p, N - p, SimplexCategory.subinterval 0 p (by omega), SimplexCategory.subinterval p (N - p) (by omega)⟩ 1

def Pr.wa (N : ℕ) : Pr N →₀ ℤ := ∑ p : Fin (N + 1), Finsupp.single
  ⟨N - p, p, SimplexCategory.subinterval p (N - p) (by omega), SimplexCategory.subinterval 0 p (by omega)⟩ ((-1) ^ ((p : ℕ) * (N - p)))

def Pr.Deg {N : ℕ} (k : ℕ) (c : Pr N →₀ ℤ) : Prop := ∀ z ∈ c.support, z.1 + z.2.1 = k

def Pr.bd {N : ℕ} (c : Pr N →₀ ℤ) : Pr (N + 1) →₀ ℤ := ∑ i : Fin (N + 2), (-1 : ℤ) ^ (i : ℕ) • Pr.push (SimplexCategory.δ i) c

end GlobalTheory.EtC

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
section
noncomputable section

open MeasureTheory Matrix
open scoped Topology Classical

namespace GlobalTheory.KSp

open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open GlobalTheory.SplitUnitary

section Abstract

structure Good (X : Type) [AddCommGroup X] [TopologicalSpace X] : Prop where
  grp : IsTopologicalAddGroup X
  t2 : T2Space X
  lc : LocallyCompactSpace X
  sc : SecondCountableTopology X
  large : ∀ K : Set X, IsCompact K → ∃ L : AddSubgroup X, IsCompact (L : Set X) ∧ IsOpen (L : Set X) ∧ K ⊆ L
  small : ∀ U ∈ 𝓝 (0 : X), ∃ L : AddSubgroup X, IsCompact (L : Set X) ∧ IsOpen (L : Set X) ∧ (L : Set X) ⊆ U

variable {X : Type} [AddCommGroup X] [TopologicalSpace X]

structure IsPair (e : X → X → ℂ) : Prop where
  add : ∀ x x' y, e (x + x') y = e x y * e x' y
  symm : ∀ x y, e x y = e y x
  norm : ∀ x y, ‖e x y‖ = 1
  lc : IsLocallyConstant fun p : X × X => e p.1 p.2
  small : ∀ U ∈ 𝓝 (0 : X), ∃ K : Set X, IsCompact K ∧ ∀ y, (∀ x ∈ K, e x y = 1) → y ∈ U
  big : ∀ U ∈ 𝓝 (0 : X), ∃ K : Set X, IsCompact K ∧ ∀ y, (∀ x ∈ U, e x y = 1) → y ∈ K

variable [MeasurableSpace X]

def four (μ : Measure X) (e : X → X → ℂ) (φ : X → ℂ) : X → ℂ := fun x => ∫ y, e x y * φ y ∂μ

def HasGauss (μ : Measure X) (f : X → ℂ) (γ : ℂ) : Prop :=
  ∀ K : Set X, IsCompact K → ∃ L : AddSubgroup X, IsCompact (L : Set X) ∧ IsOpen (L : Set X) ∧ K ⊆ L ∧
    ∫ x in (L : Set X), f x ∂μ = γ

end Abstract

section Group

variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
  {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]

def sgn (E : Type) [Field E] [Algebra F E] (t : Fˣ) : ℂ :=
  if t ∈ (Units.map (Algebra.norm F : E →* F)).range then 1 else -1

def pr (Q : Matrix α α E) (x y : Matrix α ν E) : F := form c Q (fromCols x 0) (fromCols 0 y)

def weyl (ν : Type) [Fintype ν] [DecidableEq ν] : UG c (stdJ ν E) :=
  ⟨⟨stdJ ν E, -stdJ ν E, by rw [Matrix.mul_neg, stdJ_mul_stdJ, neg_neg], by rw [Matrix.neg_mul, stdJ_mul_stdJ, neg_neg]⟩, by
    rw [mem_UG_iff]
    have h : ((stdJ ν E).map c)ᵀ = -stdJ ν E := by
      ext (i | i) (j | j) <;> simp [stdJ, Matrix.one_apply, eq_comm]
    change stdJ ν E * stdJ ν E * ((stdJ ν E).map c)ᵀ = stdJ ν E
    rw [h, stdJ_mul_stdJ]
    simp⟩

def unip (b : Matrix ν ν E) (hb : (b.map c)ᵀ = b) : UG c (stdJ ν E) :=
  ⟨⟨fromBlocks 1 b 0 1, fromBlocks 1 (-b) 0 1, by simp [fromBlocks_multiply], by simp [fromBlocks_multiply]⟩, by
    rw [mem_UG_iff]
    have h0 : (0 : Matrix ν ν E).map c = 0 := Matrix.map_zero _ (map_zero c)
    have h1 : (1 : Matrix ν ν E).map c = 1 := Matrix.map_one _ (map_zero c) (map_one c)
    simp [stdJ, fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply, h0, h1, hb]⟩

abbrev mat (g : UG c (stdJ ν E)) : Matrix (ν ⊕ ν) (ν ⊕ ν) E := ((g : GL (ν ⊕ ν) E) : Matrix (ν ⊕ ν) (ν ⊕ ν) E)

theorem mat_inv (g : UG c (stdJ ν E)) : mat c g⁻¹ = -(stdJ ν E * ((mat c g).map c)ᵀ * stdJ ν E) := by
  have hg : mat c g * stdJ ν E * ((mat c g).map c)ᵀ = stdJ ν E := (mem_UG_iff c (g : GL (ν ⊕ ν) E)).1 g.2
  have hr : mat c g * -(stdJ ν E * ((mat c g).map c)ᵀ * stdJ ν E) = 1 := by
    rw [Matrix.mul_neg, ← mul_assoc, ← mul_assoc, hg, stdJ_mul_stdJ, neg_neg]
  have hl : mat c g⁻¹ * mat c g = 1 := by
    simp [mat]
  calc mat c g⁻¹ = mat c g⁻¹ * (mat c g * -(stdJ ν E * ((mat c g).map c)ᵀ * stdJ ν E)) := by
        rw [hr, mul_one]
    _ = -(stdJ ν E * ((mat c g).map c)ᵀ * stdJ ν E) := by
        rw [← mul_assoc, hl, one_mul]

def sieg (ν : Type) [Fintype ν] [DecidableEq ν] : Subgroup (UG c (stdJ ν E)) where
  carrier := {g | (mat c g).toBlocks₂₁ = 0}
  one_mem' := by
    ext i j
    simp [mat, toBlocks₂₁]
  mul_mem' := by
    intro g h hg hh
    change (mat c g * mat c h).toBlocks₂₁ = 0
    rw [← fromBlocks_toBlocks (mat c g), ← fromBlocks_toBlocks (mat c h), fromBlocks_multiply, toBlocks_fromBlocks₂₁,
      show (mat c g).toBlocks₂₁ = 0 from hg, show (mat c h).toBlocks₂₁ = 0 from hh]
    simp
  inv_mem' := by
    intro g hg
    change (mat c g⁻¹).toBlocks₂₁ = 0
    have h0 : (0 : Matrix ν ν E).map c = 0 := Matrix.map_zero _ (map_zero c)
    rw [mat_inv, ← fromBlocks_toBlocks (mat c g), show (mat c g).toBlocks₂₁ = 0 from hg]
    simp [stdJ, fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_neg, h0]

theorem mem_sieg {g : UG c (stdJ ν E)} : g ∈ sieg c ν ↔ (mat c g).toBlocks₂₁ = 0 := by
  exact Iff.rfl

def InCell (g : UG c (stdJ ν E)) : Prop := ∃ p ∈ sieg c ν, ∃ q ∈ sieg c ν, g = p * weyl c ν * q

end Group

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type} [Field E] [Algebra F E] (c : E →ₐ[F] E)
  {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]

def sc (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Algebra F E]
    (χ : Eˣ →* Circle) (m : ℕ) (z : E) : ℂ :=
  if h : z = 0 then 0 else (χ (Units.mk0 z h) : ℂ) *
    ((nabs F (Units.map (Algebra.norm F : E →* F) (Units.mk0 z h)) ^ ((m : ℝ) / 2) : ℝ) : ℂ)

def parFun (ψ : AddChar F ℂ) (χ : Eˣ →* Circle) (Q : Matrix α α E) (g : Matrix (ν ⊕ ν) (ν ⊕ ν) E)
    (φ : Matrix α ν E → ℂ) : Matrix α ν E → ℂ :=
  fun x => sc F χ (Fintype.card α) g.toBlocks₁₁.det *
    (ψ (2⁻¹ * pr c Q (x * g.toBlocks₁₁) (x * g.toBlocks₁₂)) * φ (x * g.toBlocks₁₁))

def fou [TopologicalSpace E] [MeasurableSpace (Matrix α ν E)] (ψ : AddChar F ℂ) (Q : Matrix α α E)
    (μ : Measure (Matrix α ν E)) (φ : Matrix α ν E → ℂ) : Matrix α ν E → ℂ :=
  four μ (fun x y => ψ (pr c Q x y)) φ

structure IsKW [TopologicalSpace E] [MeasurableSpace (Matrix α ν E)] (ψ : AddChar F ℂ) (χ : Eˣ →* Circle)
    (Q : Matrix α α E) (μ : Measure (Matrix α ν E)) (κ : ℂ)
    (ω : Representation ℂ (UG c (stdJ ν E)) (SB (Matrix α ν E))) : Prop where
  par : ∀ p ∈ sieg c ν, ∀ φ : SB (Matrix α ν E), (ω p φ : Matrix α ν E → ℂ) = parFun c ψ χ Q (mat c p) φ
  wey : ∀ φ : SB (Matrix α ν E), (ω (weyl c ν) φ : Matrix α ν E → ℂ) = κ • fou c ψ Q μ φ

end Local

end GlobalTheory.KSp

end
end

