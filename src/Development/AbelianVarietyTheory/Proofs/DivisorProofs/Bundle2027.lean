module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1986
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1960
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1971
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1942
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1970

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinFormBilinFormsEqSumMinimiserValues
section
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc
open Matrix

namespace GlobalTheory.Poinc

theorem exists_pos_nat_mul_eq_int_family {κ : Type} [Fintype κ] (f : κ → ℚ) :
    ∃ D : ℕ, 0 < D ∧ ∃ z : κ → ℤ, ∀ k, (z k : ℚ) = D * f k := by
  classical
  refine ⟨∏ k, (f k).den, Finset.prod_pos (fun k _ => (f k).den_pos),
    fun k => (f k).num * ((∏ k, (f k).den) / (f k).den : ℕ), fun k => ?_⟩
  obtain ⟨m, hm⟩ : (f k).den ∣ ∏ k, (f k).den := Finset.dvd_prod_of_mem _ (Finset.mem_univ k)
  dsimp only
  rw [hm, Nat.mul_div_cancel_left _ (f k).den_pos]
  push_cast
  rw [← Rat.mul_den_eq_num]
  ring

theorem int_matrix_rat_kernel_eq_zero {ι I : Type} [Fintype ι] [Fintype I] (A : Matrix ι I ℤ)
    (hA : ∀ x, A *ᵥ x = 0 → x = 0) (x : I → ℚ) (hx : A.map (Int.cast : ℤ → ℚ) *ᵥ x = 0) : x = 0 := by
  obtain ⟨D, hD, z, hz⟩ := exists_pos_nat_mul_eq_int_family x
  have h1 : A *ᵥ z = 0 := by
    funext i
    apply Int.cast_injective (α := ℚ)
    have := congrFun hx i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply] at this ⊢
    push_cast
    simp only [hz, mul_left_comm _ (D : ℚ), ← Finset.mul_sum, this, mul_zero]
  have h2 := hA z h1
  funext j
  have := hz j
  rw [h2, Pi.zero_apply, Int.cast_zero, eq_comm, mul_eq_zero] at this
  rcases this with h | h
  · exact absurd h (Nat.cast_ne_zero.mpr hD.ne')
  · exact h

theorem exists_vecMul_eq_nat_smul {ι I : Type} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I]
    (A : Matrix ι I ℤ) (hA : ∀ x, A *ᵥ x = 0 → x = 0) (w : I → ℤ) :
    ∃ D : ℕ, 0 < D ∧ ∃ ν : ι → ℤ, ν ᵥ* A = (D : ℤ) • w := by
  set Aq := A.map (Int.cast : ℤ → ℚ) with hAq
  have hinj : Function.Injective Aq.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    exact int_matrix_rat_kernel_eq_zero A hA x hx
  let f : Module.Dual ℚ (I → ℚ) :=
    { toFun := fun x => (fun i => (w i : ℚ)) ⬝ᵥ x
      map_add' := fun x y => dotProduct_add _ _ _
      map_smul' := fun c x => by simp [dotProduct_smul] }
  obtain ⟨l, hl⟩ := LinearMap.dualMap_surjective_of_injective hinj f
  set lv : ι → ℚ := fun c => l (fun j => if c = j then 1 else 0) with hlvdef
  have hlv : ∀ y, l y = lv ⬝ᵥ y := by
    intro y
    rw [LinearMap.pi_apply_eq_sum_univ l y]
    simp [dotProduct, lv, mul_comm]
  have key : ∀ i, (w i : ℚ) = (lv ᵥ* Aq) i := by
    intro i
    have := LinearMap.congr_fun hl (Pi.single i 1)
    simp only [LinearMap.dualMap_apply, Matrix.mulVecLin_apply, hlv] at this
    rw [Matrix.dotProduct_mulVec, dotProduct_single, mul_one] at this
    rw [this]
    simp [f, dotProduct_single]
  obtain ⟨D, hD, ν, hν⟩ := exists_pos_nat_mul_eq_int_family lv
  refine ⟨D, hD, ν, ?_⟩
  funext i
  apply Int.cast_injective (α := ℚ)
  simp only [Matrix.vecMul, dotProduct, Pi.smul_apply, smul_eq_mul]
  push_cast
  rw [key i]
  simp only [Matrix.vecMul, dotProduct, hν, Aq, Matrix.map_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intros
  ring

theorem exists_nat_mul_eq_sum_of_injective {M ι : Type} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
    [Fintype ι] [DecidableEq ι] (g : M →ₗ[ℤ] (ι → ℤ)) (hg : Function.Injective g) (w : M →ₗ[ℤ] ℤ) :
    ∃ D : ℕ, 0 < D ∧ ∃ ν : ι → ℤ, ∀ x, (D : ℤ) * w x = ∑ c, ν c * g x c := by
  classical
  set e := (Module.Free.chooseBasis ℤ M).equivFun with he
  set A := LinearMap.toMatrix' (g ∘ₗ e.symm.toLinearMap) with hAdef
  have hA : ∀ x, A *ᵥ x = 0 → x = 0 := by
    intro x hx
    rw [hAdef, LinearMap.toMatrix'_mulVec] at hx
    have h := hg (hx.trans (map_zero g).symm)
    simpa using h
  obtain ⟨D, hD, ν, hν⟩ :=
    exists_vecMul_eq_nat_smul A hA (fun i => w (e.symm (fun j => if i = j then 1 else 0)))
  refine ⟨D, hD, ν, fun x => ?_⟩
  have h1 : g x = A *ᵥ e x := by rw [hAdef, LinearMap.toMatrix'_mulVec]; simp
  have h2 : w x = ∑ i, e x i * w (e.symm (fun j => if i = j then 1 else 0)) := by
    have := LinearMap.pi_apply_eq_sum_univ (w ∘ₗ e.symm.toLinearMap) (e x)
    simpa using this
  have h3 : ∑ c, ν c * g x c = ν ⬝ᵥ (A *ᵥ e x) := by rw [h1]; rfl
  rw [h3, Matrix.dotProduct_mulVec, hν, h2]
  simp [dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]

theorem linForm_eq_sum_qW_lifts : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (N : ℕ) [NeZero N], 3 ≤ N →
    (∃ ε : Fin 8 → ℤ, Nat.Coprime N (2 * (∑ u, ∑ v, W u v * ε u * ε v).natAbs)) → ∀ r : ℕ,
    ∀ μ : ((Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ)), (∀ c u i, ((μ c u i : ℤ) : ZMod N) = c u i) →
    ∀ ℓ : LinearMap.BilinForm ℤ (Fin r → ℤ) →ₗ[ℤ] ℤ, ∃ (D : ℕ) (ν : (Fin 8 → Fin r → ZMod N) → ℤ), 0 < D ∧
      ∀ b : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ x y, b x y = b y x) → (D : ℤ) * ℓ b = ∑ c, ν c * qW W b (μ c) := by
  intro W hW N hN0 hN hε r μ hμ ℓ
  let S : Submodule ℤ (LinearMap.BilinForm ℤ (Fin r → ℤ)) :=
    { carrier := {b | ∀ x y, b x y = b y x}
      add_mem' := by intro a b ha hb x y; simp [ha x y, hb x y]
      zero_mem' := by intro x y; simp
      smul_mem' := by intro c b hb x y; simp [hb x y] }
  let Φ : LinearMap.BilinForm ℤ (Fin r → ℤ) →ₗ[ℤ] ((Fin 8 → Fin r → ZMod N) → ℤ) :=
    { toFun := fun b c => qW W b (μ c)
      map_add' := by intro a b; funext c; simp [qW, mul_add, Finset.sum_add_distrib]
      map_smul' := by intro k b; funext c; simp [qW, Finset.mul_sum, mul_left_comm] }
  have hinj : Function.Injective (Φ ∘ₗ S.subtype) := by
    intro x y hxy
    apply Subtype.ext
    have hs : ∀ u v, ((x : LinearMap.BilinForm ℤ (Fin r → ℤ)) - (y : LinearMap.BilinForm ℤ (Fin r → ℤ))) u v = ((x : LinearMap.BilinForm ℤ (Fin r → ℤ)) - (y : LinearMap.BilinForm ℤ (Fin r → ℤ))) v u := by
      intro u v; simp [x.2 u v, y.2 u v]
    have h0 : ∀ c, qW W ((x : LinearMap.BilinForm ℤ (Fin r → ℤ)) - (y : LinearMap.BilinForm ℤ (Fin r → ℤ))) (μ c) = 0 := by
      intro c
      have := congrFun hxy c
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.coe_mk, AddHom.coe_mk, Φ] at this
      simp only [qW, LinearMap.sub_apply, mul_sub, Finset.sum_sub_distrib] at this ⊢
      rw [this, sub_self]
    exact sub_eq_zero.mp (_root_.GlobalTheory.Poinc.symm_eq_zero_of_qW_lifts W hW N hN r hε μ hμ _ hs h0)
  obtain ⟨D, hD, ν, hν⟩ := exists_nat_mul_eq_sum_of_injective (Φ ∘ₗ S.subtype) hinj (ℓ ∘ₗ S.subtype)
  exact ⟨D, ν, hD, fun b hb => hν ⟨b, hb⟩⟩

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfCompatibleRationalLocalUnits
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.GlueRat

variable {S : Scheme.{0}} [IsIntegral S]

theorem genericPoint_mem' {U : S.Opens} {x : S} (hx : x ∈ U) : genericPoint S ∈ U :=
  ((genericPoint_spec S).mem_open_set_iff U.isOpen).mpr ⟨x, trivial, hx⟩

theorem unit_eq_of_germ {V : S.Opens} {a b : Γ(S, V)ˣ}
    (h : ∀ hg : genericPoint S ∈ V, S.presheaf.germ V (genericPoint S) hg (a : Γ(S, V)) =
      S.presheaf.germ V (genericPoint S) hg (b : Γ(S, V))) : a = b := by
  by_cases hg : genericPoint S ∈ V
  · exact Units.ext (germ_injective_of_isIntegral S (genericPoint S) hg (h hg))
  · exact unit_ext fun x hx => (hg (genericPoint_mem' hx)).elim

theorem germ_res_unit {U V : S.Opens} (hle : V ≤ U) (hg : genericPoint S ∈ V) (a : Γ(S, U)ˣ) :
    S.presheaf.germ V (genericPoint S) hg ((res hle a : Γ(S, V)ˣ) : Γ(S, V)) =
      S.presheaf.germ U (genericPoint S) (hle hg) (a : Γ(S, U)) :=
  S.presheaf.germ_res_apply (homOfLE hle) _ hg _

theorem exists_unit_of_local {W : S.Opens} (f : S.presheaf.stalk (genericPoint S))
    (H : ∀ x ∈ W, ∃ (V : S.Opens) (_ : V ≤ W) (_ : x ∈ V) (u : Γ(S, V)ˣ),
      ∀ h : genericPoint S ∈ V, S.presheaf.germ V (genericPoint S) h (u : Γ(S, V)) = f) :
    ∃ s : Γ(S, W)ˣ, ∀ h : genericPoint S ∈ W, S.presheaf.germ W (genericPoint S) h (s : Γ(S, W)) = f := by
  choose V hVW hxV u hu using fun x : W => H x.1 x.2
  obtain ⟨s, hs⟩ := glue_unit W V hVW (fun x hx => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hx⟩, hxV _⟩) u
    (fun i j z hz => by
      rw [← gm_res (𝟙 S) z (inf_le_left : V i ⊓ V j ≤ V i) hz,
        ← gm_res (𝟙 S) z (inf_le_right : V i ⊓ V j ≤ V j) hz]
      congr 1
      refine unit_eq_of_germ fun hg => ?_
      rw [germ_res_unit, germ_res_unit, hu i (hg.1), hu j hg.2])
  refine ⟨s, fun h => ?_⟩
  rw [← germ_res_unit (hVW ⟨_, h⟩) (hxV ⟨_, h⟩), hs]
  exact hu _ _

end GlobalTheory.GlueRat


open GlobalTheory.GlueRat in
theorem GlobalTheory.GlueRat.lbIso_of_rat : ∀ (S : Scheme.{0}) [IsIntegral S] (A B : LB S) (f : B.ι × A.ι → S.presheaf.stalk (genericPoint S)),
    (∀ p, ∀ x ∈ B.U p.1 ⊓ A.U p.2, ∃ (V : S.Opens) (_ : V ≤ B.U p.1 ⊓ A.U p.2) (_ : x ∈ V) (u : Γ(S, V)ˣ),
      ∀ h : genericPoint S ∈ V, S.presheaf.germ V (genericPoint S) h (u : Γ(S, V)) = f p) →
    (∀ p q (h1 : genericPoint S ∈ B.U p.1 ⊓ B.U q.1) (h2 : genericPoint S ∈ A.U p.2 ⊓ A.U q.2),
      f p * S.presheaf.germ _ (genericPoint S) h2 (A.g p.2 q.2 : Γ(S, A.U p.2 ⊓ A.U q.2)) =
        S.presheaf.germ _ (genericPoint S) h1 (B.g p.1 q.1 : Γ(S, B.U p.1 ⊓ B.U q.1)) * f q) →
    LBIso A B := by
  intro S _ A B f H1 H2
  choose s hs using fun p => exists_unit_of_local (f p) (H1 p)
  refine ⟨⟨s⟩, fun p q => unit_eq_of_germ fun hg => ?_⟩
  have hp : genericPoint S ∈ B.U p.1 ⊓ A.U p.2 := hg.1
  have hq : genericPoint S ∈ B.U q.1 ⊓ A.U q.2 := hg.2
  have h1 : genericPoint S ∈ B.U p.1 ⊓ B.U q.1 := ⟨hg.1.1, hg.2.1⟩
  have h2 : genericPoint S ∈ A.U p.2 ⊓ A.U q.2 := ⟨hg.1.2, hg.2.2⟩
  refine ((germ_res_unit _ hg _).trans (hs p hp)).trans ?_
  set O := (LB.div B A).U p ⊓ (LB.div B A).U q
  have lB : O ≤ B.U p.1 ⊓ B.U q.1 := le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
  have lA : O ≤ A.U p.2 ⊓ A.U q.2 := le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
  have lq : O ≤ B.U q.1 ⊓ A.U q.2 := inf_le_right
  change f p = S.presheaf.germ O (genericPoint S) hg
    (((res lB (B.g p.1 q.1) * (res lA (A.g p.2 q.2))⁻¹ * res lq (s q) : Γ(S, O)ˣ)) : Γ(S, O))
  have e : S.presheaf.germ O (genericPoint S) hg (((res lA (A.g p.2 q.2))⁻¹ : Γ(S, O)ˣ) : Γ(S, O)) *
      S.presheaf.germ _ (genericPoint S) h2 (A.g p.2 q.2 : Γ(S, A.U p.2 ⊓ A.U q.2)) = 1 := by
    rw [← germ_res_unit lA hg, ← map_mul, Units.inv_mul, map_one]
  have H := H2 p q h1 h2
  simp only [Units.val_mul, map_mul, germ_res_unit, hs q hq]
  calc f p = f p * (S.presheaf.germ O (genericPoint S) hg (((res lA (A.g p.2 q.2))⁻¹ : Γ(S, O)ˣ) : Γ(S, O)) *
      S.presheaf.germ _ (genericPoint S) h2 (A.g p.2 q.2 : Γ(S, A.U p.2 ⊓ A.U q.2))) := by rw [e, _root_.mul_one]
    _ = _ := by rw [mul_comm (S.presheaf.germ O _ hg _), ← _root_.mul_assoc, H]; ring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleTrivialOfGeneratorFpqcDescent
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw

namespace GlobalTheory.FlatDescent

theorem injective_app_of_flat {X Y : Scheme.{0}} (p : Y ⟶ X) [Flat p] [Surjective p] [QuasiCompact p]
    (U : X.Opens) : Function.Injective (p.app U) := by
  have := effectiveEpi_morphismRestrict p U
  intro a b hab
  have hb : Function.Bijective U.topIso.inv := ConcreteCategory.bijective_of_isIso _
  apply hb.1
  apply injective_appTop_of_epi (p ∣_ U)
  rw [appTop_morphismRestrict_apply, appTop_morphismRestrict_apply, hab]

theorem unit_ext_of_flat {X Y : Scheme.{0}} (p : Y ⟶ X) [Flat p] [Surjective p] [QuasiCompact p]
    {U : X.Opens} {a b : Γ(X, U)ˣ} (h : ∀ y : Y, p y ∈ U → gm p y U a = gm p y U b) : a = b := by
  have e : pullU p U a = pullU p U b := unit_ext fun y hy => by
    rw [gm_pull (𝟙 Y) p y U hy, gm_pull (𝟙 Y) p y U hy, Category.id_comp]
    exact h y hy
  exact Units.ext (injective_app_of_flat p U (congrArg Units.val e))

theorem exists_unit_of_gm_eq {X X' Z : Scheme.{0}} (f : X' ⟶ X) [Flat f] [Surjective f] [QuasiCompact f]
    {g₁ g₂ : Z ⟶ X'} (h : IsPullback g₁ g₂ f f) (U : X.Opens) (s : Γ(X', f ⁻¹ᵁ U)ˣ)
    (hs : ∀ z : Z, f (g₁ z) ∈ U → gm g₁ z _ s = gm g₂ z _ s) :
    ∃ a : Γ(X, U)ˣ, pullU f U a = s := by
  have hg : g₁ ⁻¹ᵁ f ⁻¹ᵁ U ≤ g₂ ⁻¹ᵁ f ⁻¹ᵁ U := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, h.w]
  have e : res le_rfl (pullU g₁ _ s) = res hg (pullU g₂ _ s) := unit_ext fun z hz => by
    rw [gm_res _ z _ hz, gm_res _ z _ hz, gm_pull (𝟙 Z) g₁ z _ hz, gm_pull (𝟙 Z) g₂ z _ (hg hz),
      Category.id_comp, Category.id_comp]
    exact hs z hz
  obtain ⟨a, ha, -⟩ := (existsUnique_app_eq_iff f h U _ rfl le_rfl hg s.val).2 (congrArg Units.val e)
  obtain ⟨a, rfl⟩ := (isUnit_app_iff f U a).1 (ha ▸ s.isUnit)
  exact ⟨a, Units.ext ha⟩

theorem triv_of_gen_descent : ∀ {X X' Z : Scheme.{0}} (M : LB X), M.IsLB → ∀ (f : X' ⟶ X), Flat f →
    Surjective f → QuasiCompact f → ∀ (g₁ g₂ : Z ⟶ X'), IsPullback g₁ g₂ f f →
    ∀ t : LB.Gen (M.pull f), t.IsGen →
    (∀ (z : Z) (J : (Z ⟶ X) → M.ι), Geo.Tor.Good M z J → val t g₁ z J = val t g₂ z J) → Triv M := by
  intro X X' Z M hM f _ _ _ g₁ g₂ h t ht hv
  have le : ∀ i, f ⁻¹ᵁ M.U i ≤ LB.wchart M (fun _ : PUnit => f) (fun _ => i) := fun i x hx =>
    Set.mem_iInter.2 fun _ => hx
  have ex : ∀ i, ∃ a : Γ(X, M.U i)ˣ, pullU f _ a = res (le i) (t.s fun _ => i) := fun i =>
    exists_unit_of_gm_eq f h (M.U i) _ fun z hz => by
      have hz₂ : f (g₂ z) ∈ M.U i := (congrArg (fun q : Z ⟶ X => q z ∈ M.U i) h.w).mp hz
      obtain ⟨J, hJ, eJ⟩ := exists_good M hM z (fun _ : PUnit => g₁ ≫ f) (fun _ => i)
        (fun _ _ _ => rfl) (fun _ => hz)
      have v := hv z J hJ
      rw [val_of t g₁ z J (fun _ => i) eJ,
        val_of t g₂ z J (fun _ => i) (fun k => h.w ▸ eJ k)] at v
      exact (gm_res g₁ z _ hz _).trans (v.trans (gm_res g₂ z _ hz₂ _).symm)
  choose a ha using ex
  have ga : ∀ i (y : X'), f y ∈ M.U i →
      gm f y (M.U i) (a i) = gm (𝟙 X') y (LB.wchart M (fun _ : PUnit => f) (fun _ => i)) (t.s fun _ => i) :=
    fun i y hy => by
      have := gm_pull (𝟙 X') f y (M.U i) hy (a i)
      rw [Category.id_comp, ha] at this
      exact this.symm.trans (gm_res (𝟙 X') y (le i) hy _)
  refine ⟨⟨a⟩, fun i j => unit_ext_of_flat f fun y hy => ?_⟩
  have c := gen_trans ht (𝟙 X') y (j := fun _ => i) (j' := fun _ => j) (le i hy.1) (le j hy.2)
  rw [← ga i y hy.1, ← ga j y hy.2, trF, Fintype.prod_unique, zpow_one, Category.id_comp] at c
  exact (gm_res f y _ hy _).trans (c.trans ((map_mul _ _ _).trans (congrArg _ (gm_res f y _ hy _))).symm)

end GlobalTheory.FlatDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogOrdFracComapFormallyUnramifiedDvr
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.RestrictOrd

open IsLocalRing

theorem isLocalHom_restrict {K L : Type} [Field K] [Field L] (φ : K →+* L)
    (V : ValuationSubring L) :
    IsLocalHom (φ.restrict (V.comap φ) V fun _ hx => hx) := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨b, hb⟩ := ha
  have hb' : ((b : V) : L) = φ (a : K) := by
    rw [hb]; rfl
  have ha0 : (a : K) ≠ 0 := by
    intro h0
    have : ((b : V) : L) = 0 := by rw [hb', h0, map_zero]
    exact b.ne_zero (Subtype.ext this)
  have hmem : (a : K)⁻¹ ∈ V.comap φ := by
    change φ (a : K)⁻¹ ∈ V
    rw [map_inv₀, ← hb']
    have : ((b⁻¹ : Vˣ) : V) * (b : V) = 1 := b.inv_mul
    have h2 : (((b⁻¹ : Vˣ) : V) : L) = ((b : V) : L)⁻¹ := by
      exact eq_inv_of_mul_eq_one_left (congrArg Subtype.val this)
    rw [← h2]
    exact ((b⁻¹ : Vˣ) : V).2
  exact isUnit_iff_exists_inv.2 ⟨⟨(a : K)⁻¹, hmem⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩

theorem log_ordFrac_comap (K L : Type) [Field K] [Field L] (φ : K →+* L)
    (V : ValuationSubring L) [IsDiscreteValuationRing V] [IsDiscreteValuationRing (V.comap φ)] :
    (letI := (φ.restrict (V.comap φ) V fun _ hx => hx).toAlgebra;
      Algebra.FormallyUnramified (V.comap φ) V ∧ Algebra.EssFiniteType (V.comap φ) V) →
    ∀ g : K, g ≠ 0 →
      WithZero.log (Ring.ordFrac V (φ g)) = WithZero.log (Ring.ordFrac (V.comap φ) g) := by
  intro h g hg
  set ψ := φ.restrict (V.comap φ) V fun _ hx => hx with hψdef
  letI := ψ.toAlgebra
  obtain ⟨hu, he⟩ := h
  haveI : IsLocalHom ψ := isLocalHom_restrict φ V
  haveI : IsLocalHom (algebraMap (V.comap φ) V) := inferInstanceAs (IsLocalHom ψ)
  have hmap : (maximalIdeal (V.comap φ)).map (algebraMap (V.comap φ) V) = maximalIdeal V :=
    Algebra.FormallyUnramified.map_maximalIdeal
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible (V.comap φ)
  have ht' : Irreducible (ψ t) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, ← hmap,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer t).1 ht, Ideal.map_span,
      Set.image_singleton]
    rfl
  exact GlobalTheory.EtaleDiv.log_ordFrac_map (V.comap φ) V φ ψ (fun _ => rfl) ht ht' hg

end GlobalTheory.RestrictOrd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogarithmicDerivationLocalizationAtPrimeSpanOfRi
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

namespace GlobalTheory

theorem logDerivation_atPrime_span : ∀ (F A R : Type) [Field F] [CommRing A] [CommRing R] [IsNoetherianRing A] [Algebra F A] [Algebra A R] [Algebra F R] [IsScalarTower F A R] [Algebra.FiniteType F A] (P : Ideal A) [P.IsPrime] [IsLocalization.AtPrime R P] (I : Ideal A) (n : ℕ) (b : Fin n → Derivation ℤ A A), (∀ D : Derivation ℤ A A, (∀ c, D (algebraMap F A c) = 0) → (∀ f ∈ I, D f ∈ I) → ∃ c : Fin n → A, D = ∑ j, c j • b j) → ∀ D' : Derivation F R R, (∀ f ∈ I.map (algebraMap A R), D' f ∈ I.map (algebraMap A R)) → ∃ c : Fin n → R, ∀ a : A, D' (algebraMap A R a) = ∑ j, c j * algebraMap A R (b j a) := by
  intro F A R _ _ _ _ _ _ _ _ _ P _ _ I n b hb D' hD'
  classical

  have hloc : IsLocalizedModule P.primeCompl (Algebra.linearMap A R) :=
    isLocalizedModule_iff_isLocalization.mpr inferInstance
  have : Module.FinitePresentation A Ω[A⁄F] := Module.finitePresentation_of_finite _ _
  let Dc : Derivation F A R := D'.compAlgebraMap A
  obtain ⟨h, s, hs⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
    P.primeCompl (Algebra.linearMap A R) Dc.liftKaehlerDifferential
  let D₀ : Derivation F A A := h.compDer (KaehlerDifferential.D F A)
  have hD₀ : ∀ y : A, algebraMap A R (D₀ y) = algebraMap A R (s : A) * D' (algebraMap A R y) := by
    intro y
    have := congrArg (fun φ => φ (KaehlerDifferential.D F A y)) hs
    simp only [LinearMap.coe_comp, Function.comp_apply, Algebra.linearMap_apply,
      LinearMap.smul_apply, Derivation.liftKaehlerDifferential_comp_D] at this
    rw [Submonoid.smul_def, Algebra.smul_def] at this
    simpa [D₀, Dc] using this

  obtain ⟨G, hG⟩ := (IsNoetherian.noetherian I : I.FG)
  have hgen : ∀ g ∈ G, ∃ t ∈ P.primeCompl, t * D₀ g ∈ I := by
    intro g hg
    have hgI : g ∈ I := hG ▸ Ideal.subset_span hg
    have : algebraMap A R (D₀ g) ∈ I.map (algebraMap A R) := by
      rw [hD₀]
      exact Ideal.mul_mem_left _ _ (hD' _ (Ideal.mem_map_of_mem _ hgI))
    exact (IsLocalization.algebraMap_mem_map_algebraMap_iff P.primeCompl R I _).mp this
  choose! tg htgP htgI using hgen
  let t' : A := ∏ g ∈ G, tg g
  have ht'P : t' ∈ P.primeCompl := by
    have := prod_mem (S := P.primeCompl) (t := G) (f := tg) (fun g hg => htgP g hg)
    simpa [t'] using this
  let D₁ : Derivation ℤ A A := t' • (D₀.restrictScalars ℤ)
  have hD₁ : ∀ x, D₁ x = t' * D₀ x := fun x => by simp [D₁, smul_eq_mul]
  have hkill : ∀ c, D₁ (algebraMap F A c) = 0 := fun c => by
    rw [hD₁, Derivation.map_algebraMap, mul_zero]
  have hkeep : ∀ f ∈ I, D₁ f ∈ I := by
    intro f hf
    rw [← hG] at hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      rw [hD₁]
      have hd : tg x ∣ t' := Finset.dvd_prod_of_mem _ hx
      obtain ⟨k, hk⟩ := hd
      rw [hk, mul_comm (tg x) k, mul_assoc]
      exact Ideal.mul_mem_left _ _ (htgI x hx)
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Ideal.add_mem _ hx hy
    | smul a x hxs hx =>
      rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ hx) (Ideal.mul_mem_right _ _ ?_)
      rw [hG] at hxs; exact hxs
  obtain ⟨c, hc⟩ := hb D₁ hkill hkeep

  have hu : IsUnit (algebraMap A R (t' * s)) :=
    IsLocalization.map_units R (⟨t' * s, P.primeCompl.mul_mem ht'P s.2⟩ : P.primeCompl)
  refine ⟨fun j => hu.unit⁻¹ * algebraMap A R (c j), fun a => ?_⟩
  have e1 : algebraMap A R (D₁ a) = ∑ j, algebraMap A R (c j) * algebraMap A R (b j a) := by
    rw [hc]
    have : ∀ (s : Finset (Fin n)), (∑ j ∈ s, c j • b j) a = ∑ j ∈ s, c j * b j a := by
      intro s; induction s using Finset.induction_on with
      | empty => simp
      | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, Derivation.add_apply, ih, Derivation.smul_apply, smul_eq_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [this, map_sum]; simp only [map_mul]
  have e2 : algebraMap A R (D₁ a) = algebraMap A R (t' * s) * D' (algebraMap A R a) := by
    rw [hD₁, map_mul, hD₀, map_mul, mul_assoc]
  rw [e2] at e1
  have : D' (algebraMap A R a) = (hu.unit⁻¹ : Rˣ) * ∑ j, algebraMap A R (c j) * algebraMap A R (b j a) := by
    rw [← e1, ← mul_assoc, IsUnit.val_inv_mul, one_mul]
  rw [this, Finset.mul_sum]
  simp only [mul_assoc]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismEqOfEqOnThickenings
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem hom_eq_of_reductions_eq : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (X Z : Over (Spec (CommRingCat.of R))), IsProper X.hom → IsSeparated Z.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (b : ∀ e, (Y e).left ⟶ X.left), (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → ∀ g g' : X ⟶ Z, (∀ e, b e ≫ g.left = b e ≫ g'.left) → g = g' := by
  intro R _ _ I hI X Z hX hZ Y b hb g g' hg
  have hι : IsClosedImmersion (equalizer.ι g g').left := isClosedImmersion_equalizer_ι_left g g'
  have hN : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have hle : ∀ e : ℕ, (equalizer.ι g g').left.ker ≤ baseIdeal X.hom (I ^ (e + 1)) := by
    intro e
    rw [← (_root_.GlobalTheory.FormalAlg.baseChange_quotient R (I ^ (e + 1)) X.left (Y e).left X.hom (b e) (Y e).hom (hb e)).2.1]
    let c : Over.mk (b e ≫ X.hom) ⟶ X := Over.homMk (b e) rfl
    have hc : c ≫ g = c ≫ g' := by
      ext
      exact hg e
    have h1 : (equalizer.lift c hc).left ≫ (equalizer.ι g g').left = b e := by
      rw [← Over.comp_left, equalizer.lift_ι]
      rfl
    rw [← h1]
    exact Scheme.Hom.le_ker_comp _ _
  have hbot : (equalizer.ι g g').left.ker ≤ ⊥ :=
    _root_.GlobalTheory.FormalAlg.le_of_le_reductions R I hI X.left X.hom _ ⊥ inferInstance fun e => (hle e).trans le_sup_right
  have hiso : IsIso (equalizer.ι g g').left :=
    IsClosedImmersion.isIso_iff_ker_eq_bot.2 (le_bot_iff.1 hbot)
  ext
  rw [← cancel_epi (equalizer.ι g g').left, ← Over.comp_left, ← Over.comp_left, equalizer.condition]

end GlobalTheory.FormalAlg
end

