module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFrobGBaseChange
public import Formalism.SharpRestriction.Divisibility.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrismaticDieudonnePerfdIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsWeilChar
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0186
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
public import ReciprocityTheory.DualLattices.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0242
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2417
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2384
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2236
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2381
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2277
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2427
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0439
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2457
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0122
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2471

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentDimAddDualCotangentDimLeHeight
section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory


open GlobalTheory.PDivGroup.CotDim in
theorem GlobalTheory.PDivGroup.finrank_cot_add_finrank_cot_dual_le_of_cast_eq_zero (p : ℕ) [Fact p.Prime]
    (k : Type) [Field k] (hp : (p : k) = 0) (Γ : PDivGroup p k) :
    Module.finrank k (Cot k (Γ.A 1)) + Module.finrank k (Cot k (Γ.dual.A 1)) ≤ Γ.height := by
  letI : CharP k p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2 hp
  have hdimD := finrank_level_one Γ.dual
  have hmulP : Function.Injective (Γ.mulP 1) := fun a b e => by
    refine CartierDual.eq_of_forall_apply (R := k) fun φ => ?_
    obtain ⟨ψ, rfl⟩ := Γ.dual_mulP_surjective 1 φ
    change ψ.ofConv (Γ.mulP 1 a) = ψ.ofConv (Γ.mulP 1 b)
    rw [e]

  have hord := finrank_eq_ker_mul_range k (Γ.dual.A 1) _ ((PDivGroup.relFrob hp Γ.dual).app 1)
  have hcot (G : PDivGroup p k) :
      p ^ Module.finrank k (Cot k (G.A 1)) ≤
        Module.finrank k (G.A 1 ⧸ kerIdeal ((PDivGroup.relFrob hp G).app 1)) :=
    (FrobKerOrder.pow_finrank_cot_le (p := p) (k := k) (H := G.A 1)).trans
      (quot_finrank_le (GlobalTheory.T.relativeFrobeniusKernelIdeal_le_frobeniusKernelIdeal p k hp G 1))

  have hker : LinearMap.ker ((PDivGroup.verschiebung hp Γ).app 1 :
        Γ.A 1 →ₐ[k] (PDivGroup.frobTwist hp Γ).A 1).toLinearMap ≤
      (kerIdeal ((PDivGroup.relFrob hp Γ).app 1)).restrictScalars k := by
    intro a ha
    have h := GlobalTheory.T.mulP_mem_kerIdeal_comp_relFrob_of_verschiebung_eq_zero p k hp Γ a ha
    rw [kerIdeal_comp] at h
    change a ∈ kerIdeal ((PDivGroup.relFrob hp Γ).app 1)
    rw [← _root_.GlobalTheory.PDiv.comap_map_eq_self_of_hopf_injective k _ _ (Γ.mulP 1) hmulP
      (kerIdeal ((PDivGroup.relFrob hp Γ).app 1))]
    exact h
  have hV := _root_.GlobalTheory.PDivGroup.finrank_range_relFrob_dual_add_finrank_ker_verschiebung p k hp Γ
  have hq := Submodule.finrank_quotient_add_finrank
    ((kerIdeal ((PDivGroup.relFrob hp Γ).app 1)).restrictScalars k)
  rw [(Submodule.Quotient.restrictScalarsEquiv k (kerIdeal ((PDivGroup.relFrob hp Γ).app 1))).finrank_eq] at hq
  have hmono := Submodule.finrank_mono hker
  have hrD : Module.finrank k (Γ.A 1 ⧸ kerIdeal ((PDivGroup.relFrob hp Γ).app 1)) ≤
      Module.finrank k (LinearMap.range ((PDivGroup.relFrob hp Γ.dual).app 1 :
        (PDivGroup.frobTwist hp Γ.dual).A 1 →ₐ[k] Γ.dual.A 1).toLinearMap) := by omega
  apply (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).1
  change _ ≤ p ^ Γ.dual.height
  rw [pow_add, mul_comm, ← hdimD, hord]
  exact Nat.mul_le_mul (hcot Γ.dual) ((hcot Γ).trans hrD)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineForgetFormsBijectiveSiteAndPairs
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

theorem fnMap_pullbackBijective12_of_acyclic {C : Type 1} [Category.{0} C] (K : Cx C)
    (h1 : K.M1.Ac0 ∧ K.M1.Ac1 ∧ K.M1.Ac2) (h2 : K.M2.Ac0 ∧ K.M2.Ac1 ∧ K.M2.Ac2) (h3 : K.M3.Ac0 ∧ K.M3.Ac1 ∧ K.M3.Ac2) :
    K.fnMap.PullbackBijectiveDegreesOneTwo :=
  And.intro (GlobalTheory.T.forget_positive_h1_bijective C K h1.1 h1.2.1 h2.1) (GlobalTheory.T.forget_positive_h2_bijective C K h1.2.1 h1.2.2 h2.1 h2.2.1 h3.1)

variable {R : Type} [CommRing R] {I : Ideal R} {κ : DividedPowers I} {X : Scheme.{0}} {t : X ⟶ Sp R}
  {Y : Scheme.{0}} {i : X ⟶ Y}

theorem top_le_preimage_of_hom {T T' : Thick κ t} (f : T ⟶ T') (U : Y.Opens) (h : ⊤ ≤ (T.x ≫ i) ⁻¹ᵁ U) :
    ⊤ ≤ (T'.x ≫ i) ⁻¹ᵁ U := by
  intro p _
  rw [← f.pt, Category.assoc]
  exact h (Set.mem_univ ((spMap f.φ₀).base p))

variable (κ t i)

def liftE (S : Thick κ t ⥤ Thick κ t) (u : 𝟭 _ ⟶ S) : EE κ t i ⥤ EE κ t i where
  obj a := ⟨⟨S.obj a.obj.T, a.obj.U, a.obj.hU, top_le_preimage_of_hom (u.app a.obj.T) a.obj.U a.obj.mem⟩, a.property⟩
  map f := ⟨⟨S.map f.hom.1, f.hom.2⟩⟩
  map_id a := ObjectProperty.hom_ext _ (Subtype.ext (S.map_id a.obj.T))
  map_comp f g := ObjectProperty.hom_ext _ (Subtype.ext (S.map_comp f.hom.1 g.hom.1))

def liftT (S : Thick κ t ⥤ Thick κ t) (u v : 𝟭 _ ⟶ S) : 𝟭 (EE κ t i) ⟶ liftE κ t i S u where
  app a := ⟨⟨v.app a.obj.T, le_rfl⟩⟩
  naturality a b f := ObjectProperty.hom_ext _ (Subtype.ext (v.naturality f.hom.1))

variable {κ t i}

theorem acyc_res_pE (M : Coef (Thick κ t)) (S : Thick κ t ⥤ Thick κ t) (u v : 𝟭 _ ⟶ S)
    (r : ∀ T, M.obj (S.obj T) →+ M.obj T)
    (h : (∀ (T T' : Thick κ t) (φ : T ⟶ T') x, r T' (M.map (S.map φ) x) = M.map φ (r T x)) ∧
      (∀ T x, r T (M.map (u.app T) x) = 0) ∧ (∀ T x, r T (M.map (v.app T) x) = x)) :
    (M.res (pE κ t i)).Ac0 ∧ (M.res (pE κ t i)).Ac1 ∧ (M.res (pE κ t i)).Ac2 :=
  GlobalTheory.T.coefficients_acyclic_of_two_sections_retraction _ (M.res (pE κ t i)) (liftE κ t i S u) (liftT κ t i S u u) (liftT κ t i S u v) (fun a ↦ r a.obj.T)
    (fun a b f x ↦ h.1 a.obj.T b.obj.T f.hom.1 x) (fun a x ↦ h.2.1 a.obj.T x) (fun a x ↦ h.2.2 a.obj.T x)

theorem crystalline_forget_forms_bijective_site_and_pairs : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0})
    (t : X ⟶ Sp R) (Y : Scheme.{0}) (i : X ⟶ Y),
    (KK κ t).fnMap.PullbackBijectiveDegreesOneTwo ∧ ((KK κ t).res (pE κ t i)).fnMap.PullbackBijectiveDegreesOneTwo := by
  intro R _ I κ X t Y i
  obtain ⟨S, u, v, r1, r2, r3, h1, h2, h3a, h3b, h3c⟩ := _root_.GlobalTheory.PDForm.Nbhd.exists_retraction R I κ X t
  have h3 := And.intro h3a (And.intro h3b h3c)
  exact ⟨fnMap_pullbackBijective12_of_acyclic _ (GlobalTheory.T.coefficients_acyclic_of_two_sections_retraction _ _ S u v r1 h1.1 h1.2.1 h1.2.2)
      (GlobalTheory.T.coefficients_acyclic_of_two_sections_retraction _ _ S u v r2 h2.1 h2.2.1 h2.2.2) (GlobalTheory.T.coefficients_acyclic_of_two_sections_retraction _ _ S u v r3 h3a h3b h3c),
    fnMap_pullbackBijective12_of_acyclic _ (acyc_res_pE (i := i) _ S u v r1 h1) (acyc_res_pE (i := i) _ S u v r2 h2)
      (acyc_res_pE (i := i) _ S u v r3 h3)⟩

end GlobalTheory.PDForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeClsPullHom
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

noncomputable section

namespace GlobalTheory.MumProd.GAdjFst

open GlobalTheory.CechPic

variable {S : Scheme.{0}}

theorem psum_comp_hom {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H] (f : G ⟶ H) [IsMonHom f]
    {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) (I : Finset (Fin n)) :
    psum G x I ≫ f = psum H (fun i => x i ≫ f) I :=
  psum_hom (MonoidHom.mk' (fun z : T ⟶ G => z ≫ f) fun a b => MonObj.mul_comp a b f) x I

theorem cubeCls_pull_hom {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H] (f : G ⟶ H)
    [IsMonHom f] {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) (c : Pic H.left) :
    GlobalTheory.ZH.EndoExtend.cubeCls G x (pull f.left c) = GlobalTheory.ZH.EndoExtend.cubeCls H (fun i => x i ≫ f) c := by
  unfold GlobalTheory.ZH.EndoExtend.cubeCls
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [← pull_comp, ← Over.comp_left, psum_comp_hom]

theorem cubeCls_add {G : Over S} [GrpObj G] [IsCommMonObj G] {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G))
    (a b : Pic G.left) :
    GlobalTheory.ZH.EndoExtend.cubeCls G x (a + b) = GlobalTheory.ZH.EndoExtend.cubeCls G x a + GlobalTheory.ZH.EndoExtend.cubeCls G x b := by
  unfold GlobalTheory.ZH.EndoExtend.cubeCls
  simp only [map_add (f := _), smul_add, Finset.sum_add_distrib]

theorem cubeCls_one_left {G : Over S} [GrpObj G] [IsCommMonObj G] {T : Over S} (y : T ⟶ G) (c : Pic G.left) :
    GlobalTheory.ZH.EndoExtend.cubeCls G ![1, y] c = 0 := by
  classical
  unfold GlobalTheory.ZH.EndoExtend.cubeCls
  refine (Fintype.sum_equiv (Equiv.ulift : ULift.{0} (Finset (Fin 2)) ≃ Finset (Fin 2)) _
    (fun I => ((-1 : ℤ) ^ (2 - I.card)) • pull (psum G ![1, y] I).left c) (fun _ => rfl)).trans ?_
  have u : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  have p₀ : psum G ![1, y] ∅ = 1 := rfl
  have p₁ : psum G ![1, y] {0} = 1 := _root_.mul_one 1
  have p₂ : psum G ![1, y] {1} = y := _root_.mul_one y
  have p₄ : psum G ![1, y] {0, 1} = 1 * y := congrArg (1 * ·) (_root_.mul_one y)
  rw [u, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, p₀, p₁, p₂, p₄, _root_.one_mul]
  have c₁ : ({0, 1} : Finset (Fin 2)).card = 2 := by decide
  simp only [c₁, Finset.card_singleton, Finset.card_empty]
  norm_num

end GlobalTheory.MumProd.GAdjFst

theorem GlobalTheory.MumProd.gAdj_prod_fst : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ : DegData R I) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre I D₁ A₁ G₁) (D₂ : DegData R I) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre I D₂ A₂ G₂) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (U : UnifPre I D A (G₁ ⊗ G₂)) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X) (a₁ : A.A ⟶ A₁.A) (a₂ : A.A ⟶ A₂.A), IsProdUnif U₁ U₂ U p₁ p₂ q₁ q₂ a₁ a₂ → GAdj U₁.LG.L U.LG.L (lift (𝟙 G₁) 1) (fst G₁ G₂) := by
  intro R _ _ I D₁ A₁ G₁ _ _ U₁ D₂ A₂ G₂ _ _ U₂ D A U p₁ p₂ q₁ q₂ a₁ a₂ hU
  obtain ⟨w, hw⟩ := hU.wL
  have hL := U.LG.isLB
  have hL₁ := U₁.LG.isLB
  have hL₂ := U₂.LG.isLB
  have hE : (extLB U₁.LG.L U₂.LG.L (fst G₁ G₂).left (snd G₁ G₂).left).IsLB :=
    GlobalTheory.CechPic.isLB_tens (pull_isLB hL₁ _) (pull_isLB hL₂ _)
  have e0 : GlobalTheory.CechPic.cls _ hL = GlobalTheory.CechPic.pull (fst G₁ G₂).left (GlobalTheory.CechPic.cls _ hL₁) +
      GlobalTheory.CechPic.pull (snd G₁ G₂).left (GlobalTheory.CechPic.cls _ hL₂) :=
    (GlobalTheory.CechPic.cls_eq_iff hL hE).2 ⟨w, hw⟩
  unfold GAdj
  refine (GlobalTheory.CechPic.cls_eq_iff _ _).1 ((GlobalTheory.ZH.EndoExtend.cls_cubeLB (G₁ ⊗ G₂) _ hL).trans
    (Eq.trans ?_ (GlobalTheory.ZH.EndoExtend.cls_cubeLB G₁ _ hL₁).symm))
  rw [e0,
    GlobalTheory.MumProd.GAdjFst.cubeCls_add, GlobalTheory.MumProd.GAdjFst.cubeCls_pull_hom,
    GlobalTheory.MumProd.GAdjFst.cubeCls_pull_hom]
  have h₁ : (fun i => (![fst G₁ (G₁ ⊗ G₂) ≫ lift (𝟙 G₁) 1, snd G₁ (G₁ ⊗ G₂)] : Fin 2 → _) i ≫ fst G₁ G₂) =
      ![fst G₁ (G₁ ⊗ G₂), snd G₁ (G₁ ⊗ G₂) ≫ fst G₁ G₂] := by
    funext i; fin_cases i <;> simp
  have h₂ : (fun i => (![fst G₁ (G₁ ⊗ G₂) ≫ lift (𝟙 G₁) 1, snd G₁ (G₁ ⊗ G₂)] : Fin 2 → _) i ≫ snd G₁ G₂) =
      ![1, snd G₁ (G₁ ⊗ G₂) ≫ snd G₁ G₂] := by
    funext i; fin_cases i <;> simp
  rw [h₁, h₂, GlobalTheory.MumProd.GAdjFst.cubeCls_one_left, add_zero]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubePointsFstEqPartialSumsGrpPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
open GlobalTheory.Mum.Two

noncomputable section
namespace GlobalTheory.PairPts

private theorem psum_two_01 {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {T : Over S} (u v : T ⟶ G) :
    psum G ![u, v] {0, 1} = u * v := by
  have hl : (List.finRange 2).filter (· ∈ ({0, 1} : Finset (Fin 2))) = [0, 1] := by decide
  rw [psum, hl]
  simp [padd, pzero, Hom.mul_def, Hom.one_def]

private theorem psum_two_e {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {T : Over S} (u v : T ⟶ G) :
    psum G ![u, v] ∅ = 1 := by
  have hl : (List.finRange 2).filter (· ∈ (∅ : Finset (Fin 2))) = [] := by decide
  rw [psum, hl]
  simp [pzero, Hom.one_def]

private theorem psum_two_0 {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {T : Over S} (u v : T ⟶ G) :
    psum G ![u, v] {0} = u := by
  have hl : (List.finRange 2).filter (· ∈ ({0} : Finset (Fin 2))) = [0] := by decide
  rw [psum, hl]
  have := psum_two_e G u v
  rw [psum] at this
  simp only [List.foldr_cons, List.foldr_nil, List.filter] at this ⊢
  show u * pzero G T = u
  simp [pzero, Hom.one_def] at this ⊢

private theorem psum_two_1 {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {T : Over S} (u v : T ⟶ G) :
    psum G ![u, v] {1} = v := by
  have hl : (List.finRange 2).filter (· ∈ ({1} : Finset (Fin 2))) = [1] := by decide
  rw [psum, hl]
  show v * pzero G T = v
  simp [pzero, Hom.one_def]

theorem lamPts_fst_eq_psum : ∀ {S₀ S : Scheme.{0}} (B₀ : Over S₀) [GrpObj B₀] [IsCommMonObj B₀] (B : Over S) [GrpObj B] [IsCommMonObj B] (f : S₀ ⟶ S) (β : B₀.left ⟶ B.left) (β₂ : (G2 B₀).left ⟶ (G2 B).left), IsGrpPullback B₀ B f β → IsSquare β β₂ → ∀ (Y : Over S₀) (x y : Y ⟶ B₀) (x' y' : Y ⟶ (Over.pullback f).obj B), x'.left ≫ pullback.fst B.hom f = x.left ≫ β → y'.left ≫ pullback.fst B.hom f = y.left ≫ β → ∀ k : Fin 4, lamPts x' y' k ≫ pullback.fst B.hom f = (lift x y).left ≫ β₂ ≫ (psum B (x2 B) ((![{0, 1}, {0}, {1}, ∅] : Fin 4 → Finset (Fin 2)) k)).left := by
  intro S₀ S B₀ _ _ B _ _ f β β₂ hβ hsq Y x y x' y' hx hy k
  have hm : ((lift x y).left ≫ β₂) ≫ (G2 B).hom = (Over.mk (Y.hom ≫ f)).hom := by
    have h1 : (G2 B).hom = (fst B B).left ≫ B.hom := (Over.w (fst B B)).symm
    rw [h1, Category.assoc, ← Category.assoc β₂, hsq.1, Category.assoc, hβ.1.w, ← Category.assoc,
      ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc, ← Category.assoc x.left, Over.w x]
    rfl
  let u : Over.mk (Y.hom ≫ f) ⟶ G2 B := Over.homMk ((lift x y).left ≫ β₂) hm
  have key : ∀ g : G2 B ⟶ B, (lift x y).left ≫ β₂ ≫ g.left = (u ≫ g).left := fun g => by
    simp [u]
  have hu1 : (u ≫ fst B B).left = x.left ≫ β := by
    rw [← key, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst]
  have hu2 : (u ≫ snd B B).left = y.left ≫ β := by
    rw [← key, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd]
  have h := isGrpPullback_pullback B f
  have m : (x' * y').left ≫ pullback.fst B.hom f = ((u ≫ fst B B) * (u ≫ snd B B)).left :=
    (h.2 Y x' y' _ _ (hu1.trans hx.symm) (hu2.trans hy.symm)).symm
  have o : (1 : Y ⟶ (Over.pullback f).obj B).left ≫ pullback.fst B.hom f =
      (1 : Over.mk (Y.hom ≫ f) ⟶ B).left :=
    congrArg (fun z => z.left) (map_one (pushHom h Y))
  have hx2 : x2 B = ![fst B B, snd B B] := rfl
  fin_cases k
  · show (x' * y').left ≫ _ = (lift x y).left ≫ β₂ ≫ (psum B (x2 B) {0, 1}).left
    rw [hx2, psum_two_01, key, comp_mul, m]
  · show x'.left ≫ _ = (lift x y).left ≫ β₂ ≫ (psum B (x2 B) {0}).left
    rw [hx2, psum_two_0, key, hu1, hx]
  · show y'.left ≫ _ = (lift x y).left ≫ β₂ ≫ (psum B (x2 B) {1}).left
    rw [hx2, psum_two_1, key, hu2, hy]
  · show (1 : Y ⟶ (Over.pullback f).obj B).left ≫ _ = (lift x y).left ≫ β₂ ≫ (psum B (x2 B) ∅).left
    rw [hx2, psum_two_e, key, o]
    congr 1
    simp [Hom.one_def]

end GlobalTheory.PairPts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvPolyPullback
section
noncomputable section

open Matrix MvPolynomial ComplexConjugate
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.GoodMetric

namespace GlobalTheory.CurvatureSesquilinearExpansion

theorem eq_sum_coordVec {n : ℕ} (v : V n) : v = ∑ a, v.ofLp a • coordVec a := by
  ext j
  simp [Pi.single_apply]

theorem sesq_expand {n : ℕ} (F : V n → V n → ℂ)
    (h1 : ∀ x y z, F (x + y) z = F x z + F y z) (h2 : ∀ (c : ℂ) x z, F (c • x) z = c * F x z)
    (h3 : ∀ x y z, F x (y + z) = F x y + F x z)
    (h4 : ∀ (c : ℂ) x z, F x (c • z) = conj c * F x z) (ξ η : V n) :
    F ξ η = ∑ a, ∑ b, ξ.ofLp a * conj (η.ofLp b) * F (coordVec a) (coordVec b) := by
  have s1 (z : V n) (f : Fin n → V n) : F (∑ a, f a) z = ∑ a, F (f a) z :=
    map_sum (AddMonoidHom.mk' (fun x => F x z) fun x y => h1 x y z) f Finset.univ
  have s2 (x : V n) (f : Fin n → V n) : F x (∑ a, f a) = ∑ a, F x (f a) :=
    map_sum (AddMonoidHom.mk' (fun z => F x z) fun y z => h3 x y z) f Finset.univ
  conv_lhs => rw [eq_sum_coordVec ξ, eq_sum_coordVec η, s1]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [s2]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [h2, h4, mul_assoc]

theorem curv_expand {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {G : V n → Matrix r r ℂ} {z : V n}
    (h : MContDiffAt 2 G z) (hu : IsUnit (G z).det) (ξ η : V n) (i j : r) :
    curv G z ξ η i j =
      ∑ a, ∑ b, ξ.ofLp a * conj (η.ofLp b) * curv G z (coordVec a) (coordVec b) i j := by
  have m1 (x y w : V n) : mddbar G z (x + y) w = mddbar G z x w + mddbar G z y w := by
    ext a b; simp
  have m2 (c : ℂ) (x w : V n) : mddbar G z (c • x) w = c • mddbar G z x w := by
    ext a b; simp
  have m3 (x y w : V n) : mddbar G z x (y + w) = mddbar G z x y + mddbar G z x w := by
    ext a b; simp
  have m4 (c : ℂ) (x w : V n) : mddbar G z x (c • w) = conj c • mddbar G z x w := by
    ext a b; simp
  refine sesq_expand (fun ξ η => curv G z ξ η i j) ?_ ?_ ?_ ?_ ξ η
  · intro x y w
    simp only [curv_eq h hu, mdel_add_vec, m1, transpose_add, Matrix.mul_add, Matrix.sub_apply,
      Matrix.add_apply]
    ring
  · intro c x w
    simp only [curv_eq h hu, mdel_smul_vec, m2, transpose_smul, Matrix.mul_smul, Matrix.sub_apply,
      Matrix.smul_apply, smul_eq_mul]
    ring
  · intro x y w
    simp only [curv_eq h hu, mdbar_add_vec, m3, transpose_add, Matrix.mul_add, Matrix.add_mul,
      Matrix.sub_apply, Matrix.add_apply]
    ring
  · intro c x w
    simp only [curv_eq h hu, mdbar_smul_vec, m4, transpose_smul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring

theorem curvPoly_pullback : (let d1 : {n n' : ℕ} → (ReciprocityTheory.L2DbarEstimates.V n' →L[ℂ] ReciprocityTheory.L2DbarEstimates.V n) → MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n' × Fin n') ℂ := @(fun {n n' : ℕ} (L : ReciprocityTheory.L2DbarEstimates.V n' →L[ℂ] ReciprocityTheory.L2DbarEstimates.V n) ↦ MvPolynomial.aeval fun (x : Fin n × Fin n) ↦ ∑ c : Fin n', ∑ d : Fin n', (MvPolynomial.C : (fun (x : Fin n) ↦ ℂ) (Prod.fst x) → MvPolynomial (Fin n' × Fin n') ((fun (x : Fin n) ↦ ℂ) (Prod.fst x))) (WithLp.ofLp ((L : ReciprocityTheory.L2DbarEstimates.V n' → ReciprocityTheory.L2DbarEstimates.V n) (GlobalTheory.GoodMetric.coordVec c)) (Prod.fst x) * (starRingEnd ℂ : ℂ → ℂ) (WithLp.ofLp ((L : ReciprocityTheory.L2DbarEstimates.V n' → ReciprocityTheory.L2DbarEstimates.V n) (GlobalTheory.GoodMetric.coordVec d)) (Prod.snd x))) * MvPolynomial.X (c, d)); ∀ {n n' : ℕ} {r : Type} [inst : Fintype r] [inst_1 : DecidableEq r] {G : ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ} {φ : ReciprocityTheory.L2DbarEstimates.V n' → ReciprocityTheory.L2DbarEstimates.V n} {w : ReciprocityTheory.L2DbarEstimates.V n'}, ContDiffAt ℂ (2 : WithTop ℕ∞) φ w → GlobalTheory.HermFrame.MContDiffAt ((⊤ : ℕ∞) : WithTop ℕ∞) G (φ w) → IsUnit (Matrix.det (G (φ w))) → GlobalTheory.GoodMetric.curvPoly (fun (x : ReciprocityTheory.L2DbarEstimates.V n') ↦ G (φ x)) w = (AlgHom.mapMatrix (d1 (fderiv ℂ φ w)) : Matrix r r (MvPolynomial (Fin n × Fin n) ℂ) → Matrix r r (MvPolynomial (Fin n' × Fin n') ℂ)) (GlobalTheory.GoodMetric.curvPoly G (φ w))) := by
  intro d1 n n' r _ _ G φ w hφ hG hu
  have h2 : MContDiffAt 2 G (φ w) := hG.of_le (by norm_cast)
  refine Matrix.ext fun i j => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [d1, curvPoly, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_sum, map_mul,
    aeval_X, aeval_C, algebraMap_eq, curv_comp_holo h2 hu hφ, Finset.mul_sum]
  symm
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [curv_expand h2 hu (fderiv ℂ φ w (coordVec c))]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

end GlobalTheory.CurvatureSesquilinearExpansion
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarChernConnectionEntryEqCurvature
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernCalc

theorem coefwise_dbar_sum_smul_bas {n : ℕ} {J : Type} [Fintype J] (u : J → V n → ℂ) (S : J → Finset (Fin (n + n)))
    (v η : V n) (hu : ∀ a, DifferentiableAt ℝ (u a) v) :
    coefwise (fun f => GlobalTheory.dbar f v η) (fun x => ∑ a, u a x • bas n (S a)) =
      ∑ a, GlobalTheory.dbar (u a) v η • bas n (S a) := by
  refine (bas n).ext_elem fun S' => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [coefwise, map_sum, map_smul, Module.Basis.repr_self, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hd (a : J) : DifferentiableAt ℝ (fun x => if S a = S' then u a x else 0) v := by
    split_ifs
    exacts [hu a, differentiableAt_const _]
  rw [GlobalTheory.dbar_sum fun a _ => hd a, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs <;> simp

theorem dbarAt_conn : ∀ (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (v : V n), MContDiffAt ∞ G v → IsUnit (G v).det → ∀ i j, dbarAt (fun x => ∑ a, conn G x (coordVec a) i j • dz a) v = (curvEv G v i j : Alt n) := by
  intro n r _ _ G v hG hu i j
  have hc (a : Fin n) : DifferentiableAt ℝ (fun x => conn G x (coordVec a) i j) v :=
    (hG.conn hu (j := 1) (by norm_cast) (coordVec a)).diff i j
  have h (b : Fin n) := coefwise_dbar_sum_smul_bas (fun a x => conn G x (coordVec a) i j)
    (fun a => {finSumFinEquiv (.inl a)}) v (coordVec b) hc
  simp only [bas_singleton] at h
  have e : (curvEv G v i j : Alt n) = ∑ a, ∑ b, curv G v (coordVec a) (coordVec b) i j • (dz a * dzb b) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [curvEv, curvPoly, Matrix.map_apply, Matrix.of_apply, map_sum, map_mul, aeval_C, aeval_X,
      ← Algebra.smul_def, AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_smul, sym]
  rw [e, Finset.sum_comm]
  simp only [dbarAt, dz, h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  rw [mul_smul_comm, dzb]
  conv_lhs =>
    rw [eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap
      (R := ℂ) (M := Fin n ⊕ Fin n → ℂ) (Pi.single (Sum.inr b) 1) (Pi.single (Sum.inl a) 1)),
      smul_neg, ← neg_smul]
  rfl

end GlobalTheory.ChernCalc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DensMulPullHeadL
section
set_option autoImplicit false

open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.CxForm
open GlobalTheory.GoodMetric (coordVec)

namespace GlobalTheory.LocFub.TopDens

theorem dens_smul {n : ℕ} (c : ℂ) (α : Alt n) : dens (c • α) = c * dens α := by
  simp [dens, mul_div_assoc]

theorem dens_add {n : ℕ} (α β : Alt n) : dens (α + β) = dens α + dens β := by
  simp [dens, add_div]

theorem dens_zero {n : ℕ} : dens (0 : Alt n) = 0 := by simp [dens]

end GlobalTheory.LocFub.TopDens
end

