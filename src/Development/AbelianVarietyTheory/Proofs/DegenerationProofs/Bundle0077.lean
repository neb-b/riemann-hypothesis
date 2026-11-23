module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaPtEqUnitMulTh
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0066
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0055

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TauBimultOfBaseChange
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

noncomputable section

namespace GlobalTheory

namespace TauDescent

open ReciprocityTheory.ChartRestriction.G.DVR

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'} {β : D'.P.A.left ⟶ D.P.A.left}

theorem cub_of_grpPullback (hG : GlobalFnsSt) (gp : IsGrpPullback D'.P.A D.P.A (spMap φ) β)
    (v : LB.Iso D'.P.L (D.P.L.pull β)) (hvg : v.IsGen) {T' : Over (Sp R')} {z : T'.left} {J J'}
    (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J') (x x' y : T' ⟶ D'.P.A) :
    val (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t
        ((lift x (lift x' y)).left ≫ (cubeMapOf gp).F3) z J =
      (∏ I : thK.{0}, gw v ((lift x (lift x' y)).left ≫ thφ D'.P.A (x3 D'.P.A) I) z
        (J (((lift x (lift x' y)).left ≫ thφ D'.P.A (x3 D'.P.A) I) ≫ β))
        (J' ((lift x (lift x' y)).left ≫ thφ D'.P.A (x3 D'.P.A) I)) ^ thε I) * cubV D'.cub z J' x x' y := by
  obtain ⟨t, ht, hv⟩ := exists_up ((isGen_iff v).1 hvg) D.P.isLB D'.P.isLB (φ' := thφ D'.P.A (x3 D'.P.A))
    (ε := thε) D'.cub.t D'.cub.isGen
  have hv' : ∀ (Z : Scheme.{0}) (r : Z ⟶ (G3 D'.P.A).left) (z : Z) J J', Good D.P.L z J → Good D'.P.L z J' →
      val t r z J = (∏ I : thK.{0}, gw v (r ≫ thφ D'.P.A (x3 D'.P.A) I) z
        (J ((r ≫ thφ D'.P.A (x3 D'.P.A) I) ≫ β)) (J' (r ≫ thφ D'.P.A (x3 D'.P.A) I)) ^ thε I) *
        val (L := D'.P.L) (φ := thφ D'.P.A (x3 D'.P.A)) (ε := thε) D'.cub.t r z J' := fun Z r z J J' hJ hJ' => by
    refine (hv Z r z _ _ (hJ.mem _ r) (hJ'.mem _ r)).trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun I _ => ?_) rfl)
    rw [Category.assoc]
  let e : 𝟙_ (Over (Sp R')) ⟶ G3 D'.P.A := lift 1 (lift 1 1)
  have sj : Function.Surjective
      ((snd D'.P.A (D'.P.A ⊗ D'.P.A)).left ≫ (snd D'.P.A D'.P.A).left ≫ D'.P.A.hom).appTop.hom :=
    surj_comp (surj_snd hG D'.P.isAb _) (surj_comp (surj_snd hG D'.P.isAb _) (hG _ _ D'.P.isAb).2)
  have he : e.left ≫ (snd D'.P.A (D'.P.A ⊗ D'.P.A)).left ≫ (snd D'.P.A D'.P.A).left ≫ D'.P.A.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w e
  have key := gen_unique' D.P.isLB (φ := fun I => (cubeMapOf gp).F3 ≫ thφ D.P.A (x3 D.P.A) I) (ε := thε)
    (fun V _ k => Finset.prod_congr rfl fun I _ => congrArg (fun q => k q ^ thε I) ((cubeMapOf gp).psum_comm I.down))
    _ e.left he sj (pullGen_isGen _ _ _ _ D.cub.isGen (cubeMapOf gp).F3) ht (fun y I hI => by
      choose I' hI' using fun χ : (𝟙_ (Over (Sp R'))).left ⟶ D'.P.A.left => exists_chart D'.P.isLB (χ y)
      have C' : IsCub (cubV D'.cub y I') := isCub_cubV D'.cub hI'
      have p := prod_cub (1 : 𝟙_ (Over (Sp R')) ⟶ D'.P.A) 1 1
        (fun q => gw v q y (I (q ≫ β)) (I' q))
      rw [_root_.mul_one, _root_.mul_one] at p
      refine Eq.trans ?_ ((hv' _ e.left y I I' hI hI').trans (congrArg₂ (· * ·) p (C'.face 1 1))).symm
      have o : pushPt gp.1.w (1 : 𝟙_ (Over (Sp R')) ⟶ D'.P.A) = 1 := map_one (pushHom gp _)
      have q : e.left ≫ (cubeMapOf gp).F3 =
          (lift (pushPt gp.1.w (1 : 𝟙_ (Over (Sp R')) ⟶ D'.P.A)) (lift (pushPt gp.1.w 1)
            (pushPt gp.1.w 1))).left := hom_ext_triple _ fun i => by
        rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
        fin_cases i <;> simp [e, x3, pushPt, cubeMapOf]
      refine (val_pull hI _ _ _).trans ?_
      rw [q, o]
      set_option backward.isDefEq.respectTransparency false in
        simpa only [cubV, _root_.mul_assoc, _root_.mul_one, mul_inv_cancel, _root_.one_mul, inv_mul_cancel] using
          (isCub_cubV D.cub (T := Over.mk ((𝟙_ (Over (Sp R'))).hom ≫ spMap φ)) hI).face 1 1) _ (lift x (lift x' y)).left z J hJ
  exact (val_pull hJ _ _ _).symm.trans (key.trans (hv' _ _ z J J' hJ hJ'))

set_option maxHeartbeats 1000000 in
theorem tauBimult_down (hG : GlobalFnsSt) (v : LB.Iso D'.P.L (D.P.L.pull β)) (xe : D'.X ≃+ D.X)
    (gp : IsGrpPullback D'.P.A D.P.A (spMap φ) β) (hvg : v.IsGen)
    (hc : ∀ x, (D'.c x).left ≫ β = spMap φ ≫ (D.c (xe x)).left) (hρ : RigCmp φ D D' β v)
    (gam : (TK R').left ⟶ (TK R).left) (hgam : gam ≫ jK R = jK R' ≫ spMap φ) (hψ : PsiCmp D D' β v xe gam)
    (hB : D'.TauBimult) : D.TauBimult := by
  intro a a' b
  obtain ⟨a, rfl⟩ := xe.surjective a
  obtain ⟨a', rfl⟩ := xe.surjective a'
  obtain ⟨b, rfl⟩ := xe.surjective b
  have sep : D.P.A.left.IsSeparated := by
    have := D.P.isAb.proper
    refine ⟨?_⟩
    rw [← terminal.comp_from D.P.A.hom]
    infer_instance
  obtain ⟨y⟩ : Nonempty (TK R').left := inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing R')))
  have red : IsReduced (TK R).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of (FractionRing R))))
  have sub : Subsingleton (TK R).left := inferInstanceAs (Subsingleton (PrimeSpectrum (FractionRing R)))
  refine TauPull.corr_of_dense D.P.isLB gam y (fun V hV => ?_) fun J hJ => ?_
  · obtain ⟨x, hx⟩ := hV
    rw [Subsingleton.elim (gam y) x]; exact hx
  choose J' hJ₀ using fun χ : (TK R').left ⟶ D'.P.A.left => exists_chart D'.P.isLB (χ y)
  have hJ' : Good D'.P.L y J' := hJ₀
  let T : Over (Spec (CommRingCat.of R)) := Over.mk ((TK R').hom ≫ spMap φ)
  let κ : T ⟶ TK R := Over.homMk gam hgam
  let B : (TK R' ⟶ D'.P.A) → (T ⟶ D.P.A) := fun x => pushPt gp.1.w x
  have βc : ∀ χ, B (cP D' _ χ) = cP D _ (xe χ) := fun χ => Over.OverMorphism.ext (by
    show ((TK R').hom ≫ (D'.c χ).left) ≫ β = ((TK R').hom ≫ spMap φ) ≫ (D.c (xe χ)).left
    rw [Category.assoc, hc, Category.assoc])
  let Ω : (TK R' ⟶ D'.P.A) → ((TK R').left.presheaf.stalk y)ˣ := fun x => gw v x.left y (J (x.left ≫ β)) (J' x.left)
  let θ : (T ⟶ D.P.A) → (T ⟶ D.P.A) → (T ⟶ D.P.A) → ((TK R').left.presheaf.stalk y)ˣ := th D (T := T) y J
  have cub : ∀ a b c : TK R' ⟶ D'.P.A, θ (B a) (B b) (B c) =
        Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b * Ω c * (Ω 1)⁻¹ *
          th D' y J' a b c := by
    intro a b c
    have e := cub_of_grpPullback hG gp v hvg (T' := TK R') hJ hJ' a b c
    have q : (lift a (lift b c)).left ≫ (cubeMapOf gp).F3 = (lift (B a) (lift (B b) (B c))).left :=
      hom_ext_triple _ fun i => by
        rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
        fin_cases i <;> simp [x3] <;> rfl
    rw [q] at e
    exact e.trans (congrArg₂ (· * ·) (prod_cub a b c (fun q => gw v q y (J (q ≫ β)) (J' q))) rfl)
  have vψ : ∀ χ, val (D.psi (xe χ)) gam y J = (Ω (cP D' _ χ))⁻¹ * val (D'.psi χ) (𝟙 _) y J' := fun χ => by
    have h₁ : D'.xK χ ≫ β = gam ≫ D.xK (xe χ) := by
      show (jK R' ≫ (D'.c χ).left) ≫ β = gam ≫ jK R ≫ (D.c (xe χ)).left
      rw [Category.assoc, hc, ← Category.assoc, ← hgam, Category.assoc]
    have e := CubTransport.val_pmaps (fun _ => h₁) (hψ χ) (𝟙 _) hJ hJ'
    rw [Fintype.prod_unique, zpow_neg_one, Category.id_comp, Category.id_comp] at e
    exact e
  have vρ : val D.rigK gam y J = Ω 1 * val D'.rigK (𝟙 _) y J' := by
    have h₁ : eSec D'.P.A ≫ β = spMap φ ≫ eSec D.P.A := by
      have o := congrArg (fun q => q.left) (map_one (pushHom gp (𝟙_ (Over (Sp R')))))
      have o' : (toUnit (𝟙_ (Over (Sp R'))) ≫ η[D'.P.A]).left ≫ β =
          ((𝟙_ (Over (Sp R'))).hom ≫ spMap φ) ≫ eSec D.P.A := o
      rw [toUnit_unit, Category.id_comp] at o'
      exact o'.trans (congrArg (· ≫ eSec D.P.A) (Category.id_comp _))
    have e := CubTransport.val_pmaps (fun _ => h₁) hρ (TK R').hom hJ hJ'
    rw [Fintype.prod_unique, zpow_one] at e
    have b₁ : gam ≫ (toUnit (TK R)).left = (TK R').hom ≫ spMap φ := hgam
    have b₂ : 𝟙 _ ≫ (toUnit (TK R')).left = (TK R').hom := Category.id_comp _
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (val_pull hJ' _ _ _).symm))
    rw [b₁, b₂]
    exact e
  have key := (val_mul hJ' _ _ _).symm.trans ((val_corr hJ' (hB a a' b) (𝟙 _)).trans (val_mul hJ' _ _ _))
  replace key := (congrArg₂ (· * ·) rfl
    (val_cub D'.cub (𝟙 (TK R')) hJ' (cP D' _ a) (cP D' _ a') (cP D' _ b))).symm.trans key
  rw [Category.id_comp, Category.id_comp, Category.id_comp, TauPull.val_tau _ hJ', TauPull.val_tau _ hJ',
    TauPull.val_tau _ hJ'] at key
  refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
  have cb : val (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t
      (lift (cP D (TK R) (xe a)) (lift (cP D (TK R) (xe a')) (cP D (TK R) (xe b)))).left) gam y J =
      θ (cP D T (xe a)) (cP D T (xe a')) (cP D T (xe b)) := by
    refine (val_cub D.cub κ hJ (cP D _ (xe a)) (cP D _ (xe a')) (cP D _ (xe b))).trans ?_
    rw [comp_cP, comp_cP, comp_cP]
  refine (congrArg₂ (· * ·) rfl cb).trans ?_
  rw [← βc, ← βc, ← βc, cub, TauPull.val_tau _ hJ, TauPull.val_tau _ hJ, TauPull.val_tau _ hJ, ← map_add (f := _), ← map_add (f := _),
    ← map_add, ← map_add, vψ, vψ, vψ, vψ, vψ, vψ, vψ, vρ, cPoint_add, cPoint_add, cPoint_add, cPoint_add]
  apply Additive.ofMul.injective
  have e' := congrArg Additive.ofMul key
  simp only [ofMul_mul, ofMul_inv] at e' ⊢
  linear_combination (norm := abel) e'

end TauDescent

theorem tauBimult_of_baseChange : GlobalFnsSt → ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (φ : R →+* V) (D : DegPre R) (D' : DegPre V) (β : D'.P.A.left ⟶ D.P.A.left) (v : LB.Iso D'.P.L (D.P.L.pull β)) (xe : D'.X ≃+ D.X), IsGrpPullback D'.P.A D.P.A (spMap φ) β → v.IsGen → (∀ x, (D'.c x).left ≫ β = spMap φ ≫ (D.c (xe x)).left) → RigCmp φ D D' β v → ∀ gam : (TK V).left ⟶ (TK R).left, gam ≫ jK R = jK V ≫ spMap φ → PsiCmp D D' β v xe gam → D'.TauBimult → D.TauBimult :=
  fun hG _ _ _ _ _ _ _ _ _ _ v xe gp hv hc hρ gam hgam hψ hB =>
    TauDescent.tauBimult_down hG v xe gp hv hc hρ gam hgam hψ hB

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TestQuadraticFormEqPsiValuationMul
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.PsiForm

theorem q_eq_val_mul : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), ∃ (ϖ : u.V) (Q : u.D.toPre.X → ℤ), Irreducible ϖ ∧ DVR.QForm.IsQ u.D.toPre ϖ Q ∧ ‖(u.j ϖ : PadicAlgCl p)‖ < 1 ∧ ∀ χ, l.q χ = Q χ * (-Real.log ‖(u.j ϖ : PadicAlgCl p)‖) := by
  intro o Ω _ _ _ _ S ρ p _ y₀ u l
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible u.V
  choose Q hQ using DVR.QForm.exists_QVal hϖ u.D
  have hj : (u.j ϖ : PadicAlgCl p) =
      algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) ϖ) := rfl
  refine ⟨ϖ, Q, hϖ, hQ, ?_, fun χ => ?_⟩
  · rw [hj]
    exact norm_lt_one_of_irreducible u.norm_le hϖ
  · have hc := u.D.toPre.P.isLB.cover
    let x : Sp u.V := IsLocalRing.closedPoint u.V
    have hx : (u.D.toPre.c χ).left x ∈ ⨆ i, u.D.toPre.P.L.U i := by rw [hc]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    have htop : ⊤ ≤ (u.D.toPre.c χ).left ⁻¹ᵁ u.D.toPre.P.L.U i :=
      ((IsLocalRing.closedPoint_mem_iff (R := u.V) _).1 hi).ge
    have h1 := l.q_eq χ (fun _ => i) htop
    have h2 := norm_of_hasVal u.norm_le hϖ
      (hasVal_valF u.D.toPre.P.L _ _ (DVR.QForm.ptK_eq u.D.toPre χ) (-1) _ (hQ χ) (fun _ => i) htop)
    have h3 := neg_injective (Real.exp_injective (h1.symm.trans h2))
    rw [hj, h3, mul_comm]

end GlobalTheory.ZH.PsiForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionValuesCoordsOperatorPermute
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.EvCrd
open GlobalTheory.ThetaCompare

theorem defect_eq_one {G U : Type} [CommGroup G] [CommGroup U] (f b n : G → U) (X : G) (N M Q : ℕ) (hN : Odd N)
    (hX : X ^ N = 1) (hM : X ^ M = 1)
    (h₁ : ∀ z, f z ^ Q * (b (X * z) * (b z)⁻¹) = f 1 ^ Q * (b (X * 1) * (b 1)⁻¹))
    (h₂ : ∀ z, b z * (b z⁻¹)⁻¹ * (n z ^ Q)⁻¹ * n (z ^ M) = b 1 * (b 1⁻¹)⁻¹ * (n 1 ^ Q)⁻¹ * n (1 ^ M))
    (hp : ∏ j ∈ Finset.range N, f (X ^ j) = 1) (hs : f X⁻¹ * n 1 * (f 1 * (n X⁻¹)⁻¹) = 1) (z : G) :
    f z ^ Q * (b (X * z) * (b z)⁻¹) = 1 := by
  set κ := f 1 ^ Q * (b (X * 1) * (b 1)⁻¹) with hκ
  have e₁ : κ ^ N = 1 := by
    have : ∀ j ∈ Finset.range N, κ = f (X ^ j) ^ Q * (b (X ^ (j + 1)) / b (X ^ j)) := fun j _ => by
      rw [← h₁ (X ^ j), pow_succ' X j, div_eq_mul_inv]
    rw [show κ ^ N = ∏ _j ∈ Finset.range N, κ by rw [Finset.prod_const, Finset.card_range],
      Finset.prod_congr rfl this, Finset.prod_mul_distrib, Finset.prod_pow, hp,
      Finset.prod_range_div (fun j => b (X ^ j)) N, hX, pow_zero, div_self', one_pow, _root_.one_mul]
  have e₂ : κ ^ 2 = 1 := by
    have a₁ := h₁ X⁻¹
    have a₂ := h₂ X⁻¹
    have a₃ := congrArg (· ^ Q) hs
    rw [inv_pow, hM, inv_inv, inv_one, one_pow] at a₂
    rw [mul_inv_cancel] at a₁
    rw [_root_.mul_one] at hκ
    simp only [one_pow, mul_pow, inv_pow] at a₃
    rw [sq]
    nth_rewrite 1 [← a₁]
    rw [hκ]
    apply Additive.ofMul.injective
    replace a₂ := congrArg Additive.ofMul a₂
    replace a₃ := congrArg Additive.ofMul a₃
    simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_one] at a₂ a₃ ⊢
    linear_combination (norm := module) a₃ - a₂
  obtain ⟨l, rfl⟩ := hN
  rw [pow_succ, pow_mul, e₂, one_pow, _root_.one_mul] at e₁
  exact (h₁ z).trans e₁

variable {S : Scheme.{0}}


open CommPairing GlobalLift in
theorem lift_pow (hG : GlobalFnsSt) (P : PolAV S) {T : Over S} {N M : ℕ} (hN : Odd N)
    {α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ M).left] ![(M : ℤ) ^ 2, -1])}
    (hα : α.IsGen) {x : T ⟶ P.A} (hx : x ^ N = 1) (hM : x ^ M = 1) {θ : ThetaGrp P.A P.L N T}
    (H : SymLift P.A P.L N N x θ) {y : T.left} {J} (hJ : Good P.L y J) (z : T ⟶ P.A) :
    tval θ (ptSecT P.A z).left y J ^ (M ^ 2) *
        (val α (ptSecT P.A (x * z)).left y J ^ N * (val α (ptSecT P.A z).left y J ^ N)⁻¹) = 1 := by
  have := P.isAb.comm
  obtain ⟨rfl, hp, ν, hν, hs⟩ := H
  have rα := Reg.two (y := y) (J := J) α hα (snd T P.A) (snd T P.A ^ M) rfl rfl
  have rb := rα.pow hJ N
  have rf := Reg.two (y := y) (J := J) (φ := ![(snd T P.A).left, (translPt P.A θ.pt).left]) θ.φ θ.isGen
    (snd T P.A) (translPt P.A θ.pt) rfl rfl
  have rn := Reg.two (y := y) (J := J) (φ := ![(snd T P.A).left, (snd T P.A ≫ (GrpObj.inv : P.A ⟶ P.A)).left]) ν hν
    (snd T P.A) (snd T P.A)⁻¹ rfl rfl
  have c₁ := ((rf.pow hJ (M ^ 2)).mul hJ ((rb.pull hJ (translPt P.A θ.pt)).mul hJ rb.inv)).const hG P.isAb P.isLB hJ
    (fun U _ h => by
      have q : translPt P.A θ.pt ^ M = snd T P.A ^ M := by
        rw [show translPt P.A θ.pt = (fst T P.A ≫ θ.pt) * snd T P.A from rfl, mul_pow, ← SymLiftOdd.comp_pow', hM,
          MonObj.comp_one, _root_.one_mul]
      simp only [SymLiftOdd.comp_pow', lift_snd, q]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_zpow, ofMul_one]
      module)
  have c₂ := (((rb.mul hJ (rb.pull hJ (snd T P.A)⁻¹).inv).mul hJ (rn.pow hJ (M ^ 2)).inv).mul hJ
    (rn.pull hJ (snd T P.A ^ M))).const hG P.isAb P.isLB hJ (fun U _ h => by
      simp only [SymLiftOdd.comp_pow', SymLiftOdd.comp_inv', lift_snd, inv_pow]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_zpow, ofMul_one]
      module)
  simp only [pt_translPt, SymLiftOdd.comp_pow', SymLiftOdd.comp_inv', pt_snd] at c₁ c₂
  have q₁ := val_corr hJ hp (ptSecT P.A 1).left
  have q₂ := val_corr hJ hs (ptSecT P.A 1).left
  rw [GlobalLift.val_powGen _ _ _ hJ, val_one] at q₁
  rw [GlobalLift.val_symGen _ _ _ hJ, val_one, pt_translT, pt_negT, _root_.mul_one, inv_one] at q₂
  simp only [pt_translT, _root_.mul_one] at q₁
  exact defect_eq_one (fun z => tval θ (ptSecT P.A z).left y J)
    (fun z => val α (ptSecT P.A z).left y J ^ N)
    (fun z => nval ν (ptSecT P.A z).left y J) θ.pt N M (M ^ 2) hN hx hM
    (fun z => c₁ z 1) (fun z => c₂ z 1) ((Finset.prod_range _).trans q₁) q₂ z

theorem sval_sum {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S} {a : ℤ} {I : Type} [Fintype I]
    {s : I → LB.Sec (LPow A L a T)} {s' : LB.Sec (LPow A L a T)} {c : I → Γ(T.left, ⊤)}
    (H : ∀ j, s'.f j = ∑ l, liftFun A _ (c l) * (s l).f j) (x : T ⟶ A) {z : T.left} {J} (hJ : Good L z J) :
    sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s' (ptSecT A x).left z J =
      ∑ l, gs (𝟙 _) z ⊤ (c l) *
        sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) (s l) (ptSecT A x).left z J := by
  have hy := hJ.mem (fun _ : Fin 1 => (snd T A).left) (ptSecT A x).left
  refine (congrArg (gs _ z _) (H _)).trans ?_
  have hs : ∀ (W : (T ⊗ A).left.Opens) (_ : (ptSecT A x).left z ∈ W) (u : I → Γ((T ⊗ A).left, W)),
      gs (ptSecT A x).left z W (∑ l, u l) = ∑ l, gs (ptSecT A x).left z W (u l) := fun W hW u => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [gs_eq _ z W hW, map_sum]
  refine (hs _ hy _).trans (Finset.sum_congr rfl fun l _ => (gs_mul _ z _ hy _ _).trans (congrArg (· * _) ?_))
  refine (gs_res _ z _ hy _).trans ((gs_pull _ (fst T A).left z ⊤ trivial _).trans ?_)
  rw [← Over.comp_left, ptSecT, lift_fst]; rfl


open CommPairing in
theorem exists_root_stalk (hG : GlobalFnsSt) (P : PolAV S) {T : Over S} {N M : ℕ} (hN : Odd N)
    {rig : LB.Gen (P.L.pull (eSec P.A))} {x h w : T ⟶ P.A} (hx : x ^ N = 1) (hM : x ^ M = 1) (hw : w = x * h)
    {θ : ThetaGrp P.A P.L N T} (H : SymLift P.A P.L N N x θ) {τ τ'} (hτ : IsTorsFrame P rig M h τ)
    (hτ' : IsTorsFrame P rig M w τ') (y : T.left) :
    ∃ ξ : (T.left.presheaf.stalk y)ˣ, ξ ^ (M ^ 2) = 1 ∧
      ∀ (I : Type) [Fintype I] (s : I → LB.Sec (LPow P.A P.L N T)) (t : LB.Sec (LPow P.A P.L N T))
        (c v : I → Γ(T.left, ⊤)) (v' : Γ(T.left, ⊤)),
        (∀ σ, IsActOf P.A P.L N θ t σ → ∀ j, σ.f j = ∑ l, liftFun P.A _ (c l) * (s l).f j) →
        (∀ l, IsValueAt P.A P.L N (s l) h (powFrame P.A P.L h τ N) (v l)) →
        IsValueAt P.A P.L N t w (powFrame P.A P.L w τ' N) v' →
        ∑ l, gs (𝟙 _) y ⊤ (c l) * gs (𝟙 _) y ⊤ (v l) = ξ.val * gs (𝟙 _) y ⊤ v' := by
  subst hw
  choose J hJ using fun χ : T.left ⟶ P.A.left => exists_chart P.isLB (χ y)
  replace hJ : Good P.L y J := hJ
  obtain ⟨β, hβ, -⟩ := hτ.2.2
  obtain ⟨α, hα, -⟩ := VVRank.exists_gen_pullTo (φ' := ![(snd T P.A).left, (snd T P.A ^ M).left]) β hβ
    (snd T P.A).left (fun k => by
      fin_cases k
      · exact Category.comp_id _
      · change (snd T P.A).left ≫ (mulA P.A M).left = (snd T P.A ^ M).left
        rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id])
  have a₁ := lift_pow hG P hN hα hx hM H hJ h
  have a₂ := torsFrame_pow hG P hα hτ hJ
  have a₃ := torsFrame_pow hG P hα hτ' hJ
  refine ⟨tval θ (ptSecT P.A h).left y J * val τ' (𝟙 _) y J ^ N * (val τ (𝟙 _) y J ^ N)⁻¹, ?_,
    fun I _ s t c v v' hc hv hv' => ?_⟩
  · apply Additive.ofMul.injective
    replace a₁ := congrArg Additive.ofMul a₁
    replace a₂ := congrArg Additive.ofMul a₂
    replace a₃ := congrArg Additive.ofMul a₃
    simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_one] at a₁ a₂ a₃ ⊢
    linear_combination (norm := module) a₁ + N • a₃ - N • a₂
  · obtain ⟨σ, hσ⟩ : ∃ σ, IsActOf P.A P.L (N : ℤ) θ t σ := VVRank.exists_isTwistPull P.A P.isLB θ.isGen t
    have p : ∀ (z : T ⟶ P.A) (e), val (powFrame P.A P.L z e N) (𝟙 _) y J = val e (𝟙 _) y J ^ N := fun z e =>
      (map_zpow _ _ _).trans (zpow_natCast _ _)
    have b₁ := sval_twist hσ (ptSecT P.A h).left hJ
    have b₂ := sval_sum (hc σ hσ) h hJ
    have b₃ := sval_valueAt hv' hJ
    rw [pt_translT, congrArg (fun q => ptSecT P.A (q * h)) H.pt_eq, b₃, b₂, p] at b₁
    simp only [fun l => sval_valueAt (hv l) hJ, p, ← _root_.mul_assoc, ← Finset.sum_mul] at b₁
    rw [(Units.eq_mul_inv_iff_mul_eq _).2 b₁, Units.val_mul, Units.val_mul]
    change (tval θ (ptSecT P.A h).left y J).val * _ * _ * _ = _
    ring

theorem valR_comp {R : Type} [CommRing R] {X Y : Scheme.{0}} (x : Sp R ⟶ Y) (g : Y ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ g ⁻¹ᵁ U) (f : Γ(X, U)) : valR x (g ⁻¹ᵁ U) ((g.app U).hom f) = valR (x ≫ g) U f := by
  rw [CrdCalc.valR_eq x _ h, CrdCalc.valR_eq (x ≫ g) U h]
  rfl

theorem valR_fn {R K : Type} [CommRing R] [CommRing K] (y : R →+* K) (b : R) : valR (spMap y) ⊤ (fn b) = y b := by
  rw [CrdCalc.valR_eq _ _ le_rfl]
  have n := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom y)
  have e := congrArg (fun q => q.hom b) n
  change (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (y b) = (spMap y).appTop.hom (fn b) at e
  have e' : ((spMap y).appLE ⊤ ⊤ le_rfl) = (spMap y).appTop := (Scheme.Hom.app_eq_appLE _).symm
  change (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (((spMap y).appLE ⊤ ⊤ le_rfl).hom (fn b)) = _
  rw [e', ← e]
  exact (Scheme.ΓSpecIso (CommRingCat.of K)).inv_hom_id_apply _

theorem crd_of_isValueAt {R K : Type} [CommRing R] [Field K] (y : R →+* K) (P : PolAV (Sp R)) {k : ℤ} {I : Type}
    {s : I → LB.Sec (LPow P.A P.L k (baseOver (Sp R)))} {z : baseOver (Sp R) ⟶ P.A} {τ} {v : I → R}
    (H : ∀ i, IsValueAt P.A P.L k (s i) z τ (fn (v i))) :
    Crd (LPow P.A P.L k (baseOver (Sp R))) s (spMap y ≫ (ptSecT P.A z).left) (fun i => y (v i)) := by
  let x : Sp K ⟶ (baseOver (Sp R)).left := spMap y
  obtain ⟨j₀, hj⟩ := exists_chart P.isLB (z.left (x (IsLocalRing.closedPoint K)))
  let W := LB.wchart P.L (fun _ : Fin 1 => z.left) (fun _ => j₀)
  have hW : ⊤ ≤ x ⁻¹ᵁ W := (CrdCalc.top_le_iff x W).2 (Set.mem_iInter.2 fun _ => hj)
  have hU := hW.trans (x.preimage_mono (val_le P.A P.L z (fun _ => j₀)))
  refine ⟨fun _ => j₀, (Units.map (CrdCalc.valHom x W hW).toMonoidHom (τ.s fun _ => j₀))⁻¹, hU, fun i => ?_⟩
  have e := congrArg (valR x W) (H i fun _ => j₀)
  have e₁ := ((CrdCalc.valR_res x (val_le P.A P.L z (fun _ => j₀)) hW _).trans
    (valR_comp x (ptSecT P.A z).left _ hU ((s i).f fun _ => j₀))).symm.trans e
  have e₂ := e₁.trans ((CrdCalc.valR_mul x W hW _ _).trans (congrArg₂ (· * ·)
    ((CrdCalc.valR_res x le_top hW _).trans (valR_fn y (v i))) (CrdCalc.valR_eq x W hW _)))
  refine (Units.eq_inv_mul_iff_mul_eq _).2 ?_
  exact (mul_comm _ _).trans e₂.symm

theorem ev_crd_act : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real), (∀ (K : Type) [Field K] (y : S.R →+* K) (a : S.Gam), ρ.Crd (spMap y ≫ (ρ.pt a).left) (fun i => y ⟨S.ev a i, S.ev_mem a i⟩)) ∧ ∀ a h : S.Gam, ∃ e : ℕ, ∀ i, ∑ n, algebraMap o Ω (S.ρ a n i) * S.ev h n = algebraMap o Ω (S.ζ ^ e) * S.ev (h + S.r • a) i := by
  intro hL o Ω _ _ _ hb S ρ
  refine ⟨fun K _ y a => ⟨_, ?_, crd_of_isValueAt y ρ.P (fun i => ρ.ev_val i a)⟩, fun a h => ?_⟩
  · rw [Category.assoc, ← Over.comp_left, pt_snd]
  have := ρ.P.isAb.comm
  have hN : Odd S.N := by rw [ρ.N_eq]; exact ρ.n_odd.pow.pow
  have h₀ : ρ.pt 0 = 1 := by
    have := ρ.pt_add 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hp : ∀ (n : ℕ) b, ρ.pt (n • b) = ρ.pt b ^ n := fun n b => by
    induction n with
    | zero => rw [zero_smul, h₀, pow_zero]
    | succ n ih => rw [succ_nsmul, ρ.pt_add, ih, pow_succ]
  have hx : ρ.pt (S.r • a) ^ S.N = 1 := by rw [hp, ← pow_mul, (ρ.fr_tors a).1]
  let iso := Scheme.ΓSpecIso (CommRingCat.of S.R)
  let y : Sp S.R := (⊥ : PrimeSpectrum S.R)
  obtain ⟨ξ, hξ, e⟩ := exists_root_stalk hL.1.globalFns ρ.P hN hx (ρ.fr_tors _).1
    (by rw [ρ.pt_add, mul_comm]) (ρ.U_sym a) (ρ.fr_tors h) (ρ.fr_tors (h + S.r • a)) y
  let g : S.R →+* (Sp S.R).presheaf.stalk y := ((Sp S.R).presheaf.germ ⊤ y trivial).hom.comp iso.inv.hom
  have hg : Function.Injective g :=
    (germ_injective_of_isIntegral (Sp S.R) (U := ⊤) y trivial).comp (ConcreteCategory.bijective_of_isIso iso.inv).1
  have hgs : ∀ b : S.R, gs (𝟙 (baseOver (Sp S.R)).left) y ⊤ (fn b) = g b := fun b => gs_eq _ y ⊤ trivial _
  have hi : Function.Injective (algebraMap o S.R) := fun b b' h => hb.inj (congrArg Subtype.val h)
  have hζ : IsPrimitiveRoot (g (algebraMap o S.R S.ζ)) ((S.r * S.N) ^ 2) :=
    (S.prim.map_of_injective hi).map_of_injective hg
  have : NeZero ((S.r * S.N) ^ 2) := ⟨(pow_pos (Nat.mul_pos S.r_pos hN.pos) 2).ne'⟩
  have : IsDomain ((baseOver (Sp S.R)).left.presheaf.stalk y) := inferInstanceAs (IsDomain ((Sp S.R).presheaf.stalk y))
  obtain ⟨k, -, hk⟩ := hζ.eq_pow_of_pow_eq_one (ξ := ξ.val) (congrArg Units.val hξ)
  refine ⟨k, fun i => ?_⟩
  have e' := e S.J ρ.s (ρ.s i) _ _ _ (ρ.U_act a i) (fun l => ρ.ev_val l h) (ρ.ev_val i _)
  simp only [hgs] at e'
  have q : ∑ n, algebraMap o S.R (S.ρ a n i) * ⟨S.ev h n, S.ev_mem _ _⟩ =
      algebraMap o S.R (S.ζ ^ k) * ⟨S.ev (h + S.r • a) i, S.ev_mem _ _⟩ := hg (by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_mul, map_pow, map_pow, hk]
    simp only [map_mul]
    exact e')
  have q' := congrArg S.R.val q
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum] at q'
  exact q'

end GlobalTheory.ZH.EvCrd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniversalBasisMoveBaseChangeStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.universalBasis_move_baseChange : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (P : PolAV S) (P' : PolAV S') (φ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A f φ → LBIso P'.L (P.L.pull φ) → ∀ (n : ℤ) (κ : Type) [Fintype κ] (T₀ : Over S) (τ : S' ⟶ T₀.left), τ ≫ T₀.hom = f → ∀ b₀ : κ → SecM P.A P.L n T₀, UnivBasis P n b₀ → ∃ b : κ → SecM P'.A P'.L n (baseOver S'), UnivBasis P' n b := by
  first | exact @GlobalTheory.UnivBasisMove.univBasis_move | exact GlobalTheory.UnivBasisMove.univBasis_move | (intros; apply GlobalTheory.UnivBasisMove.univBasis_move <;> assumption)
end

