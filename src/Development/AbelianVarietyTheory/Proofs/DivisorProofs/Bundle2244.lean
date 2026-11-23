module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2062
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalSiegelOfGenericPrincipalSpecialAmple
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2193
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2151
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2150
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2053

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerSymmetricAmple
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
open GlobalTheory.PrincSubring

noncomputable section
namespace GlobalTheory.EighthPowerBundle

open GlobalTheory.CechPic

def pre0 {S : Scheme.{0}} (h : ℕ) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (A ⊗ A).left)
    (hP : IsSymmetricPair h A P) : SiegPre 0 1 (0 : ℤ) (specZIsTerminal.from S) where
  A := A
  ab := hP.1
  P := P
  isLB := hP.2.2.1
  rig₁ := hP.2.2.2.1
  rig₂ := hP.2.2.2.2.1
  symm := hP.2.2.2.2.2
  lev := fun _ => 1
  lev_add := fun _ _ => (_root_.mul_one _).symm
  lev_tors := fun _ => one_pow _
  geom := fun k _ _ x β z _ hz => by
    rw [map_zero] at hz
    exact absurd hz z.ne_zero

theorem powLB_props : ∀ {S : Scheme.{0}} (h : ℕ) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (A ⊗ A).left),
    IsSymmetricPair h A P → Out.RelAmple A (diagPull A P) → IsAbelianScheme (Out.powObj A 8) ∧ (powLB A P).IsLB ∧
      Out.RelAmple (Out.powObj A 8) (powLB A P) ∧ Out.Rigidified (Out.powObj A 8) (powLB A P) ∧
      Out.Sym (Out.powObj A 8) (powLB A P) := by
  intro S h A _ _ P hP hA
  let c := pre0 h A P hP
  have hA' : Out.RelAmple c.A c.diag := hA
  obtain ⟨hpos, -⟩ := isE8_W8
  let pr : Fin 8 → (Out.powObj A 8 ⟶ A) := Out.powPr A
  have hmon : ∀ u, IsMonHom (pr u) := fun u => inferInstance
  have huniv : ∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ Out.powObj A 8, ∀ u, x ≫ pr u = y u := fun T y =>
    ⟨(Out.powIsLimit A 8).lift (Fan.mk T y), fun u => (Out.powIsLimit A 8).fac (Fan.mk T y) ⟨u⟩,
      fun x hx => (Out.powIsLimit A 8).uniq (Fan.mk T y) x fun u => hx u.as⟩
  have hL : (powLB A P).IsLB := LB.isLB_linComb hP.2.2.1 _ _
  have hLW : cls (powLB A P) hL = PrincipalIntegral.quad (cls c.P c.isLB) W8 pr := cls_linComb hP.2.2.1 _ _ _
  have hadd := PrincipalIntegral.pair_mul c SemiRigid.globalFns hA'
  exact ⟨AbelianSchemeGerms.isAbelianScheme_powObj A hP.1 7, hL,
    PosDefAmple.relAmple_linComb_of_posDef SemiRigid.globalFns 0 1 8 ℤ 0 S _ c (Out.powObj A 8) pr W8 hmon huniv hA'
      hpos,
    PrincipalIntegral.rigidified hadd hmon hL hLW,
    PrincipalIntegral.sym hadd (PrincipalIntegral.pair_comm c) hmon hL hLW⟩

end GlobalTheory.EighthPowerBundle
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndDataSymmAndOfOAct
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.RosatiSymmetry

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A]

theorem padd_comm' {T : Over S} (x y : T ⟶ A) : padd A x y = padd A y x := by
  show x * y = y * x
  exact mul_comm x y

abbrev sw : A ⊗ A ⟶ A ⊗ A := lift (snd A A) (fst A A)

theorem sw_padd (x y : A ⊗ A ⟶ A) : sw A ≫ padd A x y = padd A (sw A ≫ x) (sw A ≫ y) := by
  simp only [padd, comp_lift_assoc]

theorem formEq_sw (f g : A ⟶ A) (Y : Scheme.{0}) (p : Y ⟶ (A ⊗ A).left) :
    FormEq (fun k => p ≫ (sw A).left ≫ rosatiφ A g f k) (fun k => - rosatiε k)
      (fun k => p ≫ rosatiφ A f g k) rosatiε := by
  intro U _ h
  have e0 : (sw A).left ≫ (padd A (fst A A ≫ g) (snd A A)).left = (padd A (fst A A) (snd A A ≫ g)).left := by
    rw [← Over.comp_left, sw_padd, padd_comm']; simp only [lift_fst_assoc, lift_snd]
  have e1 : (sw A).left ≫ (fst A A ≫ g).left = (snd A A ≫ g).left := by
    rw [← Over.comp_left, lift_fst_assoc]
  have e2 : (sw A).left ≫ (snd A A).left = (fst A A).left := by
    rw [← Over.comp_left, lift_snd]
  have e3 : (sw A).left ≫ (padd A (fst A A) (snd A A ≫ f)).left = (padd A (fst A A ≫ f) (snd A A)).left := by
    rw [← Over.comp_left, sw_padd, padd_comm']; simp only [lift_fst, lift_snd_assoc]
  have e4 : (sw A).left ≫ (fst A A).left = (snd A A).left := by
    rw [← Over.comp_left, lift_fst]
  have e5 : (sw A).left ≫ (snd A A ≫ f).left = (fst A A ≫ f).left := by
    rw [← Over.comp_left, lift_snd_assoc]
  simp only [Fin.prod_univ_six, rosatiφ, rosatiε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_succ, Matrix.cons_val, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Matrix.head_cons, e0, e1, e2, e3, e4, e5]
  simp only [neg_neg, zpow_neg, zpow_one]
  ac_rfl

theorem formEq_sw' (f g : A ⟶ A) :
    FormEq (fun k => (sw A).left ≫ rosatiφ A g f k) (fun k => - rosatiε k) (rosatiφ A f g) rosatiε := by
  simpa only [Category.id_comp] using formEq_sw A f g _ (𝟙 _)

theorem rosatiAdj_symm (L : LB A.left) (hL : L.IsLB) (f g : A ⟶ A) (h : RosatiAdj A L f g) : RosatiAdj A L g f := by
  intro s
  obtain ⟨U, hs, t, ht⟩ := h s
  refine ⟨U, hs, ?_⟩
  have hW : (A ⊗ A).hom ⁻¹ᵁ U ≤ (sw A).left ⁻¹ᵁ ((A ⊗ A).hom ⁻¹ᵁ U) := by
    intro x hx
    show ((sw A).left ≫ (A ⊗ A).hom) x ∈ U
    rw [Over.w]; exact hx
  let σ := (sw A).left.resLE ((A ⊗ A).hom ⁻¹ᵁ U) ((A ⊗ A).hom ⁻¹ᵁ U) hW
  have hσ : σ ≫ ((A ⊗ A).hom ⁻¹ᵁ U).ι = ((A ⊗ A).hom ⁻¹ᵁ U).ι ≫ (sw A).left := Scheme.Hom.resLE_comp_ι _ _
  have hF : FormEq (fun k => σ ≫ ((A ⊗ A).hom ⁻¹ᵁ U).ι ≫ rosatiφ A f g k) (fun k => - rosatiε k)
      (fun k => ((A ⊗ A).hom ⁻¹ᵁ U).ι ≫ rosatiφ A g f k) rosatiε := by
    have e : (fun k => σ ≫ ((A ⊗ A).hom ⁻¹ᵁ U).ι ≫ rosatiφ A f g k) =
        fun k => ((A ⊗ A).hom ⁻¹ᵁ U).ι ≫ (sw A).left ≫ rosatiφ A f g k := by
      funext k; rw [← Category.assoc, hσ, Category.assoc]
    rw [e]; exact formEq_sw A g f _ _
  obtain ⟨t', ht', -⟩ := exists_gen hL hF (LB.invGen L _ _ (LB.pullGen L _ _ t σ))
    (DVR.invGen_isGen L _ _ _ (DVR.pullGen_isGen L _ _ t ht σ))
  exact ⟨t', ht'⟩

end GlobalTheory.Mum.RosatiSymmetry

namespace GlobalTheory.Mum.RosatiSymmetry
variable {R : Type} [CommRing R] [IsDomain R]

theorem val_tau_symm (D : DegPre R) {Z : Scheme.{0}} {z : Z} {J : (Z ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J)
    (r : Z ⟶ (TK R).left) (a b : D.X) : val (D.tau a b) r z J = val (D.tau b a) r z J := by
  simp only [DegPre.tau, val_mul hJ, val_inv]
  have e : val (D.psi (a + b)) r z J = val (D.psi (b + a)) r z J := by rw [add_comm]
  rw [e, mul_right_comm (val (D.psi (b + a)) r z J)]

theorem tauBal_symm (D : DegPre R) (f g : D.P.A ⟶ D.P.A) (a a' : D.X → D.X) (H : D.TauBal f g a a') :
    D.TauBal g f a' a := by
  intro u' hu' hn y y'
  have hL := D.P.isLB
  obtain ⟨u, hu, hv⟩ := exists_gen hL (formEq_sw' D.P.A f g)
    (LB.invGen D.P.L _ _ (LB.pullGen D.P.L _ _ u' (sw D.P.A).left))
    (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ u' hu' _))
  have hz : zero2 D.P.A ≫ (sw D.P.A).left = zero2 D.P.A := by
    rw [zero2, ← Over.comp_left, comp_lift, lift_snd, lift_fst]
  have hp : D.pt2 y' y ≫ (sw D.P.A).left = D.pt2 y y' := by
    rw [DegPre.pt2, DegPre.pt2, ← Over.comp_left, comp_lift, lift_snd, lift_fst]
  have hnu : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L) := by
    refine corr_of_val hL fun z J hJ => ?_
    have h1 := val_corr hJ hn (𝟙 _)
    rw [val_pull hJ, val_one] at h1
    rw [val_pull hJ, val_one, hv _ _ _ _ hJ, val_inv, val_pull hJ, Category.assoc, hz, h1, inv_one]
  have H' := H u hu hnu y' y
  refine corr_of_val hL fun z J hJ => ?_
  have h2 := val_corr hJ H' (𝟙 _)
  rw [val_mul hJ, val_pull hJ, hv _ _ _ _ hJ, val_inv, val_pull hJ, Category.assoc, hp] at h2
  rw [val_mul hJ, val_pull hJ, val_tau_symm D hJ _ (a' y) y', ← h2, val_tau_symm D hJ _ (a y') y]
  group

end GlobalTheory.Mum.RosatiSymmetry

namespace GlobalTheory.Mum

theorem endData_symm_and_ofOAct : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R),
    (∀ (a a' : D.P.A ⟶ D.P.A) (h h' : D.X →+ D.X), EndData D a a' h h' → EndData D a' a h' h) ∧
    ∀ (O : Type) [Ring O] [StarRing O] [Module O D.X] (o : D.OAct O) (x : O),
      EndData D (o.onB.act x) (o.onB.act (star x)) (DistribSMul.toAddMonoidHom D.X x)
        (DistribSMul.toAddMonoidHom D.X (star x)) := by
  intro R _ _ D
  refine ⟨fun a a' h h' ⟨h1, h2, h3, h4, h5, h6⟩ => ⟨h2, h1, RosatiSymmetry.rosatiAdj_symm D.P.A D.P.L D.P.isLB a a' h3,
    h5, h4, RosatiSymmetry.tauBal_symm D a a' h h' h6⟩, fun O _ _ _ o x => ?_⟩
  exact ⟨o.onB.hom x, o.onB.hom (star x), o.onB.rosati x, fun y => o.c_lin x y, fun y => o.c_lin (star x) y,
    o.tau_bal x⟩

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfCompEqOfConnectedSpacePullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem section_eq_of_apply_eq {k : Type} [Field k] {X : Scheme.{0}} (p : X ⟶ Sp k) (q q' : Sp k ⟶ X)
    (hq : q ≫ p = 𝟙 _) (hq' : q' ≫ p = 𝟙 _) (h : q (closedPoint k) = q' (closedPoint k)) : q = q' := by
  obtain ⟨⟨y, a⟩, rfl⟩ := (Scheme.SpecToEquivOfField k X).symm.surjective q
  obtain ⟨⟨y', a'⟩, rfl⟩ := (Scheme.SpecToEquivOfField k X).symm.surjective q'
  simp only [Scheme.SpecToEquivOfField_symm_apply] at hq hq' h ⊢
  obtain rfl : y = y' := by
    have k₁ : ∀ (y : X) (p : Spec (X.residueField y)), X.fromSpecResidueField y p = y := fun y p =>
      Set.mem_singleton_iff.1 (X.range_fromSpecResidueField y ▸ Set.mem_range_self p)
    exact (k₁ y _).symm.trans (h.trans (k₁ y' _))
  obtain ⟨c, hc⟩ := Spec.map_surjective (X.fromSpecResidueField y ≫ p)
  have key : ∀ b : X.residueField y ⟶ CommRingCat.of k, (Spec.map b ≫ X.fromSpecResidueField y) ≫ p = 𝟙 _ →
      ∀ o, b.hom (c.hom o) = o := fun b hb o => by
    rw [Category.assoc, ← hc, ← Spec.map_comp] at hb
    have := Spec.map_injective (hb.trans (Spec.map_id _).symm)
    simpa using RingHom.congr_fun (congrArg CommRingCat.Hom.hom this) o
  obtain rfl : a = a' := by
    ext u
    have hu : c.hom (a.hom u) = u := a.hom.injective (key a hq _)
    rw [← hu, key a hq, key a' hq']
  rfl

theorem eq_of_comp_eq_of_connectedSpace_pullback : ∀ (P Q : Scheme.{0}) (b : P ⟶ Q), LocallyQuasiFinite b → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ν : Sp Ω ⟶ Q) (ξ₁ ξ₂ : Sp Ω ⟶ P), ξ₁ ≫ b = ν → ξ₂ ≫ b = ν → ConnectedSpace (pullback b ν : Scheme.{0}) → ξ₁ = ξ₂ := by
  intro P Q b hb Ω _ _ ν ξ₁ ξ₂ h₁ h₂ hc
  haveI := hb
  have hsub : ∀ x y : (pullback b ν : Scheme.{0}), x = y := by
    intro x y
    have hopen : ∀ z : (pullback b ν : Scheme.{0}), IsOpen ({z} : Set (pullback b ν : Scheme.{0})) := by
      intro z
      have hd := (pullback.snd b ν).isDiscrete_preimage_singleton (pullback.snd b ν z)
      obtain ⟨U, hU, hUz⟩ := isDiscrete_iff_forall_exists_isOpen.mp hd z rfl
      have hU' : U ∩ (pullback.snd b ν) ⁻¹' {pullback.snd b ν z} = U :=
        Set.inter_eq_left.mpr fun w _ => Subsingleton.elim _ _
      rw [hU'] at hUz
      exact hUz ▸ hU
    have hcl : IsClopen ({x} : Set (pullback b ν : Scheme.{0})) := by
      refine ⟨?_, hopen x⟩
      rw [← isOpen_compl_iff, ← Set.biUnion_of_singleton ({x}ᶜ : Set (pullback b ν : Scheme.{0}))]
      exact isOpen_biUnion fun z _ => hopen z
    rcases isClopen_iff.mp hcl with h | h
    · exact absurd h (Set.singleton_ne_empty x)
    · have : y ∈ ({x} : Set (pullback b ν : Scheme.{0})) := h ▸ Set.mem_univ y
      exact (Set.mem_singleton_iff.mp this).symm
  have e₁ : ξ₁ ≫ b = 𝟙 (Sp Ω) ≫ ν := by rw [h₁, Category.id_comp]
  have e₂ : ξ₂ ≫ b = 𝟙 (Sp Ω) ≫ ν := by rw [h₂, Category.id_comp]
  have hσ := section_eq_of_apply_eq (pullback.snd b ν) (pullback.lift ξ₁ (𝟙 _) e₁) (pullback.lift ξ₂ (𝟙 _) e₂)
    (pullback.lift_snd _ _ _) (pullback.lift_snd _ _ _) (hsub _ _)
  have := congrArg (fun σ => σ ≫ pullback.fst b ν) hσ
  simp only [pullback.lift_fst] at this
  exact this

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfDerHomEq
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR

namespace GlobalTheory.ParPt

section Alg

variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B]

def derHom (δ : Ω[B⁄R] →ₗ[B] B) : B →ₐ[R] DualNumber B where
  toFun b := TrivSqZeroExt.inl b + TrivSqZeroExt.inr (δ (D R B b))
  map_one' := by ext <;> simp
  map_mul' a b := by
    ext
    · simp
    · simp [MulOpposite.smul_eq_mul_unop]; ring
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  commutes' r := by ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl']

theorem fst_derHom (δ : Ω[B⁄R] →ₗ[B] B) (b : B) : (derHom δ b).fst = b := by simp [derHom]

theorem snd_derHom (δ : Ω[B⁄R] →ₗ[B] B) (b : B) : (derHom δ b).snd = δ (D R B b) := by simp [derHom]

theorem eq_of_derHom_eq {δ₁ δ₂ : Ω[B⁄R] →ₗ[B] B} (h : ∀ b, derHom δ₁ b = derHom δ₂ b) : δ₁ = δ₂ := by
  have h' : ∀ b, δ₁ (D R B b) = δ₂ (D R B b) := fun b ↦ by
    rw [← snd_derHom, ← snd_derHom, h]
  exact Derivation.liftKaehlerDifferential_unique _ _ (Derivation.ext h')

end Alg

section Geo

variable {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (U : X.affineOpens)

theorem eq_of_affPt_eq {δ₁ δ₂ : Ω[Sec s U.1⁄R] →ₗ[Sec s U.1] Sec s U.1}
    (h : spMap (derHom δ₁ : Sec s U.1 →+* DualNumber (Sec s U.1)) ≫ affPt s U =
      spMap (derHom δ₂ : Sec s U.1 →+* DualNumber (Sec s U.1)) ≫ affPt s U) : δ₁ = δ₂ := by
  have := GlobalTheory.CechKS.FormLocal.ringHom_ext_affPt (s := s) U.2 h
  exact eq_of_derHom_eq fun b ↦ RingHom.congr_fun this b

theorem exists_derHom (y : Sp (DualNumber (Sec s U.1)) ⟶ X)
    (hy : y ≫ s = spMap (algebraMap R (DualNumber (Sec s U.1))))
    (he : spMap (TrivSqZeroExt.fstHom (Sec s U.1) (Sec s U.1) (Sec s U.1)).toRingHom ≫ y = affPt s U) :
    ∃ δ : Ω[Sec s U.1⁄R] →ₗ[Sec s U.1] Sec s U.1,
      spMap (derHom δ : Sec s U.1 →+* DualNumber (Sec s U.1)) ≫ affPt s U = y := by
  have hsurj : Surjective (spMap (TrivSqZeroExt.fstHom (Sec s U.1) (Sec s U.1) (Sec s U.1)).toRingHom) := by
    refine ⟨fun x ↦ ?_⟩
    have hx : x ∈ PrimeSpectrum.zeroLocus (RingHom.ker
        (TrivSqZeroExt.fstHom (Sec s U.1) (Sec s U.1) (Sec s U.1)).toRingHom : Set (DualNumber (Sec s U.1))) :=
      fun a ha ↦ by
        have ha' : a.fst = 0 := ha
        have h2 : a * a = 0 := by ext <;> simp [ha']
        exact x.isPrime.mem_of_pow_mem 2 (by rw [pow_two, h2]; exact zero_mem _)
    rw [← range_comap_of_surjective _ _ (fun b ↦ ⟨TrivSqZeroExt.inl b, rfl⟩)] at hx
    exact hx
  have htop : ⊤ ≤ y ⁻¹ᵁ U.1 := by
    intro p _
    obtain ⟨q, rfl⟩ := hsurj.surj p
    change ((spMap _ ≫ y).base q) ∈ U.1
    rw [he]
    have k := IsAffineOpen.range_fromSpec U.2
    rw [Set.ext_iff] at k
    exact (k _).1 ⟨q, rfl⟩
  let α := GlobalTheory.CechKS.FormLocal.valHom y htop hy
  have hα : spMap (α : Sec s U.1 →+* DualNumber (Sec s U.1)) ≫ affPt s U = y :=
    GlobalTheory.CechKS.FormLocal.valHom_pt U.2 y htop hy
  have hfst : ∀ b, (α b).fst = b := by
    have k : (TrivSqZeroExt.fstHom (Sec s U.1) (Sec s U.1) (Sec s U.1)).toRingHom.comp
        (α : Sec s U.1 →+* DualNumber (Sec s U.1)) = RingHom.id _ := by
      refine GlobalTheory.CechKS.FormLocal.ringHom_ext_affPt (s := s) U.2 ?_
      change spMap _ ≫ affPt s U = spMap _ ≫ affPt s U
      rw [Cris.spMap_comp, Category.assoc, hα, he, Cris.spMap_id, Category.id_comp]
    exact fun b ↦ RingHom.congr_fun k b
  let d : Derivation R (Sec s U.1) (Sec s U.1) :=
    { toFun := fun b ↦ (α b).snd
      map_add' := fun a b ↦ by simp
      map_smul' := fun r b ↦ by
        simp [Algebra.smul_def, TrivSqZeroExt.algebraMap_eq_inl']
      map_one_eq_zero' := by simp
      leibniz' := fun a b ↦ by
        simp only [map_mul, TrivSqZeroExt.snd_mul, smul_eq_mul]
        simp [MulOpposite.smul_eq_mul_unop, hfst]
        ring }
  refine ⟨d.liftKaehlerDifferential, ?_⟩
  have hd : derHom d.liftKaehlerDifferential = α := by
    ext b
    · rw [fst_derHom, hfst]
    · rw [snd_derHom, Derivation.liftKaehlerDifferential_comp_D]; rfl
  rw [hd, hα]
end Geo

section Val

attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler

variable {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (U : X.affineOpens)

theorem snd_val_derHom (δ : Ω[Sec s U.1⁄R] →ₗ[Sec s U.1] Sec s U.1) (y : Sp (DualNumber (Sec s U.1)) ⟶ X)
    (hy : y ≫ s = spMap (algebraMap R (DualNumber (Sec s U.1))))
    (e : spMap (derHom δ : Sec s U.1 →+* DualNumber (Sec s U.1)) ≫ affPt s U = y) (f : Form s) :
    TrivSqZeroExt.snd ((SqExt.ofModule R (Sec s U.1) (Sec s U.1)).val y hy f.1) =
      δ (connForm f.1 (affPt s U) (affPt_w s U)) := by
  have hx := affPt_w s U
  have hop : ∀ (b : Sec s U.1) (ω : Ω[Sec s U.1⁄R]), MulOpposite.op b • ω = b • ω := fun _ _ ↦ rfl
  let Φ : TrivSqZeroExt (Sec s U.1) Ω[Sec s U.1⁄R] →ₐ[R] TrivSqZeroExt (Sec s U.1) (Sec s U.1) :=
    { toFun := fun c ↦ TrivSqZeroExt.inl c.fst + TrivSqZeroExt.inr (δ c.snd)
      map_one' := by ext <;> simp
      map_zero' := by ext <;> simp
      map_add' := fun a b ↦ by ext <;> simp <;> ring
      map_mul' := fun a b ↦ by
        ext
        · simp
        · simp only [TrivSqZeroExt.snd_mul, hop, map_add (f := _), map_smul, TrivSqZeroExt.snd_add,
            TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_add,
            TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, smul_eq_mul]
          simp [MulOpposite.smul_eq_mul_unop]
          ring
      commutes' := fun r ↦ by
        ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl'] }
  let α₀ : Sec s U.1 →ₐ[R] Sec s U.1 := AlgHom.id R _
  have hπ : ∀ c, α₀ ((diagExt R (Sec s U.1)).π c) = (SqExt.ofModule R (Sec s U.1) (Sec s U.1)).π (Φ c) :=
    fun c ↦ by simp [Φ, α₀]
  have e₀ : spMap (α₀ : Sec s U.1 →+* Sec s U.1) ≫ affPt s U =
      spMap ((SqExt.ofModule R (Sec s U.1) (Sec s U.1)).π : TrivSqZeroExt (Sec s U.1) (Sec s U.1) →+* Sec s U.1) ≫ y := by
    rw [← e, ← Category.assoc, ← Cris.spMap_comp]
    congr 2
    ext b
    simp [α₀, fst_derHom]
  let Ψ := (diagExt R (Sec s U.1)).thickHom (SqExt.ofModule R (Sec s U.1) (Sec s U.1)) Φ α₀ hπ hx
    ((SqExt.ofModule R (Sec s U.1) (Sec s U.1)).red_w hy) e₀
  let a1 : Thick.triv (Sec s U.1) (affPt s U) hx ⟶
      Thick.triv (Sec s U.1) _ ((SqExt.ofModule R (Sec s U.1) (Sec s U.1)).red_w hy) := Thick.trivHom α₀ e₀
  let a2 : Thick.triv (Sec s U.1) (affPt s U) hx ⟶ Thick.triv (TrivSqZeroExt (Sec s U.1) (Sec s U.1)) y hy :=
    Thick.trivHom (derHom δ) e
  have k1 := Form.ev_sq f a1 ((SqExt.ofModule R (Sec s U.1) (Sec s U.1)).secHom
    ((SqExt.ofModule R (Sec s U.1) (Sec s U.1)).red_w hy)
    (SqExt.ofModule R (Sec s U.1) (Sec s U.1)).i (SqExt.ofModule R (Sec s U.1) (Sec s U.1)).π_i)
    ((diagExt R (Sec s U.1)).secHom hx (diagExt R (Sec s U.1)).i fun _ ↦ rfl) Ψ rfl rfl fun c ↦ by
      change TrivSqZeroExt.inl (α₀ c) = Φ (TrivSqZeroExt.inl c)
      ext <;> simp [Φ, α₀]
  have k2 := Form.ev_sq f a2 ((SqExt.ofModule R (Sec s U.1) (Sec s U.1)).idHom hy)
    ((diagExt R (Sec s U.1)).secHom hx (diagSec R (Sec s U.1)) (fst_derSec _)) Ψ rfl rfl fun c ↦ by
      change derHom δ c = Φ (diagSec R (Sec s U.1) c)
      ext
      · simp [Φ, fst_derHom, fst_derSec]
      · simp [Φ, snd_derHom, snd_derSec]
  have hΦ : ∀ z, TrivSqZeroExt.snd (Φ z) = δ z.snd := fun z ↦ by simp [Φ]
  rw [SqExt.val_apply, k1, k2, add_sub_add_right_eq_sub]
  change TrivSqZeroExt.snd (Φ _ - Φ _) = _
  rw [← map_sub, hΦ]
  rfl

end Val

end GlobalTheory.ParPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfCobEqZeroOfPow
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PDivGroup

open GlobalTheory.PDiv

theorem eq_zero_of_cob_eq_zero_of_pow (p : ℕ) (R : Type) [CommRing R] (N : ℕ)
    (hN : (p : R) ^ N = 0) (G : PDivGroup p R) (B : G.funs) (hB : G.cob B = 0) : B = 0 := by
  have key : ∀ k : ℕ, (∀ n, GlobalTheory.PDiv.mulBy R (G.A n) (p ^ k) (B.1 n) = 0) → ∀ n, B.1 n = 0 := by
    intro k
    induction k with
    | zero =>
      intro h n
      have h1 := (mulBy_of_cobOne_eq_zero (congrArg (fun x : G.cocycles => x.1 n) hB) (p ^ 0)).1
      rw [h n, pow_zero, one_smul] at h1
      exact h1.symm
    | succ k ih =>
      intro h
      refine ih fun n => Test.mulP_injective G n ?_
      rw [map_zero, map_mulBy, ← B.2 n, mulP_res, mulBy_mulBy, ← pow_succ, h]
  refine Subtype.ext (funext (key N fun n => ?_))
  rw [(mulBy_of_cobOne_eq_zero (congrArg (fun x : G.cocycles => x.1 n) hB) (p ^ N)).1,
    ← Nat.cast_smul_eq_nsmul R, Nat.cast_pow, hN, zero_smul]

end GlobalTheory.PDivGroup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinatePolynomialSubMemMaximalIdealPowStatement
section
open IsLocalRing GlobalTheory.FormalOrigin GlobalTheory.FormalOrigin.Extend
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coordinate_polynomial_sub_mem_maximalIdeal_pow : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [CommRing A] [IsLocalRing A] (inc : R →+* A) (ev : A →+* R), (∀ r, ev (inc r) = r) → ∀ (n : ℕ) (z : Fin n → A), maximalIdeal A = (maximalIdeal R).map inc ⊔ Ideal.span (Set.range z) → ∀ (k : ℕ) (f : A), ∃ p ∈ Subring.closure (Set.range inc ∪ Set.range z), f - p ∈ maximalIdeal A ^ k := by
  first | exact @GlobalTheory.exists_mem_closure_sub_mem_maximalIdeal_pow | exact GlobalTheory.exists_mem_closure_sub_mem_maximalIdeal_pow | (intros; apply GlobalTheory.exists_mem_closure_sub_mem_maximalIdeal_pow <;> assumption)
end

