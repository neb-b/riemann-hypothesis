module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCubicalRigidifiedExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2944
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2550
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2940
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogDerivPolarizationRaynaudEqPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianPartConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2949
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2947
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2941
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0590
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2620
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2937
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2942
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2728
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdjointnessIsoExtendsDescendedGroup
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ExtAdj

section Gen
variable {X Y B : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

theorem exists_normalized {ψ : K → (Y ⟶ X)} {ε : K → ℤ} (p : Y ⟶ B) (e : B ⟶ Y) (he : e ≫ p = 𝟙 B)
    (s : LB.Gen (LB.LinComb L ψ ε)) (hs : s.IsGen) :
    ∃ s₂ : LB.Gen (LB.LinComb L (Sum.elim ψ (fun k => p ≫ e ≫ ψ k)) (Sum.elim ε (fun k => -ε k))),
      s₂.IsGen ∧ ∀ y J, Good L y J → val s₂ e y J = 1 := by
  refine ⟨LB.mulGen L _ _ _ _ s (LB.pullGen L _ _ (LB.invGen L _ _ (LB.pullGen L ψ ε s e)) p),
    DVR.mulGen_isGen _ _ _ _ _ _ _ hs (DVR.pullGen_isGen _ _ _ _ (DVR.invGen_isGen _ _ _ _
      (DVR.pullGen_isGen _ _ _ _ hs e)) p), fun y J hJ => ?_⟩
  rw [val_mul hJ, val_pull hJ, val_inv, val_pull hJ, he, Category.id_comp, mul_inv_cancel]

theorem formEq_sec {ψ : K → (Y ⟶ X)} {ε : K → ℤ} (p : Y ⟶ B) (e : B ⟶ Y) (he : e ≫ p = 𝟙 B) :
    FormEq (K := PEmpty) (PEmpty.elim : PEmpty → (B ⟶ X)) PEmpty.elim
      (fun k => e ≫ Sum.elim ψ (fun k => p ≫ e ≫ ψ k) k) (Sum.elim ε (fun k => -ε k)) := by
  intro U _ h
  rw [Fintype.prod_empty, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, ← Category.assoc, he, Category.id_comp, zpow_neg, Finset.prod_inv_distrib,
    mul_inv_cancel]
end Gen

section Cube
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {T : Over S}

def cφ (x : Fin 2 → (T ⟶ G)) : ULift.{0} (Finset (Fin 2)) → (T.left ⟶ G.left) := fun I => (psum G x I.down).left

def cε : ULift.{0} (Finset (Fin 2)) → ℤ := fun I => (-1) ^ (2 - I.down.card)

theorem cls_diff {L : LB G.left} (hL : L.IsLB) (x₁ x₂ : Fin 2 → (T ⟶ G))
    (h : (LB.LinComb L (Sum.elim (cφ x₁) (cφ x₂)) (Sum.elim cε (fun I => -cε I))).IsLB) :
    CechPic.cls _ h = CechPic.cls (LB.LinComb L (cφ x₁) cε) (LB.isLB_linComb hL _ _) -
      CechPic.cls (LB.LinComb L (cφ x₂) cε) (LB.isLB_linComb hL _ _) := by
  rw [CechPic.cls_linComb hL, CechPic.cls_linComb hL, CechPic.cls_linComb hL, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, neg_smul, Finset.sum_neg_distrib, sub_eq_add_neg]

theorem lbIso_of_gen {L : LB G.left} (hL : L.IsLB) (x₁ x₂ : Fin 2 → (T ⟶ G))
    (t : LB.Gen (LB.LinComb L (Sum.elim (cφ x₁) (cφ x₂)) (Sum.elim cε (fun I => -cε I)))) (ht : t.IsGen) :
    LBIso (cubeLB G x₁ L) (cubeLB G x₂ L) := by
  have z := (CechPic.cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 ⟨t, ht⟩
  rw [cls_diff hL x₁ x₂, sub_eq_zero] at z
  exact (CechPic.cls_eq_iff _ _).1 z

theorem gen_of_lbIso {L : LB G.left} (hL : L.IsLB) (x₁ x₂ : Fin 2 → (T ⟶ G))
    (H : LBIso (cubeLB G x₁ L) (cubeLB G x₂ L)) :
    ∃ t : LB.Gen (LB.LinComb L (Sum.elim (cφ x₁) (cφ x₂)) (Sum.elim cε (fun I => -cε I))), t.IsGen := by
  refine (CechPic.cls_eq_zero_iff (LB.isLB_linComb hL _ _)).1 ?_
  rw [cls_diff hL x₁ x₂, sub_eq_zero]
  exact (CechPic.cls_eq_iff (LB.isLB_linComb hL (cφ x₁) cε) (LB.isLB_linComb hL (cφ x₂) cε)).2 H

end Cube

section Origin
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

theorem eSec_cφ (x : Fin 2 → (G2 G ⟶ G)) (hx : ∀ i, η[G2 G] ≫ x i = 1) (I : ULift.{0} (Finset (Fin 2))) :
    eSec (G2 G) ≫ cφ x I = eSec G := by
  have h1 : η[G2 G] ≫ psum G x I.down = 1 := by
    have a := psum_hom (preHom (G := G) η[G2 G]) x I.down
    have b := psum_hom (1 : (𝟙_ (Over S) ⟶ G) →* (𝟙_ (Over S) ⟶ G)) (fun _ => 1) I.down
    simp only [MonoidHom.one_apply] at b
    exact a.trans ((congrArg (fun z => psum G z I.down) (funext hx)).trans b.symm)
  have h2 := congrArg (fun z => z.left) h1
  simp only [Over.comp_left] at h2
  refine h2.trans ?_
  simp [Hom.one_def, eSec]

theorem eSec_x2 (i : Fin 2) : η[G2 G] ≫ x2 G i = η[G] := by
  fin_cases i <;> simp [x2]

theorem one_cube₁ (f : G ⟶ G) [IsMonHom f] (i : Fin 2) : η[G2 G] ≫ (![fst G G ≫ f, snd G G] : Fin 2 → (G2 G ⟶ G)) i = 1 := by
  fin_cases i <;> simp [Hom.one_def]

theorem one_cube₂ (f : G ⟶ G) [IsMonHom f] (i : Fin 2) : η[G2 G] ≫ (![fst G G, snd G G ≫ f] : Fin 2 → (G2 G ⟶ G)) i = 1 := by
  fin_cases i <;> simp [Hom.one_def]
end Origin

section Push
variable {S U : Scheme.{0}} {j : U ⟶ S} {G : Over S} [GrpObj G] [IsCommMonObj G]
  {A : Over U} [GrpObj A] [IsCommMonObj A] {e : A.left ⟶ G.left}

abbrev jTwo (he : IsGrpPullback A G j e) : (G2 A).left ⟶ (G2 G).left :=
  (lift (pushPt he.1.w (fst A A)) (pushPt he.1.w (snd A A))).left

theorem doubleProductMapOfGrpPullback_comp_doubleCoordinate (he : IsGrpPullback A G j e) (i : Fin 2) : jTwo he ≫ (x2 G i).left = (x2 A i).left ≫ e := by
  fin_cases i
  · exact congrArg (fun z => z.left) (lift_fst (pushPt he.1.w (fst A A)) (pushPt he.1.w (snd A A)))
  · exact congrArg (fun z => z.left) (lift_snd (pushPt he.1.w (fst A A)) (pushPt he.1.w (snd A A)))

theorem eSec_jTwo (he : IsGrpPullback A G j e) : eSec (G2 A) ≫ jTwo he = j ≫ eSec (G2 G) := by
  refine GlobalTheory.Mum.PowCart.square_over_hom_ext _ fun i => ?_
  have a : eSec (G2 A) ≫ (x2 A i).left = eSec A := congrArg (fun z => Over.Hom.left z) (eSec_x2 (G := A) i)
  have b : eSec (G2 G) ≫ (x2 G i).left = eSec G := congrArg (fun z => Over.Hom.left z) (eSec_x2 (G := G) i)
  rw [Category.assoc, doubleProductMapOfGrpPullback_comp_doubleCoordinate, ← Category.assoc, a, Category.assoc, b]
  exact (cubeMapOf he).e_comm

theorem cφ_push (he : IsGrpPullback A G j e) (x' : Fin 2 → (G2 A ⟶ A)) (x : Fin 2 → (G2 G ⟶ G))
    (hx : ∀ i, (x' i).left ≫ e = jTwo he ≫ (x i).left) (I : ULift.{0} (Finset (Fin 2))) :
    cφ x' I ≫ e = jTwo he ≫ cφ x I :=
  psum_push he x' x (lift (pushPt he.1.w (fst A A)) (pushPt he.1.w (snd A A)))
    (fun i => Over.OverMorphism.ext (by rw [Over.comp_left]; exact hx i)) I.down
end Push

section Drop
variable {X Y B : Scheme.{0}} {K0 : Type} [Fintype K0]

theorem formEq_drop {ψ : K0 ⊕ K0 → (Y ⟶ X)} {ε₀ : K0 → ℤ} (p : Y ⟶ B) (e : B ⟶ Y) (z : B ⟶ X)
    (hz : ∀ k, e ≫ ψ k = z) :
    FormEq (Sum.elim ψ (fun k => p ≫ e ≫ ψ k))
      (Sum.elim (Sum.elim ε₀ (fun k => -ε₀ k)) (fun k => -(Sum.elim ε₀ (fun k => -ε₀ k)) k))
      ψ (Sum.elim ε₀ (fun k => -ε₀ k)) := by
  intro U _ h
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, hz, zpow_neg, neg_neg, inv_inv,
    Finset.prod_inv_distrib]
  group
end Drop

theorem adj_extends : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∀ (tF : SAB H (Xo.XF c)), SABMap tF Xo.univ.t (pullback.fst _ _) → ∀ (G : Over S) [GrpObj G] [IsCommMonObj G] (e : tF.G.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback tF.G G j e → (∀ {k : Type} [Field k] {m n : ℕ} (C : MonoFam Xo c φ (ChartRing k m n)), IsTaut C → ∀ ξ : Sp (ChartRing k m n) ⟶ S, C.y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK C.t (jK _)) (b : SABMap tK tF C.y), ∃ πC : C.t.G.left ⟶ G.left, IsGrpPullback C.t.G G ξ πC ∧ a.φ ≫ πC = b.φ ≫ e) → ∀ (act : OAct (𝓞 E) G), (∀ a, (tF.act.act a).left ≫ e = e ≫ (act.act a).left) → ∀ (PP : RigLB G) (cub : CubicalStr G PP) (cm : CubeMap tF.G G), cm.F = e → cm.e = j → cm.IsPullCubical tF.cub cub → ∀ a, LBIso (cubeLB G ![fst G G ≫ act.act a, snd G G] PP.L) (cubeLB G ![fst G G, snd G G ≫ act.act (H.bar a)] PP.L) := by
  intro E _ _ _ H Dw l Xo c φ _ _ _ Z zs i OZ N d J S π j _ BD hU _ tF _ G _ _ e hsa he _ act hact PP cub cm hF _ hpc a
  obtain ⟨⟨-, -, -, -, -, -⟩, -, -, -, ⟨⟨hnorm, -⟩, hproj, -, hdense, -, -⟩, -⟩ := hU
  have := hsa.smooth
  have := hsa.geomConnected
  haveI : LocallyOfFiniteType (π ≫ zs) := by
    obtain ⟨M, i', hi', hcomp⟩ := hproj
    haveI := hi'
    haveI := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str c.F M
    rw [← hcomp]
    infer_instance
  haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (π ≫ zs)
  haveI : IsDominant j := ⟨hdense⟩
  have hS : Geo.Tor.IsNormalScheme S := (GlobalTheory.isNormalScheme_iff_pred S).mp hnorm
  obtain ⟨w, hw, -, -⟩ := hpc
  have hw' := (isGen_iff w).1 hw
  haveI := act.hom a
  haveI := act.hom (H.bar a)
  haveI := tF.act.hom a
  haveI := tF.act.hom (H.bar a)
  let x₁ : Fin 2 → (G2 G ⟶ G) := ![fst G G ≫ act.act a, snd G G]
  let x₂ : Fin 2 → (G2 G ⟶ G) := ![fst G G, snd G G ≫ act.act (H.bar a)]
  let y₁ : Fin 2 → (G2 tF.G ⟶ tF.G) := ![fst tF.G tF.G ≫ tF.act.act a, snd tF.G tF.G]
  let y₂ : Fin 2 → (G2 tF.G ⟶ tF.G) := ![fst tF.G tF.G, snd tF.G tF.G ≫ tF.act.act (H.bar a)]
  let ψ := Sum.elim (cφ x₁) (cφ x₂)
  let ψ' := Sum.elim (cφ y₁) (cφ y₂)
  let ε₁ : ULift.{0} (Finset (Fin 2)) ⊕ ULift.{0} (Finset (Fin 2)) → ℤ := Sum.elim cε (fun I => -cε I)
  obtain ⟨s, hs⟩ := gen_of_lbIso tF.PP.isLB y₁ y₂ (tF.adj a)
  obtain ⟨s₂, hs₂, h1⟩ := exists_normalized (G2 tF.G).hom (eSec (G2 tF.G)) (CubeExtension.eSec_comp _) s hs
  have hsm := CubeExtension.smooth_tensor G G
  have hgc := CubeExtension.geometricallyConnected_tensor G G
  have hpb : IsPullback (jTwo he) (G2 tF.G).hom (G2 G).hom j := GlobalTheory.Mum.PowCart.isPullback_two he.1
  have f0 : jTwo he ≫ (fst G G).left = (fst tF.G tF.G).left ≫ e := doubleProductMapOfGrpPullback_comp_doubleCoordinate he 0
  have f1 : jTwo he ≫ (snd G G).left = (snd tF.G tF.G).left ≫ e := doubleProductMapOfGrpPullback_comp_doubleCoordinate he 1
  have hψ : ∀ k, ψ' k ≫ e = jTwo he ≫ ψ k := by
    rintro (I | I)
    · refine cφ_push he y₁ x₁ (fun i => ?_) I
      fin_cases i
      · show (fst tF.G tF.G ≫ tF.act.act a).left ≫ e = jTwo he ≫ (fst G G ≫ act.act a).left
        rw [Over.comp_left, Over.comp_left, Category.assoc, hact a, ← Category.assoc, ← f0, Category.assoc]
      · exact f1.symm
    · refine cφ_push he y₂ x₂ (fun i => ?_) I
      fin_cases i
      · exact f0.symm
      · show (snd tF.G tF.G ≫ tF.act.act (H.bar a)).left ≫ e = jTwo he ≫ (snd G G ≫ act.act (H.bar a)).left
        rw [Over.comp_left, Over.comp_left, Category.assoc, hact (H.bar a), ← Category.assoc, ← f1, Category.assoc]
  have hφ : ∀ k, Sum.elim ψ' (fun k => (G2 tF.G).hom ≫ eSec (G2 tF.G) ≫ ψ' k) k ≫ cm.F =
      jTwo he ≫ Sum.elim ψ (fun k => (G2 G).hom ≫ eSec (G2 G) ≫ ψ k) k := by
    rw [hF]
    rintro (k | k)
    · exact hψ k
    · simp only [Sum.elim_inr, Category.assoc]
      rw [hψ k, ← Category.assoc (eSec (G2 tF.G)), eSec_jTwo he, Category.assoc, ← Category.assoc (G2 tF.G).hom,
        ← hpb.w, Category.assoc]
  obtain ⟨c', hc', -⟩ := DenseCubeExt.exists_extension hS j (G2 G).hom (eSec (G2 G)) (jTwo he) (G2 tF.G).hom
    (eSec (G2 tF.G)) hsm hgc (CubeExtension.eSec_comp _) hpb (eSec_jTwo he) PP.isLB tF.PP.isLB hw'
    (Sum.elim ψ (fun k => (G2 G).hom ≫ eSec (G2 G) ≫ ψ k)) (Sum.elim ψ' (fun k => (G2 tF.G).hom ≫ eSec (G2 tF.G) ≫ ψ' k))
    (Sum.elim ε₁ (fun k => -ε₁ k)) hφ (formEq_sec _ _ (CubeExtension.eSec_comp _))
    (formEq_sec _ _ (CubeExtension.eSec_comp _)) s₂ hs₂ h1
  have hz : ∀ k, eSec (G2 G) ≫ ψ k = eSec G := by
    rintro (I | I)
    · exact eSec_cφ x₁ (one_cube₁ (act.act a)) I
    · exact eSec_cφ x₂ (one_cube₂ (act.act (H.bar a))) I
  obtain ⟨t, ht, -⟩ := exists_gen PP.isLB (formEq_drop (ε₀ := cε) (G2 G).hom (eSec (G2 G)) (eSec G) hz) c' hc'
  exact lbIso_of_gen PP.isLB x₁ x₂ t ht

end GlobalTheory.ExtAdj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFiltrationOrthogonalPerfect
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.PoincareKer.mem_fil_left : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] [Nontrivial R]
    (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B →
    SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left,
    AbDual.IsPerfect A B P → ∀ φ : HdR A →ₗ[R] HdR B →ₗ[R] R, AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ →
    ∀ x : HdR A, (∀ y ∈ Fil B, φ x y = 0) → x ∈ Fil A := by
  intro hHdR R _ _ A B _ _ g hA hB hgA hgB P hP φ hφ x hx
  have hφ' := _root_.GlobalTheory.pairing_swap_eq_neg_flip R A B P hP.isLB φ hφ
  refine _root_.GlobalTheory.PoincareKer.mem_fil_of_orth hHdR R B A g hB hA hgB hgA (AbDual.swap P) hP.swap (-φ.flip) hφ' x ?_
  intro y hy
  simp [hx y hy]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFrameGeneratorValuePullbackStatement
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.HodgeFrameGen
open GlobalTheory.QCoh (pullbackSections)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_frame_generator_value_pullback : ∀ {S' T Z : Scheme.{0}} {G : Over S'} [GrpObj G] {H : Over T} [GrpObj H] {x : T ⟶ S'}
    {ψ : H.left ⟶ G.left} [QuasiSeparated G.hom] {g : ℕ} (h : IsGrpPullback H G x ψ)
    {a : Fin g → Γ(omega H, ⊤)} (ha : IsFrame a) (r : Z ⟶ T) {B : Over Z} [GrpObj B] {ρ : B.left ⟶ H.left}
    (q : IsGrpPullback B H r ρ) (x' : Z ⟶ S') (ψ' : B.left ⟶ G.left) (h' : IsGrpPullback B G x' ψ'),
    r ≫ x = x' → ρ ≫ ψ = ψ' → ∀ {b : Fin g → Γ(omega B, ⊤)} (hb : IsFrame b),
    (∀ i, b i = (omegaBase q).app ⊤ (pullbackSections r _ le_top (a i))) → ∀ (z : Z)
    (J : (Z ⟶ S') → (hodge G g).ι), Good (hodge G g) z J →
    val (L := hodge G g) (φ := fun _ : PUnit => x) (ε := fun _ => 1) (gen h ha) r z J =
      val (L := hodge G g) (φ := fun _ : PUnit => x') (ε := fun _ => 1) (gen h' hb) (𝟙 Z) z J := by
  first | exact @GlobalTheory.HodgeFrameGen.val_gen_pull | exact GlobalTheory.HodgeFrameGen.val_gen_pull | (intros; apply GlobalTheory.HodgeFrameGen.val_gen_pull <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsLastBis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc

theorem USetup.range_π_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (η : Xo.XF c) (A : Set C.Z), (∀ w, X₁.uΩ w = η) → closure {C.i η} = A → Set.range X₁.π = A := by
  intro E _ _ _ H Dw _ l Xo c C X₁ η A hη hA
  haveI := X₁.fin
  have hc : IsClosedMap X₁.π.base := X₁.π.isClosedMap
  let w₀ : Sp X₁.Ω₁ := IsLocalRing.closedPoint X₁.Ω₁
  have hgen : X₁.M.pt w₀ = genericPoint X₁.M.Z := X₁.M.pt_apply w₀
  have hpt : X₁.π (X₁.M.pt w₀) = C.i η := by
    have h := congrArg (fun f => f.base w₀) X₁.comp
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
    rw [← hη w₀]
    simpa using h
  have huniv : closure ({genericPoint X₁.M.Z} : Set X₁.M.Z) = Set.univ := genericPoint_spec X₁.M.Z
  rw [← hA, ← hpt, hgen, ← Set.image_singleton, ← Set.image_univ, ← huniv]
  exact (hc.closure_image_eq_of_continuous X₁.π.continuous _).symm

end GlobalTheory.UPoinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantFieldCombKillsWeightZeroOfCoboundary
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatUniq

theorem comb_kills_weight_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [Algebra ℚ R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (K : Type) (Wk : K → Y.H.left.Opens) (jk : K → Q.P.L.ι), (∀ k, ∃ V : Q.P.A.left.Opens, Wk k = Y.q.left ⁻¹ᵁ V) → ⨆ k, Wk k = ⊤ → (∀ k, Wk k ≤ Y.q.left ⁻¹ᵁ Q.P.L.U (jk k)) → ∀ (P : ∀ k, Γ(Y.H.left, Wk k)) (e : Fin n → R), (∀ k, IsWt Y 0 _ (P k)) → (∀ k k' (Wo : Y.H.left.Opens), Wo ≤ Wk k ⊓ Wk k' → rsT (P k') Wo - rsT (P k) Wo = ∑ a, constFn Y.H.hom Wo (e a) * dlg Y.H Y.q.left Q.P.L (dd a) (jk k) (jk k') Wo) → ∀ (V : Q.P.A.left.Opens) f, IsWt Y 0 (Y.q.left ⁻¹ᵁ V) f → ∑ a, constFn Y.H.hom _ (e a) * dd a _ f = 0 := by
  intro R _ _ _ _ _ Q O _ _ _ oa Y n v dd hinv K Wk jk hWk hcov hjk P e hP hcob V f hf
  haveI : IsMonHom Y.q := Y.q_linear.isMonHom
  obtain ⟨dw, hdw⟩ := GlobalTheory.RayBasis.exists_isInv (∑ a, e a • v a)
  obtain ⟨δ, hδ⟩ := GlobalTheory.RayBasis.exists_isInv (GlobalTheory.Heat.LiePush.pushL Y.q (∑ a, e a • v a))
  have hcomb : ∀ (W : Y.H.left.Opens) (s : Γ(Y.H.left, W)),
      dw W s = ∑ a, constFn Y.H.hom W (e a) * dd a W s := by
    intro W s
    have h := GlobalTheory.Heat.LiePush.isInv_pbT (𝟙 Y.H) hdw (w := v) hinv e
      (PullbackSections.tanM_ext (by rw [GlobalTheory.Heat.LiePush.tv_pushL]; exact Category.comp_id _)) W s W le_rfl
    simpa only [Over.id_left, GlobalTheory.Heat.LiePush.pbT_id] using h
  have hpull : ∀ (U : Q.P.A.left.Opens) (s : Γ(Q.P.A.left, U)) (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ U →
      dw W (pbT Y.q.left s W) = pbT Y.q.left (δ U s) W := by
    intro U s W hW
    have h := GlobalTheory.Heat.LiePush.isInv_pbT Y.q hdw (g := 1) (w := fun _ => GlobalTheory.Heat.LiePush.pushL Y.q (∑ a, e a • v a))
      (d' := fun _ => δ) (fun _ => hδ) (fun _ => 1) (by simp) U s W hW
    have h1 : constFn Q.P.A.hom U (1 : R) = 1 := by simp [constFn]
    simpa [h1] using h
  obtain ⟨Vs, b, hVcov, hVle, hb⟩ := _root_.GlobalTheory.Heat.AbDescent.descent R Q O oa Y dw δ hpull K Wk jk hWk hcov hjk P hP
    (fun k k' Wo hWo => by
      rw [hcob k k' Wo hWo]
      simp only [dlg, hcomb, Finset.sum_mul, _root_.mul_assoc])
  have hw0 : GlobalTheory.Heat.LiePush.pushL Y.q (∑ a, e a • v a) = 0 := _root_.GlobalTheory.LieRigid.lie_inj R Q.P _ δ hδ K Vs jk hVcov hVle b hb
  have hδ0 : ∀ (U : Q.P.A.left.Opens) (s : Γ(Q.P.A.left, U)), δ U s = 0 := by
    intro U s
    have h := GlobalTheory.Heat.LiePush.isInv_pbT (𝟙 Q.P.A) hδ (g := 0) (w := Fin.elim0) (d' := Fin.elim0)
      (fun a => a.elim0) Fin.elim0
      (by rw [hw0, map_zero]; simp) U s U le_rfl
    simpa only [Over.id_left, GlobalTheory.Heat.LiePush.pbT_id, Finset.univ_eq_empty, Finset.sum_empty] using h
  obtain ⟨g, hg⟩ := GlobalTheory.Heat.AbConst.exists_app_eq Y hf
  have hfg : f = pbT Y.q.left g (Y.q.left ⁻¹ᵁ V) := by
    rw [← hg, GlobalTheory.KS.pbT_of_le _ le_rfl, Scheme.Hom.app_eq_appLE]
  rw [← hcomb, hfg, hpull V g _ le_rfl, hδ0, GlobalTheory.KS.pbT_zero]

end GlobalTheory.HeatUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOfSemiAbelianHomRetractStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAbelianScheme_of_semiAbelian_hom_retract : ∀ (S : Scheme.{0}) (A G : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj G] [IsCommMonObj G] (inc : G ⟶ A) (pr : A ⟶ G), IsAbelianScheme A → IsSemiAbelian G → IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → IsAbelianScheme G := by
  first | (exact @GlobalTheory.isAbelianScheme_of_retract_of_isSemiAbelian) | (exact GlobalTheory.isAbelianScheme_of_retract_of_isSemiAbelian) | (intros; apply GlobalTheory.isAbelianScheme_of_retract_of_isSemiAbelian  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionDenseGenericFibreNormalisation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem isOpenImmersion_dense_genericFibre_normalization : ∀ (o F : Type) [CommRing o] [IsDomain o] [IsDedekindDomain o] [Algebra.FiniteType ℤ o] [Field F] [CharZero F] (b : o →+* F) (n : ℕ) (X : Scheme.{0}) (s : X ⟶ Sp F) (f : X ⟶ PSpace o n) [QuasiCompact f] [QuasiSeparated f], Function.Injective b → (∀ x : F, ∃ a d : o, b d ≠ 0 ∧ x * b d = b a) → Geo.Tor.IsNormalScheme X → IsSeparated s → LocallyOfFiniteType s → QuasiCompact s → f ≫ PSpace.str o n = s ≫ spMap b → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ X), Set.Finite {y : Sp K ⟶ X | y ≫ s = x ≫ s ∧ y ≫ f = x ≫ f}) → ∀ iF : X ⟶ pullback (f.fromNormalization ≫ PSpace.str o n) (spMap b), iF ≫ pullback.fst _ _ = f.toNormalization → iF ≫ pullback.snd _ _ = s → IsOpenImmersion iF ∧ Dense (Set.range iF) := by
  intro o F _ _ _ _ _ _ b n X s f _ _ hb hfrac hN _ _ _ hfs hfib iF h1 h2
  letI : Algebra o F := b.toAlgebra
  haveI : FaithfulSMul o F := (faithfulSMul_iff_algebraMap_injective _ _).mpr hb
  haveI : IsFractionRing o F := IsFractionRing.of_field o F fun x => by
    obtain ⟨a, d, hd, e⟩ := hfrac x
    exact ⟨a, d, (eq_div_iff hd).mpr e⟩
  haveI : GlobalTheory.IsNormalScheme X := GlobalTheory.IsNormalScheme.of_pred hN
  haveI : IsReduced X := inferInstance
  obtain ⟨-, i₀, hoi, hd, hsnd, hfst⟩ :=
    GlobalTheory.SecCompact.exists_openImmersion_genericFibre F o n X s f hfs hfib
  have e : iF = i₀ := by
    apply pullback.hom_ext
    · rw [h1, hfst]
    · rw [h2, hsnd]
  subst e
  exact ⟨hoi, hd⟩

end GlobalTheory.UMin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyBijectiveOnTorsionCoprimeDegree
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

namespace GlobalTheory

theorem isogeny_torsion_bij {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A]
    [IsCommMonObj B] (la : A ⟶ B) (mu : B ⟶ A) (d M : ℕ) (T : Over S) :
    IsMonHom la → IsMonHom mu → la ≫ mu = 𝟙 A ^ d → mu ≫ la = 𝟙 B ^ d → M.Coprime d →
      (∀ y : T ⟶ A, y ^ M = 1 → y ≫ la = 1 → y = 1) ∧
        (∀ g : T ⟶ B, g ^ M = 1 → ∃ y : T ⟶ A, y ^ M = 1 ∧ y ≫ la = g) := by
  intro hla hmu hlm hml hMd
  refine ⟨fun y hyM hyl => ?_, fun g hgM => ?_⟩
  · have hyd : y ^ d = 1 := by
      have h1 : y ≫ (la ≫ mu) = y ^ d := by
        rw [hlm, MonObj.comp_pow, Category.comp_id]
      rw [← h1, ← Category.assoc, hyl, MonObj.one_comp]
    have h := (pow_gcd_eq_one (a := y) (m := M) (n := d)).2 ⟨hyM, hyd⟩
    rwa [Nat.Coprime.gcd_eq_one hMd, pow_one] at h
  ·
    set e := d ^ (Nat.totient M - 1) with he
    have hde : d * e % M = 1 % M := by
      rcases Nat.eq_zero_or_pos M with h0 | hpos
      · subst h0
        have hd1 : d = 1 := (Nat.coprime_zero_left d).1 hMd
        subst hd1
        simp [he]
      · have ht : 0 < Nat.totient M := Nat.totient_pos.2 hpos
        have hpow : d * e = d ^ Nat.totient M := by
          rw [he, ← pow_succ']
          congr 1
          omega
        rw [hpow]
        exact Nat.ModEq.pow_totient (Nat.Coprime.symm hMd)
    refine ⟨(g ≫ mu) ^ e, ?_, ?_⟩
    · rw [← pow_mul, mul_comm, pow_mul, ← MonObj.pow_comp, hgM, MonObj.one_comp, one_pow]
    · have h1 : (g ≫ mu) ≫ la = g ^ d := by
        rw [Category.assoc, hml, MonObj.comp_pow, Category.comp_id]
      rw [MonObj.pow_comp, h1, ← pow_mul, pow_eq_pow_mod (d * e) hgM, hde,
        ← pow_eq_pow_mod 1 hgM, pow_one]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelDegreeLeDieudonneColengthOfHeightOneStatement
section
open CategoryTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem GlobalTheory.T.kernelDegree_le_dieudonneColength_of_heightOne
    (p : ℕ) [Fact p.Prime] (T : GlobalTheory.Dieu.Theory p) (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H) (q' : H ⟶ G) (e : ℕ)
    (h₁ : q ≫ q' = (p : ℤ_[p]) • 𝟙 G) (h₂ : q' ≫ q = (p : ℤ_[p]) • 𝟙 H)
    (hF : frobKerIdeal p k (G.A 1) ≤ kerIdeal (q.app 1)) (he : GlobalTheory.Dieu.HasLogDeg q e) :
    (e : ℕ∞) ≤ Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) ∧
      (e : ℕ∞) ≤ Module.length (WittVector p k) (T.M H.dual ⧸ LinearMap.range (T.map (dualHom G H q))) ∧
      e ≤ Module.finrank k (G.omega ⧸ LinearMap.range (omegaMap G H q)) :=
  GlobalTheory.Dieu.le_colength_of_htOne p T k G H q q' e h₁ h₂ hF he
end

