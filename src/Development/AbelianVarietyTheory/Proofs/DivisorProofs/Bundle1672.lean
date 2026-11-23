module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1570
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Formalism.PieriBlockIdeals.Bundle0003
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0472
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
public import Formalism.LocalToGlobal.Columns.AdelicLemmas
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0991
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1646
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaPullbackConstantSqEqDet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0088

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemVertexLatticeOrthonormalCoordsTopNodeIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TopLatSplit

open Formalism.L2.Col.Br

private theorem forall_idx {N n : ℕ} (hN : N = n + 1) (p : Fin N → Prop) :
    (∀ i, p i) ↔ (∀ k, p (iC hN k)) ∧ p (iL hN) := by
  subst hN
  exact Fin.forall_fin_succ'

private theorem frame_mulVec {R : Type} [CommRing R] {N n : ℕ} (hN : N = n + 1) (Fr : Matrix (Fin N) (Fin N) R)
    (Q : Matrix (Fin N) (Fin n) R) (a : Fin N → R) (hC : ∀ i k, Fr i (iC hN k) = Q i k) (hL : ∀ i, Fr i (iL hN) = a i)
    (t : Fin N → R) : Fr *ᵥ t = Q *ᵥ (fun k => t (iC hN k)) + t (iL hN) • a := by
  subst hN
  funext i
  simp only [Matrix.mulVec, dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← hC, ← hL]
  rw [Fin.sum_univ_castSucc, mul_comm (t _)]
  rfl

private theorem block {R : Type} [CommRing R] {N n : ℕ} (hN : N = n + 1) (A Fr : GL (Fin N) R) (B fr : GL (Fin n) R)
    (P : Matrix (Fin N) (Fin n) R) (a : Fin N → R) (hP : A.val * P = P * B.val) (ha : A.val *ᵥ a = a)
    (hC : ∀ i k, Fr.val i (iC hN k) = (P * fr.val) i k) (hL : ∀ i, Fr.val i (iL hN) = a i) (v : Fin N → R) :
    (∀ k, (((Fr⁻¹ * A * Fr)⁻¹).val *ᵥ v) (iC hN k) = (((fr⁻¹ * B * fr)⁻¹).val *ᵥ fun k => v (iC hN k)) k) ∧
      (((Fr⁻¹ * A * Fr)⁻¹).val *ᵥ v) (iL hN) = v (iL hN) := by
  obtain ⟨z, hzC, hzL⟩ : ∃ z : Fin N → R, (∀ k, z (iC hN k) = (((fr⁻¹ * B * fr)⁻¹).val *ᵥ fun k => v (iC hN k)) k) ∧
      z (iL hN) = v (iL hN) := by
    subst hN
    refine ⟨Fin.snoc (α := fun _ => R) (((fr⁻¹ * B * fr)⁻¹).val *ᵥ fun k => v (iC rfl k)) (v (iL rfl)), fun k => ?_, ?_⟩
    · exact Fin.snoc_castSucc (α := fun _ => R) _ _ k
    · exact Fin.snoc_last (α := fun _ => R) _ _
  have e1 : B.val * fr.val * ((fr⁻¹ * B * fr)⁻¹).val = fr.val := by
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    group
  have e2 : A.val *ᵥ (Fr.val *ᵥ z) = Fr.val *ᵥ v := by
    rw [frame_mulVec hN Fr.val _ a hC hL z, frame_mulVec hN Fr.val _ a hC hL v, funext hzC, hzL, Matrix.mulVec_add,
      Matrix.mulVec_smul, ha, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hP, Matrix.mul_assoc P,
      Matrix.mul_assoc P, e1]
  have e3 : ((Fr⁻¹ * A * Fr)⁻¹).val *ᵥ v = z := by
    have e4 : (Fr⁻¹ * A * Fr).val *ᵥ z = v := by
      rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e2, Matrix.mulVec_mulVec,
        Units.inv_mul, Matrix.one_mulVec]
    rw [← e4, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  rw [e3]
  exact ⟨hzC, hzL⟩

private theorem mem_latAt {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    (S : GridChoice W Set.univ) (X : Node) (hX : DefNode D.R.m X) (x : FinPt G X)
    (v : Fin (G.V X).rank → D.host.E) :
    v ∈ GlobalTheory.SumSize.latAt S X x ↔ ∀ i, ((((Formalism.UG.bc (eToEAf D) (S.N.fr X))⁻¹ *
      (Lev.finE (G.V X) x.1 * Lev.finE (G.V X) (S.N.u X).1) * Formalism.UG.bc (eToEAf D) (S.N.fr X))⁻¹).val *ᵥ
        fun i => eToEAf D (v i)) i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  rw [← map_inv]
  exact (GlobalTheory.MovedSD.mem_globLat_move D (G.Λ X) (S.N.fr X) _ _ (S.N.u_lat X hX) v).trans (Formalism.L2.Col.mem_latS_std _)

private theorem finE_val {D : D7} (V : HSp D) (g : Formalism.L2.Theta.GA D V) : (Lev.finE V g).val = (mt V g).map (toEAf D) := by
  ext i j
  rfl

private theorem emb_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {N n : ℕ} (x u : Matrix (Fin N) (Fin N) R)
    (y u' : Matrix (Fin n) (Fin n) R) (P : Matrix (Fin N) (Fin n) R) (hx : x * P = P * y) (hu : u * P = P * u') :
    x.map f * u.map f * P.map f = P.map f * (y.map f * u'.map f) := by
  rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, Matrix.mul_assoc, hu, ← Matrix.mul_assoc, hx,
    Matrix.mul_assoc]

private theorem vec_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {N : ℕ} (x u : Matrix (Fin N) (Fin N) R)
    (a : Fin N → R) (hx : x *ᵥ a = a) (hu : u *ᵥ a = a) :
    (x.map f * u.map f) *ᵥ (fun i => f (a i)) = fun i => f (a i) := by
  funext i
  rw [← Matrix.map_mul]
  refine (RingHom.map_mulVec f (x * u) a i).symm.trans ?_
  rw [← Matrix.mulVec_mulVec, hu, hx]

end GlobalTheory.TopLatSplit

open GlobalTheory.TopLatSplit in
set_option maxHeartbeats 800000 in
theorem _root_.GlobalTheory.T.mem_vertexLatticeOrthonormalCoords_topNode_iff : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} (S : GridChoice W Set.univ)
    (y : FinPt G (.grid D.R.m D.R.m)) (v : Fin (G.V (.top D.R.m)).rank → D.host.E),
    v ∈ GlobalTheory.SumSize.latAt S (.top D.R.m) (finEmb G.sp.topDec y) ↔
      (fun k => v (Formalism.L2.Col.Br.iC G.sp.topDec.rank.symm k)) ∈ GlobalTheory.SumSize.latAt S (.grid D.R.m D.R.m) y ∧
        ∃ c : 𝓞 D.host.E, (c : D.host.E) = v (Formalism.L2.Col.Br.iL G.sp.topDec.rank.symm) := by
  intro D T L sc G W S y v
  have hrel := finEmb_rel G.sp.topDec y
  have hx1 : mt (G.V (.top D.R.m)) (finEmb G.sp.topDec y).1 * topEmb G = topEmb G * mt (G.V (.grid D.R.m D.R.m)) y.1 := hrel.1
  have hx2 : mt (G.V (.top D.R.m)) (finEmb G.sp.topDec y).1 *ᵥ topVec G = topVec G :=
    hrel.2 (fun i => G.sp.topDec.a i 0) (funext fun k => congr_fun (congr_fun G.sp.topDec.perp k) 0)
  have hb := block (R := Lev.EAf D) (N := (G.V (.top D.R.m)).rank) (n := (G.V (.grid D.R.m D.R.m)).rank) G.sp.topDec.rank.symm
    (Lev.finE (G.V (.top D.R.m)) (finEmb G.sp.topDec y).1 * Lev.finE (G.V (.top D.R.m)) (S.N.u (.top D.R.m)).1)
    (Formalism.UG.bc (eToEAf D) (S.N.fr (.top D.R.m)))
    (Lev.finE (G.V (.grid D.R.m D.R.m)) y.1 * Lev.finE (G.V (.grid D.R.m D.R.m)) (S.N.u (.grid D.R.m D.R.m)).1)
    (Formalism.UG.bc (eToEAf D) (S.N.fr (.grid D.R.m D.R.m)))
    ((topEmb G).map (toEAf D)) (fun i => toEAf D (topVec G i))
    (by
      rw [Units.val_mul, Units.val_mul, finE_val, finE_val, finE_val, finE_val]
      exact emb_map (toEAf D) _ _ _ _ _ hx1 S.N.u_top)
    (by
      rw [Units.val_mul, finE_val, finE_val]
      exact vec_map (toEAf D) _ _ _ hx2 S.N.u_last)
    (fun i k => by
      have e := congrArg (eToEAf D) (S.N.fr_top i k)
      exact e.trans (congr_fun (congr_fun (Matrix.map_mul (f := eToEAf D)) i) k))
    (fun i => congrArg (eToEAf D) (S.N.fr_last i))
    (fun i => eToEAf D (v i))
  refine (mem_latAt S (.top D.R.m) (le_refl D.R.m) (finEmb G.sp.topDec y) v).trans ?_
  refine (forall_idx (N := (G.V (.top D.R.m)).rank) (n := (G.V (.grid D.R.m D.R.m)).rank) G.sp.topDec.rank.symm _).trans ?_
  refine and_congr ?_ ?_
  · refine Iff.trans ?_ (mem_latAt S (.grid D.R.m D.R.m) ⟨le_refl _, rfl⟩ y _).symm
    exact forall_congr' fun k => Iff.of_eq (congrArg (· ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hb.1 k))
  · refine (Iff.of_eq (congrArg (· ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) hb.2)).trans ?_
    exact GlobalTheory.NormSum.AdLattice.incl_mem_iff _
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModificationLineBundleGlobalSectionsDimPullEq
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic
open GlobalTheory.ThickeningDetermines (secIdeal)
open scoped TensorProduct
open NumberField Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.HSApp
open GlobalTheory.AllWt (wtOf cuspOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ModifSections

open Opposite

theorem isIntegral_of_iso_comp {A B C E : CommRingCat.{0}} (i : A ⟶ B) (f : B ⟶ C) (m : C ⟶ E) [IsIso i]
    [IsIso m] (h : (i ≫ f ≫ m).hom.IsIntegral) : f.hom.IsIntegral := by
  have e : f = inv i ≫ (i ≫ f ≫ m) ≫ inv m := by simp
  rw [e, CommRingCat.hom_comp, CommRingCat.hom_comp]
  refine RingHom.IsIntegral.trans _ _ ?_ (RingHom.IsIntegral.trans _ _ h ?_)
  · exact RingHom.isIntegral_of_surjective _ (ConcreteCategory.bijective_of_isIso (inv i)).2
  · exact RingHom.isIntegral_of_surjective _ (ConcreteCategory.bijective_of_isIso (inv m)).2

theorem isIntegral_app {Z₁ Z₂ : Scheme.{0}} (ρ : Z₁ ⟶ Z₂) [UniversallyClosed ρ]
    (V : Z₂.Opens) (hV : IsAffineOpen V) : (ρ.app V).hom.IsIntegral := by
  have : IsAffine V.toScheme := hV
  have h := isIntegral_appTop_of_universallyClosed (ρ ∣_ V)
  rw [morphismRestrict_appTop] at h
  have e : V.ι ''ᵁ ⊤ = V := by simp
  rw [ρ.app_eq e, Category.assoc, Category.assoc, ← Functor.map_comp] at h
  simp only [eqToHom_op, eqToHom_map, eqToHom_trans] at h
  have hi : ∀ {A B : CommRingCat.{0}} (q : A = B), IsIso (eqToHom q) := fun q => by
    subst q; rw [eqToHom_refl]; infer_instance
  exact @isIntegral_of_iso_comp _ _ _ _ _ _ _ (hi _) (hi _) h

theorem isNormalScheme_of_smooth {k : Type} [Field k] {Y : Scheme.{0}} (p : Y ⟶ Sp k) [Smooth p] :
    GlobalTheory.IsNormalScheme Y :=
  (GlobalTheory.isNormalScheme_iff Y).2 (GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth p
    ((GlobalTheory.isNormalScheme_iff _).1 inferInstance))

theorem exists_germ_eq {Y : Scheme.{0}} [IsIntegral Y] [GlobalTheory.IsNormalScheme Y] (y : Y) (hy : y = genericPoint Y)
    (V : Y.Opens) (hyV : y ∈ V) (t : Y.presheaf.stalk y)
    (h : ∀ x ∈ V, ∃ (W : Y.Opens) (hW : y ∈ W), x ∈ W ∧ W ≤ V ∧
      (Y.presheaf.germ W y hW).hom.IsIntegralElem t) :
    ∃ a : Γ(Y, V), Y.presheaf.germ V y hyV a = t := by
  subst hy
  have : Nonempty V := ⟨⟨_, hyV⟩⟩
  refine GlobalTheory.IsNormalScheme.exists_germToFunctionField_eq_of_locally V t fun x hx => ?_
  obtain ⟨W, hW, hxW, hWV, hi⟩ := h x hx
  have hne : Nonempty W := ⟨⟨_, hW⟩⟩
  have := GlobalTheory.IsNormalScheme.isIntegrallyClosedIn_functionField (X := Y) W
  obtain ⟨s, hs⟩ := (IsIntegrallyClosedIn.isIntegral_iff (R := Γ(Y, W)) (A := Y.functionField)).1 hi
  exact ⟨W, hne, s, hxW, hWV, hs⟩

theorem isoOver_top {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [GlobalTheory.IsNormalScheme Y]
    (σ : X ⟶ Y) [UniversallyClosed σ] (U : Y.Opens) [IsIso (σ ∣_ U)]
    (hU : ((σ ⁻¹ᵁ U : X.Opens) : Set X).Nonempty) : IsoOver σ ⊤ := by
  intro V _
  have hηU : genericPoint X ∈ σ ⁻¹ᵁ U :=
    ((genericPoint_spec X).mem_open_set_iff (σ ⁻¹ᵁ U).isOpen).2 (by simpa using hU)
  have hmem : ∀ V : Y.Opens, (V : Set Y).Nonempty → σ (genericPoint X) ∈ V := by
    intro V hV
    obtain ⟨y, hyV, hyU⟩ := nonempty_preirreducible_inter V.isOpen U.isOpen hV ⟨_, hηU⟩
    obtain ⟨x, hx⟩ := (σ ∣_ U).surjective ⟨y, hyU⟩
    have hx' : σ x.1 = y := (morphismRestrict_base_coe σ U x).symm.trans (congrArg Subtype.val hx)
    have hne : ((σ ⁻¹ᵁ V : X.Opens) : Set X).Nonempty := ⟨x.1, show σ x.1 ∈ V from hx' ▸ hyV⟩
    exact ((genericPoint_spec X).mem_open_set_iff (σ ⁻¹ᵁ V).isOpen).2 (by simpa using hne)
  have hgen : σ (genericPoint X) = genericPoint Y := by
    have h1 : σ (genericPoint X) ⤳ genericPoint Y :=
      specializes_iff_forall_open.2 fun s hs hg => hmem ⟨s, hs⟩ ⟨_, hg⟩
    exact (h1.antisymm ((genericPoint_spec Y).specializes (Set.mem_univ _))).eq
  have hS : IsIso (σ.stalkMap (genericPoint X)) :=
    ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff (morphismRestrictStalkMap σ U ⟨_, hηU⟩)).1
      (((isIso_iff_isIso_stalkMap (σ ∣_ U)).1 inferInstance).2 ⟨_, hηU⟩)
  have hSb := ConcreteCategory.bijective_of_isIso (σ.stalkMap (genericPoint X))
  by_cases hV : (V : Set Y).Nonempty
  swap
  · exact isoOver_of_isIso σ (O := U) V fun y hy => (hV ⟨y, hy⟩).elim
  have hyV := hmem V hV
  refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨fun a a' e => ?_, fun b => ?_⟩
  · apply germ_injective_of_isIntegral Y (σ (genericPoint X)) hyV
    apply hSb.1
    rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.germ_stalkMap_apply, e]
  obtain ⟨t, ht⟩ := hSb.2 (X.presheaf.germ (σ ⁻¹ᵁ V) (genericPoint X) hyV b)
  obtain ⟨a, ha⟩ := exists_germ_eq (σ (genericPoint X)) hgen V hyV t fun y hy => by
    obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWV⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hy V.isOpen
    have hWV' : W ≤ V := hWV
    have hηW : σ (genericPoint X) ∈ W := hmem W ⟨y, hyW⟩
    refine ⟨W, hηW, hyW, hWV', ?_⟩
    have hi := isIntegral_app σ W hW (X.presheaf.map (homOfLE (σ.preimage_mono hWV')).op b)
    have h2 := RingHom.IsIntegralElem.map hi (X.presheaf.germ (σ ⁻¹ᵁ W) (genericPoint X) hηW).hom
    have e1 : (X.presheaf.germ (σ ⁻¹ᵁ W) (genericPoint X) hηW).hom.comp (σ.app W).hom =
        (σ.stalkMap (genericPoint X)).hom.comp (Y.presheaf.germ W (σ (genericPoint X)) hηW).hom :=
      RingHom.ext fun a => (Scheme.Hom.germ_stalkMap_apply σ W _ hηW a).symm
    have e2 : X.presheaf.germ (σ ⁻¹ᵁ W) (genericPoint X) hηW
        (X.presheaf.map (homOfLE (σ.preimage_mono hWV')).op b) = σ.stalkMap (genericPoint X) t := by
      exact (X.presheaf.germ_res_apply (homOfLE (σ.preimage_mono hWV')) _ hηW b).trans ht.symm
    rw [e1, e2] at h2
    have h3 := RingHom.IsIntegralElem.map h2 (inv (σ.stalkMap (genericPoint X))).hom
    have e3 : (inv (σ.stalkMap (genericPoint X))).hom.comp (σ.stalkMap (genericPoint X)).hom =
        RingHom.id _ := by
      rw [← CommRingCat.hom_comp, IsIso.hom_inv_id]; rfl
    rwa [← RingHom.comp_assoc, e3, RingHom.id_comp, ← RingHom.comp_apply, e3, RingHom.id_apply] at h3
  refine ⟨a, germ_injective_of_isIntegral X (genericPoint X) hyV ?_⟩
  rw [← Scheme.Hom.germ_stalkMap_apply, ha, ht]

theorem modification_lineBundleGlobalSectionsDim_pull_eq : ∀ (k : Type) [Field k] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp k) (U : Y.Opens) (D : ℕ),
    SmoothOfRelativeDimension D p → IsProjOver p → ∀ (M : Modif p U D) [IsIntegral M.X] (B : LB Y), B.IsLB →
    letI := algebraΓOfHom p; letI := algebraΓOfHom M.str; lbH0 k (B.pull M.σ) = lbH0 k B := by
  intro k _ Y _ p U D hs hp M _ B hB
  haveI := hs
  haveI : Smooth p := SmoothOfRelativeDimension.smooth D p
  haveI : GlobalTheory.IsNormalScheme Y := isNormalScheme_of_smooth p
  haveI : IsProper (M.σ ≫ p) := GlobalTheory.CommonModel.isProper_of_isProjOver M.proj
  haveI : IsProper p := GlobalTheory.CommonModel.isProper_of_isProjOver hp
  haveI : IsProper M.σ := IsProper.of_comp M.σ p
  haveI := M.iso
  have hb := (isoOver_top M.σ U M.dense.nonempty).bijective_pull (p := p) hB (W := ⊤) le_top le_top
  letI := algebraΓOfHom p
  letI := algebraΓOfHom M.str
  rw [← H0.finrank_top M.str (B.pull M.σ), ← H0.finrank_top p B]
  exact (LinearEquiv.ofBijective _ hb).finrank_eq.symm

end GlobalTheory.ModifSections
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotSteepOnOfGermZero
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS

namespace GlobalTheory.HSApp

variable {k : Type} [Field k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {B : LB Y}

def Centred (y : Y) (ν : Valuation (Y.presheaf.stalk y) (WithZero (Multiplicative ℤ))) : Prop :=
  (∀ a, ν a ≤ 1) ∧ (∀ a ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y), ν a < 1) ∧ ∀ a, ν a = 0 → a = 0

end GlobalTheory.HSApp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OddEisensteinRatioAlgebraicUnit
section
open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

namespace GlobalTheory.VacUnit

open Formalism.MainNotions.TaylorLogMetric (hYY LocBasis YYl)
open Formalism.MainNotions.StandardLatticesGL3 (OnB LaB pullB KLat)

theorem mem_Qbar_of_pow {x : ℂ} {n : ℕ} (hn : 0 < n) (h : x ^ n ∈ Qbar) : x ∈ Qbar := by
  rw [mem_algebraicClosure_iff] at h ⊢
  exact h.of_pow hn

theorem norm_int_le {K : Type} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime] (f : K →+* ℂ_[p]) (c : 𝓞 K) :
    ‖f (c : K)‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.RingOfIntegersNormBound.norm_map_ringOfIntegers_le_one
  | exact _root_.GlobalTheory.RingOfIntegersNormBound.norm_map_ringOfIntegers_le_one
  | (apply _root_.GlobalTheory.RingOfIntegersNormBound.norm_map_ringOfIntegers_le_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.RingOfIntegersNormBound.norm_map_ringOfIntegers_le_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RingOfIntegersNormBound.norm_map_ringOfIntegers_le_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RingOfIntegersNormBound.norm_map_ringOfIntegers_le_one ..)

theorem norm_nat_coprime {p : ℕ} [Fact p.Prime] {s : ℕ} (h : Nat.Coprime s p) : ‖(s : ℂ_[p])‖ = 1 := by
  have h1 : (s : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (s : ℚ_[p]) := by simp
  rw [h1, norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact h.symm

theorem norm_det_le {p : ℕ} [Fact p.Prime] {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ_[p]) (h : ∀ i j, ‖M i j‖ ≤ 1) :
    ‖M.det‖ ≤ 1 := by
  rw [Matrix.det_apply']
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  rw [norm_mul, norm_prod]
  refine mul_le_one₀ (IsUltrametricDist.norm_intCast_le_one ℂ_[p] _) (Finset.prod_nonneg fun _ _ => norm_nonneg _) ?_
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => h _ _

variable {D : D7} {N N' r : ℕ}

theorem hYY_comb (c : Fin r → D.host.K) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (y : Matrix (Fin N') (Fin N) D.host.E) : hYY D (∑ k, c k • b k) y = ∑ k, c k * hYY D (b k) y := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hYY, ← smul_eq_mul, ← map_smul, ← map_sum]
  congr 1
  simp only [Matrix.sum_apply, Matrix.smul_apply, Finset.smul_sum, smul_eq_mul, Finset.sum_mul, smul_mul_assoc]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]

theorem exists_coord {p : ℕ} [Fact p.Prime] (f : D.host.K →+* ℂ_[p])
    {Y : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E)}
    {b b' : Fin r → Matrix (Fin N') (Fin N) D.host.E} (hl : LocBasis D p Y b) (hl' : LocBasis D p Y b') (j : Fin r) :
    ∃ a : Fin r → D.host.K, (∀ i, ‖f (a i)‖ ≤ 1) ∧ b' j = ∑ i, a i • b i := by
  obtain ⟨s, hs, hY⟩ := hl'.2.1 j
  obtain ⟨t, ht, c, hc⟩ := hl.2.2 _ hY
  have hst : Nat.Coprime (t * s) p := Nat.Coprime.mul_left ht hs
  have h0 : ((t * s : ℕ) : D.host.K) ≠ 0 := by
    intro h
    have h1 := norm_nat_coprime hst
    rw [← map_natCast f, h] at h1
    simp at h1
  refine ⟨fun i => ((t * s : ℕ) : D.host.K)⁻¹ * (c i : D.host.K), fun i => ?_, ?_⟩
  · rw [map_mul, map_inv₀, map_natCast, norm_mul, norm_inv, norm_nat_coprime hst, inv_one, one_mul]
    exact norm_int_le f _
  · have h2 : ((t * s : ℕ) : D.host.K) • b' j = ∑ i, (c i : D.host.K) • b i := by
      rw [smul_smul, ← Nat.cast_mul, Nat.cast_smul_eq_nsmul] at hc
      rw [Nat.cast_smul_eq_nsmul, hc]
      rfl
    simp only [mul_smul]
    rw [← Finset.smul_sum, ← h2, smul_smul, inv_mul_cancel₀ h0, one_smul]

theorem norm_det_eq_one {p : ℕ} [Fact p.Prime] (f : D.host.K →+* ℂ_[p])
    {Y : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E)}
    {b b' : Fin r → Matrix (Fin N') (Fin N) D.host.E} (hb : OnB D b)
    (hl : LocBasis D p Y b) (hl' : LocBasis D p Y b') :
    ‖f (Matrix.of fun i j => hYY D (b' j) (b i)).det‖ = 1 := by
  choose a ha hab using exists_coord f hl hl'
  choose a' ha' hab' using exists_coord f hl' hl
  have hM : ∀ i j, hYY D (b' j) (b i) = a j i := by
    intro i j
    rw [hab j, hYY_comb]
    simp [hb.1 _ i]
  have hMM : (Matrix.of fun i j => hYY D (b' j) (b i)) * (Matrix.of fun j k => a' k j) = 1 := by
    ext i k
    have h1 := hb.1 k i
    conv_lhs at h1 => rw [hab' k, hYY_comb]
    rw [Matrix.mul_apply, Matrix.one_apply, if_congr (eq_comm (a := i)) rfl rfl, ← h1]
    simp [mul_comm]
  have hd := congrArg (fun A => ‖f (Matrix.det A)‖) hMM
  simp only [Matrix.det_mul, map_mul, norm_mul, Matrix.det_one, map_one, norm_one] at hd
  have h1 : ‖f (Matrix.of fun i j => hYY D (b' j) (b i)).det‖ ≤ 1 := by
    rw [RingHom.map_det]
    exact norm_det_le _ fun i j => by simpa [hM] using ha j i
  have h2 : ‖f (Matrix.of fun j k => a' k j).det‖ ≤ 1 := by
    rw [RingHom.map_det]
    exact norm_det_le _ fun i j => by simpa using ha' j i
  refine le_antisymm h1 ?_
  rw [← hd]
  exact mul_le_of_le_one_right (norm_nonneg _) h2

noncomputable def phiK (D : D7) : D.host.K →+* Qbar :=
  (D.host.φ₀.comp (algebraMap D.host.K D.host.E)).codRestrict Qbar.toSubring fun x => by
    change _ ∈ Qbar
    rw [mem_algebraicClosure_iff]
    exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom
      (D.host.φ₀.comp (algebraMap D.host.K D.host.E)).toRatAlgHom

theorem at_place (hI : GlobalTheory.NormSum.Inp D) {δ t0 : ℂ} (hC : Crv D ⊤ δ) (ht : Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0)
    {e₁ e₂ : VC D N N' → ℂ} (h₁ : oddE0 D ⊤ δ t0 N N' e₁) (h₂ : oddE0 D ⊤ δ t0 N N' e₂) (hne : e₁ ≠ 0) {κ : ℂ}
    (hκ : e₂ = κ • e₁) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) : κ ∈ Qbar ∧ ‖lamC lam κ‖ = 1 := by
  have hSD : ∀ n, Formalism.MainNotions.StandardLatticesGL3.SD D (stdL D n) := fun n => by
    obtain ⟨Lt, h1, h2, -⟩ := GlobalTheory.NormSum.exists_lattice_of_adelic_point D n
    exact h2 ▸ (h1 1).2
  obtain ⟨b, ε, hb, hl, hε, hεn, -, he⟩ := h₁.2.2.2.2 p lam (by simp)
  obtain ⟨b', ε', hb', hl', hε', hεn', -, he'⟩ := h₂.2.2.2.2 p lam (by simp)
  obtain ⟨c, ζ, m, hm, hζ, hc, hpull⟩ := GlobalTheory.UnitaryTheta.const_sq_eq_det D ⊤ δ hC t0 ht N N' _ b b' hb hb'
  obtain ⟨μ, hμ, hI3⟩ := hI.mu ⊤ δ hC N N' _ _ (La0 D (tor0 D ⊤ δ) N N') (Or.inl ⟨_, b, hb, rfl⟩)
    (Or.inl ⟨_, b', hb', rfl⟩) (Or.inr ⟨_, _, hSD N, hSD N', rfl⟩) _
    (GlobalTheory.UnitaryTheta.pullB_mem D ⊤ δ hC t0 ht N N' _ b hb).1
  obtain ⟨z, hz⟩ := Function.ne_iff.1 hne
  have e2 := congrFun hκ z
  rw [he', hpull, Pi.smul_apply, smul_eq_mul] at e2
  rw [he] at e2 hz
  simp only [GlobalTheory.UnitaryTheta.iop_smul, hI3] at e2
  have hz' := right_ne_zero_of_mul hz
  have key : κ * ε = ε' * c * μ := by
    apply mul_right_cancel₀ hz'
    linear_combination -e2
  have hζQ : ζ ∈ Qbar := mem_Qbar_of_pow hm (hζ ▸ one_mem _)
  have hμQ : μ ∈ Qbar := mem_Qbar_of_pow (n := 8) (by norm_num) (hμ ▸ one_mem _)
  set u := phiK D (Matrix.of fun i j => hYY D (b' j) (b i)).det with hu
  have hun : ‖lam u‖ = 1 := norm_det_eq_one (lam.comp (phiK D)) hb hl hl'
  change c ^ 2 = ζ * (u : ℂ) at hc
  have hcQ : c ∈ Qbar := mem_Qbar_of_pow (n := 2) (by norm_num) (hc ▸ mul_mem hζQ u.2)
  rw [lamC, dite_eq_left hε] at hεn
  rw [lamC, dite_eq_left hε'] at hεn'
  have hε0 : ε ≠ 0 := left_ne_zero_of_mul hz
  have hκQ : κ ∈ Qbar := by
    rw [eq_div_of_mul_eq hε0 key]
    exact div_mem (mul_mem (mul_mem hε' hcQ) hμQ) hε
  refine ⟨hκQ, ?_⟩
  rw [lamC, dite_eq_left hκQ]
  have root : ∀ (x : Qbar) (n : ℕ), 0 < n → (x : ℂ) ^ n = 1 → ‖lam x‖ = 1 := by
    intro x n hn hx
    have : x ^ n = 1 := Subtype.ext (by simpa using hx)
    have h := congrArg (fun y => ‖lam y‖) this
    simp only [map_pow, norm_pow, map_one, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h
  have hcn : ‖lam ⟨c, hcQ⟩‖ = 1 := by
    have : (⟨c, hcQ⟩ : Qbar) ^ 2 = ⟨ζ, hζQ⟩ * u := Subtype.ext (by simpa using hc)
    have h := congrArg (fun y => ‖lam y‖) this
    simp only [map_pow, norm_pow, map_mul, norm_mul, hun, root ⟨ζ, hζQ⟩ m hm hζ, mul_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h
  have : (⟨κ, hκQ⟩ : Qbar) * ⟨ε, hε⟩ = ⟨ε', hε'⟩ * ⟨c, hcQ⟩ * ⟨μ, hμQ⟩ := Subtype.ext key
  have h := congrArg (fun y => ‖lam y‖) this
  simpa only [map_mul, norm_mul, hεn, hεn', hcn, root ⟨μ, hμQ⟩ 8 (by norm_num) hμ, mul_one] using h

theorem vac_unit : ∀ {D : D7}, GlobalTheory.NormSum.Inp D → ∀ {δ t0 : ℂ}, Crv D ⊤ δ → Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 → ∀ {N N' : ℕ} {e₁ e₂ : VC D N N' → ℂ},
  oddE0 D ⊤ δ t0 N N' e₁ → oddE0 D ⊤ δ t0 N N' e₂ → e₁ ≠ 0 → ∀ κ : ℂ, e₂ = κ • e₁ →
  κ ∈ Qbar ∧ ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), ‖lamC lam κ‖ = 1 := by
  intro D hI δ t0 hC ht N N' e₁ e₂ h₁ h₂ hne κ hκ
  refine ⟨?_, fun p _ lam => (at_place hI hC ht h₁ h₂ hne hκ p lam).2⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Algebra.IsAlgebraic ℚ Qbar := algebraicClosure.isAlgebraic ℚ ℂ
  exact (at_place hI hC ht h₁ h₂ hne hκ 2 (IsAlgClosed.lift (R := ℚ) (S := Qbar) (M := ℂ_[2])).toRingHom).1

end GlobalTheory.VacUnit
end

