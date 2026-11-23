module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2403
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2361
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0743
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2385
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharactersRestrictLinearToTraitUniformisation
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0486
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2353
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2219
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0584
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2207
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0056
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0586
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2396
public import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2371
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0488
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilVacuumScalarEqOneInertPlace
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubringEqTopOfWeightUnits
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum


set_option maxHeartbeats 1000000 in
theorem subring_eq_top_of_weight_units : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (Y : Ext D) (i : splitTorus (Sp R) D.X ⟶ Y.H), IsMonHom i → IsPullback i (toUnit _) Y.q η[D.P.A] → ∀ {κ : Type} (bs : Module.Basis κ ℤ D.X) (V : D.P.A.left.Opens), IsAffineOpen V → ∀ (u : κ → Γ(Y.H.left, Y.q.left ⁻¹ᵁ V)ˣ), (∀ c, GlobalTheory.UU.IsWt i _ (u c).val (bs c)) → ∀ S : Subring Γ(Y.H.left, Y.q.left ⁻¹ᵁ V), (∀ c, (Y.q.left.app V).hom c ∈ S) → (∀ c, (u c).val ∈ S ∧ ((u c)⁻¹).val ∈ S) → S = ⊤ := by
  intro R _ _ D Y i hi hk κ bs V hV u hu S hS hSu
  obtain ⟨hsm, haff, hsurj⟩ := Y.q_props
  have hmon : IsMonHom Y.q := Y.isMonHom_q
  let m : Multiplicative D.X →* Γ(Y.H.left, Y.q.left ⁻¹ᵁ V)ˣ :=
    AddMonoidHom.toMultiplicativeLeft (bs.constr ℤ (fun k => Additive.ofMul (u k))).toAddMonoidHom
  have hm : ∀ k, m (Multiplicative.ofAdd (bs k)) = u k := fun k =>
    congrArg Additive.toMul (bs.constr_basis ℤ (fun k => Additive.ofMul (u k)) k)
  have key : ∀ χ : D.X, GlobalTheory.UU.IsWt i _ (m (Multiplicative.ofAdd χ)).val χ ∧
      (m (Multiplicative.ofAdd χ)).val ∈ S ∧ (m (Multiplicative.ofAdd χ))⁻¹.val ∈ S := by
    intro χ
    have hχ : χ ∈ AddSubgroup.closure (Set.range bs) := by
      rw [← Submodule.span_int_eq_addSubgroupClosure, bs.span_eq]; trivial
    refine AddSubgroup.closure_induction (p := fun x _ => GlobalTheory.UU.IsWt i _ (m (Multiplicative.ofAdd x)).val x ∧
      (m (Multiplicative.ofAdd x)).val ∈ S ∧ (m (Multiplicative.ofAdd x))⁻¹.val ∈ S) ?_ ?_ ?_ ?_ hχ
    · rintro _ ⟨k, rfl⟩
      rw [hm]; exact ⟨hu k, hSu k⟩
    · rw [ofAdd_zero, map_one]; exact ⟨GlobalTheory.UU.isWt_one, S.one_mem, by simpa using S.one_mem⟩
    · intro x y _ _ hx hy
      rw [ofAdd_add, map_mul]
      refine ⟨hx.1.mul hy.1, ?_, ?_⟩
      · rw [Units.val_mul]; exact S.mul_mem hx.2.1 hy.2.1
      · rw [mul_inv, Units.val_mul]; exact S.mul_mem hx.2.2 hy.2.2
    · intro x _ hx
      rw [ofAdd_neg, map_inv]
      exact ⟨hx.1.inv, hx.2.2, by rw [inv_inv]; exact hx.2.1⟩
  have hbij := (isAffineOpen_and_bijective_of_weight_units (Sp R) D.X Y.H D.P.A Y.q i hmon hi inferInstance
    hsurj inferInstance hk V hV m (fun χ => (key χ).1)).2
  refine (Subring.eq_top_iff' S).2 fun f => ?_
  obtain ⟨x, rfl⟩ := hbij.2 f
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => rw [map_zero]; exact S.zero_mem
  | add a b ha hb => rw [map_add (f := _)]; exact S.add_mem ha hb
  | single χ c =>
    change AddMonoidAlgebra.liftNC _ _ _ ∈ S
    rw [AddMonoidAlgebra.liftNC_single]
    exact S.mul_mem (hS c) (key χ).2.1

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumMulPulledBackFunctionsGenericFibreEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_app_eq_sum_mul_of_comm : ∀ {X Y S S' T X' : Scheme.{0}} (g : X ⟶ S) (h : S' ⟶ S) (gp : T ⟶ S) (gp' : T ⟶ S') (hgp : gp' ≫ h = gp) (fst : X' ⟶ X) (snd : X' ⟶ S'), fst ≫ g = snd ≫ h → ∀ (α : Y ⟶ X) (t : Y ⟶ T) (hpb : α ≫ g = t ≫ gp) (l : Y ⟶ X') (h1 : l ≫ fst = α), l ≫ snd = t ≫ gp' → ∀ (W : X.Opens) (U : S.Opens) (hWU : W ≤ g ⁻¹ᵁ U) (n : ℕ) (c : Fin n → Γ(X, W)) (b : Fin n → Γ(T, gp ⁻¹ᵁ U)) (b' : Fin n → Γ(S', h ⁻¹ᵁ U)), (∀ m, (gp'.appLE (h ⁻¹ᵁ U) (gp ⁻¹ᵁ U) (le_preimage_of_comp_eq gp gp' h hgp U)).hom (b' m) = b m) → ∃ y : Γ(X', fst ⁻¹ᵁ W), (l.app (fst ⁻¹ᵁ W)).hom y = (Y.presheaf.map (homOfLE (extLI_preimage_le l fst α h1 W)).op).hom (∑ m, (α.app W).hom (c m) * (t.appLE (gp ⁻¹ᵁ U) (α ⁻¹ᵁ W) (locInt_le_gen g α t gp hpb W U hWU)).hom (b m)) := by
  intro X Y S S' T X' g h gp gp' hgp fst snd hsq α t hpb l h1 h2 W U hWU n c b b' hb
  subst h1
  have le : fst ⁻¹ᵁ W ≤ snd ⁻¹ᵁ (h ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, ← hsq, Scheme.Hom.comp_preimage]
    exact fun x hx => hWU hx
  refine ⟨∑ m, (fst.app W).hom (c m) * (snd.appLE (h ⁻¹ᵁ U) (fst ⁻¹ᵁ W) le).hom (b' m), ?_⟩
  have hid : ∀ z : Γ(Y, (l ≫ fst) ⁻¹ᵁ W), (Y.presheaf.map (homOfLE (extLI_preimage_le l fst (l ≫ fst) rfl W)).op).hom z = z := by
    intro z
    have : (homOfLE (extLI_preimage_le l fst (l ≫ fst) rfl W)).op = 𝟙 (Opposite.op ((l ≫ fst) ⁻¹ᵁ W)) := rfl
    erw [this, Y.presheaf.map_id]
    rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hid, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul]
  congr 1
  rw [← hb m]
  have key : ∀ (f₁ f₂ : Y ⟶ S') (e : f₁ = f₂) (V : Y.Opens) (e₁ e₂), f₁.appLE (h ⁻¹ᵁ U) V e₁ = f₂.appLE (h ⁻¹ᵁ U) V e₂ := by
    intro f₁ f₂ e V e₁ e₂; subst e; rfl
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
  exact congrArg (fun φ => CommRingCat.Hom.hom φ (b' m)) (key _ _ h2 _ _ _)

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveLabelHomLatticeModLevelThetaMember
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep.Labels

theorem comp_pow_overScheme_grpObj {S : Scheme.{0}} {A T T' : Over S} [GrpObj A] (ρ : T' ⟶ T) (x : T ⟶ A) (n : ℕ) :
    ρ ≫ x ^ n = (ρ ≫ x) ^ n := by
  induction n with
  | zero => simp only [pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, MonObj.comp_mul, ih, pow_succ]


open GlobalTheory.TorusExt in
attribute [local instance] gtGroup in
theorem yy_hom : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), (∀ a, ∃ mu, 𝔪.YY a mu) ∧ (∀ mu, ∃ a, 𝔪.YY a mu) ∧ (∀ a mu mu', 𝔪.YY a mu → (𝔪.YY a mu' ↔ ∀ v, CongMod (X₁.S.r * X₁.S.N) (mu' v) (mu v))) ∧ (∀ a a' mu mu', 𝔪.YY a mu → 𝔪.YY a' mu' → 𝔪.YY (a + a') (mu + mu')) := by
  intro g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hB := 𝔪.D.tau_bimult
  have hk : 1 ≤ X₁.S.r * X₁.S.N := by
    have := X₁.S.r_pos; have := X₁.S.N_ge
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  obtain ⟨x, hx, xadd, -, xonto⟩ := GlobalTheory.ThetaDvr.torsion_points 𝔪.yK 𝔪.cart
  obtain ⟨rig, e, -, he, -⟩ := GlobalTheory.ThetaDvr.frames 𝔪.yK 𝔪.cart ⟨𝔪.wl, 𝔪.wl_gen⟩ x hx
  obtain ⟨f, f₁, f₂, f₃, f₄, -⟩ := GlobalTheory.TorsionIso.torsion_eq hL V (maximalIdeal V) hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U
    (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) hk
  have tor : ∀ p y, QkToAkU 𝔪.U.toUnifPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) p y →
      y ^ (X₁.S.r * X₁.S.N) = 1 := fun p y h => by
    obtain ⟨w, hw⟩ := 𝔪.U.ext
    exact (h w hw).1
  have uniq : ∀ a (y : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ 𝔪.A.A), y ^ (X₁.S.r * X₁.S.N) = 1 →
      y.left ≫ 𝔪.φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) ≫
        (X₁.ρ.pt a).left → y = x a := by
    intro a y hy hya
    obtain ⟨b, rfl⟩ := xonto y hy
    obtain ⟨c, -, hc⟩ := X₁.ρ.pt_bij (AlgebraicClosure (FractionRing V))
      (spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK))
      ((Over.homMk (spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK)) (by simp) :
        Over.mk (spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK)) ⟶
          baseOver (Sp X₁.S.R)) ≫ X₁.ρ.pt a)
      (by rw [← comp_pow_overScheme_grpObj, (X₁.ρ.fr_tors a).1, MonObj.comp_one])
    have h1 := hc a rfl
    have h2 := hc b (by
      ext1
      simp only [Over.comp_left, Over.homMk_left]
      rw [← hx b, hya])
    rw [h1.trans h2.symm]
  have ex : ∀ a, ∃ p, QkToAkU 𝔪.U.toUnifPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) p (x a) :=
    fun a => by
      obtain ⟨p, hp⟩ := f₂ (x a) (he a).1
      exact ⟨p, (f₁ _ _).2 hp.symm⟩
  have yyI : ∀ a mu, 𝔪.YY a mu ↔ ∃ p : QkPt 𝔪.D.toPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N),
      p.y = 𝔪.e₈ mu ∧ QkToAkU 𝔪.U.toUnifPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) p (x a) := by
    intro a mu
    constructor
    · rintro ⟨p, y, hpy, hq, hov⟩
      obtain rfl := uniq a y (tor p y hq) hov
      exact ⟨p, hpy, hq⟩
    · rintro ⟨p, hpy, hq⟩
      exact ⟨p, x a, hpy, hq, hx a⟩
  refine ⟨fun a => ?_, fun mu => ?_, fun a mu mu' h => ?_, fun a a' mu mu' h h' => ?_⟩
  · obtain ⟨p, hp⟩ := ex a
    exact ⟨𝔪.e₈.symm p.y, (yyI a _).2 ⟨p, by simp, hp⟩⟩
  · obtain ⟨p, hp⟩ := exists_qkPt (F := AlgebraicClosure (FractionRing V)) hL.1.mulN (Or.inr hL.1.polBaseChange) hB
      (n := X₁.S.r * X₁.S.N) (by omega) (𝔪.e₈ mu)
    obtain ⟨a, ha⟩ := xonto (f p) (tor p _ ((f₁ _ _).2 rfl))
    exact ⟨a, (yyI a mu).2 ⟨p, hp, (f₁ _ _).2 ha.symm⟩⟩
  · obtain ⟨p, hpy, hq⟩ := (yyI a mu).1 h
    rw [yyI]
    constructor
    · rintro ⟨p', hpy', hq'⟩
      have hpp : QkPt.Equiv _ _ p p' := (f₃ p p').1 (((f₁ _ _).1 hq).symm.trans ((f₁ _ _).1 hq'))
      obtain ⟨z, hz, -⟩ := (equiv_iff hB _ _).1 hpp
      have e' : mu' = mu + (X₁.S.r * X₁.S.N) • 𝔪.e₈.symm z := 𝔪.e₈.injective (by
        rw [map_add (f := _), map_nsmul, AddEquiv.apply_symm_apply, ← hpy, ← hpy', hz])
      intro v
      exact ⟨𝔪.e₈.symm z v, by rw [e']; rfl⟩
    · intro hc
      choose w hw using hc
      refine ⟨qkShift hB p (𝔪.e₈ w), ?_, (f₁ _ _).2 (((f₁ _ _).1 hq).trans ((f₃ _ _).2 (equiv_qkShift hB p _)))⟩
      show p.y + (X₁.S.r * X₁.S.N) • 𝔪.e₈ w = 𝔪.e₈ mu'
      rw [hpy, ← map_nsmul, ← map_add (f := _)]
      congr 1
      funext v
      exact (hw v).symm
  · obtain ⟨p, hpy, hq⟩ := (yyI a mu).1 h
    obtain ⟨p', hpy', hq'⟩ := (yyI a' mu').1 h'
    refine (yyI _ _).2 ⟨qkAdd hB p p', ?_, ?_⟩
    · show p.y + p'.y = 𝔪.e₈ (mu + mu')
      rw [map_add (f := _), hpy, hpy']
    · rw [f₁, f₄ _ _ _ (qkAdd_qkAdd hB p p'), ← (f₁ _ _).1 hq, ← (f₁ _ _).1 hq', xadd]

end GlobalTheory.Poinc.Sep.Labels
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOpenContainingClosedFibreSmoothSquare
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.NearSurj

theorem surjective_of_open_closedFibre : ∀ {R : Type} [CommRing R] [IsLocalRing R] (U : Over (Sp R)), Smooth U.hom → Surjective U.hom → ∀ (V : (U ⊗ U).left.Opens), (∀ z : (U ⊗ U).left, (U ⊗ U).hom z = closedPoint R → z ∈ V) → Surjective (V.ι ≫ (U ⊗ U).hom) := by
  intro R _ _ U hs hsu V hV
  have : Smooth (U ⊗ U).hom := inferInstanceAs (Smooth (pullback.fst U.hom U.hom ≫ U.hom))
  obtain ⟨u, hu⟩ := U.hom.surjective (closedPoint R)
  let d : U.left ⟶ (U ⊗ U).left := pullback.lift (𝟙 _) (𝟙 _) rfl
  have hd : (U ⊗ U).hom (d u) = closedPoint R := by
    rw [← hu, ← Scheme.Hom.comp_apply]
    change (pullback.lift (𝟙 U.left) (𝟙 U.left) rfl ≫ pullback.fst U.hom U.hom ≫ U.hom) u = _
    rw [pullback.lift_fst_assoc, Category.id_comp]
  have hmem : d u ∈ V := hV _ hd
  have ho : IsOpenMap (V.ι ≫ (U ⊗ U).hom) := (V.ι ≫ (U ⊗ U).hom).isOpenMap
  refine ⟨fun r => ?_⟩
  obtain ⟨y, hy⟩ : d u ∈ Set.range V.ι := by rw [Scheme.Opens.range_ι]; exact hmem
  have h₂ : (V.ι ≫ (U ⊗ U).hom) y = closedPoint R := by
    rw [Scheme.Hom.comp_apply, hy]; exact hd
  exact (IsLocalRing.specializes_closedPoint r).mem_open ho.isOpen_range ⟨_, h₂⟩

end GlobalTheory.Mum.NearSurj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TauCoordMulSq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open MonObj
open Classical

noncomputable section

namespace GlobalTheory.PsiFromTauEven

open GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues

theorem tauCoord_mul_sq (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] (D : DegPre A) (hB : D.TauBimult)
    (hE : D.PsiEven) (y : D.X) (r : A) (hr : PsiCoord D y r) (x : (FractionRing A)ˣ) (hx : IsTauCoord D y (-y) x) :
    ∃ w : Aˣ, (x : FractionRing A) * algebraMap A (FractionRing A) r ^ 2 = algebraMap A (FractionRing A) w := by
  obtain ⟨x₀, hx₀, e₀⟩ := (GlobalTheory.PeriodFormCompare.psiCoord_iff D y r).1 hr
  have h0 : IsPsiCoord D (y + -y) (psiCoord D 0) := by rw [add_neg_cancel]; exact psiCoord_spec D 0
  obtain ⟨u₂, hu₂⟩ := _root_.GlobalTheory.TauCoordQuot.main A D y (-y) x _ _ _ hx h0 hx₀ (psiCoord_spec D (-y))
  obtain ⟨u₃, hu₃⟩ := _root_.GlobalTheory.PsiEvenCoordUnit.main A D hE y _ _ hx₀ (psiCoord_spec D (-y))
  obtain ⟨u₄, hu₄⟩ := GlobalTheory.MonoTriv.psiCoord_zero D hB _ (psiCoord_spec D 0)
  refine ⟨u₂ * u₄ * u₃⁻¹, ?_⟩
  have hne : (x₀ : FractionRing A) ≠ 0 := x₀.ne_zero
  have h3 : algebraMap A (FractionRing A) (u₃ : A) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).2 u₃.ne_zero
  rw [hu₂, hu₃, hu₄, ← e₀]
  simp only [Units.val_mul, map_mul, map_units_inv]
  field_simp

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsDiscreteValuationRing V → ∀ (g : R →+* V) (gK : FractionRing R →+* FractionRing V), (∀ r, gK (algebraMap R _ r) = algebraMap V _ (g r)) →
  ∀ (D : DegPre R) (D' : DegPre V), D.TauBimult → D.PsiEven → D'.TauBimult → D'.PsiEven → ∀ ρ : D.X →+ D'.X,
    (∀ (a b : D.X) (x : (FractionRing R)ˣ) (x' : (FractionRing V)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D a b x → GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord D' (ρ a) (ρ b) x' →
      ∃ u : Vˣ, gK (x : FractionRing R) = algebraMap V (FractionRing V) (u : V) * (x' : FractionRing V)) →
    ∀ (y : D.X) (r : R) (r' : V), PsiCoord D y r → PsiCoord D' (ρ y) r' → Associated (g r) r' := by
  intro R _ _ _ V _ _ _ hV g gK hgK D D' hB hE hB' hE' ρ hρ y r r' hr hr'
  obtain ⟨x, hx⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D y (-y)
  obtain ⟨x', hx'⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord V D' (ρ y) (-(ρ y))
  obtain ⟨w, hw⟩ := tauCoord_mul_sq R D hB hE y r hr x hx
  obtain ⟨w', hw'⟩ := tauCoord_mul_sq V D' hB' hE' (ρ y) r' hr' x' hx'
  have hx'' : IsTauCoord D' (ρ y) (ρ (-y)) x' := by rwa [map_neg]
  obtain ⟨u, hu⟩ := hρ y (-y) x x' hx hx''
  have e := congrArg gK hw
  rw [map_mul, map_pow, hgK, hgK, hu] at e
  let v : Vˣ := u * w' * (Units.map g.toMonoidHom w)⁻¹
  have key : (g r) ^ 2 * (v : V) = r' ^ 2 := by
    have k1 : ((u : V) * w') * (g r) ^ 2 = g w * r' ^ 2 := by
      apply IsFractionRing.injective V (FractionRing V)
      simp only [map_mul, map_pow]
      rw [← hw', ← e]; ring
    have hw1 : (g w : V) * ((Units.map g.toMonoidHom w)⁻¹ : Vˣ) = 1 := by
      have h : ((Units.map g.toMonoidHom w : Vˣ) : V) = g w := rfl
      rw [← h, Units.mul_inv]
    simp only [v, Units.val_mul]
    calc g r ^ 2 * (↑u * ↑w' * ↑(Units.map g.toMonoidHom w)⁻¹)
        = (↑u * ↑w') * g r ^ 2 * ↑(Units.map g.toMonoidHom w)⁻¹ := by ring
      _ = r' ^ 2 * ((g w : V) * ((Units.map g.toMonoidHom w)⁻¹ : Vˣ)) := by rw [k1]; ring
      _ = r' ^ 2 := by rw [hw1, _root_.mul_one]
  have hsq : Associated ((g r) ^ 2) (r' ^ 2) := ⟨v, key⟩
  haveI : IsIntegrallyClosed V := inferInstance
  exact associated_of_dvd_dvd ((IsIntegrallyClosed.pow_dvd_pow_iff two_ne_zero).1 hsq.dvd)
    ((IsIntegrallyClosed.pow_dvd_pow_iff two_ne_zero).1 hsq.symm.dvd)

end GlobalTheory.PsiFromTauEven
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataTauBimultiplicative
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

open ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.TensBimult

theorem alg {U X X' : Type} [CommGroup U] [AddCommGroup X] [AddCommGroup X'] {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (e : X' ≃+ (Fin r → X)) (Ψ : X → U) (ρ : U) (O ψ' : X' → U) (τ' : X' → X' → U) (t : X → X → U) (c' rig' : U)
    (a a' b : X') (ht : ∀ u v, t u v = Ψ (u + v) * (Ψ u)⁻¹ * (Ψ v)⁻¹ * ρ⁻¹)
    (hψ : ∀ u, ψ' u = O u * ∏ i, ∏ j, t (e u i) (e u j) ^ W i j)
    (hτ : ∀ u v, τ' u v = ψ' (u + v) * (ψ' u)⁻¹ * (ψ' v)⁻¹ * rig'⁻¹) (hr : ψ' 0 * rig' = 1)
    (hc : c' * (O (a + a' + b) * (O (a + a'))⁻¹ * (O (a + b))⁻¹ * (O (a' + b))⁻¹ * O a * O a' * O b * (O 0)⁻¹) =
      ∏ k : (Fin r × Fin r) × Fin 4,
        (t (![e a k.1.1 + e a k.1.2, e a k.1.1, e a k.1.2, 0] k.2) (![e b k.1.1 + e b k.1.2, e b k.1.1, e b k.1.2, 0] k.2) *
          t (![e a' k.1.1 + e a' k.1.2, e a' k.1.1, e a' k.1.2, 0] k.2) (![e b k.1.1 + e b k.1.2, e b k.1.1, e b k.1.2, 0] k.2) *
          (t (![e a k.1.1 + e a k.1.2, e a k.1.1, e a k.1.2, 0] k.2 + ![e a' k.1.1 + e a' k.1.2, e a' k.1.1, e a' k.1.2, 0] k.2)
            (![e b k.1.1 + e b k.1.2, e b k.1.1, e b k.1.2, 0] k.2))⁻¹) ^ tensε W k) :
    τ' (a + a') b * c' = τ' a b * τ' a' b := by
  have hr' : rig'⁻¹ = ψ' 0 := (eq_inv_of_mul_eq_one_right hr).symm ▸ inv_inv _
  rw [eq_mul_inv_of_mul_eq hc, hτ, hτ, hτ, hr']
  simp only [hψ, ht, Fintype.prod_prod_type, Fin.prod_univ_four, tensε, Oε, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, map_add, Pi.add_apply, map_zero, Pi.zero_apply,
    add_zero, zero_add]
  have e1 : ∀ x x1, Ψ (e a x + e a x1 + (e a' x + e a' x1) + (e b x + e b x1)) = Ψ (e a x + e a' x + e b x + (e a x1 + e a' x1 + e b x1)) := fun x x1 => congrArg Ψ (by abel)
  have e2 : ∀ x x1, Ψ (e a x + e a x1 + (e a' x + e a' x1)) = Ψ (e a x + e a' x + (e a x1 + e a' x1)) := fun x x1 => congrArg Ψ (by abel)
  have e3 : ∀ x x1, Ψ (e a x + e a x1 + (e b x + e b x1)) = Ψ (e a x + e b x + (e a x1 + e b x1)) := fun x x1 => congrArg Ψ (by abel)
  have e4 : ∀ x x1, Ψ (e a' x + e a' x1 + (e b x + e b x1)) = Ψ (e a' x + e b x + (e a' x1 + e b x1)) := fun x x1 => congrArg Ψ (by abel)
  simp only [e1, e2, e3, e4]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_prod, ofMul_zpow, smul_add, smul_neg, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, _root_.mul_one, mul_neg, neg_smul]
  abel

end GlobalTheory.TensBimult

namespace GlobalTheory.TensBimult

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), Tens D.toPre D' W → (∀ (z : (TK R).left) (J : ((TK R).left ⟶ D'.P.A.left) → D'.P.L.ι), Good D'.P.L z J → val (D'.psi 0) (𝟙 _) z J * val D'.rigK (𝟙 _) z J = 1) → D'.TauBimult := by
  intro R _ _ _ _ D D' r W T hn a a' b
  have hG : GlobalFnsSt := GlobalTheory.lawsAndExpansions.1.1.globalFns
  refine corr_of_val D'.P.isLB fun y J' hJ' => ?_
  obtain ⟨J, hJ⟩ : ∃ J, Good D.toPre.P.L y J :=
    ⟨fun ψ => (exists_chart D.toPre.P.isLB (ψ y)).choose, fun ψ => (exists_chart D.toPre.P.isLB (ψ y)).choose_spec⟩
  have key := GlobalTheory.T.tensorPreData_cubicalStructure_eq_prod_pulled_back hG R D.toPre D' W T (TK R) y J J' hJ hJ' (cP D' _ a) (cP D' _ a') (cP D' _ b)
  have hψ : ∀ u, val (D'.psi u) (𝟙 _) y J' = gm (cP D' (TK R) u).left y _ (T.w.s (fun k => J ((cP D' (TK R) u).left ≫ tensφ T.pr k), J' (cP D' (TK R) u).left)) * ∏ i, ∏ j, val (D.toPre.tau (T.xe u i) (T.xe u j)) (𝟙 _) y J ^ W i j :=
    fun u => T.psi u y J J' hJ hJ'
  have vt : ∀ u v, val (D'.tau u v) (𝟙 _) y J' = val (D'.psi (u + v)) (𝟙 _) y J' * (val (D'.psi u) (𝟙 _) y J')⁻¹ * (val (D'.psi v) (𝟙 _) y J')⁻¹ * (val D'.rigK (𝟙 _) y J')⁻¹ := by
    intro u v; simp only [DegPre.tau, val_mul hJ', val_inv]
  have vtE : ∀ u v, val (D.toPre.tau u v) (𝟙 _) y J = val (D.toPre.psi (u + v)) (𝟙 _) y J * (val (D.toPre.psi u) (𝟙 _) y J)⁻¹ * (val (D.toPre.psi v) (𝟙 _) y J)⁻¹ * (val D.toPre.rigK (𝟙 _) y J)⁻¹ := by
    intro u v; simp only [DegPre.tau, val_mul hJ, val_inv]
  have hB : ∀ u u' v, val (D.toPre.tau (u + u') v) (𝟙 _) y J * cubV D.toPre.cub y J (cP D.toPre _ u) (cP D.toPre _ u') (cP D.toPre _ v) = val (D.toPre.tau u v) (𝟙 _) y J * val (D.toPre.tau u' v) (𝟙 _) y J := fun u u' v =>
    (GlobalTheory.TauBimultBox.val_lhs D.toPre hJ u u' v).symm.trans ((val_corr hJ (D.tau_bimult u u' v) (𝟙 _)).trans (val_mul hJ _ _ _))
  have c0 : ∀ (E : DegPre R) (S : Over (Spec (CommRingCat.of R))), cP E S 0 = 1 := fun E S => by
    have := cPoint_add E S 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have hP : ∀ u (k : (Fin r × Fin r) × Fin 4), cP D' (TK R) u ≫ ![T.pr k.1.1 * T.pr k.1.2, T.pr k.1.1, T.pr k.1.2, 1] k.2 = cP D.toPre (TK R) (![T.xe u k.1.1 + T.xe u k.1.2, T.xe u k.1.1, T.xe u k.1.2, 0] k.2) := by
    intro u k
    have e : ∀ i, cP D' (TK R) u ≫ T.pr i = cP D.toPre (TK R) (T.xe u i) := fun i => by
      rw [cP, Category.assoc, T.c_pr]; rfl
    obtain ⟨⟨i, j⟩, m⟩ := k
    fin_cases m
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      rw [MonObj.comp_mul, e, e, cPoint_add]
    · simpa using e i
    · simpa using e j
    · simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
      rw [c0]; simp [Hom.one_def]
  rw [GlobalTheory.TauBimultBox.val_lhs D' hJ' a a' b, val_mul hJ']
  have hC : ∀ u u' v, cubV D.toPre.cub y J (cP D.toPre _ u) (cP D.toPre _ u') (cP D.toPre _ v) = val (D.toPre.tau u v) (𝟙 _) y J * val (D.toPre.tau u' v) (𝟙 _) y J * (val (D.toPre.tau (u + u') v) (𝟙 _) y J)⁻¹ := fun u u' v => by
    rw [← hB u u' v, mul_comm, inv_mul_cancel_left]
  simp only [hP, hC] at key
  have h1 : cP D' (TK R) a * cP D' (TK R) a' * cP D' (TK R) b = cP D' (TK R) (a + a' + b) := by rw [cPoint_add, cPoint_add]
  have h2 : cP D' (TK R) a * cP D' (TK R) a' = cP D' (TK R) (a + a') := (cPoint_add _ _ _ _).symm
  have h3 : cP D' (TK R) a * cP D' (TK R) b = cP D' (TK R) (a + b) := (cPoint_add _ _ _ _).symm
  have h4 : cP D' (TK R) a' * cP D' (TK R) b = cP D' (TK R) (a' + b) := (cPoint_add _ _ _ _).symm
  rw [h1, h2, h3, h4, ← c0 D' (TK R)] at key
  refine alg W T.xe (fun u => val (D.toPre.psi u) (𝟙 _) y J) (val D.toPre.rigK (𝟙 _) y J)
    (fun u => gm (cP D' (TK R) u).left y _ (T.w.s (fun k => J ((cP D' (TK R) u).left ≫ tensφ T.pr k), J' (cP D' (TK R) u).left)))
    (fun u => val (D'.psi u) (𝟙 _) y J') (fun u v => val (D'.tau u v) (𝟙 _) y J') (fun u v => val (D.toPre.tau u v) (𝟙 _) y J)
    (cubV D'.cub y J' (cP D' (TK R) a) (cP D' (TK R) a') (cP D' (TK R) b)) (val D'.rigK (𝟙 _) y J') a a' b vtE hψ vt (hn y J' hJ') ?_
  beta_reduce
  exact key

end GlobalTheory.TensBimult
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegenerationDataTauBimultiplicative
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TensPolBimult

theorem base_of_isCN {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (h : IsCN R) : Base R :=
  ⟨⟨h.1, inferInstance, h.2.1, h.2.2.1⟩, h.2.2.2⟩

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (D'.P.A ⟶ Q.B)), (∀ i, IsMonHom (pr i)) → IsLimit (Fan.mk D'.P.A pr) → ∀ (xe : D'.X ≃+ (Fin r → Q.X)), (∀ z i, D'.c z ≫ pr i = Q.c (xe z i)) → ∀ (w : LB.Iso D'.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))), w.IsGen → (∀ y z J J', Good Q.M.L z J → Good D'.P.L z J' → val (D'.psi y) (𝟙 _) z J' = gm (D'.xK y) z _ (w.s (fun k => J (D'.xK y ≫ tensφ pr k), J' (D'.xK y))) * ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j) → (∀ (z : (TK R).left) (J : ((TK R).left ⟶ D'.P.A.left) → D'.P.L.ι), Good D'.P.L z J → val (D'.psi 0) (𝟙 _) z J * val D'.rigK (𝟙 _) z J = 1) → D'.TauBimult := by
  intro R _ _ _ hR Q D' r W pr hpr hlim xe hc w hw hpsi hn
  exact GlobalTheory.PolTensBimult.main R (base_of_isCN hR) Q D' W pr xe ⟨hpr, ⟨hlim⟩, hc, w, hw, hpsi⟩ hn

end GlobalTheory.TensPolBimult
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilVacuumScalarEqOneInertPlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_vacuum_scalar_eq_one_inert_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, ∀ c : ℂ, Acts (evFin F v) (om' (1, k)) (G.M'.vac v) (c • G.M'.vac v) → c = 1 := by
  first | exact @GlobalTheory.InertScalar.scalar_eq_one | exact GlobalTheory.InertScalar.scalar_eq_one | (intros; apply GlobalTheory.InertScalar.scalar_eq_one <;> assumption)
end

