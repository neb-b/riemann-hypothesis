module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2477
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2789
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0188
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNumberFieldQkPointsComplexDegeneration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0918
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTransportAdelicSchwartzThetaTrans
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1725
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1760
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1700
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1896
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1998
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2790
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0223
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveLatticeTwistGenerated
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2795
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0689
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0711
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0688
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonoClassifyingOfInjectiveFamily
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2796
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0001
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2637
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2798
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0433
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2808

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusTorsionPointOfLabelOrthogonal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

namespace GlobalTheory.Poinc.Sep.TorPt


open GlobalTheory.ZH.TorusPerp in
theorem torus_label_over : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (AlgebraicClosure (FractionRing V))ˣ), χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ b mu, 𝔪.YY b mu → (χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : AlgebraicClosure (FractionRing V)) = algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (eStd X₁.S.g _ τ b).val))))) → ∀ (q : QkPt 𝔪.D.toPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N)) (y : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ 𝔪.A.A), q.y = 0 → IsTor χ q.g → QkToAkU 𝔪.U.toUnifPre (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) q y → y.left ≫ 𝔪.φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) ≫ (X₁.ρ.pt τ).left := by
  intro g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪 τ χ hχ1 hlab q y hqy hqτ hq
  haveI : CharZero V := 𝔪.cn.2.2.2
  have : IsDomain X₁.o₁ := X₁.ar.inj.isDomain _
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  have hG := hL.1.globalFns
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hkpos : 0 < X₁.S.r * X₁.S.N := Nat.mul_pos (by have := X₁.S.r_pos; omega) (by have := X₁.S.N_ge; omega)
  obtain ⟨x, hx, xadd, -, xonto⟩ := GlobalTheory.ThetaDvr.torsion_points 𝔪.yK 𝔪.cart
  obtain ⟨f, f₁, f₂, -, -, f₅⟩ := GlobalTheory.TorsionIso.torsion_eq hL V (maximalIdeal V) hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U
    (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) hkpos

  have hζ : IsPrimitiveRoot (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) (X₁.S.r * X₁.S.N) :=
    X₁.S.prim.pow (pow_pos hkpos 2) (pow_two _)
  let yb : X₁.S.R →+* AlgebraicClosure (FractionRing V) :=
    (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK
  let c₀ : (X₁.S.R)ˣ := Units.map (algebraMap X₁.o₁ X₁.S.R).toMonoidHom (hζ.isUnit hkpos.ne').unit
  let ω : (AlgebraicClosure (FractionRing V))ˣ := Units.map yb.toMonoidHom c₀
  have hωv : (ω : AlgebraicClosure (FractionRing V)) = yb (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))) := rfl
  have hω : IsPrimitiveRoot ω (X₁.S.r * X₁.S.N) := by
    have : NeZero ((X₁.S.r * X₁.S.N : ℕ) : AlgebraicClosure (FractionRing V)) := ⟨Nat.cast_ne_zero.2 hkpos.ne'⟩
    apply (IsPrimitiveRoot.coe_units_iff).1
    rw [hωv, ← (Polynomial.isRoot_cyclotomic_iff (R := AlgebraicClosure (FractionRing V))),
      ← Polynomial.map_cyclotomic _ (yb.comp (algebraMap X₁.o₁ X₁.S.R))]
    exact (hζ.isRoot_cyclotomic hkpos).map (yb.comp (algebraMap X₁.o₁ X₁.S.R))

  have hy : (TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap 𝔪.yK = spMap yb := (Spec.map_comp _ _).symm
  let h : Over.mk ((TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap 𝔪.yK) ⟶ baseOver (Sp X₁.S.R) :=
    Over.homMk ((TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap 𝔪.yK) (by simp)
  have hh : h.left = spMap yb := hy
  let Φ := ptHom 𝔪.cart (TFK (R := V) (AlgebraicClosure (FractionRing V)))
  have hΦ : ∀ b, Φ (x b) = h ≫ X₁.ρ.pt b := fun b => Over.OverMorphism.ext ((hx b).trans (by rw [← hh]; rfl))
  have weil : ∀ b b', WeilIs 𝔪.A.A 𝔪.A.L (X₁.S.r * X₁.S.N : ℕ) (x b) (x b') (unitOn (ω ^ (eStd X₁.S.g _ b b').val)) :=
    fun b b' => by
    have w := GlobalTheory.CommPairing.weilIs_pull hG X₁.ρ.P.isAb X₁.ρ.P.isLB h (X₁.ρ.weil b b' (c₀ ^ (eStd X₁.S.g _ b b').val) (by
      rw [pow_mul, map_pow]; rfl))
    rw [← hΦ, ← hΦ] at w
    refine (GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ _ _ _ _ _ _ X₁.ρ.P.isLB 𝔪.A.isLB 𝔪.cart ⟨𝔪.wl, 𝔪.wl_gen⟩ _ _ _ _
      (Φ (x b)) (Φ (x b')) _ rfl rfl).2 ?_
    convert w using 1
    rw [← map_pow, ← map_unitOn, ← hh]
  have pt_nsmul : ∀ (n : ℕ) b, x (n • b) = x b ^ n := fun n b =>
    map_pow (MonoidHom.mk' (fun a : Multiplicative X₁.S.Gam => x a.toAdd) fun _ _ => xadd _ _) (Multiplicative.ofAdd b) n
  have onto : ∀ b, ∃ q', f q' = x b := fun b => f₂ _ (by
    rw [← pt_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod (X₁.S.r * X₁.S.N)), ZMod.natCast_self, zero_smul]
    exact (MonoidHom.mk' (fun a : Multiplicative X₁.S.Gam => x a.toAdd) fun _ _ => xadd _ _).map_one)
  have hyf : y = f q := (f₁ q y).1 hq
  have hq1 : y ^ (X₁.S.r * X₁.S.N) = 1 := by
    obtain ⟨w, hw⟩ := 𝔪.U.ext
    exact (hq w hw).1
  obtain ⟨a', rfl⟩ := xonto y hq1
  have haa : a' = τ := by
    rw [← sub_eq_zero]
    refine eq_zero_of_eStd _ _ _ fun b => ?_
    obtain ⟨q', hq'⟩ := onto b
    have w₁ := (f₅ q q' _).1 (weilQkIs_tor hG q q' hqy hqτ)
    rw [← hyf, hq'] at w₁
    have e₁ := unitOn_injective (GlobalTheory.CommutatorPairing.weilIs_unique hG 𝔪.A.isAb 𝔪.A.isLB (weil a' b) w₁)
    have hYY : 𝔪.YY b (𝔪.e₈.symm q'.y) := ⟨q', x b, by simp, (f₁ _ _).2 hq'.symm, hx b⟩
    have e₂ := hlab b _ hYY
    rw [AddEquiv.apply_symm_apply] at e₂
    have e₃ : ω ^ (eStd X₁.S.g _ a' b).val = ω ^ (eStd X₁.S.g _ τ b).val := by
      rw [e₁]
      ext1
      rw [e₂, Units.val_pow_eq_pow_val, hωv, pow_mul, map_pow, map_pow, map_pow]
      rfl
    have e₄ := ZMod.val_injective _ (hω.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) e₃)
    have e₅ := eStd_add_left X₁.S.g _ (a' - τ) τ b
    rw [sub_add_cancel, e₄] at e₅
    exact left_eq_add.1 (e₅.trans (add_comm _ _))
  subst haa
  exact hx a'

theorem labels_hom : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), ∃ yy : X₁.S.Gam →+ 𝔪.D.toPre.X ⧸ (nsmulAddMonoidHom (X₁.S.r * X₁.S.N) : 𝔪.D.toPre.X →+ 𝔪.D.toPre.X).range, Function.Surjective yy ∧ ∀ a mu, 𝔪.YY a mu ↔ yy a = QuotientAddGroup.mk (𝔪.e₈ mu) := by
  intro g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.Poinc.Sep.Labels.yy_hom g n F W Z i X₁ z₁ act V ev X m t δ 𝔪
  choose mu hmu using h1
  have key : ∀ a nu, 𝔪.YY a nu ↔
      (QuotientAddGroup.mk (𝔪.e₈ (mu a)) : 𝔪.D.toPre.X ⧸ (nsmulAddMonoidHom (X₁.S.r * X₁.S.N) : 𝔪.D.toPre.X →+ 𝔪.D.toPre.X).range) =
        QuotientAddGroup.mk (𝔪.e₈ nu) := by
    intro a nu
    rw [h3 a (mu a) nu (hmu a), QuotientAddGroup.eq]
    constructor
    · intro hc
      choose w hw using hc
      refine ⟨𝔪.e₈ w, ?_⟩
      have e : nu = mu a + (X₁.S.r * X₁.S.N) • w := funext fun v => by simpa using hw v
      rw [nsmulAddMonoidHom_apply, e, map_add (f := _), map_nsmul]
      abel
    · rintro ⟨z, hz⟩
      rw [nsmulAddMonoidHom_apply] at hz
      intro v
      refine ⟨𝔪.e₈.symm z v, ?_⟩
      have e : nu = mu a + (X₁.S.r * X₁.S.N) • 𝔪.e₈.symm z := 𝔪.e₈.injective (by
        rw [map_add (f := _), map_nsmul, AddEquiv.apply_symm_apply, hz]
        abel)
      rw [e]
      rfl
  let yy : X₁.S.Gam →+ 𝔪.D.toPre.X ⧸ (nsmulAddMonoidHom (X₁.S.r * X₁.S.N) : 𝔪.D.toPre.X →+ 𝔪.D.toPre.X).range :=
    AddMonoidHom.mk' (fun a => QuotientAddGroup.mk (𝔪.e₈ (mu a))) fun a b => by
      have h := (key (a + b) (mu a + mu b)).1 (h4 a b (mu a) (mu b) (hmu a) (hmu b))
      refine h.trans ?_
      rw [map_add (f := _), QuotientAddGroup.mk_add]
  refine ⟨yy, fun c => ?_, fun a nu => (key a nu)⟩
  induction c using QuotientAddGroup.induction_on with
  | H α =>
    obtain ⟨a, ha⟩ := h2 (𝔪.e₈.symm α)
    refine ⟨a, ?_⟩
    have := (key a _).1 ha
    rw [AddEquiv.apply_symm_apply] at this
    exact this


open GlobalTheory.ZH.TorusPerp GlobalTheory.ZH.PerpTorus GlobalTheory.TorusExt GlobalTheory.TorsionExt in
attribute [local instance] gtGroup in
theorem exists_torus_char : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ, χ ^ (X₁.S.r * X₁.S.N) = 1 ∧ (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) := by
  intro g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪 τ hτ
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  have hB := 𝔪.D.tau_bimult
  have hkpos : 0 < X₁.S.r * X₁.S.N := Nat.mul_pos (by have := X₁.S.r_pos; omega) (by have := X₁.S.N_ge; omega)
  obtain ⟨yy, yyonto, hyy⟩ := labels_hom g n F W Z i X₁ z₁ act V ev X m t δ 𝔪
  obtain ⟨x₀, hx₀⟩ := X₁.div z₁
  have hker : τ ∈ X₁.S.perp yy.ker := fun h hh => by
    have h0 : 𝔪.YY h 0 := (hyy h 0).2 (by rw [(AddMonoidHom.mem_ker).1 hh, map_zero]; rfl)
    exact hτ h ((_root_.GlobalTheory.Poinc.Sep.mem_HH_iff_yy_zero g n F W Z i X₁ z₁ act x₀ hx₀ V ev X m t δ 𝔪 h).2 h0)
  obtain ⟨mf, hmf⟩ := exists_form X₁.S yy yyonto τ hker
  have hζ : IsPrimitiveRoot (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) (X₁.S.r * X₁.S.N) := X₁.S.prim.pow (pow_pos hkpos 2) (pow_two _)
  let ω : (FractionRing V)ˣ := Units.map (𝔪.yK.comp (algebraMap X₁.o₁ X₁.S.R)).toMonoidHom (hζ.isUnit hkpos.ne').unit
  have hωv : (ω : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))) := rfl
  have hω1 : ω ^ (X₁.S.r * X₁.S.N) = 1 := by
    ext1
    rw [Units.val_pow_eq_pow_val, hωv, ← map_pow, ← map_pow, hζ.pow_eq_one, map_one, map_one, Units.val_one]
  let χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ :=
    (AddChar.zmodChar (X₁.S.r * X₁.S.N) hω1).toMonoidHom.comp mf.toMultiplicative
  have hχ : ∀ α, χ (Multiplicative.ofAdd α) = ω ^ (mf α).val := fun _ => rfl
  have hχ1 : χ ^ (X₁.S.r * X₁.S.N) = 1 := MonoidHom.ext fun α => by
    show (ω ^ (mf α.toAdd).val) ^ (X₁.S.r * X₁.S.N) = 1
    rw [pow_right_comm, hω1, one_pow]
  refine ⟨χ, hχ1, fun g₀ hg₀ => ?_⟩

  obtain ⟨q, hqy, hqg⟩ := GlobalTheory.ZH.ClassWeight.exists_qkPt_tor hg₀ hχ1
  have hsq : (spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) ≫ X₁.ρ.P.A.hom = 𝟙 _ ≫ spMap 𝔪.yK := by
    rw [Category.assoc, Over.w]; simp
  let ℓ := 𝔪.cart.1.lift (spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) (𝟙 _) hsq
  have hℓ : ℓ ≫ 𝔪.A.A.hom = (TFK (R := V) (FractionRing V)).hom := by
    rw [𝔪.cart.1.lift_snd]
    show _ = Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) (FractionRing V)))
    rw [Algebra.algebraMap_self]
    exact (Spec.map_id _).symm
  let xF : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A := Over.homMk ℓ hℓ
  have hxF : xF.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left := 𝔪.cart.1.lift_fst _ _ _
  refine ⟨q, xF, hqy, hqg, ?_, hxF⟩
  have hf : (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp
      (algebraMap (FractionRing V) (FractionRing V)) = algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) := by
    ext; simp
  obtain ⟨qb, hqb, -⟩ := existsUnique_qkExt (F' := AlgebraicClosure (FractionRing V)) hB
    (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) hf q
  rw [qkToAkU_iff_of_algebra hL.1.globalFns hL.1.kerPow 𝔪.U hkpos hqb xF]
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  obtain ⟨f, f₁, -⟩ := GlobalTheory.TorsionIso.torsion_eq hL V (maximalIdeal V) hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U
    (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) hkpos
  have hqbf := (f₁ qb (f qb)).2 rfl
  let χb : Multiplicative 𝔪.D.toPre.X →* (AlgebraicClosure (FractionRing V))ˣ :=
    (Units.map (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).toMonoidHom).comp χ
  have hχb1 : χb ^ (X₁.S.r * X₁.S.N) = 1 := MonoidHom.ext fun α => by
    rw [MonoidHom.pow_apply, MonoidHom.one_apply]
    show Units.map _ (χ α) ^ _ = 1
    rw [← map_pow, ← MonoidHom.pow_apply, hχ1, MonoidHom.one_apply, map_one]
  have hqbt : IsTor χb qb.g := by
    have e1 : q.g = torusPt _ _ (Additive.ofMul χ) := (isTorusPtF_iff_eq _ _).1 ((isTor_iff _ _).1 (hqg ▸ hg₀))
    have hg : qb.g = gtExt _ _ hf q.g := (eq_gtExt_iff _ hf _ _).2 hqb.2
    rw [hg]
    rw [e1, GlobalTheory.QkNumberField.gtExt_torusPt, isTor_iff]
    exact isTorusPtF_torusPt _
  have hlab : ∀ b mu, 𝔪.YY b mu → (χb (Multiplicative.ofAdd (𝔪.e₈ mu)) : AlgebraicClosure (FractionRing V)) =
      algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))
        (𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (eStd X₁.S.g _ τ b).val)))) := by
    intro b mu h
    show algebraMap _ _ ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : FractionRing V)) = _
    rw [hχ, hmf b _ ((hyy b mu).1 h), Units.val_pow_eq_pow_val, hωv, ← map_pow, ← map_pow, ← pow_mul]
  have hover := torus_label_over g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 τ χb hχb1 hlab qb (f qb) (hqb.1.trans hqy) hqbt hqbf
  have heq : fieldMap (FractionRing V) (AlgebraicClosure (FractionRing V)) ≫ xF = f qb := by
    refine Over.OverMorphism.ext (𝔪.cart.1.hom_ext ?_ (by rw [Over.w, Over.w]))
    rw [hover, Over.comp_left, Category.assoc, hxF, ← Category.assoc]
    congr 1
    exact (Spec.map_comp _ _).symm
  rw [heq]
  exact hqbf

end GlobalTheory.Poinc.Sep.TorPt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepHermitianPairRationalSchrodinger
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilSchrodinger

theorem exists_isUWeilPair_hsp : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∃ om, GlobalTheory.WeilM.IsUWeilPair (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.WeilM.adeleClass D.host.F) ψ ξ
            (incM D.host.F JA) (incM D.host.F JB) co χT χS om := by
  intro D ψ hψ S T χS χT hS hT rS rT JA JB ξ hA hB κ _ co hrat
  obtain ⟨ω, hω⟩ := GlobalTheory.weilRepresentationUnitaryPair D ψ S T χS χT hψ hS hT rS rT
  obtain ⟨om, hom⟩ := _root_.GlobalTheory.ThetaTransform.exists_isTransport D ψ hψ S T χS χT hS hT rS rT JA JB ξ hA hB κ co hrat ω hω
  have h2 := GlobalTheory.T.transportedWeil_preserves_schwartz_heisenberg_equivariant D ψ hψ S T χS χT hS hT rS rT JA JB ξ hA hB κ co hrat ω hω om hom
  have h3 := _root_.GlobalTheory.WeilAdm.transport_adm D ψ hψ S T χS χT hS hT rS rT JA JB ξ hA hB κ co hrat ω hω om hom
  have h4 := _root_.GlobalTheory.WeilUnitaryTransport.isUnitaryOn_transport D ψ hψ S T χS χT hS hT rS rT JA JB ξ hA hB κ co hrat ω hω om hom
  have h5 := _root_.GlobalTheory.WeilCont.continuous_transport D ψ hψ S T χS χT hS hT rS rT JA JB ξ hA hB κ co hrat ω hω om hom
  have h6 := _root_.GlobalTheory.DblSchr.doubledModel D ψ hψ S T χS χT hS hT rS rT JA JB ξ hA hB κ co hrat ω hω om hom
  have h7 := _root_.GlobalTheory.WeilSchrodinger.DblTarget.exists_dbl_target D ψ hψ S T χS χT hS hT rS rT JA JB ξ hA hB κ co hrat ω hω om hom
  have hsp : GlobalTheory.WeilM.IsUSplitting (GlobalTheory.WeilM.adeleClass D.host.F) ψ co
      (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig)) om := ⟨⟨h2.1, h2.2, h3⟩, h4, h5⟩
  exact ⟨om, ⟨isUSplitting_inr hsp, h6⟩, ⟨transD _ co, transD_e co, isUSplitting_inl hsp, h7⟩, h5⟩

end GlobalTheory.WeilSchrodinger

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZhModelProperOverUSetup
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.UPoinc.exists_zhModel_proper_over_uSetup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X : USetup C), IsProjOver X.M.s → ∃ (Y : RatModel X.o₁ X.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X.S.J) (_ : ZHOut X.ρ Y U₀ EE) (q : Y.Z ⟶ X.M.Z), X.S.Over₀ Y U₀ ∧ X.S.IsEE Y U₀ EE ∧ IsProper q ∧ Y.pt ≫ q = X.M.pt ∧ (∀ z : X.M.Z, _root_.IsPreconnected (q.base ⁻¹' {z})) ∧ ∀ (p : ℕ) [Fact p.Prime] (z : X.M.Z) (ct : UCTrait X p z), ∃ y : Sp (OO p) ⟶ Y.Z, y ≫ q = ct.y := by
  intro E _ _ _ H Dw _ l Xo cf C X₁ hproj
  obtain ⟨m, c, hc⟩ := RatModel.exists_isCl_of_isProjOver hproj
  have hc0 : ∃ j, c j ≠ 0 := by
    obtain ⟨j, hj⟩ := hc.1 (genericPoint X₁.M.Z)
    exact ⟨j, hj.1⟩
  obtain ⟨Y, U₀, EE, hO, hdiv, hE, ⟨G⟩⟩ := GlobalTheory.zhSt_holds X₁.o₁ X₁.Ω₁ X₁.S X₁.ρ X₁.big (Fin (m + 1)) c hc0
    (GlobalTheory.ZH.finite_closure_theta_ratios_of_isCl X₁.o₁ X₁.Ω₁ X₁.S X₁.M (Fin (m + 1)) c hc)
  obtain ⟨q, hq⟩ := hc.exists_isHom (M' := Y) (φ := AlgHom.id X₁.o₁ X₁.Ω₁) hdiv
  have hYp : IsProper Y.s := ((GlobalTheory.isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hO.proj).1
  have hsep : IsSeparated X₁.M.s := X₁.M.sep
  have hqp : IsProper q := by
    haveI : IsProper (q ≫ X₁.M.s) := by rw [hq.inducedModelMorphism_comp_structureMap]; exact hYp
    exact IsProper.of_comp q X₁.M.s
  have hpt : Y.pt ≫ q = X₁.M.pt :=
    hq.trans ((congrArg (· ≫ X₁.M.pt) (Spec.map_id _)).trans (Category.id_comp _))
  refine ⟨Y, U₀, EE, G, q, hO, hE, hqp, hpt, ?_, ?_⟩
  · obtain ⟨U, hU, hiso⟩ := GlobalTheory.ZH.RatModel.exists_isIso_morphismRestrict_of_isProjOver X₁.o₁ X₁.Ω₁ Y X₁.M hO.proj q hq
    have : IsDedekindDomain X₁.o₁ := (inferInstance : ArithBase X₁.o₁ X₁.Ω₁).ded
    have := X₁.M.lft
    have : IsLocallyNoetherian X₁.M.Z := LocallyOfFiniteType.isLocallyNoetherian X₁.M.s
    exact GlobalTheory.ZariskiConn.fibre_preconnected Y.Z X₁.M.Z q (fun x => ⟨X₁.normal.isDomain_stalk x, X₁.normal.isIntegrallyClosed_stalk x⟩) U hU hiso
  · intro p _ z₁ ct
    exact GlobalTheory.exists_lift_of_isProper_of_isHom_id X₁.o₁ X₁.Ω₁ Y X₁.M q hq hqp p ct.y
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FieldChartOfInj
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualOpen

theorem fieldChart_of_inj : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ g : ℕ,
    SmoothOfRelativeDimension g A.hom → ∀ (U : Over S) (M : LB (A ⊗ U).left), SmoothOfRelativeDimension g U.hom →
    Fam A M → Inj A M → FieldChart A M := by
  intro S A _ hA g hg U M hU hM hI K _ _ s T t N hN
  obtain ⟨B, b, P, hP, hgood⟩ := _root_.GlobalTheory.DualCon.FieldRep.hasRep_field S A hA g hg K s
  obtain ⟨φ, hφb, hφS, hφm⟩ := _root_.GlobalTheory.DualCon.classify_mono S A B (Over.mk s) U b P M hP hM hI
  have hpb : IsPullback (fst U (Over.mk s)).left (snd U (Over.mk s)).left U.hom (Over.mk s).hom :=
    .of_hasPullback _ _
  have hsnd : SmoothOfRelativeDimension g (snd U (Over.mk s)).left :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hpb hU
  have hcomp : SmoothOfRelativeDimension g (φ.left ≫ b.left) := by
    rw [← Over.comp_left, hφb]; exact hsnd
  have hopen : IsOpenImmersion φ.left :=
    _root_.GlobalTheory.isOpenImmersion_of_mono_of_smoothOfRelativeDimension _ _ _ φ.left b.left g hgood.smooth hcomp hφm
  exact _root_.GlobalTheory.RepChart.repChart S A B (Over.mk s) U b P M hP hM φ hφb hφS hopen T t N hN

end GlobalTheory.DualOpen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDoubleCosetDefiniteHermitianFormLevelStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_doubleCoset_definiteHermitianForm_level : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ (L : G.Level) (K' : Subgroup (Gr G 1)),
  Subgroup.Commensurable K' (KHT p G.m G.n 1 G.Fw) → ∀ B : GlobalTheory.LKDef.DForm G,
    Finite (DoubleCoset.Quotient (B.emb.range : Set (G.GAf × Gr G 1))
      ((L.K.toSubgroup.prod K' : Subgroup (G.GAf × Gr G 1)) : Set (G.GAf × Gr G 1))) := by
  first | (exact @GlobalTheory.DefClassFin.finite_doubleCoset) | (exact GlobalTheory.DefClassFin.finite_doubleCoset) | (intros; apply GlobalTheory.DefClassFin.finite_doubleCoset <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FstIsFinFFrames
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StageDict

theorem fst_isFinF_frames : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → Formalism.L2.Host.HChar D.host.E) (S : T → Finset (HeightOneSpectrum (𝓞 D.host.E)))
    (FA : GlobalTheory.ChainFr.Fr A) (FW : GlobalTheory.ChainFr.Fr WW), (∀ τ, (GlobalTheory.SquareComm.frSgn true FA).cart τ = -X.rA.s τ) →
    (∀ τ, FW.cart τ = X.rW.s τ) → X.Is ψ θ α β νH S → ∀ t, GlobalTheory.SquareComm.IsFinF ψ θ true FA FW (X.f t) := by
  intro D T A A' WW X ψ θ α β νH S FA FW hcA hcW hX t
  have hv := hX.isVac
  have hν : Formalism.L2.Theta.IsHeckeChar D (α t / β t) := by
    have h := (hX.weil t).hecT
    rw [← inv_div]
    refine ⟨?_, fun x => ?_⟩
    · exact continuous_inv.comp h.1
    · show ((β t / α t) _)⁻¹ = 1
      rw [h.2 x, inv_one]
  have hI : X.ideal S t ≠ ⊥ := by
    unfold Tri.ideal
    rw [← Ideal.zero_eq_bot]
    refine Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ ?_
    rw [Ideal.zero_eq_bot]
    exact w.ne_bot
  obtain ⟨f₁, h1, h1t⟩ := GlobalTheory.Adopt.first_standard_pair_member_has_theta_function D ψ θ A WW X.rA X.rW (α t / β t) (X.e t) (S t) (X.ideal S t) X.vac
    hX.rigA hX.rigW hν (hX.idem t) hI hv
  have heq : X.f t = f₁ := by
    obtain ⟨⟨Tm, hT⟩, hall⟩ := hX.fst t
    rw [hall Tm hT, h1.2 Tm hT]
  have hft : IsThetaFunO ψ (GlobalTheory.Grid.neg A) WW (X.f t) := heq ▸ h1t
  refine ⟨hft, fun τ => ?_⟩
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hX.idem t)
  have hF := GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hv.1.1.1 hv.2.inf ho.infPart_eq ho.conj.infPart_eq
    (hX.fst t) hv.2.theta hft (hv.2.fock τ)
  rw [hcA τ, hcW τ]
  exact hF

end GlobalTheory.StageDict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeomOver
section
noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.Et.CovChar

variable (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

variable {R} {X Y : Scheme.{0}} (f : Y ⟶ X)

end GlobalTheory.Et.CovChar

namespace GlobalTheory.AV.AbVar

open ReciprocityTheory.ChartRestriction.G.Geo.Tor MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

variable {K : Type} [Field K]

abbrev geomX (A : AbVar K) : Scheme.{0} := GlobalTheory.Et.geom (AlgebraicClosure K) A.X.hom

abbrev geomOver (A : AbVar K) : Over (Sp K) :=
  Over.mk (pullback.fst A.X.hom (spMap (algebraMap K (AlgebraicClosure K))) ≫ A.X.hom)

def transl (A : AbVar K) (a : A.Pt) : geomX A ⟶ geomX A :=
  pullback.lift
    ((lift (Over.homMk (pullback.fst _ _) : geomOver A ⟶ A.X)
      (Over.homMk (pullback.snd _ _ ≫ a.left) (by
        rw [Category.assoc, Over.w a]; exact pullback.condition.symm) : geomOver A ⟶ A.X) ≫ μ[A.X]).left)
    (pullback.snd _ _) (by
      rw [Over.w]; exact pullback.condition)

end GlobalTheory.AV.AbVar
end
end

