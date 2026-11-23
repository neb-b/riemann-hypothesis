module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MahlerCompactness

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsObjOfUniformisedTripleComplex
section
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

namespace GlobalTheory.UnifObj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def negZeta (n : ℕ) : ℂˣ := Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) / n)) (Complex.exp_ne_zero _)

theorem negZeta_prim {n : ℕ} (hn : 0 < n) : IsPrimitiveRoot (negZeta n) n := by
  rw [← IsPrimitiveRoot.coe_units_iff]
  have := (Complex.isPrimitiveRoot_exp n hn.ne').inv
  rwa [← Complex.exp_neg, ← neg_div] at this

theorem negZeta_pow {n m : ℕ} (hn : 0 < n) (hm : 0 < m) : negZeta (n * m) ^ m = negZeta n := by
  have h₁ : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have h₂ : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, negZeta, negZeta, Units.val_mk0, Units.val_mk0, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

theorem negZeta_zpow (n : ℕ) (j : ℤ) :
    ((negZeta n ^ j : ℂˣ) : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (j : ℂ) / n) := by
  rw [Units.val_zpow_eq_zpow_val, negZeta, Units.val_mk0, ← Complex.exp_int_mul]
  congr 1
  ring

theorem exists_tateIso (D D' : Datum H) {g : ℕ} (ty : Fin g → (E →+* ℂ)) (P' : D'.La →+ (Fin g → ℂ))
    {Q : Type} [Group Q] (act : 𝓞 E → Q → Q) (w : ℕ → Q → Q → ℂˣ → Prop) (e : (Fin g → ℂ) → Q)
    (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (hlin : ∀ (a : 𝓞 E) x i, P' (a • x) i = ty i (a : E) * P' x i)
    (hinj : Function.Injective P') (hadd : ∀ z z', e (z + z') = e z * e z') (hsur : Function.Surjective e)
    (hker : ∀ z, e z = 1 ↔ z ∈ P'.range) (hact : ∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = act a (e z))
    (hw : ∀ (k : ℕ) (a b : D'.La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / k) →
      w k (e ((k : ℂ)⁻¹ • P' a)) (e ((k : ℂ)⁻¹ • P' b)) c)
    (htow : ∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e)
    (hbij : ∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e)
    (hiso : ∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ D'.EF (f n a) (f n a') - D.EF a a') :
    ∃ I : TateIso D ℂ Q act w, ∀ n a, I.ev n a = e ((n : ℂ)⁻¹ • P' (f n a)) := by
  have e0 : e 0 = 1 := (hker 0).2 (zero_mem _)
  have epow : ∀ (m : ℕ) z, e z ^ m = e ((m : ℂ) • z) := fun m z => by
    induction m with
    | zero => simp [e0]
    | succ m ih => rw [pow_succ, ih, ← hadd, Nat.cast_succ, add_smul, one_smul]
  have eP : ∀ a, e (P' a) = 1 := fun a => (hker _).2 ⟨a, rfl⟩
  have div : ∀ n : ℕ, 0 < n → ∀ a, (n : ℂ)⁻¹ • P' (n • a) = P' a := fun n hn a => by
    rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ (Nat.cast_ne_zero.2 hn.ne')]
  have md : ∀ n : ℕ, 0 < n → ∀ a c, e ((n : ℂ)⁻¹ • P' (a + n • c)) = e ((n : ℂ)⁻¹ • P' a) := fun n hn a c => by
    rw [map_add (f := _), smul_add, hadd, div n hn, eP, _root_.mul_one]
  refine ⟨{ ζ := negZeta
            ζ_prim := fun n hn => negZeta_prim hn
            ζ_pow := fun n m hn hm => negZeta_pow hn hm
            ev := fun n a => e ((n : ℂ)⁻¹ • P' (f n a))
            add := fun n a b => by rw [map_add (f := _), map_add (f := _), smul_add, hadd]
            lin := fun n c a => ?_
            ker := fun n hn a => ?_
            onto := fun n hn x => ?_
            tower := fun n m hn hm a => ?_
            isom := fun n hn a b => hw n _ _ _ hn ?_ }, fun _ _ => rfl⟩
  · rw [← hact, map_smul]
    congr 1
    funext i
    rw [Pi.smul_apply, Pi.smul_apply, hlin, smul_eq_mul, smul_eq_mul, mul_left_comm]
  · rw [← (hbij n hn).1, hker]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨c, hinj ?_⟩
      rw [map_nsmul, hc, ← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ (Nat.cast_ne_zero.2 hn.ne')]
    · rintro ⟨c, hc⟩
      exact ⟨c, by rw [hc, div n hn]⟩
  · constructor
    · intro hx
      obtain ⟨z, rfl⟩ := hsur x
      rw [epow, hker] at hx
      obtain ⟨a', ha'⟩ := hx
      obtain ⟨a, c, rfl⟩ := (hbij n hn).2 a'
      exact ⟨a, by rw [← md n hn _ c, ha', inv_smul_smul₀ (Nat.cast_ne_zero.2 hn.ne')]⟩
    · rintro ⟨a, rfl⟩
      rw [epow, smul_inv_smul₀ (Nat.cast_ne_zero.2 hn.ne'), eP]
  · obtain ⟨c, hc⟩ := htow n m hn hm a
    have h₂ : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    rw [epow, smul_smul, ← md n hn _ c, ← hc, Nat.cast_mul, mul_inv, mul_left_comm, mul_inv_cancel₀ h₂,
      _root_.mul_one]
  · rw [← negZeta_zpow]
    congr 1
    obtain ⟨j, hj⟩ := hiso n hn a b
    rw [sub_eq_iff_eq_add.1 hj, zpow_add, zpow_mul, zpow_natCast, (negZeta_prim hn).pow_eq_one, one_zpow,
      _root_.one_mul]

def tateExtend {D : Datum H} {k K : Type} [Field k] [Field K] (φ : k →+* K) {Q Q' : Type} [Group Q] [Group Q']
    {act : 𝓞 E → Q → Q} {act' : 𝓞 E → Q' → Q'} {w : ℕ → Q → Q → kˣ → Prop} {w' : ℕ → Q' → Q' → Kˣ → Prop}
    (I : TateIso D k Q act w) (j : Q →* Q') (hj : Function.Injective j)
    (htor : ∀ n : ℕ, 0 < n → ∀ y, y ^ n = 1 → ∃ x, j x = y) (hact : ∀ a x, j (act a x) = act' a (j x))
    (hw : ∀ n x y c, w n x y c → w' n (j x) (j y) (Units.map φ.toMonoidHom c)) : TateIso D K Q' act' w' where
  ζ n := Units.map φ.toMonoidHom (I.ζ n)
  ζ_prim n hn := (I.ζ_prim n hn).map_of_injective (Units.map_injective φ.injective)
  ζ_pow n m hn hm := by rw [← map_pow, I.ζ_pow n m hn hm]
  ev n a := j (I.ev n a)
  add n a b := by rw [I.add, map_mul]
  lin n c a := by rw [I.lin, hact]
  ker n hn a := by rw [← I.ker n hn, map_eq_one_iff j hj]
  onto n hn y := by
    constructor
    · intro hy
      obtain ⟨x, rfl⟩ := htor n hn y hy
      rw [← map_pow, map_eq_one_iff j hj] at hy
      obtain ⟨a, rfl⟩ := (I.onto n hn x).1 hy
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      rw [← map_pow, (I.onto n hn _).2 ⟨a, rfl⟩, map_one]
  tower n m hn hm a := by rw [← map_pow, I.tower n m hn hm]
  isom n hn a b := by
    rw [← map_zpow]
    exact hw _ _ _ _ (I.isom n hn a b)

theorem unitOn_map {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (c : Aˣ) :
    Units.map (spMap φ).appTop.hom.toMonoidHom (unitOn c) = unitOn (Units.map φ.toMonoidHom c) :=
  Units.ext (congrArg (fun q => q.hom (c : A)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))).symm

theorem exists_smul_eq {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] {I J : Ideal O} {n : ℕ}
    (h : I * J = Ideal.span {(n : O)}) {c : O} (hc : c ∈ I) {a : M} (ha : a ∈ J • (⊤ : Submodule O M)) :
    ∃ b : M, c • a = n • b := by
  have := Submodule.smul_mem_smul hc ha
  rw [← Submodule.mul_smul, h, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at this
  obtain ⟨b, -, hb⟩ := this
  exact ⟨b, by rw [← hb, Nat.cast_smul_eq_nsmul]⟩

theorem exists_obj (hL : Out.Laws) {D : Datum H} {l : Level H} (hA : l.A = 1) {B k : Type} [CommRing B] [Field k]
    [IsAlgClosed k] [CharZero k] (b : Base l B) (σ : B →+* k) (t : SAB H (Sp k)) {g : ℕ} (hp : IsProper t.G.hom)
    (hg : SmoothOfRelativeDimension g t.G.hom) (ha : Out.RelAmple t.G t.PP.L) (hk : Out.KTriv t.G t.PP.L)
    (hdet : DetCond D t.act (𝟙 (Sp k)) (σ b.ρ))
    (I : TateIso D k (𝟙_ (Over (Sp k)) ⟶ t.G) (fun a x => x ≫ t.act.act a)
      (fun n x y c => Out.WeilIs t.G t.PP.L n x y (unitOn c))) :
    ∃ (o : Obj D l b (spMap σ)) (m : SABMap t o.t (𝟙 _)),
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
        (I.ev l.M a).left ≫ m.φ = (o.eta a).left := by
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  obtain ⟨u, hu, π, hπ, huπ⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 l.coprime)
  have hη : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
      I.ev l.M (π • a) = I.ev l.M a := fun a h => by
    conv_rhs => rw [← one_smul (𝓞 E) a, ← huπ, add_smul, I.add,
      (I.ker _ hM _).2 (exists_smul_eq l.prod hu h), _root_.one_mul]
  have := t.semi.smooth
  refine ⟨{ t := t
            proper := hp
            ample := ha
            ktriv := hk
            eta := fun a => I.ev l.M (π • a)
            eta_add := fun a c => by rw [smul_add, I.add]
            eta_ker := fun a h => (I.ker _ hM _).2 (exists_smul_eq ((mul_comm _ _).trans l.prod) hπ h)
            etaA := fun _ => 1
            etaA_add := fun _ _ => (_root_.mul_one _).symm
            etaA_ker := fun _ => rfl
            geom := fun K _ _ x β hx => ?_ }, LevelTwist.sabMapId t, fun a h => ?_⟩
  · obtain ⟨φ, rfl⟩ : ∃ φ : k →+* K, x = spMap φ := ⟨(Spec.preimage x).hom, (Spec.map_preimage x).symm⟩
    obtain rfl : φ.comp σ = β :=
      congrArg CommRingCat.Hom.hom (Spec.map_injective ((Spec.map_comp _ _).trans hx))
    have : CharZero K := charZero_of_injective_ringHom φ.injective
    let J : TateIso D K (Over.mk (spMap φ) ⟶ t.G) (fun a x => x ≫ t.act.act a)
        (fun n x y c => Out.WeilIs t.G t.PP.L n x y (unitOn c)) :=
      tateExtend φ I (MonoidHom.mk' (fun z => toUnit (Over.mk (spMap φ)) ≫ z) fun _ _ => MonObj.comp_mul _ _ _)
        (HeckePoint.toUnit_comp_injective _ _)
        (fun n hn y hy => HeckePoint.exists_of_torsion hL.mulN (HeckePoint.polOf t hp ha hk hg) _
          (Nat.cast_ne_zero.2 hn.ne') (Nat.cast_ne_zero.2 hn.ne') y hy)
        (fun a z => (Category.assoc (toUnit _) z _).symm) (fun n y z c h => by
          have := CommPairing.weilIs_pull hL.globalFns (HeckePoint.isAbelianScheme_of_proper t hp) t.PP.isLB
            (toUnit (Over.mk (spMap φ))) h
          rw [Over.toUnit_left] at this
          rw [← unitOn_map]
          exact this)
    refine ⟨LieExt.detCond_extend D φ t.G t.act hdet, J, ?_, fun a => ?_, fun a h => ?_⟩
    · have h₁ := J.ζ_prim _ l.A_pos
      have h₂ := b.ζ_prim
      rw [hA, IsPrimitiveRoot.one_right_iff] at h₁ h₂
      rw [hA, h₁, h₂, map_one, Units.val_one]
    · rw [hA, MonObj.comp_one]
      exact ((J.ker 1 one_pos a).2 ⟨a, (one_smul _ _).symm⟩).symm
    · exact congrArg (toUnit (Over.mk (spMap φ)) ≫ ·) (hη a h)
  · exact (Category.comp_id _).trans (congrArg (fun q => q.left) (hη a h).symm)

theorem exists_obj_of_uniformised : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D D' : Datum H) (l : Level H) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P' : D'.La →+ (Fin g → ℂ)) (t : SAB H (Sp ℂ)) (e : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ t.G)) (f : ℕ → D.La →ₗ[𝓞 E] D'.La), l.A = 1 → σ (baseKA l).ρ = H.rt0 → D'.p = D.p → D'.q = D.q → IsPeriod D' ty P' → (IsProper t.G.hom ∧ SmoothOfRelativeDimension g t.G.hom ∧ Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L ∧ DetCond D' t.act (𝟙 (Sp ℂ)) H.rt0 ∧ (∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧ (∀ z, e z = 1 ↔ z ∈ P'.range) ∧ (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ t.act.act a) ∧ IsHolTo Set.univ (fun z => (e z).left) ∧ ∀ (k : ℕ) (a b : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / k) → Out.WeilIs t.G t.PP.L k (e ((k : ℂ)⁻¹ • P' a)) (e ((k : ℂ)⁻¹ • P' b)) (unitOn c)) → (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) → (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ D'.EF (f n a) (f n a') - D.EF a a') → ∃ (o : Obj D l (baseKA l) (spMap σ)) (m : SABMap t o.t (𝟙 _)), ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), (e ((l.M : ℂ)⁻¹ • P' (f l.M a))).left ≫ m.φ = (o.eta a).left := by
  intro hL E _ _ _ H D D' l σ g ty P' t e f hA hσ hp hq hP ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, _, hw⟩ ⟨htow, hbij⟩ hiso
  have hd : DetCond D t.act (𝟙 (Sp ℂ)) (σ (baseKA l).ρ) := fun τ => by
    rw [hσ, ← hp, ← hq]
    exact h₅ τ
  obtain ⟨I, hI⟩ := exists_tateIso D D' ty P' (fun a x => x ≫ t.act.act a)
    (fun n x y c => Out.WeilIs t.G t.PP.L n x y (unitOn c)) e f hP.1 hP.2.1 h₆ h₇ h₈ h₉ (fun k a b c hk hc => by have := hw k a b c hk hc; beta_reduce; exact this) htow hbij hiso
  obtain ⟨o, m, h⟩ := exists_obj hL hA (baseKA l) σ t h₁ h₂ h₃ h₄ hd I
  refine ⟨o, m, fun a ha => ?_⟩
  exact (congrArg (fun q => q.left ≫ m.φ) (hI l.M a).symm).trans (h a ha)

end GlobalTheory.UnifObj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSymmetricInterpolating
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.PointInterp

variable {k : Type} [Field k] {X Y : Scheme.{0}}

def valueAt (p : Spec (CommRingCat.of k) ⟶ X) (U : X.Opens) (h : ⊤ ≤ p ⁻¹ᵁ U) : Γ(X, U) →+* k :=
  (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.comp (p.appLE U ⊤ h).hom

theorem top_le_iff (p : Spec (CommRingCat.of k) ⟶ X) (U : X.Opens) (z : Spec (CommRingCat.of k)) :
    ⊤ ≤ p ⁻¹ᵁ U ↔ p z ∈ U :=
  ⟨fun h => h (show z ∈ (⊤ : (Spec (CommRingCat.of k)).Opens) from trivial), fun h y _ => by
    obtain rfl : y = z := Subsingleton.elim (α := PrimeSpectrum k) _ _
    exact h⟩

theorem valueAt_rs (p : Spec (CommRingCat.of k) ⟶ X) {U V : X.Opens} (hle : V ≤ U) (h : ⊤ ≤ p ⁻¹ᵁ V)
    (h' : ⊤ ≤ p ⁻¹ᵁ U) (a : Γ(X, U)) : valueAt p V h (rs X hle a) = valueAt p U h' a :=
  congrArg (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom (BoxSection.appLE_res p hle h h' a)

theorem valueAt_cst (f : X ⟶ Spec (CommRingCat.of k)) (p : Spec (CommRingCat.of k) ⟶ X) (hp : p ≫ f = 𝟙 _)
    (U : X.Opens) (h : ⊤ ≤ p ⁻¹ᵁ U) (c : k) : valueAt p U h (cst f U c) = c := by
  refine (valueAt_rs p le_top h le_top _).trans ?_
  have e : p.appLE ⊤ ⊤ le_top = p.appTop := Scheme.Hom.appLE_eq_app p
  have e' : f.appTop ≫ p.appTop = 𝟙 _ := by rw [← Scheme.Hom.comp_appTop, hp, Scheme.Hom.id_appTop]
  change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (f.appTop ≫ p.appLE ⊤ ⊤ le_top) ≫
    (Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom c = c
  rw [e, e', Category.id_comp, Iso.inv_hom_id]
  rfl

theorem valueAt_ne_zero_iff (p : Spec (CommRingCat.of k) ⟶ X) (U : X.Opens) (h : ⊤ ≤ p ⁻¹ᵁ U) (a : Γ(X, U)) :
    valueAt p U h a ≠ 0 ↔ ⊤ ≤ p ⁻¹ᵁ X.basicOpen a := by
  have hb := Scheme.basicOpen_appLE p ⊤ U h a
  rw [top_inf_eq] at hb
  rw [← hb, ← isUnit_iff_ne_zero]
  constructor
  · intro hu
    have hu' := hu.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
    have : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (valueAt p U h a) = (p.appLE U ⊤ h).hom a :=
      (Scheme.ΓSpecIso (CommRingCat.of k)).hom_inv_id_apply _
    rw [this] at hu'
    exact (Scheme.basicOpen_of_isUnit _ hu').ge
  · intro hu
    refine IsUnit.map (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom ?_
    exact (Spec (CommRingCat.of k)).toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy =>
      (Scheme.mem_basicOpen _ _ y hy).1 (hu hy)

theorem eq_of_valueAt_eq (p q : Spec (CommRingCat.of k) ⟶ X) {U : X.Opens} (hU : IsAffineOpen U)
    (hp : ⊤ ≤ p ⁻¹ᵁ U) (hq : ⊤ ≤ q ⁻¹ᵁ U) (h : valueAt p U hp = valueAt q U hq) : p = q := by
  have e : p.appLE U ⊤ hp = q.appLE U ⊤ hq := by
    rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of k)).hom]
    exact CommRingCat.hom_ext h
  have hV := isAffineOpen_top (Spec (CommRingCat.of k))
  have : IsIso hV.fromSpec := by rw [IsAffineOpen.fromSpec_top]; infer_instance
  rw [← cancel_epi hV.fromSpec, ← hU.SpecMap_appLE_fromSpec p hV hp, ← hU.SpecMap_appLE_fromSpec q hV hq, e]

def subMulSec (f : X ⟶ Spec (CommRingCat.of k)) {H : LB X} (s t : LB.Sec H) (c : k) : LB.Sec H where
  f j := s.f j - cst f _ c * t.f j
  compat i j := by
    rw [map_sub, map_sub, map_mul, map_mul, s.compat i j, t.compat i j]
    have e₁ := rs_cst f (inf_le_left : H.U i ⊓ H.U j ≤ H.U i) c
    have e₂ := rs_cst f (inf_le_right : H.U i ⊓ H.U j ≤ H.U j) c
    rw [e₁, e₂]
    ring

theorem top_le_nonzeroLocus_iff {H : LB X} (s : LB.Sec H) (p : Spec (CommRingCat.of k) ⟶ X) (l : H.ι)
    (hl : ⊤ ≤ p ⁻¹ᵁ H.U l) : ⊤ ≤ p ⁻¹ᵁ nonzeroLocus s ↔ valueAt p _ hl (s.f l) ≠ 0 := by
  let z : Spec (CommRingCat.of k) := (default : PrimeSpectrum k)
  rw [valueAt_ne_zero_iff, top_le_iff _ _ z, top_le_iff _ _ z]
  exact mem_nonzeroLocus_iff_mem_basicOpen_chart s l ((top_le_iff _ _ z).1 hl)

theorem exists_separating (f : X ⟶ Spec (CommRingCat.of k)) {H : LB X} (hH : H.IsLB) {n : ℕ}
    {s : Fin (n + 1) → LB.Sec H} (hs : VeryAmpleBy f H s) (p q : Spec (CommRingCat.of k) ⟶ X)
    (hp : p ≫ f = 𝟙 _) (hq : q ≫ f = 𝟙 _) (hne : p ≠ q) :
    ∃ σ : LB.Sec H, ⊤ ≤ p ⁻¹ᵁ nonzeroLocus σ ∧ ¬ ⊤ ≤ q ⁻¹ᵁ nonzeroLocus σ := by
  let z : Spec (CommRingCat.of k) := (default : PrimeSpectrum k)
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1
    (show p z ∈ ⨆ i, nonzeroLocus (s i) by rw [hs.1]; trivial)
  have hpa := (top_le_iff p _ z).2 ha
  by_cases hqa : ⊤ ≤ q ⁻¹ᵁ nonzeroLocus (s a)
  swap
  · exact ⟨s a, hpa, hqa⟩
  obtain ⟨haff, r, hr, hsurj⟩ := hs.2 a
  obtain ⟨b, hb⟩ : ∃ b, valueAt p _ hpa (r b) ≠ valueAt q _ hqa (r b) := by
    by_contra hc
    push_neg at hc
    refine hne (eq_of_valueAt_eq p q haff hpa hqa (RingHom.ext fun x => ?_))
    obtain ⟨F, rfl⟩ := hsurj x
    induction F using MvPolynomial.induction_on with
    | C c => rw [MvPolynomial.eval₂Hom_C, valueAt_cst f p hp, valueAt_cst f q hq]
    | add F G hF hG => rw [map_add (f := _), map_add (f := _), map_add (f := _), hF, hG]
    | mul_X F j hF => rw [map_mul, MvPolynomial.eval₂Hom_X', map_mul, map_mul, hF, hc]
  have key : ∀ (x : Spec (CommRingCat.of k) ⟶ X) (hx : x ≫ f = 𝟙 _) (hxa : ⊤ ≤ x ⁻¹ᵁ nonzeroLocus (s a)) (c : k),
      ⊤ ≤ x ⁻¹ᵁ nonzeroLocus (subMulSec f (s b) (s a) c) ↔ valueAt x _ hxa (r b) ≠ c := by
    intro x hx hxa c
    obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show x z ∈ ⨆ i, H.U i by rw [hH.cover]; trivial)
    have hxl := (top_le_iff x _ z).2 hl
    have hm : ⊤ ≤ x ⁻¹ᵁ (nonzeroLocus (s a) ⊓ H.U l) := le_inf hxa hxl
    have e := congrArg (valueAt x _ hm) (hr b l)
    rw [map_mul, valueAt_rs x _ hm hxl, valueAt_rs x _ hm hxl, valueAt_rs x _ hm hxa] at e
    have h0 := (top_le_nonzeroLocus_iff (s a) x l hxl).1 hxa
    rw [top_le_nonzeroLocus_iff _ x l hxl]
    change valueAt x _ hxl ((s b).f l - cst f _ c * (s a).f l) ≠ 0 ↔ _
    rw [map_sub, map_mul, valueAt_cst f x hx, e, ← sub_mul, mul_ne_zero_iff, sub_ne_zero]
    exact and_iff_left h0
  exact ⟨subMulSec f (s b) (s a) (valueAt q _ hqa (r b)), (key p hp hpa _).2 hb,
    fun h => (key q hq hqa _).1 h rfl⟩

end GlobalTheory.PointInterp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniversalFibreUniformisedTriple
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

namespace GlobalTheory.UnivFibre

theorem exists_fibre_uniformised : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i : Fin U.n) (P : (U.Di i).La →+ (Fin g → ℂ)), σ (baseKA l).ρ = H.rt0 → g = Module.finrank ℚ E / 2 * (D.p + D.q) → IsPeriod (U.Di i) ty P → ∃ (t : SAB H (Sp ℂ)) (e : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ t.G)) (m : SABMap t Xo.univ.t (U.u i P)), (∀ z, (e z).left ≫ m.φ = (U.ex i P z).left) ∧ (IsProper t.G.hom ∧ SmoothOfRelativeDimension g t.G.hom ∧ Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L ∧ DetCond (U.Di i) t.act (𝟙 (Sp ℂ)) H.rt0 ∧ (∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧ (∀ z, e z = 1 ↔ z ∈ P.range) ∧ (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ t.act.act a) ∧ IsHolTo Set.univ (fun z => (e z).left) ∧ ∀ (k : ℕ) (a b : (U.Di i).La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((U.Di i).EF a b : ℂ) / k) → Out.WeilIs t.G t.PP.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P b)) (unitOn c)) := by
  intro E _ _ _ H D l Xo σ g ty U i P hσ hg hP
  obtain ⟨t, ⟨m⟩⟩ : ∃ t : SAB H (Sp ℂ), Nonempty (SABMap t Xo.univ.t (U.u i P)) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (U.u i P) Xo.univ.t
    exact ⟨_, ⟨m⟩⟩
  have hL : LBIso t.PP.L (Xo.univ.t.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  obtain ⟨π, hπ⟩ := LiePull.exists_pushEquiv m.cart (𝟙_ (Over (Sp ℂ))) (U.u i P) (Category.id_comp _).symm
  have he : ∀ z, (π.symm (U.ex i P z)).left ≫ m.φ = (U.ex i P z).left := fun z => by
    rw [← hπ, π.apply_symm_apply]
  obtain ⟨ha, hk⟩ := amplePt _ ℂ (U.u i P) Xo.univ.t.G t.G m.φ m.cart _ _ Xo.univ.t.PP.isLB t.PP.isLB hL
    Xo.univ.ample Xo.univ.ktriv
  have hdet := (Xo.univ.geom ℂ (U.u i P) σ (U.over_σ i P hP)).1
  rw [hσ] at hdet
  refine ⟨t, fun z => π.symm (U.ex i P z), m, he,
    MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 Xo.univ.proper, ?_, ha, hk, fun τ => ?_,
    fun z w => (congrArg π.symm (U.ex_add i P hP z w)).trans (map_mul π.symm _ _), π.symm.surjective.comp (U.ex_onto i P hP),
    fun z => by rw [← U.ex_ker i P hP z, map_eq_one_iff _ π.symm.injective], fun a z => ?_, ?_,
    fun k a b c hk hc => ?_⟩
  · rw [hg]
    have := smoothOfRelativeDimension_isStableUnderBaseChange (Module.finrank ℚ E / 2 * (D.p + D.q))
    exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension _) m.cart.1
      (ObjDim.smoothOfRelativeDimension Xo.univ)
  · rw [LiePull.lieMult_pull _ _ _ Xo.univ.t.G t.G _ m.φ Xo.univ.t.act t.act m.cart m.act,
      LiePull.lieMult_pull _ _ _ Xo.univ.t.G t.G _ m.φ Xo.univ.t.act t.act m.cart m.act, Category.id_comp,
      (U.sig i).1, (U.sig i).2]
    exact hdet τ
  · apply π.injective
    rw [π.apply_symm_apply, U.ex_lin i P hP]
    apply Over.OverMorphism.ext
    rw [hπ, Over.comp_left, Over.comp_left, Category.assoc, ← he z, Category.assoc]
    exact congrArg _ (m.act a).symm
  · refine HolTorsion.isHolTo_of_isPullback m.cart.1
      (HolTorsion.isHolTo_congr (HolHom.isHolTo_ex U i hP) fun z _ => he z)
      (HolTorsion.isHolTo_congr (c := fun _ => 𝟙 (Sp ℂ))
        (HolHom.isHolTo_of_holAt isOpen_univ fun z _ => HolHom.holAt_const _ _)
        fun z _ => Over.w (π.symm (U.ex i P z)))
  · have h := U.ex_weil i P hP k a b c hk hc
    have key : ∀ (y : Sp ℂ ⟶ Xo.X) (_ : y = (𝟙_ (Over (Sp ℂ))).hom ≫ U.u i P) (x₀ y₀ : Over.mk y ⟶ Xo.univ.t.G)
        (x x' : 𝟙_ (Over (Sp ℂ)) ⟶ t.G), x.left ≫ m.φ = x₀.left → x'.left ≫ m.φ = y₀.left →
        Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k x₀ y₀ (unitOn c) → Out.WeilIs t.G t.PP.L k x x' (unitOn c) := by
      rintro y rfl x₀ y₀ x x' h₁ h₂ h₃
      exact (weilIs_grpPullback_of_comm _ _ _ _ _ m.φ _ _ Xo.univ.t.PP.isLB t.PP.isLB m.cart hL _ k x x' x₀ y₀ _
        h₁.symm h₂.symm).2 h₃
    exact key _ (Category.id_comp _).symm _ _ _ _ (he _) (he _) h

end GlobalTheory.UnivFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteDimensionalOfLeHolSub
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree

namespace GlobalTheory.CuspSecFin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem mem_SS_of_mem_holSub {Comp : Type} (X : Comp → Data E r) (la : ∀ k, Wt (X k).Ψ r)
    {P : FDSec X} (hP : P ∈ holSub X la) (k : Comp) : P k ∈ (X k).SS (la k) := by
  obtain ⟨⟨h0, hadd, hsmul⟩, -⟩ := siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0
  induction hP using Submodule.span_induction with
  | mem P hP => exact hP k
  | zero => exact h0
  | add P Q _ _ h1 h2 => exact hadd _ h1 _ h2
  | smul a P _ h1 => exact hsmul a _ h1

end GlobalTheory.CuspSecFin
end

