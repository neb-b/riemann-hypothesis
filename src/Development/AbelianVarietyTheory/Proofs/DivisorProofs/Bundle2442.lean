module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0154
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1100
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2318
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2359
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2398
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGtOver
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2403
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0074
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1163
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2338
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1148
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2206
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2247
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1181
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedTraitDescentFiniteExt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2379
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0559

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThGOfPolFibField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin

theorem exists_thG_of_symLift (hLaw : Laws) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S)
    {ρ : LB.Gen (P.L.pull (eSec P.A))} (hρ : ρ.IsGen) (k : ℕ) (T' : Over S)
    (th : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T')) (y : T' ⟶ P.A) (hy : y ^ (k ^ 2) = 1)
    (U : ThetaGrp P.A P.L ((k ^ 2 : ℕ) : ℤ) T') (hU : SymLift P.A P.L ((k ^ 2 : ℕ) : ℤ) (k ^ 2) y U) :
    ∃ c, ThG P.A P.L ρ k th y c := by
  have hL := P.isLB
  obtain ⟨α₀, hα₀⟩ := hLaw.mulPull _ P k
  have e₁ : (snd T' P.A).left ≫ (mulA P.A k).left = (snd T' P.A ^ k).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  obtain ⟨α, hα, -⟩ := exists_gen hL (φ' := ![(snd T' P.A).left, (snd T' P.A ^ k).left])
    (ε' := ![((k ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)])
    (fun U _ f => by
      refine Finset.prod_congr rfl fun i _ => ?_
      fin_cases i
      · exact congrArg₂ (fun q n => f q ^ n) (Category.comp_id _) (Nat.cast_pow k 2).symm
      · exact congrArg (fun q => f q ^ (-1 : ℤ)) e₁)
    (LB.pullGen P.L ![𝟙 P.A.left, (mulA P.A k).left] ![(k : ℤ) ^ 2, -1] α₀ (snd T' P.A).left)
    (DVR.pullGen_isGen _ _ _ _ hα₀ _)
  obtain ⟨τ, hτ, -⟩ := exists_gen hL (φ' := fun _ : Fin 1 => (1 : T' ⟶ P.A).left) (ε' := fun _ => ((k ^ 2 : ℕ) : ℤ))
    (fun U _ f => by
      rw [Fintype.prod_unique, Fin.prod_univ_one]
      exact congrArg₂ (fun q n => f q ^ n) rfl (by simp))
    (GeneratorPullback.powGen P.L _ _ (LB.pullGen P.L (fun _ : PUnit => eSec P.A) (fun _ => 1) ρ (toUnit T').left) (k ^ 2))
    (DVR.powGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hρ _) _)
  obtain ⟨s₁, hs₁⟩ := ThetaPtExist.exists_isTwistPull hL (mulT P.A T' k) (snd T' P.A ^ k) (lift_snd _ _)
    ((k ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α hα th
  obtain ⟨s₂, hs₂⟩ := ThetaPtExist.exists_isTwistPull hL (translT P.A U.pt) (translPt P.A U.pt) (lift_snd _ _)
    ((k ^ 2 : ℕ) : ℤ) ((k ^ 2 : ℕ) : ℤ) U.φ U.isGen s₁
  obtain ⟨w, hw⟩ := ThetaPtExist.exists_isValueAt hL s₂ 1 τ hτ
  obtain ⟨e, he⟩ := exists_thG hL hρ k _ rfl (x := fun _ : Unit => y) (fun _ => hy) (th := th) (α := α)
    (U := fun _ => U) (s₂ := fun _ => s₂) (w := fun _ => w) hα hτ hs₁ (fun _ => hU) (fun _ => hs₂) (fun _ => hw)
  exact ⟨_, he ()⟩

theorem exists_thG_of_polFib_field : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m : ℕ) (F : Type) [Field F] (x : Sp F ⟶ S) (θ : SecAt G L x) (p : Over.mk x ⟶ G), Odd m → (m : F) ≠ 0 → PolFib G L g x → p ^ (m ^ 2) = 1 → ∃ c : F, ThG G L ρ m θ p (GlobalTheory.ZH.fn c) := by
  intro S G _ _ L ρ hL hρ g m K _ x θ p hm hK hP hpm
  obtain ⟨P, α, -, hp, w, hw⟩ := hP
  have hLaw : Laws := GlobalTheory.firstFiveLaws.1
  have hL₁ := P.isLB
  have := P.isAb.comm
  obtain ⟨ρ', hρ', hr⟩ := exists_rigidificationPullbackCompatibleIso hp hw hL hL₁ hρ
  let T := baseOver (Sp K)
  let τ : T.left ⟶ (Over.mk x).left := 𝟙 (Sp K)
  haveI : IsIso τ := inferInstanceAs (IsIso (𝟙 (Sp K)))
  have hτ : τ ≫ (Over.mk x).hom = T.hom ≫ x := rfl
  obtain ⟨q, hq, hqm⟩ := exists_torsion_down hp τ hτ p hpm
  let e := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm
  have hu : IsUnit (m : Γ(Spec (CommRingCat.of K), ⊤)) := by
    rw [← map_natCast e]
    exact (IsUnit.mk0 _ hK).map e
  haveI : Subsingleton T.left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  obtain ⟨z₀⟩ : Nonempty T.left := inferInstanceAs (Nonempty (PrimeSpectrum K))
  obtain ⟨V, hV, U, hU⟩ := (hLaw.symLift _ P (m ^ 2) hm.pow (by rw [Nat.cast_pow]; exact hu.pow 2) T q hqm).1 z₀
  obtain rfl : V = ⊤ := eq_top_iff.2 fun y _ => by rwa [Subsingleton.elim y z₀]
  let T' : Over (Sp K) := overRes (T := T) ⊤
  let j₀ : T' ⟶ T := overResι (T := T) ⊤
  haveI : IsIso j₀.left := inferInstanceAs (IsIso (Sp K).topIso.hom)
  let τ' : T'.left ⟶ (Over.mk x).left := j₀.left ≫ τ
  have hτ' : τ' ≫ (Over.mk x).hom = T'.hom ≫ x := by
    rw [Category.assoc, hτ, ← Category.assoc, Over.w j₀]
  have hq' : τ' ≫ p.left = (j₀ ≫ q).left ≫ α := by
    rw [Category.assoc, hq, Over.comp_left, Category.assoc]
  have hqm' : (j₀ ≫ q) ^ (m ^ 2) = 1 := by rw [← MonObj.comp_pow, hqm, MonObj.comp_one]
  obtain ⟨th, hrel⟩ := GlobalTheory.ThetaPtMove.exists_secRel hp τ' hτ' hw hL hL₁ θ
  obtain ⟨c, hc⟩ := exists_thG_of_symLift hLaw P hρ' m T' th (j₀ ≫ q) hqm' U hU
  have up := ThG.up hp τ' hτ' hw hL hL₁ hr hq' hpm hrel hc
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (show Γ(Sp K, ⊤) from (CategoryTheory.inv τ').appTop.hom c), ?_⟩
  convert up using 1
  exact (Scheme.ΓSpecIso (CommRingCat.of K)).hom_inv_id_apply _

end GlobalTheory.UMin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaConstantValueNeZero
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.Sep

theorem UMem.exists_th_ne_zero : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0})
    (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type)
    [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ)
    (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ),
    ∃ b, 𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩ ≠ 0 := by
  intro g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪
  haveI : CharZero V := 𝔪.cn.2.2.2
  haveI : CharZero (FractionRing V) :=
    (RingHom.charZero_iff (IsFractionRing.injective V (FractionRing V))).1 inferInstance
  exact GlobalTheory.ThetaGeneric.exists_th_ne_zero GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2 _ _ X₁.S X₁.ρ
    (FractionRing V) 𝔪.yK

end GlobalTheory.Poinc.Sep

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTie
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc

theorem UDeep.exists_tie (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (_hpq : 1 ≤ Dw.p + Dw.q) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf)
    (X₁ : USetup C) (D : UDeep X₁) (w₁ : UWit X₁) : ∃ w₂ : UWit D.X, D.Comparison₂ w₁ w₂ := by
  obtain ⟨P₀, a, a', ha, ha', hL, hL', hpt⟩ := D.same
  have e : spMap (algebraMap X₁.Ω₁ D.X.Ω₁) ≫ spMap X₁.S.R.val.toRingHom =
      spMap ((algebraMap X₁.Ω₁ D.X.Ω₁).comp X₁.S.R.val.toRingHom) := by
    rw [← Spec.map_comp]; rfl
  have w : a ≫ X₁.ρ.P.A.hom = (P₀.A.hom ≫ spMap (algebraMap X₁.Ω₁ D.X.Ω₁)) ≫ spMap X₁.S.R.val.toRingHom := by
    rw [Category.assoc, e]; exact ha.1.w
  have e₁ := w₁.hα.1.lift_fst _ _ w
  let m : P₀.A.left ⟶ w₁.G.left := w₁.hα.1.lift _ _ w
  have hm : IsGrpPullback P₀.A w₁.G (spMap (algebraMap X₁.Ω₁ D.X.Ω₁)) m :=
    w₁.hα.cancel (ha.congr e.symm e₁.symm) (w₁.hα.1.lift_snd _ _ w)
  have hβ : IsGrpPullback P₀.A Xo.univ.t.G (D.X.uΩ ≫ pullback.fst _ _) (m ≫ w₁.β) :=
    (hm.comp w₁.hβ).congr (by rw [D.pt]; simp only [USetup.uΩ, Category.assoc]) rfl
  have hLβ : LBIso (D.X.ρ.P.L.pull a') (Xo.univ.t.PP.L.pull (m ≫ w₁.β)) :=
    LBIso.trans (pull_isLB D.X.ρ.P.isLB _) P₀.isLB (pull_isLB Xo.univ.t.PP.isLB _) hL'.symm
      (LBIso.trans P₀.isLB (pull_isLB X₁.ρ.P.isLB _) (pull_isLB Xo.univ.t.PP.isLB _) hL
        (GenSpread.lbIso_pull_comp m e₁.symm rfl w₁.hL))
  refine ⟨{ G := P₀.A, α := a', β := m ≫ w₁.β, hα := ha', hβ := hβ, hL := hLβ }, m, hm, rfl, fun x => ?_⟩
  obtain ⟨v, hv, hv'⟩ := hpt x
  refine ⟨v, ?_, hv'⟩
  show v ≫ m ≫ w₁.α = _
  rw [e₁, hv, ← Category.assoc, e]

end GlobalTheory.UPoinc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusComponentsOfUnimodularTensor
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

namespace GlobalTheory.Mum.TensTor

theorem gtRelV_onto (F : Type) [Field F] (N N' : NumD F) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F) (hT : TensFacts W φ e wv)
    (hdet : IsUnit (W + W.transpose).det) (v' : N'.Gt) : ∃ vs : Fin r → N.Gt, GtRelV W φ e wv v' vs :=
  Vonto.of_exist_mul hT hdet (VExist.gtRelV_exists F N N' W φ e wv hT)
    (gtRelV_mul F N N' W φ e wv hT) v'

end GlobalTheory.Mum.TensTor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusPt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mum

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

namespace Ext

open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht GlobalTheory.TorusModel GlobalTheory.TorusExt GlobalTheory.Serre

theorem exists_torusPt {T : Over (Sp R)} (x : T ⟶ splitTorus (Sp R) D.X) : ∃ g : GtPt D T, g.b = 1 ∧
    ∀ (χ : D.X) (Z : Scheme.{0}) (r : Z ⟶ T.left) y J, Good D.P.L y J →
      (val (g.s χ) r y J).val = gs r y ⊤ ((coord x).hom (AddMonoidAlgebra.single χ 1)) := by
  let u : Multiplicative D.X →* Γ(T.left, ⊤) :=
    { toFun := fun χ => (coord x).hom (AddMonoidAlgebra.single χ.toAdd 1)
      map_one' := Diag.coord_single_zero x
      map_mul' := fun a b => Diag.coord_single_add x _ _ }
  let v : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (Y := T.left) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim) := fun χ =>
    ⟨fun _ => res le_top (u.toHomUnits (Multiplicative.ofAdd χ))⟩
  have hv : ∀ χ (Z : Scheme.{0}) (r : Z ⟶ T.left) y J, Good D.P.L y J →
      val (v χ) r y J = gm r y ⊤ (u.toHomUnits (Multiplicative.ofAdd χ)) := fun χ Z r y J hJ =>
    gm_res r y _ (hJ.mem PEmpty.elim r) _
  obtain ⟨g, hb, hg⟩ := exists_pt (1 : T ⟶ D.P.A) v (fun χ i j => by
      obtain rfl : i = j := funext fun k => k.elim
      have e : (LB.LinComb D.P.L (Y := T.left) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim).g i i = 1 := by
        dsimp only [LB.LinComb]
        erw [Fintype.prod_empty]
        rfl
      rw [e, _root_.one_mul])
    (fun χ U _ h => by
      rw [prod_pt, _root_.mul_one, Fintype.prod_empty, inv_mul_cancel, _root_.one_mul, mul_inv_cancel])
    (fun y J hJ => by rw [hv _ _ _ _ _ hJ, ofAdd_zero, map_one, map_one])
    (fun χ χ' y J hJ => by
      have C : IsCub (th D (T := T) y J) := isCub_cubV D.cub hJ
      rw [C.face₃, _root_.mul_one, hv _ _ _ _ _ hJ, hv _ _ _ _ _ hJ, hv _ _ _ _ _ hJ, ofAdd_add, map_mul, map_mul])
  exact ⟨g, hb, fun χ Z r y J hJ => by
    rw [hg _ _ _ _ _ hJ, hv _ _ _ _ _ hJ]; exact (gs_unit r y ⊤ trivial _).symm⟩

variable (Y : Ext D)

theorem pt_b {T : Over (Sp R)} (x : T ⟶ Y.H) : (Y.Φ T x).b = x ≫ Y.q := by
  have h := ((isPull_iff _ _ _).1 (Y.rep.1 T Y.H x (𝟙 _))).1
  rwa [Category.comp_id] at h

def torI : splitTorus (Sp R) D.X ⟶ Y.H :=
  (Y.Φ _).symm (exists_torusPt (D := D) (𝟙 _)).choose

theorem torI_pt {T : Over (Sp R)} (x : T ⟶ splitTorus (Sp R) D.X) : (Y.Φ T (x ≫ Y.torI)).b = 1 ∧
    ∀ (χ : D.X) y J, Good D.P.L y J →
      (cv (Y.Φ T (x ≫ Y.torI)) χ y J).val = gs (𝟙 _) y ⊤ ((coord x).hom (AddMonoidAlgebra.single χ 1)) := by
  obtain ⟨h₁, h₂⟩ := (isPull_iff _ _ _).1 (Y.rep.1 T _ x Y.torI)
  obtain ⟨e₁, e₂⟩ := (exists_torusPt (D := D) (𝟙 _)).choose_spec
  have e : Y.Φ _ Y.torI = (exists_torusPt (D := D) (𝟙 _)).choose := Equiv.apply_symm_apply _ _
  rw [e] at h₁ h₂
  refine ⟨by rw [h₁, e₁, MonObj.comp_one], fun χ y J hJ => ?_⟩
  rw [h₂ χ y J hJ, e₂ χ _ _ y J hJ]
  conv_rhs => rw [← Category.comp_id x, coord_comp]
  exact (gs_eq x.left y ⊤ trivial _).trans (gs_eq (𝟙 _) y ⊤ trivial _).symm

theorem torI_q : Y.torI ≫ Y.q = 1 := by
  have h := (Y.torI_pt (𝟙 _)).1
  rwa [pt_b, Category.id_comp] at h

theorem isMonHom_torI : IsMonHom Y.torI :=
  isMonHom_of_mul _ fun T x x' => (Y.Φ T).injective <| by
    refine isAdd_unique ((TorusModel.isAdd_iff _ _ _).2 ⟨?_, fun χ y J hJ => Units.ext ?_⟩) (Y.rep.2 T _ _)
    · rw [(Y.torI_pt _).1, (Y.torI_pt _).1, (Y.torI_pt _).1, _root_.mul_one]
    · have C : IsCub (th D (T := T) y J) := isCub_cubV D.cub hJ
      rw [(Y.torI_pt x').1, C.face₃, _root_.mul_one, Units.val_mul, (Y.torI_pt _).2 χ y J hJ, (Y.torI_pt _).2 χ y J hJ,
        (Y.torI_pt _).2 χ y J hJ]
      exact (congrArg (gs _ y ⊤) (Diag.coord_mul x x' χ)).trans (gs_mul (𝟙 _) y ⊤ trivial _ _)

theorem isKernel_torI : IsPullback Y.torI (toUnit _) Y.q η[D.P.A] := by
  have ex : ∀ {T : Over (Sp R)} y, ∃ J, Good D.P.L (Z := T.left) y J := fun y => by
    choose I hI using fun χ => exists_chart D.P.isLB ((χ : _ ⟶ D.P.A.left) y)
    exact ⟨I, hI⟩
  refine Diag.isPullback_toUnit_of_lift _ Y.torI_q (fun {T} a b h => Diag.hom_ext fun χ => fn_ext fun y _ => ?_)
    fun {T} x hx => ?_
  · obtain ⟨J, hJ⟩ := ex y
    exact ((Y.torI_pt a).2 χ y J hJ).symm.trans (h ▸ (Y.torI_pt b).2 χ y J hJ)
  · have hb : (Y.Φ T x).b = 1 := (Y.pt_b x).trans hx
    have hF : ∀ χ, FormEq (DegPre.gtφT D T (Y.Φ T x).b χ) DegPre.gtε (K' := PEmpty.{1}) PEmpty.elim PEmpty.elim :=
      fun χ U _ h => by
        rw [prod_pt, hb, _root_.mul_one, Fintype.prod_empty, inv_mul_cancel, _root_.one_mul, mul_inv_cancel]
    choose s _ vs using fun χ => exists_gen D.P.isLB (hF χ) _ ((Y.Φ T x).isGen χ)
    have le : (⊤ : T.left.Opens) ≤ LB.wchart D.P.L (K := PEmpty.{1}) PEmpty.elim PEmpty.elim :=
      fun _ _ => Set.mem_iInter.2 fun k => k.elim
    let u : D.X → Γ(T.left, ⊤)ˣ := fun χ => res le ((s χ).s PEmpty.elim)
    have hu : ∀ χ y J, Good D.P.L y J → gs (𝟙 _) y ⊤ (u χ).val = (cv (Y.Φ T x) χ y J).val := fun χ y J hJ =>
      (gs_unit _ y ⊤ trivial _).trans (congrArg Units.val ((gm_res _ y le trivial _).trans
        ((val_of (s χ) _ y J PEmpty.elim fun k => k.elim).symm.trans (vs χ _ _ y J hJ))))
    let g : Multiplicative D.X →* Γ(T.left, ⊤) :=
      { toFun := fun χ => (u χ.toAdd).val
        map_one' := fn_ext fun y _ => by
          obtain ⟨J, hJ⟩ := ex y
          refine (hu 0 y J hJ).trans ?_
          rw [cv_zero _ hJ, gs_eq _ y ⊤ trivial, map_one, map_one, Units.val_one]
        map_mul' := fun a b => fn_ext fun y _ => by
          obtain ⟨J, hJ⟩ := ex y
          have C : IsCub (th D (T := T) y J) := isCub_cubV D.cub hJ
          have e := cv_add (Y.Φ T x) hJ a.toAdd b.toAdd
          rw [hb, C.face₃, _root_.mul_one] at e
          refine (hu _ y J hJ).trans (Eq.trans ?_ (gs_mul _ y ⊤ trivial _ _).symm)
          exact (congrArg Units.val e).trans (congrArg₂ (· * ·) (hu _ y J hJ) (hu _ y J hJ)).symm }
    refine ⟨Diag.ofChar T g, (Y.Φ T).injective (pt_ext ((Y.torI_pt _).1.trans hb.symm) fun χ y J hJ => Units.ext ?_)⟩
    exact ((Y.torI_pt _).2 χ y J hJ).trans ((congrArg (gs _ y ⊤) (Diag.coord_ofChar T g χ)).trans (hu χ y J hJ))

theorem cv_torI {Z : Over (Sp R)} (t : Z ⟶ splitTorus (Sp R) D.X) (χ : D.X) (z : Z.left) J (hJ : Good D.P.L z J) :
    cv (Y.Φ Z (t ≫ Y.torI)) χ z J = gm t.left z ⊤ (charUnit (Sp R) D.X χ) := by
  have hc : t.left.appTop.hom (charUnit (Sp R) D.X χ).val = (coord t).hom (AddMonoidAlgebra.single χ 1) := by
    rw [GlobalTheory.SplitTorus.charUnit_val]
    conv_rhs => rw [← Category.comp_id t, coord_comp]
    rfl
  refine Units.ext (((Y.torI_pt t).2 χ z J hJ).trans ?_)
  rw [← gs_unit t.left z ⊤ trivial, ← hc]
  exact (gs_eq (𝟙 _) z ⊤ trivial _).trans (gs_eq t.left z ⊤ trivial _).symm

theorem cv_torI_mul {Z : Over (Sp R)} (t : Z ⟶ splitTorus (Sp R) D.X) (g : Z ⟶ Y.H) (χ : D.X) (z : Z.left) J
    (hJ : Good D.P.L z J) :
    cv (Y.Φ Z ((t ≫ Y.torI) * g)) χ z J = gm t.left z ⊤ (charUnit (Sp R) D.X χ) * cv (Y.Φ Z g) χ z J := by
  have h := ((TorusModel.isAdd_iff _ _ _).1 (Y.rep.2 Z (t ≫ Y.torI) g)).2 χ z J hJ
  have C : IsCub (th D (T := Z) z J) := isCub_cubV D.cub hJ
  rw [(Y.torI_pt t).1, C.face₂, _root_.mul_one, Y.cv_torI t χ z J hJ] at h
  exact h

end Ext

theorem ext_torus : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (Y : Ext D), ∃ i : splitTorus (Sp R) D.X ⟶ Y.H,
    IsMonHom i ∧ IsPullback i (toUnit _) Y.q η[D.P.A] ∧ ∀ (χ : D.X) (Z : Over (Sp R)) (t : Z ⟶ splitTorus (Sp R) D.X)
      (g : Z ⟶ Y.H) (z : Z.left) J, Good D.P.L z J →
        val ((Y.Φ Z ((t ≫ i) * g)).s χ) (𝟙 _) z J = gm t.left z ⊤ (charUnit (Sp R) D.X χ) * val ((Y.Φ Z g).s χ) (𝟙 _) z J :=
  fun _ _ _ _ Y => ⟨Y.torI, Y.isMonHom_torI, Y.isKernel_torI, fun χ _ t g z J hJ => Y.cv_torI_mul t g χ z J hJ⟩

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistNefSquarefreeMonomialsSmall
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef GlobalTheory.CechPic GlobalTheory.Points GlobalTheory.ChartGlue

namespace GlobalTheory.HSNef.BoxTwist

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}

theorem isometric_shift_tens (N M : HermLB p) (u : ℝ) :
    ((N.tens M).shift (fun _ => u) fun _ => rfl).Isometric (N.tens (M.shift (fun _ => u) fun _ => rfl)) :=
  HermLB.isometric_of_chart id (fun _ => le_rfl) (fun _ _ _ _ _ => rfl) fun _ _ _ _ => (add_assoc _ _ _).symm

variable [IsIntegral X]

theorem isRatSec_const_mul {B : LB X} {r : B.ι → X.functionFieldˣ} (hr : IsRatSec B r) (g : X.functionFieldˣ) :
    IsRatSec B fun i => g * r i := fun a b h => by
  beta_reduce
  rw [Units.val_mul, Units.val_mul, hr a b h]
  ring

theorem exists_pair_small (Q : Pair p) (W : HermLB p) (g : X.functionField) (hg : g ≠ 0) (u : ℝ) :
    ∃ P : Pair p, P.L = W ∧ P.A = Q.A.shift (fun _ => u) (fun _ => rfl) ∧
      ∀ f, g * f ∈ Q.Bl 0 1 (Real.exp u) → f ∈ P.Bl 0 1 1 := by
  obtain ⟨r, hr⟩ := exists_isRatSec W.isLB
  let P : Pair p := ⟨W, Q.A.shift (fun _ => u) (fun _ => rfl), r, fun j => Units.mk0 g hg * Q.r' j, hr,
    isRatSec_const_mul Q.hr' _⟩
  have e (f i i' j) : P.loc 0 1 f i j = Q.loc 0 1 (g * f) i' j := by
    simp only [Pair.loc, P, zpow_zero, zpow_one, Units.val_mul, Units.val_mk0]
    ring
  refine ⟨P, rfl, rfl, fun f hf => ⟨fun x i j _ hj => ?_, fun σ y => ?_⟩⟩
  · obtain ⟨i', hi'⟩ := exists_chart Q.L.isLB x
    rw [e f i i' j]
    exact hf.1 x i' j hi' hj
  · have h := hf.2 σ y
    have e' : P.nu 0 1 σ y f = Q.nu 0 1 σ y (g * f) * Real.exp (-u) := by
      rw [Pair.nu, Pair.nu, e f _ (pick (Q.L.φ σ).isLB y), mul_assoc, ← Real.exp_add]
      congr 2
      have : (P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y = (Q.A.φ σ).φ (pick (Q.A.φ σ).isLB y) y + 2 * u := rfl
      rw [this]
      push_cast
      ring
    rw [e']
    calc _ ≤ Real.exp u * Real.exp (-u) := mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]

theorem exists_twist : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (N : HermLB p) (x : Fin D → X.functionField), ∃ H : HermLB p, (N.tens H).IsNef D ∧ ∀ W : HermLB p, ∃ P : Pair p, P.L = W ∧ P.A = H ∧ ∀ S : Finset (Fin D), ∏ i ∈ S, x i ∈ P.Bl 0 1 1 := by
  intro hC k _ X _ p D hX N x
  obtain ⟨A, hA, hAn, -⟩ := GlobalTheory.AmpleNefSmall.exists_ample_nef_smallSec hC k X p D hX
  obtain ⟨P, rfl, rfl⟩ := exists_pair N A
  obtain ⟨c, g, -, hg, -, hgf⟩ := _root_.GlobalTheory.HSNef.Den.exists_clear_denominators k X p D hX P hA (-1) (Finset (Fin D)) fun S => ∏ i ∈ S, x i
  choose v hv0 hv using fun S => _root_.GlobalTheory.HSNef.bounded_norm k X p D hX P (-1) c _ (hgf S)
  let u : ℝ := ∑ S, v S
  have hu : 0 ≤ u := Finset.sum_nonneg fun S _ => hv0 S
  have hvu (S) : v S ≤ u := Finset.single_le_sum (fun S _ => hv0 S) (Finset.mem_univ S)
  let M : HermLB p := P.L.dual.tens (P.A.pow c)
  obtain ⟨h₁, h₂, -⟩ := Pair.rep_base k X p P
  have hM : P.Rep (-1) c M := by
    simpa using Pair.rep_tens k X p P _ _ _ _ _ _ (Pair.rep_dual k X p P _ _ _ h₁) (Pair.rep_pow k X p P _ _ _ c h₂)
  obtain ⟨Q, -, hQ, hB⟩ := _root_.GlobalTheory.HSNef.change_pair k X p P _ _ _ _ M M hM hM
  have hi : (P.A.pow c).Isometric (P.L.tens M) :=
    HermLB.icls_eq_iff.1 (by simp only [M, HermLB.icls_tens, HermLB.icls_dual]; abel)
  have hn : (P.L.tens M).IsNef D :=
    (_root_.GlobalTheory.HSNef.isometric_keeps hC k X p D hX _ _ hi).2.1 (GlobalTheory.NefPow.isNef_pow hC k X p D hX _ c hAn)
  refine ⟨M.shift (fun _ => u) fun _ => rfl, (_root_.GlobalTheory.HSNef.isometric_keeps hC k X p D hX _ _ (isometric_shift_tens _ _ u)).2.1
    (GlobalTheory.NefShift.isNef_shift_nonneg k X p D hX _ u hu hn), fun W => ?_⟩
  obtain ⟨R, hR, hR', h⟩ := exists_pair_small Q W g hg u
  refine ⟨R, hR, by rw [hR', hQ], fun S => h _ ?_⟩
  rw [hB]
  simp only [zero_mul, one_mul, zero_add]
  exact ⟨(hv S).1, fun σ y => ((hv S).2 σ y).trans (Real.exp_le_exp.2 (hvu S))⟩

end GlobalTheory.HSNef.BoxTwist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedTraitDescentFiniteExtStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformisedTrait_descent_finite_ext : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (D' : DegData W (maximalIdeal W)) (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (A' : PolAV (Sp (FractionRing W))), Nonempty (IsPullDeg φ D.toPre D'.toPre) → IsSemiAbelian G' → Nonempty (Unif (maximalIdeal W) D' A' G') → (letI := A'.isAb.comm; GlobalTheory.ZH.HypS A'.A A'.L) → ∀ (A₀ : PolAV (Sp (Kb R))) (e₀ : Kb R →+* Kb W), (∀ r, e₀ (algebraMap (FractionRing R) (Kb R) (algebraMap R _ r)) = algebraMap (FractionRing W) (Kb W) (algebraMap W _ (φ r))) → (letI := A₀.isAb.comm; GlobalTheory.ZH.HypS A₀.A A₀.L) → GeomIso A₀ A' e₀ (algebraMap (FractionRing W) (Kb W)) → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : R →+* R₁) (D₁ : DegData R₁ (maximalIdeal R₁)) (A : PolAV (Sp (FractionRing R₁))), FinExt ρ ∧ Nonempty (IsPullDeg ρ D.toPre D₁.toPre) ∧ (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) ∧ UniTrait D₁.toPre A := by
  first | exact @GlobalTheory.Mum.ClosureDescent.exists_uniTrait | exact GlobalTheory.Mum.ClosureDescent.exists_uniTrait | (intros; apply GlobalTheory.Mum.ClosureDescent.exists_uniTrait <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleTrivialOnPullbackSquaresOfLocalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.TrivLocus
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleTrivialOnPullbackSquares_of_local : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (N : LB A.left), IsAbelianScheme A → N.IsLB → Out.Rigidified A N → ∀ (T : Scheme.{0}) (t : T ⟶ S), (∀ τ : T, ∃ V : T.Opens, τ ∈ V ∧ TrivCond A N V (V.ι ≫ t)) → TrivCond A N T t := by
  first | (exact @GlobalTheory.TrivLocus.trivCond_of_local) | (exact GlobalTheory.TrivLocus.trivCond_of_local) | (intros; apply GlobalTheory.TrivLocus.trivCond_of_local  <;> assumption)
end

