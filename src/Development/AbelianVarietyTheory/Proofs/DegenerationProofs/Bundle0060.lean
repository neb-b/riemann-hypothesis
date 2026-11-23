module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDenseClosedPointsChartSplitting
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

noncomputable section
namespace GlobalTheory.ZJ.DenseSplit

theorem exists_ringHom_kb (F : Type) [Field F] [Finite F] :
    ∃ (p : ℕ) (_ : Fact p.Prime), Nonempty (F →+* kb p) := by
  obtain ⟨p, hp⟩ := CharP.exists F
  have hpp : Fact p.Prime := ⟨CharP.char_is_prime F p⟩
  have : CharP (kb p) p := (CharP.charP_iff_prime_eq_zero hpp.out).mpr
    (GlobalTheory.natCast_self_residueField_padicAlgCl_eq_zero p)
  have := (kb_isAlgClosed_and_conj p).1
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  letI : Algebra (ZMod p) (kb p) := ZMod.algebra _ p
  have : Module.Finite (ZMod p) F := Module.Finite.of_finite
  exact ⟨p, hpp, ⟨(IsAlgClosed.lift (R := ZMod p) (S := F) (M := kb p)).toRingHom⟩⟩

theorem isNoetherianRing_of_lft (R : Type) [CommRing R] (π : Sp R ⟶ Sp ℤ) [LocallyOfFiniteType π] :
    IsNoetherianRing R := by
  have : IsLocallyNoetherian (Sp R) := LocallyOfFiniteType.isLocallyNoetherian π
  exact isLocallyNoetherian_Spec.mp this

theorem exists_dense_splitOn : ∀ (C : Core) (L : C.Law), C.HasTests → C.HasCharts → letI := L.grp; letI := L.comm; ∀ z : C.Z, ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsNoetherianRing R) (t : Sp R ⟶ C.Z) (_ : IsImmersion t), t (⊥ : PrimeSpectrum R) = z ∧ ∃ (Ch : Charts ((Over.pullback t).obj C.GG).left) (d : ℕ) (c : Fin d → Ch.Cl) (Sg : Set (Sp R)), Dense Sg ∧ Ch.SplitOn c Sg ∧ ∀ x ∈ Sg, IsClosed ({t x} : Set C.Z) := by
  intro C L hT hC z
  letI := L.grp; letI := L.comm
  obtain ⟨R, _, _, t, _, htz, Ch, hCh⟩ := hC z
  have := C.lft
  have := C.flat
  obtain ⟨-, hfin, -, -, hdense⟩ := GlobalTheory.jacobson_closedPoints_tools_int (Sp R) (t ≫ C.π)
  refine ⟨R, inferInstance, inferInstance, isNoetherianRing_of_lft R (t ≫ C.π), t, inferInstance, htz, Ch, ?_⟩
  let κ := Σ d : Fin (C.g + 1), (Fin d → Ch.Cl)
  let Sg : κ → Set (Sp R) := fun k => {x | Charts.SplitOn (G := (Over.pullback t).obj C.GG) Ch k.2 {x} ∧
    IsClosed ({t x} : Set C.Z)}
  obtain ⟨k, hk⟩ := hdense κ Sg inferInstance (by
    intro x hx
    have := hfin x hx
    obtain ⟨p, hp, ⟨r⟩⟩ := exists_ringHom_kb ((Sp R).residueField x)
    let xb : Sp (kb p) ⟶ Sp R := Spec.map (CommRingCat.ofHom r) ≫ (Sp R).fromSpecResidueField x
    have hxb : ∀ s, xb s = x := fun s => by
      have : xb s ∈ Set.range ((Sp R).fromSpecResidueField x) := ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
      rwa [Scheme.range_fromSpecResidueField] at this
    have hrange : Set.range xb = {x} := by
      ext w
      exact ⟨fun ⟨s, hs⟩ => hs ▸ hxb s, fun hw => ⟨IsLocalRing.closedPoint (kb p), (hxb _).trans hw.symm⟩⟩
    obtain ⟨hlift, hcl⟩ := GlobalTheory.exists_integral_point_lifting_residue_point C.Z C.π C.U C.ne p
    obtain ⟨y, hy, hyU⟩ := hlift (xb ≫ t)
    obtain ⟨τ⟩ := hT p y hyU
    have e : (rPt p ≫ spMap τ.j) ≫ τ.y₀ = xb ≫ t := by rw [Category.assoc, τ.fac, hy]
    have g1 : IsGrpPullback ((Over.pullback (rPt p ≫ spMap τ.j)).obj τ.H) C.GG (xb ≫ t)
        (pullback.fst τ.H.hom (rPt p ≫ spMap τ.j) ≫ τ.f) :=
      ((isGrpPullback_pullback _ _).comp (L.test p y τ)).congr e rfl
    have g2 : IsGrpPullback ((Over.pullback t).obj C.GG) C.GG t (pullback.fst C.GG.hom t) :=
      isGrpPullback_pullback _ _
    have g3 : IsGrpPullback ((Over.pullback xb).obj ((Over.pullback t).obj C.GG)) ((Over.pullback t).obj C.GG) xb
        (pullback.fst ((Over.pullback t).obj C.GG).hom xb) :=
      isGrpPullback_pullback _ _
    let h : pullback τ.H.hom (rPt p ≫ spMap τ.j) ⟶ pullback C.GG.hom t :=
      pullback.lift (pullback.fst _ _ ≫ τ.f) (pullback.snd _ _ ≫ xb) (g1.1.w.trans (Category.assoc _ _ _).symm)
    have h1 : h ≫ pullback.fst _ _ = pullback.fst _ _ ≫ τ.f := pullback.lift_fst _ _ _
    have h2 : h ≫ pullback.snd _ _ = pullback.snd _ _ ≫ xb := pullback.lift_snd _ _ _
    have g4 : IsGrpPullback ((Over.pullback (rPt p ≫ spMap τ.j)).obj τ.H) ((Over.pullback t).obj C.GG) xb h :=
      g2.cancel (g1.congr rfl h1.symm) h2
    have ha : IsAffineHom h := MorphismProperty.of_isPullback (P := @IsAffineHom) g4.1.flip inferInstance
    have ha' : IsAffineHom (pullback.fst ((Over.pullback t).obj C.GG).hom xb) :=
      MorphismProperty.of_isPullback (P := @IsAffineHom) g3.1.flip inferInstance
    obtain ⟨d, hd, c, hs⟩ := hCh p y τ xb hy.symm h h1 h2
    have w : pullback.fst ((Over.pullback t).obj C.GG).hom xb ≫ ((Over.pullback t).obj C.GG).hom =
      ((Over.pullback xb).obj ((Over.pullback t).obj C.GG)).hom ≫ xb := g3.1.w
    let φ := g4.1.lift _ _ w
    have f1 : φ ≫ h = _ := g4.1.lift_fst _ _ w
    have f2 : φ ≫ _ = _ := g4.1.lift_snd _ _ w
    have g5 : IsGrpPullback ((Over.pullback xb).obj ((Over.pullback t).obj C.GG))
        ((Over.pullback (rPt p ≫ spMap τ.j)).obj τ.H) (𝟙 _) φ :=
      g4.cancel (g3.congr (Category.id_comp _).symm f1.symm) (f2.trans (Category.comp_id _).symm)
    have hφ : IsAffineHom φ := MorphismProperty.of_isPullback (P := @IsAffineHom) g5.1.flip inferInstance
    have hs' := @SplitPull.pull_pull_and_split_pull.2 (kb p) (kb p) _ _
      ((Over.pullback (rPt p ≫ spMap τ.j)).obj τ.H) _ ((Over.pullback xb).obj ((Over.pullback t).obj C.GG)) _
      (𝟙 _) φ hφ g5 (Ch.pull h) d c hs
    refine ⟨⟨⟨d, Nat.lt_succ_of_le hd⟩, c⟩, ?_, ?_⟩
    · rintro _ rfl
      refine ⟨kb p, inferInstance, xb, ha', hrange, ?_⟩
      have key : ∀ (ψ : ((Over.pullback xb).obj ((Over.pullback t).obj C.GG)).left ⟶ pullback C.GG.hom t)
          [IsAffineHom ψ], φ ≫ h = ψ →
          Charts.Split (H := (Over.pullback xb).obj ((Over.pullback t).obj C.GG)) (Ch.pull ψ) c := by
        intro ψ _ hψ
        subst hψ
        exact hs'
      exact @key _ ha' f1
    · have := hcl (xb ≫ t) (IsLocalRing.closedPoint (kb p))
      exact ((Scheme.Hom.comp_apply xb t _).trans (congrArg t (hxb _))) ▸ this)
  exact ⟨k.1, k.2, Sg k, hk, fun x hx => hx.1 x rfl, fun x hx => hx.2⟩

end GlobalTheory.ZJ.DenseSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGoodTorsionTranslateGeometricPoint
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal

noncomputable section
namespace GlobalTheory.ThetaReal
open GlobalTheory.ThetaPtMove

theorem exists_good_translate : Laws → ∀ (S : Scheme.{0}) (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (n : ℕ), 2 ≤ n → (n : K) ≠ 0 → ∀ (th : LB.Sec (LPow P.A P.L 1 (baseOver S))), UnivBasis P 1 (fun _ : Fin 1 => SecM.ofSec P.A th) → ∀ a : Over.mk x ⟶ P.A, ∃ y : Over.mk x ⟶ P.A, y ^ n = 1 ∧ ∀ (z : baseOver S ⟶ P.A) (τ : LB.Gen (LB.LinComb P.L (Y := (baseOver S).left) (K := Fin 1) (fun _ => z.left) (fun _ => 1))) (v : Γ((baseOver S).left, ⊤)), (Over.homMk x (by simp) : Over.mk x ⟶ baseOver S) ≫ z = a * y → τ.IsGen → IsValueAt P.A P.L 1 th z τ v → v ≠ 0 := by
  intro hL S P K _ _ x n hn hK th hth a
  let β : Over.mk x ⟶ baseOver S := Over.homMk x (by simp)
  have : IsAffine (Over.mk x).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of K)))
  have : Nontrivial Γ((Over.mk x).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  obtain ⟨c, hc⟩ := hth (Over.mk x) β
  have h₀ : SecM.ofSec P.A (VVRank.pullS P.A 1 β th) ≠ 0 := fun e => c.ne_zero 0 ((hc 0).trans e)
  obtain ⟨y, hy, hu⟩ := GlobalTheory.UT.ExactTerm.exists_good_point hL.goodPt hL.polBaseChange P x hn hK _ h₀ a
  refine ⟨y, hy, fun z τ v hz _ hv h0 => ?_⟩
  let p : (Over.mk x).left := IsLocalRing.closedPoint K
  obtain ⟨J, hJ⟩ := GlobalTheory.ConstFam.exists_good' P.isLB p
  have q := hu p J hJ
  have e : (ptSecT P.A (a * y)).left ≫ (β ▷ P.A).left = β.left ≫ (ptSecT P.A z).left := by
    rw [← Over.comp_left, ← Over.comp_left, ← hz]
    congr 1
    ext1 <;> simp [ptSecT, β]
  rw [VVRank.sv_pullS _ _ _ _ _ _ hJ, e, sv_of_isValueAt hv _ p hJ, h0,
    GlobalTheory.UT.ExactTerm.gs_zero' β.left p ⊤ trivial, MulZeroClass.zero_mul] at q
  exact not_isUnit_zero q

end GlobalTheory.ThetaReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsTorsFrameOfSymLift
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal
noncomputable section
namespace GlobalTheory.TorsFrame

open CommPairing GlobalLift ThetaCoord

theorem val_powGen {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (n : ℕ) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) :
    val (GeneratorPullback.powGen L φ ε t n) r z J = val t r z J ^ n := map_pow _ _ _

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}

theorem exists_pow_two (hL : L.IsLB) {Y : Scheme.{0}} {f g : Y ⟶ A.left} {k : ℤ} (m : ℕ)
    {u : LB.Gen (LB.LinComb L (K := Fin 2) ![f, g] ![k, -k])} (hu : u.IsGen) :
    ∃ u' : LB.Gen (LB.LinComb L (K := Fin 2) ![f, g] ![m * k, -(m * k)]), u'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → val u' r z J = val u r z J ^ m := by
  obtain ⟨t, ht, hv⟩ := exists_gen hL (φ' := ![f, g]) (ε' := ![m * k, -(m * k)])
    (fun U _ h => by
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, mul_neg])
    (GeneratorPullback.powGen L _ _ u m) (DVR.powGen_isGen _ _ _ _ hu _)
  exact ⟨t, ht, fun Z r z J hJ => (hv Z r z J hJ).trans (val_powGen _ _ _ _ _)⟩

theorem exists_symLift_pow (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {k : ℤ} {q : ℕ} {x : T ⟶ A}
    {θ : ThetaGrp A L k T} (H : SymLift A L k q x θ) (m : ℕ) :
    ∃ θ' : ThetaGrp A L (m * k) T, SymLift A L (m * k) q x θ' ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J → tval θ' r z J = tval θ r z J ^ m := by
  obtain ⟨ν, hν, -⟩ := H.sym
  obtain ⟨u, hu, vu⟩ := exists_pow_two hL m (u := θ.φ) θ.isGen
  obtain ⟨ν', hν', vν⟩ := exists_pow_two hL m (u := ν) hν
  have vu' : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
      tval (⟨θ.pt, u, hu⟩ : ThetaGrp A L (m * k) T) r z J = tval θ r z J ^ m := vu
  have vν' : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
      nval (k := m * k) ν' r z J = nval ν r z J ^ m := vν
  refine ⟨⟨θ.pt, u, hu⟩, symLift_of_tval hL H.pt_eq (ν := ν') hν' (fun T' π z J hJ p => ?_)
    (fun T' π z J hJ p => ?_), vu'⟩
  · rw [Finset.prod_congr rfl fun j _ => vu' _ _ z J hJ, Finset.prod_pow, prod_tval H π hJ p, one_pow]
  · rw [vu' _ _ z J hJ, vu' _ _ z J hJ, vν' _ _ z J hJ, vν' _ _ z J hJ, ← inv_pow, ← mul_pow, ← mul_pow, ← mul_pow,
      sym_tval hG hA hL H hν π hJ p, one_pow]

theorem eSec_hom : eSec A ≫ A.hom = 𝟙 S := Over.w η[A]

theorem eSec_mulA (n : ℕ) : eSec A ≫ (mulA A n).left = eSec A := by
  have e : η[A] = (1 : 𝟙_ (Over S) ⟶ A) := by rw [Hom.one_def, toUnit_unit, Category.id_comp]
  rw [eSec, ← Over.comp_left, MonObj.comp_pow, Category.comp_id, e, one_pow]

theorem one_left : (1 : T ⟶ A).left = T.hom ≫ eSec A := rfl

theorem exists_norm (hL : L.IsLB) {rig : LB.Gen (L.pull (eSec A))} (hr : rig.IsGen) {n : ℕ}
    {α₀ : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, (mulA A n).left] ![(n : ℤ) ^ 2, -1])} (h₀ : α₀.IsGen) :
    ∃ α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, (mulA A n).left] ![(n : ℤ) ^ 2, -1]), α.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ S) (z : Z) (J), Good L z J → val α (r ≫ eSec A) z J =
        val (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) rig r z J ^ (n ^ 2) *
          (val (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) rig r z J)⁻¹ := by
  obtain ⟨t, ht, hv⟩ := exists_gen hL (φ' := ![𝟙 A.left, (mulA A n).left]) (ε' := ![(n : ℤ) ^ 2, -1])
    (fun U _ h => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, eSec_mulA, Category.comp_id]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen L _ _ _ _ α₀ (LB.pullGen L _ _ (LB.mulGen L _ _ _ _
      (LB.mulGen L _ _ _ _ (GeneratorPullback.powGen L (fun _ : PUnit => eSec A) (fun _ => 1) rig (n ^ 2))
        (LB.invGen L (fun _ : PUnit => eSec A) (fun _ => 1) rig))
      (LB.invGen L _ _ (LB.pullGen L _ _ α₀ (eSec A)))) A.hom))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ h₀ (DVR.pullGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.powGen_isGen _ _ _ _ hr _) (DVR.invGen_isGen _ _ _ _ hr))
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ h₀ _))) _))
  refine ⟨t, ht, fun Z r z J hJ => ?_⟩
  have e : (r ≫ eSec A) ≫ A.hom = r := by rw [Category.assoc, eSec_hom, Category.comp_id]
  rw [hv _ _ z J hJ, val_mul hJ, val_pull hJ, e, val_mul hJ, val_mul hJ, val_inv, val_inv, val_pull hJ, val_powGen,
    mul_comm, inv_mul_cancel_right]

theorem val_rigT (rig : LB.Gen (L.pull (eSec A))) {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) {J} (hJ : Good L z J) :
    val (rigT A L rig T 1) r z J =
      val (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) rig (r ≫ T.hom) z J := by
  rw [val_of (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) rig (r ≫ T.hom) z J
    (fun _ => J (r ≫ T.hom ≫ eSec A)) (fun _ => by rw [Category.assoc])]
  have hm := hJ.mem (fun _ : Fin 1 => T.hom ≫ eSec A) r
  refine (map_zpow _ _ _).trans ((zpow_one _).trans ((gm_res r z _ hm _).trans ?_))
  exact gm_pull r T.hom z _ (show T.hom (r z) ∈ LB.wchart L (fun _ : PUnit => eSec A)
    (fun _ => J (r ≫ T.hom ≫ eSec A)) from Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hm 0) _

theorem tval_pow (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {ν : LB.Gen (negLB A L 1 T)}
    (hν : ν.IsGen) {n : ℕ} (hn : Odd n)
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, (mulA A n).left] ![(n : ℤ) ^ 2, -1])} (hα : α.IsGen)
    {y : T ⟶ A} (hy : y ^ (n ^ 2) = 1) {θ : ThetaGrp A L (n ^ 2 : ℕ) T} (H : SymLift A L (n ^ 2 : ℕ) (n ^ 2) y θ)
    {z : T.left} {J} (hJ : Good L z J) :
    tval θ (lift (𝟙 T) (1 : T ⟶ A)).left z J ^ (n ^ 2) =
      val α (1 : T ⟶ A).left z J ^ (n ^ 2) * val α (1 : T ⟶ A).left z J *
        (val α y.left z J ^ (n ^ 2) * val α (y ^ n).left z J)⁻¹ := by
  have e₁ : ∀ p : T ⊗ A ⟶ A, p.left ≫ (mulA A n).left = (p ^ n).left := fun p => by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  obtain ⟨β, hβ, vβ⟩ := exists_gen hL (φ' := ![(snd T A).left, (snd T A ^ (n ^ 2)).left])
    (ε' := ![((n ^ 2 : ℕ) : ℤ) * (n ^ 2 : ℕ), -1])
    (fun U _ h => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, e₁, Category.comp_id, ← pow_mul, ← sq]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen L _ _ _ _ (GeneratorPullback.powGen L _ _ (LB.pullGen L _ _ α (snd T A).left) (n ^ 2))
      (LB.pullGen L _ _ α (snd T A ^ n).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.powGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hα _) _)
      (DVR.pullGen_isGen _ _ _ _ hα _))
  have vβ' : ∀ p : T ⟶ A, bval (b := 1) β (lift (𝟙 T) p).left z J =
      val α p.left z J ^ (n ^ 2) * val α (p ^ n).left z J := fun p => by
    refine (vβ _ _ z J hJ).trans ?_
    rw [val_mul hJ, val_powGen, val_pull hJ, val_pull hJ, ← Over.comp_left, ← Over.comp_left, MonObj.comp_pow, lift_snd]
  obtain ⟨o, ho, vo⟩ := exists_symLift_one hL hν 1
  obtain ⟨θ₁, H₁, v₁⟩ := exists_symLift_mulPull hA hL (one_dvd (n ^ 2)) (b := 1) hβ hy (hy.symm ▸ ho)
  obtain ⟨θ₂, H₂, v₂⟩ := exists_symLift_pow hG hA hL H (n ^ 2)
  have e : tval θ₂ (lift (𝟙 T) (1 : T ⟶ A)).left z J = tval θ₁ (lift (𝟙 T) (1 : T ⟶ A)).left z J :=
    val_corr hJ (SymLiftOdd.symLift_unique hG hA hL hn.pow θ₂ θ₁ H₂ H₁) _
  rw [v₂ _ _ z J hJ, v₁ _ _ z J hJ, vo _ _ z J hJ, vβ', vβ', one_pow, _root_.mul_one, _root_.mul_one,
    Category.id_comp] at e
  exact e

end GlobalTheory.TorsFrame

namespace GlobalTheory


open TorsFrame CommPairing in
theorem exists_isTorsFrame_of_symLift : Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A))), rig.IsGen → ∀ (n : ℕ), Odd n → ∀ (T : Over S) (y x : T ⟶ P.A), y ^ (n ^ 2) = 1 → y ^ n = x → ∀ θ : ThetaGrp P.A P.L (n ^ 2 : ℕ) T, SymLift P.A P.L (n ^ 2 : ℕ) (n ^ 2) y θ → ∃ τ : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => 1)), IsTorsFrame P rig n x τ := by
  intro hLaw S _ P rig hr n hn T y x hy hx θ H
  subst hx
  have hL := P.isLB
  obtain ⟨α₀, h₀⟩ := hLaw.mulPull S P n
  obtain ⟨α, hα, vα⟩ := exists_norm hL hr h₀
  obtain ⟨ν, hν⟩ := exists_gen_negLB hLaw.globalFns S P 1 T
  have e₁ : y.left ≫ (mulA P.A n).left = (y ^ n).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  have e₂ : (lift (𝟙 T) (1 : T ⟶ P.A)).left ≫ (snd T P.A).left = T.hom ≫ eSec P.A := by
    rw [← Over.comp_left, lift_snd, one_left]
  have e₃ : (lift (𝟙 T) (1 : T ⟶ P.A)).left ≫ (translPt P.A θ.pt).left = y.left := by
    rw [← Over.comp_left, translPt, comp_lift_assoc, lift_fst_assoc, lift_snd, Category.id_comp, H.pt_eq]
    exact congrArg (·.left) (_root_.mul_one y)
  obtain ⟨τ, hτ, vτ⟩ := exists_gen hL (φ' := fun _ : Fin 1 => (y ^ n).left) (ε' := fun _ => 1)
    (fun U _ h => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, e₁, e₂, e₃, Category.comp_id]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen P.L _ _ _ _ (GeneratorPullback.powGen P.L _ _
        (LB.pullGen P.L (fun _ : PUnit => eSec P.A) (fun _ => 1) rig T.hom) (n ^ 2))
      (LB.invGen P.L _ _ (LB.mulGen P.L _ _ _ _
        (LB.pullGen P.L ![(snd T P.A).left, (translPt P.A θ.pt).left] ![(n ^ 2 : ℕ), -(n ^ 2 : ℕ)] θ.φ
          (lift (𝟙 T) (1 : T ⟶ P.A)).left) (LB.pullGen P.L _ _ α y.left))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.powGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hr _) _)
      (DVR.invGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ θ.isGen _)
        (DVR.pullGen_isGen _ _ _ _ hα _))))
  refine ⟨τ, by rw [← pow_mul, ← sq, hy], hτ, α, hα, corr_of_val hL fun z J hJ => ?_,
    corr_of_val hL fun z J hJ => ?_⟩
  · refine (val_pull hJ _ _ _).trans ((vα _ _ z J hJ).trans (Eq.symm ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) ((map_zpow _ _ _).trans ?_) (val_inv _ _)))))
    rw [← Nat.cast_pow, zpow_natCast]; rfl
  · have a : val (powFrame P.A P.L (y ^ n) τ ((n : ℤ) ^ 2)) (𝟙 _) z J = val τ (𝟙 _) z J ^ (n ^ 2) :=
      (map_zpow _ _ _).trans (by rw [← Nat.cast_pow, zpow_natCast]; rfl)
    have b := tval_pow hLaw.globalFns P.isAb hL hν hn hα hy H hJ
    have c : val (LB.pullGen P.L ![(snd T P.A).left, (translPt P.A θ.pt).left] ![(n ^ 2 : ℕ), -(n ^ 2 : ℕ)] θ.φ
        (lift (𝟙 T) (1 : T ⟶ P.A)).left) (𝟙 T.left) z J = tval θ (lift (𝟙 T) (1 : T ⟶ P.A)).left z J :=
      (val_pull hJ _ _ _).trans (by rw [Category.id_comp]; rfl)
    rw [one_left, vα _ _ z J hJ] at b
    rw [a, vτ _ _ z J hJ, val_mul hJ, val_mul hJ, val_inv, val_mul hJ, c, val_powGen, val_pull hJ, val_pull hJ,
      val_pull hJ, val_rigT rig _ z hJ, Category.id_comp, Category.id_comp, Category.id_comp, mul_pow, inv_pow, mul_pow, b]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    module

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLabelMapTorsionCharacters
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.LabelMap

theorem exists_lift_points {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') {Γ : Type} [AddCommGroup Γ]
    (pt : Γ → (baseOver S ⟶ G)) (hadd : ∀ a b, pt (a + b) = pt a * pt b) :
    ∃ xx : Multiplicative Γ →* (T ⟶ G'),
      (∀ a x, x.left ≫ φ = (T.hom ≫ f) ≫ (pt a).left ↔ x = xx (Multiplicative.ofAdd a)) ∧
      ∀ (k : ℕ), (∀ z : Over.mk (T.hom ≫ f) ⟶ G, z ^ k = 1 → ∃ a, (T.hom ≫ f) ≫ (pt a).left = z.left) →
        ∀ x : T ⟶ G', x ^ k = 1 → ∃ a, xx (Multiplicative.ofAdd a) = x := by
  let Φ : (T ⟶ G') →* (Over.mk (T.hom ≫ f) ⟶ G) :=
    MonoidHom.mk' (fun x => toBase h.1.w x) fun x y => Over.OverMorphism.ext (h.2 T x y _ _ rfl rfl).symm
  have hΦ : ∀ x, (Φ x).left = x.left ≫ φ := fun _ => rfl
  have inj : Function.Injective Φ := fun x y e => Over.OverMorphism.ext (h.1.hom_ext
    ((hΦ x).symm.trans ((congrArg (fun z => z.left) e).trans (hΦ y))) ((Over.w x).trans (Over.w y).symm))
  have surj : Function.Surjective Φ := fun z =>
    ⟨Over.homMk (h.1.lift z.left T.hom (Over.w z)) (h.1.lift_snd _ _ _), Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩
  let e := MulEquiv.ofBijective Φ ⟨inj, surj⟩
  let U : Over.mk (T.hom ≫ f) ⟶ baseOver S := Over.homMk (T.hom ≫ f) (Category.comp_id _)
  let q : Multiplicative Γ →* (Over.mk (T.hom ≫ f) ⟶ G) :=
    MonoidHom.mk' (fun a => U ≫ pt a.toAdd) fun a b =>
      (congrArg (U ≫ ·) (hadd a.toAdd b.toAdd)).trans (MonObj.comp_mul U _ _)
  have key : ∀ a x, x.left ≫ φ = (T.hom ≫ f) ≫ (pt a).left ↔ x = e.symm (q (Multiplicative.ofAdd a)) := fun a x =>
    ⟨fun H => e.eq_symm_apply.2 (Over.OverMorphism.ext H),
      fun H => congrArg (fun z => z.left) (e.eq_symm_apply.1 H)⟩
  refine ⟨e.symm.toMonoidHom.comp q, key, fun k hk x hx => ?_⟩
  obtain ⟨a, ha⟩ := hk (Φ x) (by rw [← map_pow, hx, map_one])
  exact ⟨a, ((key a x).1 ha.symm).symm⟩


attribute [local instance] TorusExt.gtGroup in

theorem pow_eq_one_of_qkAdd {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] (hB : D.TauBimult) {k : ℕ} {M : Type} [Group M] (f : QkPt D F k → M)
    (heq : ∀ q q', QkPt.Equiv D F q q' → f q = f q') (hadd : ∀ q q' q'', QkAdd q q' q'' → f q'' = f q * f q')
    (q : QkPt D F k) : f q ^ k = 1 := by
  letI := TorusExt.gtGroup D F
  let iota : D.X →+ GtPtF D F := AddMonoidHom.mk' (fun x => (TorusExt.exists_iota hB x).choose) fun x x' => by
    obtain ⟨b, v⟩ := (TorusExt.isIota_iff_val _ _).1 (TorusExt.exists_iota (F := F) hB x).choose_spec
    obtain ⟨b', v'⟩ := (TorusExt.isIota_iff_val _ _).1 (TorusExt.exists_iota (F := F) hB x').choose_spec
    obtain ⟨b'', v''⟩ := (TorusExt.isIota_iff_val _ _).1 (TorusExt.exists_iota (F := F) hB (x + x')).choose_spec
    refine (TorusExt.isAdd_iff_eq _ _ _).1 ((TorusExt.isAdd_iff_val _ _ _).2 ⟨by rw [b, b', b'', ReciprocityTheory.ChartRestriction.G.DVR.cPoint_add], fun χ y J hJ => ?_⟩)
    have C : IsCub (ReciprocityTheory.ChartRestriction.G.DVR.th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
    rw [v χ y J hJ, v' χ y J hJ, v'' χ y J hJ, b, b', C.s01, C.s12]
    exact ReciprocityTheory.ChartRestriction.G.DVR.tau_mul (𝟙 (TF (R := R) F)) hJ hB x x' χ
  have isIota_iff_eq (x : D.X) (g : GtPtF D F) : GtPtF.IsIota x g ↔ g = iota x :=
    ⟨fun h => TorusExt.isIota_unique h (TorusExt.exists_iota hB x).choose_spec,
      fun h => h ▸ (TorusExt.exists_iota hB x).choose_spec⟩
  have qk_nsmul (q : QkPt D F k) : k • q.g = iota q.y := by
    obtain ⟨h, h₁, h₂⟩ := q.eq
    exact ((TorusExt.isNsmul_iff_eq _ _ _).1 h₁).symm.trans ((isIota_iff_eq _ _).1 h₂)
  let qkMk (y : D.X) (g : GtPtF D F) (h : k • g = iota y) : QkPt D F k :=
    ⟨y, g, k • g, (TorusExt.isNsmul_iff_eq _ _ _).2 rfl, (isIota_iff_eq _ _).2 h⟩
  let qkZero : QkPt D F k := qkMk 0 0 (by rw [nsmul_zero, map_zero])
  let qkAdd (p p' : QkPt D F k) : QkPt D F k :=
    qkMk (p.y + p'.y) (p.g + p'.g) (by rw [nsmul_add, qk_nsmul, qk_nsmul, map_add (f := _)])
  have qkAdd_rel (p p' : QkPt D F k) : QkAdd p p' (qkAdd p p') :=
    ⟨_, rfl, (TorusExt.isAdd_iff_eq _ _ _).2 rfl, qk_equiv_refl hB _⟩
  have fz : f qkZero = 1 := by
    have e := hadd _ _ _ (qkAdd_rel (qkZero) (qkZero))
    rw [show qkAdd (qkZero) (qkZero) = qkZero from
      TorusExt.qk_ext (add_zero _) (add_zero _)] at e
    exact mul_eq_left.1 e.symm
  let m : ℕ → QkPt D F k := fun n => qkMk (n • q.y) (n • q.g) (by
    rw [smul_comm, qk_nsmul, map_nsmul])
  have hm : ∀ n, f (m n) = f q ^ n := fun n => by
    induction n with
    | zero => exact (congrArg f (TorusExt.qk_ext (zero_nsmul _) (zero_nsmul _))).trans (fz.trans (pow_zero _).symm)
    | succ n ih =>
      rw [pow_succ, ← ih, ← hadd _ _ _ (qkAdd_rel _ _)]
      exact congrArg f (TorusExt.qk_ext (succ_nsmul _ _) (succ_nsmul _ _))
  rw [← hm, ← fz]
  exact (heq _ _ ⟨q.y, (zero_add _).symm, iota q.y, (isIota_iff_eq _ _).2 rfl, (TorusExt.isAdd_iff_eq _ _ _).2 ((qk_nsmul q).trans (zero_add _).symm)⟩).symm

theorem exists_labelMap : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀), ∃ yy : S.Gam →+ u.D.toPre.X ⧸ (nsmulAddMonoidHom (S.r * S.N) : u.D.toPre.X →+ u.D.toPre.X).range, Function.Surjective yy ∧ (∀ (a : S.Gam) (pk : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) pk x → x.left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left → yy a = QuotientAddGroup.mk pk.y) := by
  intro L _ hU o Ω _ _ _ _ S ρ p _ y₀ u
  haveI : CharZero u.V := ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V _)).charZero
  have hk : 1 ≤ S.r * S.N := Nat.mul_pos S.r_pos (by have := S.N_ge; omega)
  obtain ⟨f, hrel, honto, heq, hadd, -⟩ := hU u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) (S.r * S.N) hk
  obtain ⟨xx, hxx, hsurj⟩ := exists_lift_points u.cart (TFK (R := u.V) (PadicAlgCl p)) ρ.pt ρ.pt_add
  have hy : (TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK = spMap y₀ := by
    exact (Spec.map_comp (CommRingCat.ofHom u.yK) (CommRingCat.ofHom (algebraMap _ _))).symm.trans
      (congrArg spMap u.fac)
  have hsurj' := hsurj (S.r * S.N) fun z hz =>
    (ρ.pt_bij (PadicAlgCl p) _ z hz).exists.imp fun a ha => congrArg (fun w => w.left) ha
  have htors : ∀ a : S.Gam, xx (Multiplicative.ofAdd a) ^ (S.r * S.N) = 1 := fun a => by
    have : (S.r * S.N) • a = 0 := funext fun i => by
      rw [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul]; rfl
    rw [← map_pow, ← ofAdd_nsmul, this, ofAdd_zero, map_one]
  choose P hP using fun a => honto _ (htors a)
  have hB := u.D.tau_bimult
  have wd : ∀ q q' : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N), f q = f q' →
      (QuotientAddGroup.mk q.y : u.D.toPre.X ⧸ (nsmulAddMonoidHom (S.r * S.N) : u.D.toPre.X →+ u.D.toPre.X).range) =
        QuotientAddGroup.mk q'.y := fun q q' e => by
    obtain ⟨z, hz, -⟩ := (heq q q').1 e
    exact QuotientAddGroup.eq.2 ⟨z, by rw [hz, neg_add_cancel_left]; rfl⟩
  have ftors : ∀ q, f q ^ (S.r * S.N) = 1 := pow_eq_one_of_qkAdd hB f (fun q q' e => (heq q q').2 e) hadd
  let D := u.D.toPre
  let F := PadicAlgCl p
  let R := u.V
  let k := S.r * S.N
  letI := TorusExt.gtGroup D F
  let iota : D.X →+ GtPtF D F := AddMonoidHom.mk' (fun x => (TorusExt.exists_iota hB x).choose) fun x x' => by
    obtain ⟨b, v⟩ := (TorusExt.isIota_iff_val _ _).1 (TorusExt.exists_iota (F := F) hB x).choose_spec
    obtain ⟨b', v'⟩ := (TorusExt.isIota_iff_val _ _).1 (TorusExt.exists_iota (F := F) hB x').choose_spec
    obtain ⟨b'', v''⟩ := (TorusExt.isIota_iff_val _ _).1 (TorusExt.exists_iota (F := F) hB (x + x')).choose_spec
    refine (TorusExt.isAdd_iff_eq _ _ _).1 ((TorusExt.isAdd_iff_val _ _ _).2 ⟨by rw [b, b', b'', ReciprocityTheory.ChartRestriction.G.DVR.cPoint_add], fun χ y J hJ => ?_⟩)
    have C : IsCub (ReciprocityTheory.ChartRestriction.G.DVR.th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
    rw [v χ y J hJ, v' χ y J hJ, v'' χ y J hJ, b, b', C.s01, C.s12]
    exact ReciprocityTheory.ChartRestriction.G.DVR.tau_mul (𝟙 (TF (R := R) F)) hJ hB x x' χ
  have isIota_iff_eq (x : D.X) (g : GtPtF D F) : GtPtF.IsIota x g ↔ g = iota x :=
    ⟨fun h => TorusExt.isIota_unique h (TorusExt.exists_iota hB x).choose_spec,
      fun h => h ▸ (TorusExt.exists_iota hB x).choose_spec⟩
  have qk_nsmul (q : QkPt D F k) : k • q.g = iota q.y := by
    obtain ⟨h, h₁, h₂⟩ := q.eq
    exact ((TorusExt.isNsmul_iff_eq _ _ _).1 h₁).symm.trans ((isIota_iff_eq _ _).1 h₂)
  let qkAdd (v v' : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N) :=
    ⟨v.y + v'.y, v.g + v'.g, (S.r * S.N) • (v.g + v'.g),
      (TorusExt.isNsmul_iff_eq _ _ _).2 rfl,
      (isIota_iff_eq _ _).2 (by rw [nsmul_add, qk_nsmul, qk_nsmul, map_add (f := _)])⟩
  have qkAdd_rel (v v' : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) : QkAdd v v' (qkAdd v v') :=
    ⟨_, rfl, (TorusExt.isAdd_iff_eq _ _ _).2 rfl, qk_equiv_refl hB _⟩
  refine ⟨AddMonoidHom.mk' (fun a => QuotientAddGroup.mk (P a).y) fun a b => ?_, fun c => ?_, fun a pk x hx hφ => ?_⟩
  · exact wd _ (qkAdd (P a) (P b)) (by
      rw [hadd _ _ _ (qkAdd_rel _ _), hP, hP, hP, ofAdd_add, map_mul])
  · obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective c
    obtain ⟨q, rfl⟩ := TorusExt.exists_qkPt (F := PadicAlgCl p) L.mulN (Or.inr L.polBaseChange) hB (Nat.pos_iff_ne_zero.1 hk) y
    obtain ⟨a, ha⟩ := hsurj' _ (ftors q)
    exact ⟨a, wd _ _ ((hP a).trans ha)⟩
  · exact wd _ _ ((hP a).trans (((hxx a x).1 (hφ.trans (by rw [hy]))).symm.trans ((hrel pk x).1 hx)))

end GlobalTheory.ZH.LabelMap
end
end

