module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2318
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2478
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2399
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2398
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2526
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointAbelianPartAndClassifyingMapLinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2517
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2427
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2328
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2491
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2368
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2501
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2349
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2360
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2374
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2332
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2522
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1096
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1099
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2545
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2151
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2300
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2344
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2500
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2428
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2486
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2533
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2567
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2576
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2524
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2122
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2256
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2084
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2217
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2117
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2512
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2431

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComponentTupleTensorTorsionUnimodular
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

noncomputable section

namespace GlobalTheory.Mum.TensTor

theorem gtRelV_npow_of_tensFacts {F : Type} [Field F] {N N' : NumD F} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
    {φ : N'.A → Fin r → N.A} {e : N'.X → Fin r → N.X} {wv : N'.A → F} (hf : TensFacts W φ e wv)
    {v' : N'.Gt} {vs : Fin r → N.Gt} (h : GtRelV W φ e wv v' vs) (k : ℕ) :
    GtRelV W φ e wv (v' ^ k) (vs ^ k) := by
  induction k with
  | zero =>
    have h0 := _root_.GlobalTheory.Mum.TensTor.gtRelV_io F N N' W φ e wv hf 0
    have he0 : ∀ j, e 0 j = 0 := fun j => by
      have := hf.2.2.1 0 0 j
      rw [add_zero] at this
      simpa using this
    have e1 : (1 : Fin r → N.Gt) = fun j => N.io (e 0 j) := funext fun j => by rw [he0, N.io_zero]; rfl
    rw [pow_zero, pow_zero, e1, ← N'.io_zero]
    exact h0
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact _root_.GlobalTheory.Mum.TensTor.gtRelV_mul F N N' W φ e wv hf _ _ _ _ ih h

theorem exists_components_of_unimodular : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N'), IsUnit (W + W.transpose).det → ∀ (k : ℕ) (p' : QkPt D'.toPre F k), ∃ ps : Fin r → QkPt D.toPre F k, PtRel T ν ν' p' ps := by
  intro R _ _ _ hB D D' r W T F _ _ _ N N' ν ν' hW k p'
  have hGt := GlobalTheory.Ex.GtValues.points_correspond
  have hf := _root_.GlobalTheory.Mum.TensTor.tensFacts_holds R hB D D' W T F N N' ν ν'
  obtain ⟨q', hq', -⟩ := ((hGt R D'.toPre D'.psi_even D'.tau_bimult F N' ν').2.2.2.2 k).1 p'
  obtain ⟨vs, hvs⟩ := GlobalTheory.T.exists_torus_components_of_unimodular_tensor F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') hf hW q'.1.2
  have hk := gtRelV_npow_of_tensFacts hf hvs k
  rw [N'.mem_QT.1 q'.2] at hk
  have hio := _root_.GlobalTheory.Mum.TensTor.gtRelV_io F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') hf q'.1.1.toAdd
  have hv := _root_.GlobalTheory.Mum.TensTor.gtRelV_components_unique F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') hf hW _ _ _ hk hio
  let qs : Fin r → N.QT k := fun j =>
    ⟨(Multiplicative.ofAdd (chi T ν ν' q'.1.1.toAdd j), vs j), N.mem_QT.2 (congrFun hv j)⟩
  choose ps hps using fun j => ((hGt R D.toPre D.psi_even D.tau_bimult F N ν).2.2.2.2 k).2.1 (qs j)
  exact ⟨ps, q', qs, hq', hps, fun _ => rfl, hvs⟩

end GlobalTheory.Mum.TensTor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescendedGeneratorThickenedAbelianPart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
open GlobalTheory.HomMum

noncomputable section
namespace GlobalTheory.HomMum

open GlobalTheory.EndRosati


set_option maxHeartbeats 800000 in
theorem exists_gen_thick_two : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ : DegData R I} {A₁ A₂ : PolAV (Sp (FractionRing R))} {G₁ G₂ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (e : ℕ) {f g : G₁ ⟶ G₂} [IsMonHom f] [IsMonHom g] {fB gB : D₁.toPre.P.A ⟶ D₂.toPre.P.A} [IsMonHom fB] [IsMonHom gB], (Over.pullback (thick R I e)).map f ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map fB → (Over.pullback (thick R I e)).map g ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map gB → ∀ (v : LB.Gen (LB.LinComb (JN D₁.toPre D₂.toPre) (fun k => mφ (thickObj R I e G₁) (thickObj R I e G₂) ((Over.pullback (thick R I e)).map f) ((Over.pullback (thick R I e)).map g) k ≫ coprod.map (U₁.gt e).pG.left (U₂.gt e).pG.left) mε)), v.IsGen → (∀ (T : Over (Sp (R ⧸ I ^ (e + 1)))) (z : T.left) (J : (T.left ⟶ D₁.toPre.P.A.left ⨿ D₂.toPre.P.A.left) → (JN D₁.toPre D₂.toPre).ι), Good (JN D₁.toPre D₂.toPre) z J → ∀ x x' y y' : T ⟶ thickObj R I e G₁, x ≫ (U₁.gt e).q = x' ≫ (U₁.gt e).q → y ≫ (U₁.gt e).q = y' ≫ (U₁.gt e).q → val v (lift x y).left z J = val v (lift x' y').left z J) → ∃ t : LB.Gen (LB.LinComb (JN D₁.toPre D₂.toPre) (fun k => pullback.fst (D₁.toPre.P.A ⊗ D₁.toPre.P.A).hom (thick R I e) ≫ mφ D₁.toPre.P.A D₂.toPre.P.A fB gB k) mε), t.IsGen := by
  intro R _ _ I D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ e f g _ _ fB gB _ _ hf hg v hv hi
  have hM := jn_isLB D₁.toPre D₂.toPre
  have := (U₁.gt e).q_affine
  have pp : ∀ {c : G₁ ⟶ G₂} {cB : D₁.toPre.P.A ⟶ D₂.toPre.P.A},
      (Over.pullback (thick R I e)).map c ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map cB →
      push (U₂.gt e).pG ((Over.pullback (thick R I e)).map c) = (U₁.gt e).pG ≫ cB := fun {c cB} h => by
    rw [push, GtCoord.pG, ← Functor.map_comp_assoc, h, Functor.map_comp_assoc, Category.assoc]
    exact congrArg _ (GlobalTheory.EndRosati.push_fstG e cB)
  let m := (U₁.gt e).q ⊗ₘ (U₁.gt e).q
  have : Flat m.left := MorphismProperty.pullbackMap (P := @Flat) (U₁.gt e).q_flat (U₁.gt e).q_flat
    (Over.w (U₁.gt e).q).symm (Over.w (U₁.gt e).q).symm
  have : Surjective m.left :=
    have : MorphismProperty.IsStableUnderComposition @Surjective.{0} := ⟨fun _ _ _ _ => inferInstance⟩
    MorphismProperty.pullbackMap (P := @Surjective) (U₁.gt e).q_surj (U₁.gt e).q_surj
      (Over.w (U₁.gt e).q).symm (Over.w (U₁.gt e).q).symm
  have qc : QuasiCompact (U₁.gt e).q.left := inferInstance
  have : QuasiCompact m.left := MorphismProperty.pullbackMap (P := @QuasiCompact) qc qc
    (Over.w (U₁.gt e).q).symm (Over.w (U₁.gt e).q).symm
  let Be := thickObj R I e D₁.toPre.P.A
  let π := lift (push (fstG I e D₁.toPre.P.A) (fst Be Be)) (push (fstG I e D₁.toPre.P.A) (snd Be Be))
  have hπ : m.left ≫ π.left = (lift (push (U₁.gt e).pG (fst _ _)) (push (U₁.gt e).pG (snd _ _))).left := by
    refine (GlobalTheory.EndRosati.lift_push (fstG I e D₁.toPre.P.A) (fst _ _ ≫ (U₁.gt e).q) (snd _ _ ≫ (U₁.gt e).q)).trans ?_
    simp only [push, Functor.map_comp, Category.assoc]
    rfl
  have hφ : ∀ k, mφ (thickObj R I e G₁) (thickObj R I e G₂) ((Over.pullback (thick R I e)).map f)
      ((Over.pullback (thick R I e)).map g) k ≫ coprod.map (U₁.gt e).pG.left (U₂.gt e).pG.left =
      m.left ≫ π.left ≫ mφ D₁.toPre.P.A D₂.toPre.P.A fB gB k := fun k => by
    rw [← Category.assoc, hπ, mφ_push (U₁.gt e).pG (U₂.gt e).pG (TorusCoord.im_mul (U₁.gt e))
      (TorusCoord.im_mul (U₂.gt e)) (pp hf) (pp hg) (fst _ _) (snd _ _) k, lift_fst_snd]
    exact (Category.id_comp _).symm
  obtain ⟨v', hv', vv⟩ := exists_gen hM (φ' := fun k => m.left ≫ π.left ≫ mφ D₁.toPre.P.A D₂.toPre.P.A fB gB k)
    (ε' := mε) (fun V _ h => Finset.prod_congr rfl fun k _ => congrArg (h · ^ mε k) (hφ k)) v hv
  obtain ⟨t, ht, -⟩ := CoordCompare.exists_gen_of_val_eq hM _ _ m.left v' hv' fun Z r r' z J hJ h => by
    have hw : r ≫ (thickObj R I e G₁ ⊗ thickObj R I e G₁).hom = r' ≫ (thickObj R I e G₁ ⊗ thickObj R I e G₁).hom := by
      rw [← Over.w m, reassoc_of% h]
    let T := Over.mk (r' ≫ (thickObj R I e G₁ ⊗ thickObj R I e G₁).hom)
    let s : T ⟶ thickObj R I e G₁ ⊗ thickObj R I e G₁ := Over.homMk r hw
    let s' : T ⟶ thickObj R I e G₁ ⊗ thickObj R I e G₁ := Over.homMk r' rfl
    have hs : s ≫ m = s' ≫ m := Over.OverMorphism.ext h
    have := hi T z J hJ (s ≫ fst _ _) (s' ≫ fst _ _) (s ≫ snd _ _) (s' ≫ snd _ _)
      (by simpa [m] using congrArg (· ≫ fst _ _) hs) (by simpa [m] using congrArg (· ≫ snd _ _) hs)
    rw [lift_comp_fst_snd, lift_comp_fst_snd] at this
    exact (vv _ r z J hJ).trans (this.trans (vv _ r' z J hJ).symm)
  have hn : (lift ((Over.pullback (thick R I e)).map (fst D₁.toPre.P.A D₁.toPre.P.A))
      ((Over.pullback (thick R I e)).map (snd D₁.toPre.P.A D₁.toPre.P.A))).left ≫ π.left =
      pullback.fst (D₁.toPre.P.A ⊗ D₁.toPre.P.A).hom (thick R I e) := by
    refine (GlobalTheory.EndRosati.lift_push (fstG I e D₁.toPre.P.A) _ _).trans ?_
    rw [GlobalTheory.EndRosati.push_fstG, GlobalTheory.EndRosati.push_fstG, lift_comp_fst_snd]
    rfl
  have := (GlobalTheory.EndRosati.gen_iff_sum hM _ _).1 ⟨_, DVR.pullGen_isGen _ _ _ _ ht (lift ((Over.pullback (thick R I e)).map
    (fst D₁.toPre.P.A D₁.toPre.P.A)) ((Over.pullback (thick R I e)).map (snd D₁.toPre.P.A D₁.toPre.P.A))).left⟩
  refine (GlobalTheory.EndRosati.gen_iff_sum hM _ _).2 (Eq.trans (Finset.sum_congr rfl fun k _ => ?_) this)
  rw [← hn, Category.assoc]

end GlobalTheory.HomMum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentOfChartsPulledBackFromFlat
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.ChartDescent

theorem key_move : ∀ (B S X : Scheme.{0}) (π : S ⟶ B) (f : X ⟶ S) (Φ : pullback f (pullback.fst π π) ⟶ pullback f (pullback.snd π π)) (U : Over B) (J : Type) (e : J → (pullback U.hom π ⟶ X)), (∀ j, e j ≫ f = pullback.snd _ _) → (∀ (j : J) (T : Scheme.{0}) (y₁ y₂ : T ⟶ pullback U.hom π) (s : T ⟶ pullback π π), y₁ ≫ pullback.fst _ _ = y₂ ≫ pullback.fst _ _ → y₁ ≫ pullback.snd _ _ = s ≫ pullback.fst π π → y₂ ≫ pullback.snd _ _ = s ≫ pullback.snd π π → ∀ z : T ⟶ pullback f (pullback.fst π π), z ≫ pullback.fst _ _ = y₁ ≫ e j → z ≫ pullback.snd _ _ = s → z ≫ Φ ≫ pullback.fst _ _ = y₂ ≫ e j) → (∀ (i j : J) (T : Scheme.{0}) (w₁ w₂ h₁ : T ⟶ pullback U.hom π), w₁ ≫ pullback.fst _ _ = w₂ ≫ pullback.fst _ _ → h₁ ≫ e j = w₁ ≫ e i → ∃ h₂ : T ⟶ pullback U.hom π, h₂ ≫ e j = w₂ ≫ e i ∧ h₂ ≫ pullback.fst _ _ = h₁ ≫ pullback.fst _ _) := by
  intro B S X π f Φ U J e hf hc i j T w₁ w₂ h₁ hw hh
  have hπ : w₁ ≫ pullback.snd U.hom π ≫ π = w₂ ≫ pullback.snd U.hom π ≫ π := by
    rw [← pullback.condition, reassoc_of% hw]
  have hs1 : h₁ ≫ pullback.snd U.hom π = w₁ ≫ pullback.snd U.hom π := by
    simpa only [Category.assoc, hf] using congrArg (· ≫ f) hh
  let s : T ⟶ pullback π π := pullback.lift (w₁ ≫ pullback.snd _ _) (w₂ ≫ pullback.snd _ _)
    (by simpa only [Category.assoc] using hπ)
  have hs₁ : s ≫ pullback.fst π π = w₁ ≫ pullback.snd _ _ := pullback.lift_fst _ _ _
  have hs₂ : s ≫ pullback.snd π π = w₂ ≫ pullback.snd _ _ := pullback.lift_snd _ _ _
  let z : T ⟶ pullback f (pullback.fst π π) := pullback.lift (w₁ ≫ e i) s
    (by rw [hs₁, Category.assoc, hf])
  have hz₁ : z ≫ pullback.fst _ _ = w₁ ≫ e i := pullback.lift_fst _ _ _
  have hz₂ : z ≫ pullback.snd _ _ = s := pullback.lift_snd _ _ _
  have h1 := hc i T w₁ w₂ s hw hs₁.symm hs₂.symm z hz₁ hz₂
  let y₂ : T ⟶ pullback U.hom π := pullback.lift (h₁ ≫ pullback.fst _ _) (w₂ ≫ pullback.snd _ _)
    (by rw [Category.assoc, pullback.condition, reassoc_of% hs1, Category.assoc, hπ])
  have hy₁ : y₂ ≫ pullback.fst _ _ = h₁ ≫ pullback.fst _ _ := pullback.lift_fst _ _ _
  have hy₂ : y₂ ≫ pullback.snd _ _ = w₂ ≫ pullback.snd _ _ := pullback.lift_snd _ _ _
  have h2 := hc j T h₁ y₂ s hy₁.symm (hs1.trans hs₁.symm) (hy₂.trans hs₂.symm) z (hz₁.trans hh.symm) hz₂
  exact ⟨y₂, by rw [← h2, h1], hy₁⟩

theorem cocycle_facts : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S X : Scheme.{0}) (π : S ⟶ Sp R) (f : X ⟶ S), IsProper π → Surjective π → IsIntegral S → ∀ (U : Over (Sp R)), Flat U.hom → ∀ (J : Type) (e : J → (pullback U.hom π ⟶ X)), (∀ j, IsOpenImmersion (e j)) → (∀ j, e j ≫ f = pullback.snd _ _) → ∀ (V : J → J → U.left.Opens) (τ : ∀ i j, (V i j).toScheme ⟶ U.left), (∀ (i j : J) (a : ↥(pullback U.hom π)), pullback.fst U.hom π a ∈ V i j ↔ e i a ∈ Set.range (e j)) → (∀ (i j : J) (T : Scheme.{0}) (a b : T ⟶ pullback U.hom π) (v : T ⟶ (V i j).toScheme), a ≫ e i = b ≫ e j → v ≫ (V i j).ι = a ≫ pullback.fst _ _ → v ≫ τ i j = b ≫ pullback.fst _ _) → (∀ i, V i i = ⊤) ∧ (∀ i, τ i i = (V i i).ι) ∧ (∀ (i j k : J) (x : (V i j).toScheme), (V i j).ι x ∈ V i k → τ i j x ∈ V j k) ∧ (∀ (i j k : J) (T : Scheme.{0}) (x : T ⟶ (V i j).toScheme) (y : T ⟶ (V i k).toScheme) (w : T ⟶ (V j k).toScheme), x ≫ (V i j).ι = y ≫ (V i k).ι → x ≫ τ i j = w ≫ (V j k).ι → w ≫ τ j k = y ≫ τ i k) ∧ (∀ i j, τ i j ≫ U.hom = (V i j).ι ≫ U.hom) := by
  intro R _ _ _ _ S X π f hπp hπs hS U hU J e he hef V τ hV hτ
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.Mum.glue_overlap_cocycle (Sp R) S X π hπs U J e he V τ hV hτ
  obtain ⟨h3, h4⟩ := _root_.GlobalTheory.Mum.descend_transition_diag_over R S X π f hπp hπs hS U hU J e he hef V τ hV hτ
  exact ⟨h1, h3, h2, _root_.GlobalTheory.MumDescent.cocycle R S X π hπp hπs hS U hU J e he V τ hV hτ, h4⟩

theorem exists_descent : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S X : Scheme.{0}) (π : S ⟶ Sp R) (f : X ⟶ S), IsProper π → Surjective π → IsIntegral S → ∀ (Φ : pullback f (pullback.fst π π) ⟶ pullback f (pullback.snd π π)), Φ ≫ pullback.snd _ _ = pullback.snd _ _ → ∀ (U : Over (Sp R)), Flat U.hom → ∀ (J : Type) (e : J → (pullback U.hom π ⟶ X)), (∀ j, IsOpenImmersion (e j)) → (∀ j, e j ≫ f = pullback.snd _ _) → (∀ x : X, ∃ j, x ∈ Set.range (e j)) → (∀ (j : J) (T : Scheme.{0}) (y₁ y₂ : T ⟶ pullback U.hom π) (s : T ⟶ pullback π π), y₁ ≫ pullback.fst _ _ = y₂ ≫ pullback.fst _ _ → y₁ ≫ pullback.snd _ _ = s ≫ pullback.fst π π → y₂ ≫ pullback.snd _ _ = s ≫ pullback.snd π π → ∀ z : T ⟶ pullback f (pullback.fst π π), z ≫ pullback.fst _ _ = y₁ ≫ e j → z ≫ pullback.snd _ _ = s → z ≫ Φ ≫ pullback.fst _ _ = y₂ ≫ e j) → ∃ (G : Over (Sp R)) (β : X ⟶ G.left) (ψ : J → (U.left ⟶ G.left)), (∀ j, IsOpenImmersion (ψ j) ∧ ψ j ≫ G.hom = U.hom ∧ e j ≫ β = pullback.fst _ _ ≫ ψ j) ∧ (∀ g : G.left, ∃ j, g ∈ Set.range (ψ j)) ∧ IsPullback β f G.hom π ∧ pullback.fst f (pullback.fst π π) ≫ β = Φ ≫ pullback.fst f (pullback.snd π π) ≫ β := by
  intro R _ _ _ _ S X π f hπp hπs hS Φ hΦ U hU J e he hef hcov hc
  have hK := key_move (Sp R) S X π f Φ U J e hef hc
  choose V hV using _root_.GlobalTheory.Div.DescendOpens.overlap_preimage_open (Sp R) S X π U J e hπp hπs he hK
  choose τ hτ using fun i j => _root_.GlobalTheory.Mum.chart_transition_descends R S X π hπp hπs hS U hU J e he hK i j (V i j) (hV i j)
  obtain ⟨hVt, hτi, hland, hcoc, hτR⟩ := cocycle_facts R S X π f hπp hπs hS U hU J e he hef V τ hV hτ
  obtain ⟨G₀, ψ, hψo, hψc, hψp, hψd⟩ := _root_.GlobalTheory.GlueCopies.exists_glue_copies U.left J V τ hVt hτi hland hcoc
  obtain ⟨F, hF⟩ := hψd (Sp R) (fun _ => U.hom) (fun i j => (hτR i j).symm)
  have hcomp : ∀ (i j : J) (T : Scheme.{0}) (a b : T ⟶ pullback U.hom π), a ≫ e i = b ≫ e j →
      a ≫ pullback.fst _ _ ≫ ψ i = b ≫ pullback.fst _ _ ≫ ψ j := by
    intro i j T a b hab
    have hr : Set.range (a ≫ pullback.fst U.hom π) ⊆ Set.range (V i j).ι := by
      rintro _ ⟨t, rfl⟩
      rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
      refine (hV i j (a t)).2 ⟨b t, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← hab, Scheme.Hom.comp_apply]
    have hv : IsOpenImmersion.lift (V i j).ι (a ≫ pullback.fst _ _) hr ≫ (V i j).ι =
        a ≫ pullback.fst _ _ := IsOpenImmersion.lift_fac _ _ _
    rw [← Category.assoc, ← hv, Category.assoc, (hψp i j).w, ← Category.assoc,
      hτ i j T a b _ hab hv, Category.assoc]
  obtain ⟨β, hβ, -⟩ := _root_.GlobalTheory.GlueDesc.exists_unique_glue X G₀ (pullback U.hom π) J e (fun j => pullback.fst _ _ ≫ ψ j) he hcov hcomp
  have hw : β ≫ F = f ≫ π := by
    obtain ⟨gg, -, hgg⟩ := _root_.GlobalTheory.GlueDesc.exists_unique_glue X (Sp R) (pullback U.hom π) J e (fun _ => pullback.snd _ _ ≫ π) he hcov
      (fun i j T a b hab => by
        have h1 : a ≫ pullback.snd U.hom π = b ≫ pullback.snd U.hom π := by
          simpa only [Category.assoc, hef] using congrArg (· ≫ f) hab
        rw [reassoc_of% h1])
    rw [hgg (β ≫ F) (fun j => by rw [reassoc_of% hβ j, hF j, pullback.condition]),
      hgg (f ≫ π) (fun j => by rw [reassoc_of% hef j])]
  refine ⟨Over.mk F, β, ψ, fun j => ⟨hψo j, hF j, hβ j⟩, hψc, ?_, ?_⟩
  · refine _root_.GlobalTheory.Mum.isPullback_of_openCover_target X G₀ S (Sp R) β f F π hw J (fun _ => U.left) (fun _ => pullback U.hom π) ψ e
      (fun _ => pullback.fst _ _) (fun _ => pullback.snd _ _) hψo hψc he
      (fun j => by rw [hF j]; exact IsPullback.of_hasPullback U.hom π) hβ hef ?_
    rintro j x ⟨y, hy⟩
    obtain ⟨i, a, rfl⟩ := hcov x
    have hxa : β (e i a) = ψ i (pullback.fst U.hom π a) := by
      rw [← Scheme.Hom.comp_apply, hβ, Scheme.Hom.comp_apply]
    obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback (hψp i j) (pullback.fst U.hom π a) y
      (by rw [← hxa, hy])
    have ha : pullback.fst U.hom π a ∈ V i j := by
      have h0 : (V i j).ι z ∈ Set.range (V i j).ι := ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι] at h0; rwa [← hz]
    exact (hV i j a).1 ha
  · exact _root_.GlobalTheory.Mum.descent_eqn_of_chart_projection (Sp R) S X G₀ π f Φ U J e ψ β he hcov hef hβ hc

end GlobalTheory.Mum.ChartDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDoubleSpaceOfGenericFunctionFieldPair
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem exists_dbl_of_genPair : ∀ (F : Type) [Field F] (Y : Var F) (K : Type) [Field K] (ψ₁ ψ₂ : Y.Fn →+* K),
    GenPair Y ψ₁ ψ₂ → ∃ (W : Dbl Y) (j : W.Z.functionField →+* K), j.comp W.α₁ = ψ₁ ∧ j.comp W.α₂ = ψ₂ := by
  intro F _ Y K _ ψ₁ ψ₂ hg
  obtain ⟨h, hsp⟩ := GlobalTheory.T.genericPair_specializes_diagonal_genericPoint F Y K ψ₁ ψ₂ hg
  obtain ⟨Z, hZi, p₁, p₂, hZ, ζ, hci, hζ₁, hζ₂, hζg⟩ :=
    _root_.GlobalTheory.FlagPush.exists_closure_pair F Y K (spMap ψ₁ ≫ (ratOf Y).pt) (spMap ψ₂ ≫ (ratOf Y).pt) h
  haveI := hZi
  have hcomp : ζ ≫ Limits.pullback.lift p₁ p₂ hZ =
      Limits.pullback.lift (f := Y.str) (g := Y.str) (spMap ψ₁ ≫ (ratOf Y).pt) (spMap ψ₂ ≫ (ratOf Y).pt) h := by
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, Limits.pullback.lift_fst]; exact hζ₁.trans (Limits.pullback.lift_fst _ _ _).symm
    · rw [Category.assoc, Limits.pullback.lift_snd]; exact hζ₂.trans (Limits.pullback.lift_snd _ _ _).symm
  have hmem : Limits.pullback.diagonal Y.str (genericPoint Y.X) ∈ Set.range (Limits.pullback.lift p₁ p₂ hZ) := by
    have hcl : IsClosed (Set.range (Limits.pullback.lift p₁ p₂ hZ)) := hci.isClosedEmbedding.isClosed_range
    refine hsp.mem_closed hcl ⟨ζ (IsLocalRing.closedPoint K), ?_⟩
    rw [← hcomp]
    first | rfl | exact (Scheme.Hom.comp_apply _ _ _).symm | simp
  obtain ⟨hproj, δ, hδc, hδ₁, hδ₂, hdiag⟩ := _root_.GlobalTheory.FlagPush.dbl_of_isClosedImmersion_lift F Y Z p₁ p₂ hZ hci hmem
  let W : Dbl Y :=
    { Z := Z, integral := hZi, p₁ := p₁, p₂ := p₂, δ := δ, str_eq := hZ, proj := hproj, closed := hδc,
      δ₁ := hδ₁, δ₂ := hδ₂, diag := hdiag }
  obtain ⟨j, hj₁, hj₂⟩ := _root_.GlobalTheory.FlagPush.exists_functionField_map_of_genericPoint F Y W K ψ₁ ψ₂ ζ hζg hζ₁ hζ₂
  exact ⟨W, j, hj₁, hj₂⟩

end GlobalTheory.FlagPush
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtLam
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumExt

theorem exists_extLam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R], ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ L : LB ((Over.pullback (jK R)).obj G).left, L.IsLB → ∃ PP : LB (G2 G).left, ExtLam G L PP := by
  intro R _ _ _ G _ _ hG L hL
  haveI := hG.smooth
  haveI := hG.separated
  haveI := hG.quasiCompact
  haveI : GeometricallyIntegral G.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hG.smooth hG.geomConnected
  obtain ⟨L', hL', hb⟩ := _root_.GlobalTheory.Mum.lb_extends_over_dvr R G L hL
  refine ⟨abelian₂ G L', DVR.linComb_isLB _ hL' _ _, fun κ₂ hκ => ?_⟩
  have h := isGrpPullback_pullback G (jK R)
  let V := lift (pushPt h.1.w (fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)))
    (pushPt h.1.w (snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)))
  have hV : V.left = κ₂ := by
    apply pullback.hom_ext
    · show (V ≫ fst G G).left = κ₂ ≫ (fst G G).left
      rw [hκ.1, lift_fst]
      rfl
    · show (V ≫ snd G G).left = κ₂ ≫ (snd G G).left
      rw [hκ.2, lift_snd]
      rfl
  have c := GlobalTheory.SymSpread.lbIso_cube h hL' hL hb (x2 G) (x2 _) V (fun i => by fin_cases i <;> simp [x2, V])
  rw [hV] at c
  exact c

end GlobalTheory.MumExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtRationalTorsionUniformisedTrait
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.Enlarge

theorem exists_rational_ext : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ : R →+* R₁) (D₁ : DegData R₁ (maximalIdeal R₁)) (A : PolAV (Sp (FractionRing R₁))), FinExt ρ → Nonempty (IsPullDeg ρ D.toPre D₁.toPre) → (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) → UniTrait D₁.toPre A → ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (ρ₂ : R →+* R₂) (D₂ : DegData R₂ (maximalIdeal R₂)) (A₂ : PolAV (Sp (FractionRing R₂))), FinExt ρ₂ ∧ Nonempty (IsPullDeg ρ₂ D.toPre D₂.toPre) ∧ (letI := A₂.isAb.comm; GlobalTheory.ZH.HypS A₂.A A₂.L) ∧ UniTrait D₂.toPre A₂ ∧ ∀ σ : Kb R₂ →ₐ[FractionRing R₂] Kb R₂, (∀ p p' : QkPt D₂.toPre (Kb R₂) n, QkExt σ.toRingHom p p' → QkPt.Equiv D₂.toPre (Kb R₂) p p') ∧ ∀ x : TFK (R := R₂) (Kb R₂) ⟶ A₂.A, x ^ n = 1 → spMap σ.toRingHom ≫ x.left = x.left := by
  intro R _ _ _ hR D n hn hodd hnu R₁ _ _ _ ρ D₁ A hρ hP hS hU
  have hn1 : 1 ≤ n := hn.one_lt.le
  have hR₁ : Base R₁ := ⟨hρ.1, by haveI := hR.2; exact charZero_of_injective_ringHom hρ.2.1⟩
  obtain ⟨EQ, fQ, hQ⟩ := _root_.GlobalTheory.Mum.qkPt_rational_of_pull R₁ hR₁ D₁ n hn1
  obtain ⟨EA, fA, hA⟩ := GlobalTheory.T.exists_finite_extension_fraction_field_uniform R₁ hR₁ A n hn1
  haveI := fQ
  haveI := fA
  obtain ⟨R₂, _, _, _, i₁₂, e, hi₁₂, hi₁₂ρ, hloc, he⟩ := _root_.GlobalTheory.GalClosure.exists_finExt_realising R hR R₁ ρ hρ (EQ ⊔ EA) inferInstance
  obtain ⟨D₂, hD₂⟩ := GlobalTheory.MumPull.exists_pull R₁ R₂ i₁₂ hi₁₂.2.1 hloc D₁
  have hP₂ := nonempty_isPullDeg_comp_of_injective R R₁ R₂ ρ i₁₂ D.toPre D₁.toPre D₂.toPre hi₁₂.2.1 hP hD₂
  have hle : nonZeroDivisors R₁ ≤ (nonZeroDivisors R₂).comap i₁₂ :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective i₁₂ hi₁₂.2.1
  let ga : FractionRing R₁ →+* FractionRing R₂ := IsLocalization.map (FractionRing R₂) i₁₂ hle
  obtain ⟨A₂, g, hg, -, hm, t, ht⟩ := GlobalTheory.firstFiveLaws.1.polBaseChange _ _ (spMap ga) A
  have gp : IsGrpPullback A₂.A A.A (spMap ga) g := ⟨hg, fun T x y x₀ y₀ hx hy => by
    obtain rfl : x₀ = toBase hg.w x := Over.OverMorphism.ext hx
    obtain rfl : y₀ = toBase hg.w y := Over.OverMorphism.ext hy
    exact congrArg (·.left) (hm T x y).symm⟩
  have hlb : LBIso A₂.L (A.L.pull g) := LBIso.symm ⟨t, ht⟩
  have hfib : IsFib i₁₂ A A₂ g := ⟨ga, fun r => IsLocalization.map_eq hle r, gp, hlb⟩
  have hS₂ : (letI := A₂.isAb.comm; GlobalTheory.ZH.HypS A₂.A A₂.L) := by
    letI := A.isAb.comm
    letI := A₂.isAb.comm
    exact GlobalTheory.SymBaseChange.hypS_baseChange _ _ A.A A₂.A (spMap ga) g A.L A₂.L A.isLB A₂.isLB gp hlb hS
  let eQ : EQ →+* FractionRing R₂ := e.comp (IntermediateField.inclusion (le_sup_left : EQ ≤ EQ ⊔ EA)).toRingHom
  let eA : EA →+* FractionRing R₂ := e.comp (IntermediateField.inclusion (le_sup_right : EA ≤ EQ ⊔ EA)).toRingHom
  have hrat := hQ R₂ i₁₂ eQ hi₁₂ hloc (fun r => he r) D₂ hD₂
  refine ⟨R₂, inferInstance, inferInstance, inferInstance, i₁₂.comp ρ, D₂, A₂, hi₁₂ρ, hP₂, hS₂,
    _root_.GlobalTheory.Mum.UniEnlarge.uniTrait_of_finExt R₁ hR₁ D₁ A hU R₂ i₁₂ hi₁₂ hloc D₂ hD₂ A₂ g hfib, fun σ => ⟨_root_.GlobalTheory.Mum.GalFixQ.qkExt_equiv_of_rational R₂ D₂ n hrat σ, fun x hx => ?_⟩⟩
  obtain ⟨x₀, hx₀⟩ := hA R₂ i₁₂ eA hi₁₂.2.1 (fun r => he r) A₂ g hfib x hx
  rw [hx₀, ← Category.assoc, ← spMap_comp]
  exact congrArg (fun f => spMap f ≫ x₀) (RingHom.ext fun a => σ.commutes a)

end GlobalTheory.Mum.Enlarge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionSymmBundleExtensionOnFactor
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_finExt_lbExt_of_factor : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ExtLam G (A.L.pull gen.hom.left) ((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left) → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ φ : R →+* W, Function.Injective φ → IsLocalHom φ → ∀ (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (βW : GW.left ⟶ G.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW) (κ : pullback GW.hom (jK W) ⟶ pullback G.hom (jK R)), IsGrpPullback GW G (spMap φ) βW → κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ βW → LBIso (UW.LG.L.pull (pullback.fst GW.hom (jK W))) ((A.L.pull gen.hom.left).pull κ) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (κ₁ : pullback G₁.hom (jK R') ⟶ pullback G.hom (jK R)) (L₁ : LB G₁.left), FinExt ρ ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ κ₁ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β ∧ L₁.IsLB ∧ LBIso (L₁.pull (pullback.fst G₁.hom (jK R'))) ((A.L.pull gen.hom.left).pull κ₁) := by
  intro R _ _ _ hR D D' F A' G' _ _ hG' U' oA oG hOL G _ _ hG inc pr hinc hpr h1 h2 A gen hgen hext W _ _ _ hW φ hφ hloc GW _ _ βW DW AW UW κ hpb hκ hiso
  obtain ⟨L₁, hL₁, hiso₁⟩ := _root_.GlobalTheory.SymExtend.main R hR.1 G hG A gen hgen _ hext
  have hsp : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id _
  have hL : (A.L.pull gen.hom.left).IsLB := LB.isLB_pull A.isLB _
  refine ⟨R, inferInstance, inferInstance, inferInstance, RingHom.id R, G, inferInstance, inferInstance, 𝟙 _, 𝟙 _, L₁,
    ⟨hR.1, Function.injective_id, RingHom.Finite.id R⟩, ?_, by simp, hL₁, ?_⟩
  · haveI : IsMonHom (Iso.refl G).hom := (inferInstance : IsMonHom (𝟙 G))
    exact (isGrpPullback_of_iso (Iso.refl G)).congr hsp.symm rfl
  · exact LBIso.trans (LB.isLB_pull hL₁ _) hL (LB.isLB_pull hL _) hiso₁ (GlobalTheory.TInj.GenPull.pull_id_iso hL)

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteNormalCoverSymmBundlePowerDecomposit
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
noncomputable section

namespace GlobalTheory.CoverDec

theorem exists_cover_sqDec : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero R], IsAdicComplete (maximalIdeal R) R → ∀ (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → IsAbelianScheme ((Over.pullback (jK R)).obj G) → ∀ (L M : LB G.left), L.IsLB → M.IsLB → RelAmple ((Over.pullback (jK R)).obj G) (L.pull (pullback.fst G.hom (jK R))) → RelAmple ((Over.pullback (jK R)).obj G) (M.pull (pullback.fst G.hom (jK R))) → LBIso (L.pull (GrpObj.inv : G ⟶ G).left) L → LBIso (M.pull (GrpObj.inv : G ⟶ G).left) M → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsNoetherianRing R') (_ : IsIntegrallyClosed R') (_ : IsLocalRing R') (ρ : R →+* R') (G' : Over (Sp R')) (_ : GrpObj G') (π : G'.left ⟶ G.left), Function.Injective ρ ∧ ρ.Finite ∧ IsGrpPullback G' G (spMap ρ) π ∧ SqDec G' (L.pull π) (M.pull π) := by
  intro R _ _ _ _ hc G _ hG hAb L M hL hM hAL hAM hSL hSM
  have sL := _root_.GlobalTheory.SymBaseChange.symm_pull _ _ G (jK R) L hL hSL
  have sM := _root_.GlobalTheory.SymBaseChange.symm_pull _ _ G (jK R) M hM hSM
  obtain ⟨K', _, _, _, hD⟩ := _root_.GlobalTheory.SqDecFinite.sqDec_of_finite_extension (FractionRing R) ((Over.pullback (jK R)).obj G) hAb _ _
    (pull_isLB hL _) (pull_isLB hM _) hAL hAM sL sM
  obtain ⟨R', _, _, _, _, _, ρ, τ, hinj, hfin, hcomp⟩ := _root_.GlobalTheory.LocExt.exists_finite_normal_cover_of_finiteDimensional R hc K'
  obtain ⟨π₀, hP, hLL⟩ := _root_.GlobalTheory.GenFibreBaseChange.genFibre_pull R R' ρ (τ.comp (algebraMap (FractionRing R) K')) hcomp G
  have hD' := GlobalTheory.SqDecTransport.transport (FractionRing R) (FractionRing R') K' (FractionRing R')
    (τ.comp (algebraMap (FractionRing R) K')) (algebraMap (FractionRing R) K') (RingHom.id _) τ rfl
    ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)) π₀ hP _ _ _ _
    (pull_isLB hL _) (pull_isLB hM _) (pull_isLB (pull_isLB hL _) _) (pull_isLB (pull_isLB hM _) _)
    (hLL L hL) (hLL M hM) hD
  have h1 := _root_.GlobalTheory.SqDecIdBC.sqDec_of_baseChange_id _ _ _ _ (pull_isLB (pull_isLB hL _) _) (pull_isLB (pull_isLB hM _) _) hD'
  have h2 := _root_.GlobalTheory.GenericDec.sqDec_of_generic R' ((Over.pullback (spMap ρ)).obj G) (IsSemiAbelian.pullback (spMap ρ) G hG) _ _
    (pull_isLB hL _) (pull_isLB hM _) h1
  exact ⟨R', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ρ,
    (Over.pullback (spMap ρ)).obj G, inferInstance, pullback.fst G.hom (spMap ρ), hinj, hfin,
    isGrpPullback_pullback G (spMap ρ), h2⟩

end GlobalTheory.CoverDec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralGeneratorOfPsiCoordinateStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralGenerator_of_psiCoordinate : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (mu : D.X) (r : V), Formalism.L2.Pj.PsiCoord D mu r → ∃ gam : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c mu).left) (fun _ => -1)), gam.IsGen ∧ ∀ (z : (TF (R := V) (FractionRing V)).left) (J : ((TF (R := V) (FractionRing V)).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (Geo.Tor.val (D.psi mu) (jFK (R := V) (FractionRing V)) z J)).val = GlobalTheory.UT.cst (FractionRing V) z (algebraMap V (FractionRing V) r) * (Geo.Tor.val gam (toUnit (TF (R := V) (FractionRing V))).left z J).val := by
  first | exact @GlobalTheory.Poinc.PsiIntGen.main | exact GlobalTheory.Poinc.PsiIntGen.main | (intros; apply GlobalTheory.Poinc.PsiIntGen.main <;> assumption)
end

