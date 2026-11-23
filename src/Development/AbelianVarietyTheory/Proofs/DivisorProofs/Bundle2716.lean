module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2688
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsSharpAndPrim
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1962
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0576
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2113
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2003
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2709
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2696
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2704
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1942
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2312
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2448
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2326
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2598
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2344
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2330
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2254
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2338
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsClosedImmersionIffPullRatio
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2635
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2678
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2686
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2108
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2687

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartSiegelLevelCoverSharpTheta
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PoincChart
open GlobalTheory.SiegLev GlobalTheory.AbLaw

theorem chartL : ∀ (n N : ℕ) (X Y : Scheme.{0}) (sX : X ⟶ Sp (cycAway n)) (sY : Y ⟶ Sp (cycAway N)) (q : Y ⟶ X), 0 < n → 0 < N → Smooth sX → Smooth sY → IsFinite q → Etale q → Surjective q → ∀ η ∈ genericPoints X, ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra (cycAway N) Ω) (_ : ArithBase (cycAway N) Ω) (R : Subalgebra (cycAway N) Ω) (y : Sp R ⟶ Y), R.FG ∧ (∀ z : Ω, ∃ a ∈ R, ∃ c ∈ R, z = a / c) ∧ y ≫ sY = spMap (algebraMap (cycAway N) R) ∧ (∀ w, (spMap R.val.toRingHom ≫ y ≫ q) w = η) ∧ ((spMap R.val.toRingHom ≫ y ≫ q).stalkMap (genericPoint (Sp Ω))).hom.Finite := _root_.GlobalTheory.Poinc.Chart.exists_chart

theorem pullL : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ) (T T' : Scheme.{0}) (P : PolAV T) (P' : PolAV T') (u : T ⟶ F.X) (f : T' ⟶ T) (φ : P'.A.left ⟶ P.A.left), SharpOver F W P u → IsGrpPullback P'.A P.A f φ → LBIso P'.L (P.L.pull φ) → SharpOver F W P' (f ≫ u) := _root_.GlobalTheory.Poinc.sharpOver_pullback

theorem exists_isSharpBasis (h : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : IsE8 W) :
    ∃ bas : (Fin (2 * (8 * h)) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ)), IsSharpBasis W bas := by
  have hS : (W + W.transpose).transpose = W + W.transpose := by
    rw [Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
  have h1 : (W + W.transpose) * (W + W.transpose).adjugate = 1 := by rw [Matrix.mul_adjugate, hW.2, one_smul]
  have h2 : (W + W.transpose).adjugate * (W + W.transpose) = 1 := by rw [Matrix.adjugate_mul, hW.2, one_smul]
  let e : (Fin 8 → (Fin h ⊕ Fin h → ℤ)) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ)) :=
    { twistSnd (W + W.transpose).adjugate with
      invFun := twistSnd (W + W.transpose)
      left_inv := twistSnd_twistSnd _ _ h1
      right_inv := twistSnd_twistSnd _ _ h2 }
  refine ⟨(sharpReindex h).trans e, fun i j => ?_⟩
  rw [← sum_omegaStd_single h i j]
  exact sum_omegaStd_twistSnd _ _ hS h1 _ _

section
open MonObj

def powBaseR {n k : ℕ} (hn : n ≠ 0) (hk : k ≠ 0) : TBase (cycAway (n * k)) k where
  ζ := (cycBase (mul_ne_zero hn hk)).ζ ^ n
  unit := by
    have h : IsUnit ((n : cycAway (n * k)) * (k : cycAway (n * k))) := by
      rw [← Nat.cast_mul]
      exact isUnit_natCast (mul_ne_zero hn hk)
    exact isUnit_of_mul_isUnit_right h
  prim K _ β := by
    rw [Units.val_pow_eq_pow_val, map_pow, cycBase_ζ]
    exact (isPrimitiveRoot_map (mul_ne_zero hn hk) β).pow (Nat.pos_of_ne_zero (mul_ne_zero hn hk)) rfl

theorem powBaseR_pow {n k : ℕ} (hn : n ≠ 0) (hk : k ≠ 0) : (powBaseR hn hk).ζ ^ k = 1 := by
  show ((cycBase (mul_ne_zero hn hk)).ζ ^ n) ^ k = 1
  rw [← pow_mul]
  exact Units.ext ((Units.val_pow_eq_pow_val _ _).trans
    (Subtype.ext (Complex.isPrimitiveRoot_exp _ (mul_ne_zero hn hk)).pow_eq_one))

def lowerTo {h M N d : ℕ} {B : Type} [CommRing B] {ζ' ζ : B} {S : Scheme.{0}} {s : S ⟶ Sp B}
    (C : SiegPre h M ζ' s) (hM : M = N * d) (h0 : M ≠ 0) (hζ : ζ = ζ' ^ d) : SiegPre h N ζ s where
  A := C.A
  ab := C.ab
  P := C.P
  isLB := C.isLB
  rig₁ := C.rig₁
  rig₂ := C.rig₂
  symm := C.symm
  lev a := C.lev a ^ d
  lev_add := (SiegLower.lower C hM h0 (RingHom.id B) hζ).lev_add
  lev_tors := (SiegLower.lower C hM h0 (RingHom.id B) hζ).lev_tors
  geom K _ _ x β z hx hz := (SiegLower.lower C hM h0 (RingHom.id B) hζ).geom K x β z
    (by rw [show spMap (RingHom.id B) = 𝟙 _ from Spec.map_id _, Category.comp_id]; exact hx) hz

theorem exists_sharpOver_cover (g n k : ℕ) (F : SFam g n (zetaAway n)) (F' : SFam g (n * k) (zetaAway (n * k)))
    (κ : cycAway n →+* cycAway (n * k)) (q : F'.X ⟶ F.X) (hn : 0 < n) (hk3 : 3 ≤ k) (hko : Odd k)
    (hζ : κ (zetaAway n) = zetaAway (n * k) ^ k) (hqs : q ≫ F.s = F'.s ≫ spMap κ)
    (hq : SiegLev.SRel F'.univ F.univ k 1 q) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) [Finite J]
    (a : J → Matrix (Fin 8) (Fin 8) ℤ) (w w' : J)
    (bas : (Fin (2 * (8 * g)) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin g ⊕ Fin g → ℤ))) (hW : IsE8 W) (hb : IsSharpBasis W bas)
    (hw : (W + W.transpose) * a w = W) (hw' : (W + W.transpose) * a w' = W.transpose)
    (hs : ∀ u v, ∃ j, a j = Matrix.single u v 1) :
    ∃ (b : TBase (cycAway (n * k)) k) (t : TObj (8 * g) k J b F'.s), t.Prim w w' ∧ SharpOver F W t.pol q := by
  have hk : k ≠ 0 := by omega
  have hnk : n * k ≠ 0 := mul_ne_zero hn.ne' hk
  let b := powBaseR hn.ne' hk
  have hbζ : (b.ζ : cycAway (n * k)) = zetaAway (n * k) ^ n := Units.val_pow_eq_pow_val _ _
  let c : SiegPre g k (b.ζ : cycAway (n * k)) F'.s := lowerTo F'.univ (mul_comm n k) hnk hbζ
  have hc : c.Principal := F'.princ
  have hd : SmoothOfRelativeDimension g c.A.hom :=
    SiegSharpCover.smoothDim c (by omega) b.ζ.isUnit b.unit
  obtain ⟨L₁, L₂⟩ := abelianSchemeLaws_all
  haveI : IsDedekindDomain (cycAway (n * k)) := GlobalTheory.CycAwayReg.isDedekindDomain_cycAway _
  haveI : IsLocallyNoetherian (Sp (cycAway (n * k))) :=
    inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of _)))
  haveI := F'.smooth
  haveI : Smooth F'.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F'.s
  haveI : IsLocallyNoetherian F'.X := LocallyOfFiniteType.isLocallyNoetherian F'.s
  obtain ⟨t, ht, hp⟩ := GlobalTheory.exists_isSharp_and_prim L₁ L₂ Moduli.cube_of_isLB g (8 * g) W J a w w' bas hW hb hw hw'
    hs k (cycAway (n * k)) b F'.X F'.s c (powBaseR_pow hn.ne' hk) hko hc hd
  refine ⟨b, t, hp, ?_⟩
  let cT : SiegPre g n (zetaAway n) (F'.s ≫ spMap κ) := SiegLower.lower F'.univ (n := n) (d := k) rfl hnk κ hζ
  have hPB : SiegPB cT F.univ q := by
    obtain ⟨φ, hφ, ⟨φ₂, hsq, hP⟩, hlev⟩ := hq
    exact ⟨φ, φ₂, hφ, hsq, hP, fun a => by have e := hlev a; rw [pow_one] at e; exact e⟩
  obtain ⟨pr, h1, h2, h3, -, -⟩ := ht
  unfold SharpOver
  rw [hqs]
  exact ⟨cT, hPB, pr, h1, h2, h3⟩

end

theorem exists_chart : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ η ∈ genericPoints F.X, ∃ ℓ : ℕ, ℓ.Prime ∧ Odd ℓ ∧ ∀ j : ℕ, 1 ≤ j → ∃ (o Ω : Type) (_ : CommRing o) (_ : Field Ω) (_ : Algebra o Ω) (_ : ArithBase o Ω) (κ : cycAway n →+* o) (R : Subalgebra o Ω) (J : Type) (b : TBase o ((ℓ ^ j) ^ 2)) (t : TObj (8 * g) ((ℓ ^ j) ^ 2) J b (spMap (algebraMap o R))) (w w' : J) (x : Sp R ⟶ F.X), R.FG ∧ (∀ y : Ω, ∃ a ∈ R, ∃ c ∈ R, y = a / c) ∧ t.Prim w w' ∧ (∀ (T : Scheme.{0}) (f : T ⟶ Sp R) (P : PolAV T) (φ : P.A.left ⟶ t.A.left), IsGrpPullback P.A t.A f φ → LBIso P.L (t.L.pull φ) → SharpOver F W P (f ≫ x)) ∧ (∀ w, (spMap R.val.toRingHom ≫ x) w = η) ∧ spMap R.val.toRingHom ≫ x ≫ F.s = spMap ((algebraMap o Ω).comp κ) ∧ κ.Finite ∧ ((spMap R.val.toRingHom ≫ x).stalkMap (genericPoint (Sp Ω))).hom.Finite := by
  intro g n hg hn hodd F W hW η hη
  have hℓ : n.minFac.Prime := Nat.minFac_prime (by omega)
  have hℓn : n.minFac ∣ n := Nat.minFac_dvd n
  have hℓo : Odd n.minFac := Odd.of_dvd_nat hodd hℓn
  refine ⟨n.minFac, hℓ, hℓo, fun j hj => ?_⟩
  have h3 : 3 ≤ n.minFac := by
    have h2 := hℓ.two_le
    have : n.minFac ≠ 2 := fun e => by rw [e] at hℓo; exact absurd hℓo (by decide)
    omega
  have hk3 : 3 ≤ (n.minFac ^ j) ^ 2 :=
    le_trans (le_trans h3 (Nat.le_self_pow (by omega) _)) (Nat.le_self_pow (by omega) _)
  have hko : Odd ((n.minFac ^ j) ^ 2) := hℓo.pow.pow
  obtain ⟨κ, F', q, ⟨-, hζ, hfin, -, -⟩, ⟨hqs, hqfin, hqet, hqsurj, hq⟩, -⟩ :=
    GlobalTheory.SiegLevCover.exists_levelCover g n n.minFac j F hg hn hodd hℓ hℓn hj
  haveI := F.smooth
  haveI : Smooth F.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F.s
  haveI := F'.smooth
  haveI : Smooth F'.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F'.s
  obtain ⟨Ω, _, _, _, R, y, hRfg, hfrac, hys, hpt, hstalk⟩ :=
    chartL n (n * (n.minFac ^ j) ^ 2) F.X F'.X F.s F'.s q (by omega) (Nat.mul_pos (by omega) (pow_pos (pow_pos hℓ.pos _) _)) inferInstance inferInstance
      hqfin hqet hqsurj η hη
  obtain ⟨bas, hbas⟩ := exists_isSharpBasis g W hW
  obtain ⟨a, w, w', hw, hw', hs⟩ := EighthPowerFactor.exists_matrices hW.2
  obtain ⟨b, t', hp', hsh'⟩ := exists_sharpOver_cover g n _ F F' κ q (by omega) hk3 hko hζ hqs hq W _ a w w' bas
    hW hbas hw hw' hs
  obtain ⟨t, ht⟩ := GlobalTheory.tObj_pull _ (8 * g) _ _ b F'.X (Sp R) F'.s (spMap (algebraMap _ R)) y t' hys
  have hp : t.Prim w w' :=
    (GlobalTheory.shape_prim_pull_and_descend _ _ _ _ b (fun _ => 0) 0 w w' _ _ _ _ y t' t ht).2.1 hp'
  obtain ⟨ψ, hψ, hψL, -, -⟩ := ht
  have hsh : SharpOver F W t.pol (y ≫ q) := pullL _ _ _ _ F W _ _ t'.pol t.pol q y ψ hsh' hψ hψL
  refine ⟨cycAway (n * (n.minFac ^ j) ^ 2), Ω, inferInstance, inferInstance, inferInstance, inferInstance, κ, R, _,
    b, t, w, w', y ≫ q, hRfg, hfrac, hp, fun T f P φ h1 h2 => ?_, hpt, ?_, ((IsFinite.SpecMap_iff _).1 hfin), hstalk⟩
  · have e := pullL _ _ _ _ F W _ _ t.pol P (y ≫ q) f φ hsh h1 h2
    exact e
  · rw [Category.assoc, hqs, ← Category.assoc y, hys]
    simp only [spMap, ← Spec.map_comp]
    rfl

end GlobalTheory.PoincChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvOfFamAffine
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon.TwistDescent

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem memKL_of_lam_eq_zero {L : LB A.left} (hL : L.IsLB) {T : Over S} (x : T ⟶ A)
    (hx : lam (cls L hL) (fst T A ≫ x) (snd T A) = 0) : GlobalTheory.MemKL A L x := by
  have hD : (Out.translDiff A L x).IsLB := LB.isLB_linComb hL _ _
  intro p
  obtain ⟨V, hV, hc⟩ := exists_pull_eq_zero
    (CechPic.pull x.left (cls L hL) - CechPic.pull (1 : T ⟶ A).left (cls L hL)) p
  refine ⟨V, hV, (cls_eq_zero_iff (pull_isLB hD _)).1 ?_⟩
  have e₁ := pull_translDiff hL x hD (fst T A) (snd T A)
  rw [lift_fst_snd, Over.id_left, pull_id] at e₁
  have e₂ : cls _ hD = CechPic.pull (fst T A).left
      (CechPic.pull x.left (cls L hL) - CechPic.pull (1 : T ⟶ A).left (cls L hL)) := by
    rw [e₁, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, MonObj.comp_one,
      ← sub_eq_zero, ← hx, lam]
    abel
  rw [cls_pull hD, e₂, ← pull_comp]
  exact pull_eq_zero_of_mem V (((fst T A).left ⁻¹ᵁ V).ι ≫ (fst T A).left) (fun z ↦ z.2) hc

end GlobalTheory.DualCon.TwistDescent

namespace GlobalTheory.DualCon

end GlobalTheory.DualCon
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorThroughIsogenyOfKillsKernel
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem exists_factor_of_isogeny : ∀ (K : Type) [Field K] (A B C : AbVar K) (q : A ⟶ B) (f : A ⟶ C), IsIsogeny q → (∀ (T : Over (Sp K)) (x : T ⟶ A.X), x ≫ q.hom = 1 → x ≫ f.hom = 1) → ∃ g : B ⟶ C, q ≫ g = f := by
  intro K _ A B C q f hq hker
  have hflat : Flat q.hom.left := (_root_.GlobalTheory.AV.AbVar.isogeny_flat_finrank K A B q hq).2.1
  have hfin : IsFinite q.hom.left := hq.1
  have hsurj : Surjective q.hom.left := hq.2
  have hqc : QuasiCompact q.hom.left := inferInstance
  obtain ⟨⟨ψ, hψ, hc⟩, -⟩ := GlobalTheory.exists_monHom_factor_of_flat_surjective _ A.X B.X C.X q.hom f.hom
    inferInstance inferInstance hflat hsurj hqc hker
  refine ⟨Hom.mk ψ, ?_⟩
  apply Subtype.ext
  exact hc

end GlobalTheory.AV.AbVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFgModel
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleFibreMove

theorem exists_fg_model :
    ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G], IsAbelianScheme G → ∀ L : LB G.left, L.IsLB →
    ∃ (S : Subring R) (G₀ : Over (Sp S)) (_ : GrpObj G₀) (φ : G.left ⟶ G₀.left) (L₀ : LB G₀.left),
      Algebra.FiniteType ℤ S ∧ IsAbelianScheme G₀ ∧ IsGrpPullback G G₀ (spMap S.subtype) φ ∧ L₀.IsLB ∧
        LBIso L (L₀.pull φ) := by
  intro R _ G _ hG L hL
  classical
  obtain ⟨S₀, B₀, _, φ₀, -, hft₀, hab₀, hpb₀⟩ :=
    GlobalTheory.AbelianLimit.abelianScheme_descends_to_fg_subring_anyDim R G ∅ hG
  have := hab₀.comm
  have := hab₀.smooth
  have := hab₀.proper
  have := hab₀.geomConnected
  obtain ⟨SP, hSP⟩ := GlobalTheory.LBLimit.lb_descends_to_fg_subring R S₀ G.left B₀.left
    G.hom B₀.hom φ₀ L hpb₀.1 hL
  obtain ⟨R₁, h, hT, hft⟩ := GlobalTheory.KeyTf.exists_finiteType_subring_adjoin R S₀ SP hft₀
  let t : Sp R₁ ⟶ Sp S₀ := spMap (Subring.inclusion h)
  have e : spMap R₁.subtype ≫ t = spMap S₀.subtype := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let G₁ : Over (Sp R₁) := (Over.pullback t).obj B₀
  have hab₁ : IsAbelianScheme G₁ :=
    { comm := inferInstance
      smooth := inferInstanceAs (Smooth (pullback.snd B₀.hom t))
      proper := inferInstanceAs (IsProper (pullback.snd B₀.hom t))
      geomConnected := inferInstanceAs (GeometricallyConnected (pullback.snd B₀.hom t)) }
  have hpb₁ : IsPullback (pullback.fst B₀.hom t) G₁.hom B₀.hom t := IsPullback.of_hasPullback _ _
  have wφ : φ₀ ≫ B₀.hom = (G.hom ≫ spMap R₁.subtype) ≫ t := by
    rw [Category.assoc, e]; exact hpb₀.1.w
  let φ : G.left ⟶ G₁.left := pullback.lift φ₀ (G.hom ≫ spMap R₁.subtype) wφ
  have hφ₁ : φ ≫ pullback.fst B₀.hom t = φ₀ := pullback.lift_fst _ _ _
  have hφ₂ : φ ≫ G₁.hom = G.hom ≫ spMap R₁.subtype := pullback.lift_snd _ _ _
  have hφ : IsGrpPullback G G₁ (spMap R₁.subtype) φ :=
    (isGrpPullback_pullback B₀ t).cancel (hpb₀.congr e.symm hφ₁.symm) hφ₂
  obtain ⟨L₁, hL₁, hiso⟩ := hSP R₁ h hT G₁.left G₁.hom (pullback.fst B₀.hom t) φ hpb₁ hφ₁ hφ₂
  exact ⟨R₁, G₁, inferInstance, φ, L₁, hft, hab₁, hφ, hL₁, hiso⟩

end GlobalTheory.AmpleFibreMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteThetaSectionsThickeningCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.ClosedGen

theorem cst_eq_baseRingHom {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (W : X.Opens) :
    (GlobalTheory.QCoh.Qcqs.baseRingHom f W).hom = GlobalTheory.AbLaw.cst f W := by
  rfl

end GlobalTheory.Mum.ClosedGen


open GlobalTheory.Mum.ClosedGen in
theorem GlobalTheory.Mum.exists_ratio_gen_closed : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k → ∃ (n : ℕ) (τ : Fin n → H0 U.LG.L k), ∀ w : (thickObj R (maximalIdeal R) 0 G).left, ∃ (j : Fin n) (i : Fin 1 → U.LG.L.ι) (N : (thickObj R (maximalIdeal R) 0 G).left.Opens) (r : Fin n → Γ((thickObj R (maximalIdeal R) 0 G).left, N)), w ∈ N ∧ IsAffineOpen N ∧ N ≤ (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart U.LG.L i ∧ (∀ y ∈ N, IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (τ j) i) ∧ ∀ l, secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (τ l) i = gs (𝟙 _) y N (r l) * secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (τ j) i) ∧ ∀ g : Γ((thickObj R (maximalIdeal R) 0 G).left, N), ∃ P Q : MvPolynomial (Fin n) R, IsUnit (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q) ∧ g * MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q = MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r P := by
  intro R _ _ _ hB D A G _ _ hG U
  obtain ⟨Y⟩ : Nonempty (Ext D.toPre) := inferInstance
  obtain ⟨S, k₁, hk₁⟩ := _root_.GlobalTheory.Mum.ThetaImm.exists_immersion R hB D Y
  choose k₀f hk₀f using (_root_.GlobalTheory.ThFam.exists_intFam_lead R hB D).1
  refine ⟨max 3 (max k₁ (S.sup k₀f)), le_max_left _ _, ?_⟩
  intro k hk
  have hk3 : 3 ≤ k := le_trans (le_max_left _ _) hk
  have hkk₁ : k₁ ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hkS : S.sup k₀f ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
  obtain ⟨N, α, b, τ, hτ, hαb, himm⟩ := hk₁ k hkk₁
  have hF : ∀ j, ∃ F : IntFam (maximalIdeal R) D.toPre k, F.Lead (α j) (b j) := fun j =>
    hk₀f (α j) k (le_trans (Finset.le_sup (hαb j).1) hkS) (b j)
  choose F hF using hF
  have hs : ∀ j, ∃ σ : H0 U.LG.L k, ∀ e, U.ExpandsAt e k σ (F j).f := fun j =>
    IntFam.exists_expandsAt R hB D A G U hG k (by omega) (F j)
  choose s hs using hs
  let T : Over (Sp R) := Over.mk ((thickObj R (maximalIdeal R) 0 G).hom ≫ thick R (maximalIdeal R) 0)
  obtain ⟨ξ, hξ⟩ := GlobalTheory.TorusCoord.exists_isPointOf (U.gt 0) (T := T) (𝟙 (thickObj R (maximalIdeal R) 0 G).left)
    (Category.id_comp _)
  let ψ : T ⟶ Y.H := (Y.Φ T).symm ξ
  have hψ : GlobalTheory.TorusCoord.IsPointOf (U.gt 0) (𝟙 (thickObj R (maximalIdeal R) 0 G).left) (Y.Φ T ψ) := by
    simp only [ψ, Equiv.apply_symm_apply]; exact hξ
  haveI hψi : IsImmersion ψ.left := _root_.GlobalTheory.Mum.ClosedFibreImm.main R D A G U.toUnifPre Y ψ hψ
  set p₀ := (fstG (maximalIdeal R) 0 G).left with hp₀
  let φ := ψ.left ≫ GlobalTheory.ProjSpace.toProj Y.H.hom τ hτ
  haveI : IsImmersion φ := IsImmersion.comp _ _
  have hpre : ∀ j, φ ⁻¹ᵁ GlobalTheory.ProjSpace.chart R N j = ψ.left ⁻¹ᵁ nonzeroLocus (τ j) := fun j => by
    simp only [φ, Scheme.Hom.comp_preimage, GlobalTheory.ProjSpace.toProj_preimage_chart]
  have hstr : φ ≫ PSpace.str R N = p₀ ≫ G.hom := by
    simp only [φ, Category.assoc, GlobalTheory.ProjSpace.toProj_str]
    rw [Over.w ψ]
    exact (pullback.condition).symm
  refine ⟨N + 1, s, fun w => ?_⟩
  have hw : ψ.left w ∈ ⨆ i, nonzeroLocus (τ i) := by rw [hτ]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hw
  obtain ⟨J, hJ⟩ := GlobalTheory.TorusCoord.exists_good' U.LG.isLB w
  let i : Fin 1 → U.LG.L.ι := fun _ => J (p₀ ≫ 𝟙 G.left)
  have hi : p₀ w ∈ secChart U.LG.L i := hJ.mem (fun _ : Fin 1 => 𝟙 G.left) p₀
  have hφw : φ w ∈ GlobalTheory.ProjSpace.chart R N j := by
    show w ∈ φ ⁻¹ᵁ GlobalTheory.ProjSpace.chart R N j
    rw [hpre]; exact hj
  obtain ⟨W, hW, hwW, hWV, hWa, hgen⟩ := _root_.GlobalTheory.ProjSpace.exists_affineOpen_fraction_pullRatio R N _ φ inferInstance w (p₀ ⁻¹ᵁ secChart U.LG.L i) j hi hφw
  have hWψ : W ≤ ψ.left ⁻¹ᵁ nonzeroLocus (τ j) := hW.trans (hpre j).le
  have hr : ∀ l, GlobalTheory.ProjSpace.pullRatio φ W j hW l =
      (ψ.left.appLE (nonzeroLocus (τ j)) W hWψ).hom (GlobalTheory.ProjSpace.secRatio (τ j) (τ l)) := by
    intro l
    rw [← GlobalTheory.ProjSpace.pullRatio_toProj Y.H.hom τ hτ j l, GlobalTheory.ProjSpace.appLE_pullRatio]
  refine ⟨j, i, W, GlobalTheory.ProjSpace.pullRatio φ W j hW, hwW, hWa, hWV, fun y hy => ?_, fun g => ?_⟩
  · have hyψ : ψ.left y ∈ nonzeroLocus (τ j) := hWψ hy
    obtain ⟨hu, hl⟩ := GlobalTheory.T.closedFibre_thetaSectionGerm_eq_fourierRatio_mul R D A G U.toUnifPre Y ψ hψ k (N + 1) α b τ F s (fun j => (hαb j).2) hF
      (fun j => hs j 0) y j i hyψ (hWV hy)
    refine ⟨hu, fun l => ?_⟩
    rw [hl l, hr l, gs_appLE _ _ _ _ (𝟙 _) y hy, Category.id_comp]
  · obtain ⟨P, Q, hQ, hPQ⟩ := hgen g
    have hc : (GlobalTheory.QCoh.Qcqs.baseRingHom (φ ≫ PSpace.str R N) W).hom = GlobalTheory.AbLaw.cst (p₀ ≫ G.hom) W := by
      rw [hstr]; exact cst_eq_baseRingHom _ _
    rw [hc] at hQ hPQ
    exact ⟨P, Q, hQ, hPQ⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeometricFibreIsoOfTraitUniformisationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_geometricFibreIso_of_traitUniformisation : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (D' : DegData W (maximalIdeal W)) (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (A' : PolAV (Sp (FractionRing W))), Nonempty (IsPullDeg φ D.toPre D'.toPre) → IsSemiAbelian G' → Nonempty (Unif (maximalIdeal W) D' A' G') → (letI := A'.isAb.comm; GlobalTheory.ZH.HypS A'.A A'.L) → ∃ (A₀ : PolAV (Sp (Kb R))) (e₀ : Kb R →+* Kb W), (∀ r, e₀ (algebraMap (FractionRing R) (Kb R) (algebraMap R _ r)) = algebraMap (FractionRing W) (Kb W) (algebraMap W _ (φ r))) ∧ (letI := A₀.isAb.comm; GlobalTheory.ZH.HypS A₀.A A₀.L) ∧ GeomIso A₀ A' e₀ (algebraMap (FractionRing W) (Kb W)) := by
  first | exact @GlobalTheory.Mum.GeoDesc.exists_geomIso_of_unif | exact GlobalTheory.Mum.GeoDesc.exists_geomIso_of_unif | (intros; apply GlobalTheory.Mum.GeoDesc.exists_geomIso_of_unif <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGroupAlgebraActionOfCommuteOrderStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_groupAlgebra_action_of_commute_order : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (A : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)), (∀ b : D.O, A * (actQ D b).baseChange (AfP p) = (actQ D b).baseChange (AfP p) * A) → ∃ y, actOn L.rep (AfP p) y = A := by
  first | (exact @GlobalTheory.LKGeo.CommBC.exists_actOn_eq_of_commute) | (exact GlobalTheory.LKGeo.CommBC.exists_actOn_eq_of_commute) | (intros; apply GlobalTheory.LKGeo.CommBC.exists_actOn_eq_of_commute  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomToDualOfMumfordClassStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hom_to_dual_of_mumfordClass : ∀ (K : Type) [Field K] (A A' : AbVar K) (P : LB (A.X ⊗ A'.X).left) (hP : AbDual.IsDual A.X A'.X P), A'.dim = A.dim → ∀ c : Pic A.X.left, ∃ φ : A ⟶ A', AbVar.lam c (fst A.X A.X) (snd A.X A.X) = AbDual.evc hP.isLB (fst A.X A.X) (snd A.X A.X ≫ φ.hom) ∧ (IsAmpleCls c → IsIsogeny φ) := by
  first | (exact @GlobalTheory.AV.AbVar.exists_phi) | (exact GlobalTheory.AV.AbVar.exists_phi) | (intros; apply GlobalTheory.AV.AbVar.exists_phi  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralAdeleLimitCompatibleIntSystemStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralAdeleLimit_compatibleIntSystem : ∀ (p : ℕ) [Fact p.Prime] (a : ℕ → ℤ), (∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p → (n : ℤ) ∣ a (n * m) - a n) → ∃ α : AfP p, IsIntAf α ∧ ∀ n : ℕ, 0 < n → n.Coprime p → ∃ β : AfP p, IsIntAf β ∧ α = (a n : AfP p) + n • β := by
  first | (exact @GlobalTheory.CompatLim.exists_lim) | (exact GlobalTheory.CompatLim.exists_lim) | (intros; apply GlobalTheory.CompatLim.exists_lim  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeVectorEqNsmulOfAdelicNsmulStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_latticeVector_eq_nsmul_of_adelic_nsmul : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (n : ℕ), 0 < n → n.Coprime p → (∀ (c : ℤ) (a : AfP p), IsIntAf a → algebraMap ℚ (AfP p) (c : ℚ) = (n : AfP p) * a → (n : ℤ) ∣ c) → ∀ z : D.La, (∃ w ∈ LaHat D, inAf D z = n • w) → ∃ u : D.La, z = n • u := by
  first | (exact @GlobalTheory.LKGeo.LatDvd.exists_eq_nsmul_of_inAf) | (exact GlobalTheory.LKGeo.LatDvd.exists_eq_nsmul_of_inAf) | (intros; apply GlobalTheory.LKGeo.LatDvd.exists_eq_nsmul_of_inAf <;> assumption)
end

