module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleGeneratorExtendingDensePart
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamiliesValuesCorrespond
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0123
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0109
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0165
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EndoLbIsoSymmetryHypothesisExtendNormalModel
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ZH.EndoExtend

open GlobalTheory.CechPic

theorem pic_ext {X U : Scheme.{0}} [IsLocallyNoetherian X] (j : U ⟶ X) (hn : Geo.Tor.IsNormalScheme X)
    [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j] (P : Over X) [Smooth P.hom]
    [GeometricallyIntegral P.hom] (e : X ⟶ P.left) (he : e ≫ P.hom = 𝟙 X) {a b : Pic P.left}
    (h₁ : CechPic.pull e a = CechPic.pull e b)
    (h₂ : CechPic.pull (pullback.fst P.hom j) a = CechPic.pull (pullback.fst P.hom j) b) : a = b := by
  rw [← sub_eq_zero, ← map_sub] at h₁ h₂
  rw [← sub_eq_zero]
  obtain ⟨N, hN, hc⟩ := cls_surj (a - b)
  rw [← hc] at h₁ h₂ ⊢
  exact (cls_eq_zero_iff hN).2 (GenericExtend.exists_isGen_of_densePart X U j hn ‹_› ‹_› ‹_› ‹_› P e N he ‹_› ‹_› hN
    ((cls_eq_zero_iff (pull_isLB hN _)).1 h₁) ((cls_eq_zero_iff (pull_isLB hN _)).1 h₂))

section Cube

variable {S S' : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]

def cubeCls {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) (c : Pic G.left) : Pic T.left :=
  ∑ I : ULift.{0} (Finset (Fin n)), ((-1 : ℤ) ^ (n - I.down.card)) • CechPic.pull (psum G x I.down).left c

theorem cls_cubeLB {T : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) {L : LB G.left} (hL : L.IsLB) :
    cls (cubeLB G x L) (LB.isLB_linComb hL _ _) = cubeCls G x (cls L hL) :=
  cls_linComb hL _ _ _

theorem pull_cubeCls {T T' : Over S} {n : ℕ} (x : Fin n → (T ⟶ G)) (x' : Fin n → (T' ⟶ G)) (u : T' ⟶ T)
    (h : ∀ i, x' i = u ≫ x i) (c : Pic G.left) : CechPic.pull u.left (cubeCls G x c) = cubeCls G x' c := by
  obtain rfl : x' = fun i => u ≫ x i := funext h
  unfold cubeCls
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [map_zsmul, ← pull_comp, ← Over.comp_left]
  exact congrArg (fun z : T' ⟶ G => _ • CechPic.pull z.left c) (psum_hom (preHom u) x I.down)

theorem cubeCls_one {n : ℕ} (c : Pic G.left) (hc : CechPic.pull (eSec G) c = 0) :
    cubeCls G (fun _ : Fin n => (η[G] : 𝟙_ (Over S) ⟶ G)) c = 0 := by
  refine Finset.sum_eq_zero fun I _ => ?_
  have e₁ : (1 : 𝟙_ (Over S) ⟶ G) = η[G] := by rw [Hom.one_def]; simp
  have : psum G (fun _ : Fin n => (1 : 𝟙_ (Over S) ⟶ G)) I.down = 1 := by
    unfold psum
    induction (List.finRange n).filter (· ∈ I.down) with
    | nil => rfl
    | cons k l ih => exact (_root_.one_mul _).trans ih
  rw [e₁] at this
  rw [this]
  exact (congrArg (_ • ·) hc).trans (smul_zero _)

variable {G} in
theorem push_cubeCls {G' : Over S'} [GrpObj G'] [IsCommMonObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G f φ) {T' : Over S'} {T : Over S} {n : ℕ} (x' : Fin n → (T' ⟶ G'))
    (x : Fin n → (T ⟶ G)) (u : T'.left ⟶ T.left) (hu : u ≫ T.hom = T'.hom ≫ f)
    (hx : ∀ i, (x' i).left ≫ φ = u ≫ (x i).left) (c : Pic G.left) :
    CechPic.pull u (cubeCls G x c) = cubeCls G' x' (CechPic.pull φ c) := by
  unfold cubeCls
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [map_zsmul, ← pull_comp, ← pull_comp,
    psum_push h x' x (Over.homMk u hu) (fun i => Over.OverMorphism.ext (hx i)) I.down]
  rfl

end Cube

theorem hypS_of_densePart {X U : Scheme.{0}} [IsLocallyNoetherian X] (j : U ⟶ X) (hn : Geo.Tor.IsNormalScheme X)
    [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j] (G : Over X) [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] [GeometricallyConnected G.hom] (L : RigLB G)
    (hext : ∀ f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G, IsMonHom f →
      ∃! F : G ⟶ G, IsMonHom F ∧ (Over.pullback j).map F = f)
    (h : HypS ((Over.pullback j).obj G) (L.L.pull (pullback.fst G.hom j))) : HypS G L.L := by
  obtain ⟨w', wd', hw', hwd', hs, hp, ha⟩ := h
  obtain ⟨w, ⟨hw, rfl⟩, -⟩ := hext w' hw'
  obtain ⟨wd, ⟨hwd, rfl⟩, -⟩ := hext wd' hwd'
  have hL := L.isLB
  have hL' := pull_isLB hL (pullback.fst G.hom j)
  have hG := isGrpPullback_pullback G j
  have A : ∀ {Y Z : Over X} (a : Y ⟶ Z),
      ((Over.pullback j).map a).left ≫ pullback.fst Z.hom j = pullback.fst Y.hom j ≫ a.left :=
    fun a => pullback.lift_fst _ _ _
  have h0 : CechPic.pull (eSec G) (cls L.L hL) = 0 := (cls_eq_zero_iff (pull_isLB hL _)).2 ⟨L.rig, L.rigGen⟩
  have := geometricallyIntegral_of_smooth G.hom
  have := smooth_tensorObj_hom G G
  have := geometricallyIntegral_tensorObj_hom G G
  refine ⟨w, wd, hw, hwd, ?_, ?_, ?_⟩
  · refine (hext (𝟙 _) inferInstance).unique ⟨Serre.isMonHom_mul w wd, ?_⟩ ⟨inferInstance, CategoryTheory.Functor.map_id _ _⟩
    rw [Functor.map_mul, hs]
  · refine (cls_eq_iff hL (LB.isLB_linComb hL _ _)).1 (Eq.trans ?_ (cls_cubeLB G _ hL).symm)
    refine pic_ext j hn G (eSec G) (Over.w η[G]) (h0.trans ?_) ?_
    · refine ((pull_cubeCls G _ (fun _ => η[G]) η[G] (fun i => ?_) _).trans (cubeCls_one G _ h0)).symm
      fin_cases i <;> simp
    · have e := ((cls_eq_iff hL' (LB.isLB_linComb hL' _ _)).2 hp).trans (cls_cubeLB ((Over.pullback j).obj G) _ hL')
      have e' := push_cubeCls hG (T' := (Over.pullback j).obj G) (T := G) ![𝟙 _, (Over.pullback j).map w] ![𝟙 G, w]
        (pullback.fst G.hom j) pullback.condition (fun i => by
          fin_cases i
          · simp
          · exact A w) (cls L.L hL)
      exact e.trans e'.symm
  · refine (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).1
      ((cls_cubeLB G _ hL).trans (Eq.trans ?_ (cls_cubeLB G _ hL).symm))
    refine pic_ext j hn (G ⊗ G) (lift η[G] η[G]).left (Over.w _) ?_ ?_
    · refine (pull_cubeCls G _ (fun _ => η[G]) (lift η[G] η[G]) (fun i => ?_) _).trans
        (pull_cubeCls G _ (fun _ => η[G]) (lift η[G] η[G]) (fun i => ?_) _).symm <;>
      fin_cases i <;> simp
    · let δ := lift ((Over.pullback j).map (fst G G)) ((Over.pullback j).map (snd G G))
      have e := congrArg (CechPic.pull δ.left) ((cls_cubeLB ((Over.pullback j).obj G) _ hL').symm.trans
        (((cls_eq_iff (LB.isLB_linComb hL' _ _) (LB.isLB_linComb hL' _ _)).2 ha).trans
          (cls_cubeLB ((Over.pullback j).obj G) _ hL')))
      have e' := fun x : Fin 2 → (G ⊗ G ⟶ G) => push_cubeCls hG (T' := (Over.pullback j).obj (G ⊗ G)) (T := G ⊗ G)
        (fun i => (Over.pullback j).map (x i)) x (pullback.fst (G ⊗ G).hom j) pullback.condition (fun i => A _)
        (cls L.L hL)
      rw [pull_cubeCls _ _ (fun i => (Over.pullback j).map (![fst G G ≫ w, snd G G] i)) δ
          (fun i => by fin_cases i <;> simp [δ]),
        pull_cubeCls _ _ (fun i => (Over.pullback j).map (![fst G G, snd G G ≫ wd] i)) δ
          (fun i => by fin_cases i <;> simp [δ])] at e
      exact (e' _).trans (e.trans (e' _).symm)

section Model

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)

theorem isIso_stalkClosedPointTo : IsIso (Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) M.pt) := by
  have e : M.stalkHom (M.pt (IsLocalRing.closedPoint Ω)) =
      (Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) M.pt).hom := by
    unfold RatModel.stalkHom
    erw [TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]
  refine (ConcreteCategory.isIso_iff_bijective _).2 ?_
  change Function.Bijective (Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) M.pt).hom
  rw [← e]
  refine ⟨M.stalkHom_injective _, fun x => ?_⟩
  have hx : x ∈ M.O (M.pt (IsLocalRing.closedPoint Ω)) := by
    have h := M.O_genericPoint
    rw [← M.pt_apply (IsLocalRing.closedPoint Ω)] at h
    exact h.ge trivial
  obtain ⟨a, ha⟩ := (M.stalkEquiv _).surjective ⟨x, hx⟩
  exact ⟨a, congrArg Subtype.val ha⟩

theorem isPreimmersion_pt : IsPreimmersion M.pt := by
  have := isIso_stalkClosedPointTo M
  rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of Ω) M.pt]
  infer_instance

theorem flat_pt : Flat M.pt := by
  have := isIso_stalkClosedPointTo M
  have := GenericExt.flat_fromSpecStalk M.Z (M.pt (IsLocalRing.closedPoint Ω))
  rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of Ω) M.pt]
  infer_instance

end Model

theorem hypS_and_endo_and_iso_extend : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Over₀ M U₀ → HypS Q.G Q.L.L ∧ (∀ f : (Over.pullback M.pt).obj Q.G ⟶ (Over.pullback M.pt).obj Q.G, IsMonHom f → ∃! F : Q.G ⟶ Q.G, IsMonHom F ∧ (Over.pullback M.pt).map F = f) ∧ (∀ (n : ℕ) (x x' : Fin n → (Q.G ⊗ Q.G ⟶ Q.G)), (∀ i, IsMonHom (x i) ∧ IsMonHom (x' i)) → ∀ ε ε' : Fin n → ℤ, ∑ i, ε i = 0 → ∑ i, ε' i = 0 → LBIso ((LB.LinComb Q.L.L (fun i => (x i).left) ε).pull (pullback.fst (Q.G ⊗ Q.G).hom M.pt)) ((LB.LinComb Q.L.L (fun i => (x' i).left) ε').pull (pullback.fst (Q.G ⊗ Q.G).hom M.pt)) → LBIso (LB.LinComb Q.L.L (fun i => (x i).left) ε) (LB.LinComb Q.L.L (fun i => (x' i).left) ε')) := by
  intro hdvr o Ω _ _ _ hA S ρ M U₀ Q hO
  have := hA.ded
  have := hA.ft
  have := hA.char
  have := M.lft
  have : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  have hX : Geo.Tor.IsNormalScheme M.Z ∧ ∃ z : M.Z ⟶ Sp ℤ, LocallyOfFiniteType z ∧ Flat z :=
    ⟨hO.normal, _, MinorModel.locallyOfFiniteType_int M, MinorModel.flat_int M _⟩
  have := isPreimmersion_pt M
  have := flat_pt M
  have := Q.semi.smooth
  have := Q.semi.geomConnected
  have hL := Q.L.isLB
  refine ⟨?_, GlobalTheory.existsUnique_hom_extension_semiAbelian_normal hdvr _ _ M.pt hX ‹_› ‹_› inferInstance inferInstance _ _ Q.semi Q.semi, ?_⟩
  · have : Nonempty U₀ := hO.ne.to_subtype
    have : IsDominant U₀.ι := ⟨by
      rw [DenseRange, Scheme.Opens.range_ι]
      exact U₀.isOpen.dense hO.ne⟩
    have := ρ.P.isAb.comm
    refine hypS_of_densePart U₀.ι hO.normal Q.G Q.L (GlobalTheory.existsUnique_hom_extension_semiAbelian_normal hdvr _ _ U₀.ι hX inferInstance inferInstance
      inferInstance inferInstance _ _ Q.semi Q.semi) ?_
    have hP := ρ.P.isLB
    have h₁ : HypS ((Over.pullback Q.u₀).obj ρ.P.A) (Q.L.L.pull Q.φ) :=
      SymBaseChange.hypS_baseChange _ _ ρ.P.A ((Over.pullback Q.u₀).obj ρ.P.A) Q.u₀ (pullback.fst ρ.P.A.hom Q.u₀) _ _ hP (pull_isLB hL _)
        (isGrpPullback_pullback _ _) ⟨Q.w, Q.w_gen⟩ ρ.hypS
    let ψ := Q.cart.1.lift (pullback.fst Q.G.hom U₀.ι) (pullback.snd _ _) pullback.condition
    have hψ : ψ ≫ Q.φ = pullback.fst Q.G.hom U₀.ι := Q.cart.1.lift_fst _ _ _
    refine SymBaseChange.hypS_baseChange _ _ ((Over.pullback Q.u₀).obj ρ.P.A) ((Over.pullback U₀.ι).obj Q.G) (𝟙 _) ψ _ _ (pull_isLB hL _) (pull_isLB hL _)
      (Q.cart.cancel ((isGrpPullback_pullback Q.G U₀.ι).congr (Category.id_comp _).symm hψ.symm)
        ((Q.cart.1.lift_snd _ _ _).trans (Category.comp_id _).symm)) ?_ h₁
    refine (cls_eq_iff (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _)).1 ?_
    exact (congrArg (CechPic.pull · (cls _ hL)) hψ.symm).trans (pull_comp ψ Q.φ (cls _ hL))
  · intro n x x' hx ε ε' _ _ h
    have := smooth_tensorObj_hom Q.G Q.G
    have := geometricallyIntegral_tensorObj_hom Q.G Q.G
    have h0 : CechPic.pull (eSec Q.G) (cls Q.L.L hL) = 0 :=
      (cls_eq_zero_iff (pull_isLB hL _)).2 ⟨Q.L.rig, Q.L.rigGen⟩
    have key : ∀ (y : Fin n → (Q.G ⊗ Q.G ⟶ Q.G)) (δ : Fin n → ℤ), (∀ i, IsMonHom (y i)) →
        CechPic.pull (η[Q.G ⊗ Q.G]).left (cls _ (LB.isLB_linComb hL (fun i => (y i).left) δ)) = 0 := by
      intro y δ hy
      set_option synthInstance.maxHeartbeats 100000 in
        rw [cls_linComb hL, map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [map_zsmul, ← pull_comp, ← Over.comp_left, (hy i).one_hom]
      exact (congrArg (_ • ·) h0).trans (smul_zero _)
    refine (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).1
      (pic_ext M.pt hO.normal (Q.G ⊗ Q.G) (η[Q.G ⊗ Q.G]).left (Over.w _)
        ((key x ε fun i => (hx i).1).trans (key x' ε' fun i => (hx i).2).symm) ?_)
    exact (cls_eq_iff (pull_isLB (LB.isLB_linComb hL _ _) _) (pull_isLB (LB.isLB_linComb hL _ _) _)).2 h

end GlobalTheory.ZH.EndoExtend
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsArcSeriesIntegralAlgebraicOverPowerSeries
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.ArcSeries

theorem exists_root_system {K : Type} [Field K] [IsAlgClosed K] (u : Kˣ) : ∃ r, Roots u r := by
  have hs : ∀ (n : ℕ) (x : Kˣ), ∃ y : Kˣ, y ^ (n + 1) = x := fun n x => by
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (x : K) n.succ_pos
    exact ⟨Units.mk0 y fun e => x.ne_zero (by rw [← hy, e]; simp), Units.ext hy⟩
  choose rt hrt using hs
  let s : ℕ → Kˣ := fun n => Nat.rec u (fun n x => rt n x) n
  have h1 : ∀ n d, s (n + d) ^ ((n + d).factorial / n.factorial) = s n := fun n d => by
    induction d with
    | zero => simp [Nat.div_self n.factorial_pos]
    | succ d ih =>
      rw [← add_assoc, Nat.factorial_succ, Nat.mul_div_assoc _ (Nat.factorial_dvd_factorial (Nat.le_add_right _ _)),
        pow_mul]
      exact (congrArg (· ^ _) (hrt _ _)).trans ih
  refine ⟨fun n => s n ^ (n.factorial / n), ?_, fun n m hn hm => ?_⟩
  · change s 1 ^ 1 = u
    exact hrt 0 u
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Nat.le_mul_of_pos_right n hm)
    have a := h1 n d
    rw [← hd] at a
    change (s (n * m) ^ ((n * m).factorial / (n * m))) ^ m = s n ^ (n.factorial / n)
    rw [← a, ← pow_mul, ← pow_mul]
    congr 1
    obtain ⟨p, hp⟩ := Nat.dvd_factorial (Nat.mul_pos hn hm) le_rfl
    obtain ⟨q, hq⟩ := Nat.dvd_factorial hn le_rfl
    obtain ⟨t, ht⟩ := Nat.factorial_dvd_factorial (Nat.le_mul_of_pos_right n hm)
    have e1 : (n * m).factorial / (n * m) = p := by rw [hp]; exact Nat.mul_div_cancel_left _ (Nat.mul_pos hn hm)
    have e2 : n.factorial / n = q := by rw [hq]; exact Nat.mul_div_cancel_left _ hn
    have e3 : (n * m).factorial / n.factorial = t := by rw [ht]; exact Nat.mul_div_cancel_left _ n.factorial_pos
    rw [e1, e2, e3]
    refine Nat.eq_of_mul_eq_mul_left hn ?_
    rw [hp, hq] at ht
    linarith

theorem base_local {O : Type} [CommRing O] [IsDomain O] {ϖ : O} (h : GlobalTheory.LN.ArcBase O ϖ) :
    IsLocalRing O ∧ IsPrincipalIdealRing O := by
  rcases h with ⟨h, -⟩ | ⟨h, -⟩
  · letI := h.toField
    exact ⟨inferInstance, inferInstance⟩
  · exact ⟨inferInstance, inferInstance⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)

theorem exists_reps {n : ℕ} (hn : 0 < n) : ∃ (Ix : Type) (_ : Finite Ix) (t : Ix → D.La), ∀ a, ∃ i e, t i = a + n • e := by
  have := D.fin
  have : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  let P : Submodule ℤ D.La := LinearMap.range ((n : ℤ) • LinearMap.id)
  have : Finite (D.La ⧸ P) := Module.finite_of_fg_torsion (M := D.La ⧸ P) fun x => by
    obtain ⟨x, rfl⟩ := P.mkQ_surjective x
    refine ⟨⟨n, mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hn.ne')⟩, ?_⟩
    change (n : ℤ) • P.mkQ x = 0
    rw [← map_smul]
    exact (Submodule.Quotient.mk_eq_zero P).2 ⟨x, rfl⟩
  refine ⟨D.La ⧸ P, this, Quotient.out, fun a => ?_⟩
  obtain ⟨e, he⟩ := (Submodule.Quotient.eq P).1 (Quotient.out_eq (Submodule.Quotient.mk a : D.La ⧸ P))
  exact ⟨_, e, by rw [← natCast_zsmul]; exact (eq_add_of_sub_eq' he.symm)⟩

theorem eq_zero_of_nsmul {n : ℕ} (hn : n ≠ 0) (a : D.La) (h : n • a = 0) : a = 0 := by
  refine D.unimod.1 (LinearMap.ext fun y => ?_)
  have := congrArg (fun x => D.EF x y) h
  simp only [map_nsmul, LinearMap.smul_apply, map_zero, LinearMap.zero_apply, nsmul_eq_mul, mul_eq_zero,
    Nat.cast_eq_zero, hn, false_or] at this
  rw [this, map_zero, LinearMap.zero_apply]

theorem exists_series : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllA fun {E} _ _ _ {H} {D} {l} {Xo} {c} {W₀} Y {O'} _ _ {b} a => ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing O') K] [Algebra (PowerSeries O') K] [FaithfulSMul (PowerSeries O') K] [Algebra.IsAlgebraic (PowerSeries O') K], (∀ x, algebraMap (FractionRing O') K (algebraMap O' _ x) = algebraMap (PowerSeries O') K (PowerSeries.C x)) → Nonempty (Ser a K (algebraMap _ K)) := by
  intro hHV _ _ _ _ _ _ E _ _ _ H D l Xo c W₀ Y O' _ _ _ b ϖ a hB K _ _ _ _ _ _ hK
  have hL : Laws := hHV.1.1
  have hL2 : Laws2 := hHV.1.2.1
  have gt := _root_.GlobalTheory.Ex.GtValues.points_correspond
  have wp := _root_.GlobalTheory.WeilValues.weil_eq_values gt (_root_.GlobalTheory.Ex.brFam hL hL2)
  obtain ⟨_, _⟩ := base_local hB
  let F := AlgebraicClosure (FractionRing O')
  obtain ⟨S₀, hS₀⟩ := _root_.GlobalTheory.LN.exists_valuationSubring_isIntegral O' ϖ hB F
  have hin : ∀ r : O', algebraMap (FractionRing O') F (algebraMap O' _ r) ∈ S₀ := fun r =>
    (hS₀ _).2 (by rw [← IsScalarTower.algebraMap_apply]; exact isIntegral_algebraMap)
  obtain ⟨A₀, hA₀⟩ := _root_.GlobalTheory.Ex.ArcLift.exists_lift hL gt E H D l Xo c W₀ Y O' b ϖ a hB F S₀ hin
  let io : F →+* K := (IsAlgClosed.lift : F →ₐ[FractionRing O'] K).toRingHom
  have hio : io.comp (algebraMap (FractionRing O') F) = algebraMap (FractionRing O') K :=
    (IsAlgClosed.lift : F →ₐ[FractionRing O'] K).comp_algebraMap
  obtain ⟨A, -, I₀, l₀, -, -, x₀, q₀⟩ :=
    _root_.GlobalTheory.LiftExt.exists_lift_ext hL gt wp E H D l Xo c W₀ Y O' b ϖ a hB F K io hio ⊤ (fun _ => trivial) A₀
  have hinj := FaithfulSMul.algebraMap_injective (PowerSeries O') K
  have hX : algebraMap (PowerSeries O') K PowerSeries.X ≠ 0 := (map_ne_zero_iff _ hinj).2 PowerSeries.X_ne_zero
  obtain ⟨r, hr⟩ := exists_root_system (Units.mk0 _ hX)
  have hr1 : (r 1 : K) = algebraMap (PowerSeries O') K PowerSeries.X := by rw [hr.1]; rfl
  obtain ⟨iθ, iσ, ith, iψ⟩ := _root_.GlobalTheory.Ex.UnitVal.integral_values O' a.D₀ F S₀ hin A₀.N A₀.ν hA₀
  have level : ∀ (m j : ℕ) (z : D.La), ∃ (R₁ : Subalgebra (PowerSeries O') K) (v w : D.La → K), Odd m → 0 < j →
      Module.Finite (PowerSeries O') R₁ ∧ (∀ x, v x ∈ R₁) ∧
      Sums (PowerSeries.X : PowerSeries O') io A₀.N A₀.be.be m j (A₀.q (m ^ 2)) (A₀.q j z) (r (m ^ 2 * j)) v w := by
    intro m j z
    by_cases h : Odd m ∧ 0 < j
    swap
    · exact ⟨⊥, 0, 0, fun a b => (h ⟨a, b⟩).elim⟩
    obtain ⟨hm, hj⟩ := h
    have hm2 : 0 < m ^ 2 := pow_pos hm.pos 2
    obtain ⟨Ix, _, t, ht⟩ := exists_reps D hm2
    let k : Option Ix → ℕ := fun i => i.elim j fun _ => m ^ 2
    let p : ∀ i, A₀.N.QT (k i) := fun i => match i with
      | none => A₀.q j z
      | some i => A₀.q (m ^ 2) (t i)
    obtain ⟨K₁, A₁, f1, f2, f3, f4, f5, f6, f7⟩ :=
      _root_.GlobalTheory.FiniteValues.exists_finite_field_of_values O' a.D₀ F A₀.N A₀.ν (Set.range fun i => (p i).1.2.b) (Set.finite_range _)
    obtain ⟨O₁, _, N₀, I, hI, hp⟩ := _root_.GlobalTheory.Ex.TorsDesc.descend O' F S₀ hS₀ A₀.N K₁ A₁ f1 f3 f4 f5 f6 f7 iθ iσ ith (iψ a.gen) (Option Ix) k p
      (fun i => by cases i; exacts [hj, hm2]) fun i => f2 _ ⟨i, rfl⟩
    have : FaithfulSMul O' F := (faithfulSMul_iff_algebraMap_injective _ _).2 (by
      rw [IsScalarTower.algebraMap_eq O' (FractionRing O') F]
      exact (algebraMap (FractionRing O') F).injective.comp (IsFractionRing.injective O' _))
    have : Module.Free O' O₁ := Module.free_of_finite_type_torsion_free'
    obtain ⟨R₁, v, w, h⟩ := exists_sums (O := O') O₁.val.toRingHom io (fun x => by
        rw [← hK, ← hio]; rfl) A₀.be.be hm hj (A₀.q (m ^ 2)) (A₀.q j z) (r (m ^ 2 * j))
      (by rw [← Units.val_pow_eq_pow_val, hr.pow (Nat.mul_pos hm2 hj)]; rfl) I hI
      (fun x => by
        obtain ⟨i, e, he⟩ := ht x
        exact hp (some i) _ (((_root_.GlobalTheory.Ex.arcF_values_add_ker_onto gt E H D O' F A₀.arc _ hm2).2.1 _ _).2 ⟨e, he⟩))
      (hp none _ ((A₀.N.qEq_equivalence _).refl _))
    exact ⟨R₁, v, w, fun _ _ => h⟩
  choose R₁ v w hlev using level
  have ext : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
      [Algebra (FractionRing O') C] (gam : K →+* C),
      (∀ x, algebraMap (FractionRing O') C (algebraMap O' _ x) = gam (algebraMap (PowerSeries O') K (PowerSeries.C x))) →
      (∀ f, ‖gam (algebraMap (PowerSeries O') K f)‖ ≤ 1) → ∃ A' : Lift a C, A'.ν.IntN ∧ A.arc.Over gam A'.arc ∧
        ∃ I : NumD.Hom (gam.comp io) A₀.N A'.N, I.lam = 1 ∧ (∀ y z, A'.be.be (I.e y) (I.e z) = A₀.be.be y z) ∧
          ∀ n x, (A'.q n x).1.1.toAdd = I.e (A₀.q n x).1.1.toAdd ∧ I.Rel (A₀.q n x).1.2 (A'.q n x).1.2 := by
    intro C _ _ _ _ gam h1 h2
    obtain ⟨S, hS⟩ := exists_ball C
    obtain ⟨A', hA', I₁, l₁, r₁, z₁, x₁, q₁⟩ := _root_.GlobalTheory.LiftExt.exists_lift_ext hL gt wp E H D l Xo c W₀ Y O' b ϖ a hB K C gam
      (IsLocalization.ringHom_ext (nonZeroDivisors O') (RingHom.ext fun x => (congrArg gam (hK x)).trans (h1 x).symm))
      S (fun x => (hS _).2 (by rw [h1]; exact h2 _)) A
    refine ⟨A', ⟨S, hS, hA'⟩, ⟨I₁, r₁, z₁, fun s y => A'.ν.eX.injective ?_, fun n x _ =>
      ⟨A'.q n x, (q₁ n x).1, (q₁ n x).2, (A'.N.qEq_equivalence _).refl _⟩⟩, homComp I₀ I₁ _ fun _ => rfl, ?_, fun y z => ?_,
      fun n x => ⟨(q₁ n x).1.trans (congrArg I₁.e (q₀ n x).1), homComp_rel _ _ _ _ (q₀ n x).2 (q₁ n x).2⟩⟩
    · change A'.ν.eX (I₁.e (A.ν.eX.symm (s • A.ν.eX y))) = A'.ν.eX (A'.ν.eX.symm (s • A'.ν.eX (I₁.e y)))
      exact ((x₁ _).trans (A.ν.eX.apply_symm_apply _)).trans
        ((A'.ν.eX.apply_symm_apply _).trans (congrArg (s • ·) (x₁ y))).symm
    · change I₁.lam * Units.map _ I₀.lam = 1
      rw [l₁, l₀, map_one, _root_.mul_one]
    · change A'.be.be (I₁.e (I₀.e y)) (I₁.e (I₀.e z)) = _
      rw [A'.be_eq, A₀.be_eq, x₁, x₁, x₀, x₀]
  have hrm : ∀ m j, Odd m → 0 < j → r (m ^ 2) = r (m ^ 2 * j) ^ j ∧ r j = r (m ^ 2 * j) ^ m ^ 2 := fun m j hm hj =>
    ⟨(hr.2 _ _ (pow_pos hm.pos 2) hj).symm, by rw [mul_comm]; exact (hr.2 _ _ hj (pow_pos hm.pos 2)).symm⟩
  refine ⟨⟨⟨inferInstance, hinj, fun x => Algebra.IsAlgebraic.isAlgebraic (R := PowerSeries O') x, hK⟩, A, r, hr1,
    ⟨rfl, hr.2⟩, fun m => v m 1 0, w, ?_, ?_⟩⟩
  · intro n j hp ho hu hj S hS
    have hm : Odd (n ^ j) := ho.pow
    obtain ⟨hfin, hmem, hsum⟩ := hlev (n ^ j) 1 0 hm one_pos
    have hvS : ∀ x, v (n ^ j) 1 0 x ∈ S := fun x =>
      mem_of_isIntegral S hS ((Algebra.IsIntegral.isIntegral (⟨_, hmem x⟩ : R₁ (n ^ j) 1 0)).map (R₁ _ _ _).val)
    have key : ∀ e : ℕ, ∃ (C : Type) (_ : NormedField C) (gam : K →+* C) (u : ℝ), 0 < u ∧ u < 1 ∧
        (∀ x, S.valuation (v (n ^ j) 1 0 x) < 1 → ‖gam (v (n ^ j) 1 0 x)‖ < 1 ∧
          (S.valuation (algebraMap (PowerSeries O') K PowerSeries.X) = 1 → ‖gam (v (n ^ j) 1 0 x)‖ ≤ u ^ e)) ∧
        (∃ x, 1 ≤ ‖gam (v (n ^ j) 1 0 x)‖) ∧ ∀ x, ∃ h, u ^ (A₀.be.be (A₀.q ((n ^ j) ^ 2) x).1.1.toAdd
          (A₀.q ((n ^ j) ^ 2) x).1.1.toAdd).toNat ≤ ‖gam (v (n ^ j) 1 0 (x + n ^ (j - 1) • h))‖ := by
      intro e
      obtain ⟨C, _, _, _, _, gam, g1, g2, g3⟩ := _root_.GlobalTheory.exists_valuedField_centre_le_pow (PowerSeries O') K PowerSeries.X
        (fun h => not_isUnit_zero (by simpa using h.map PowerSeries.constantCoeff : IsUnit (0 : O')))
        PowerSeries.X_ne_zero _ hfin S hS e
      letI : Algebra (FractionRing O') C := (gam.comp (algebraMap _ K)).toAlgebra
      have h1 : ∀ x, algebraMap (FractionRing O') C (algebraMap O' _ x) =
          gam (algebraMap (PowerSeries O') K (PowerSeries.C x)) := fun x => congrArg gam (hK x)
      have hce : CExt O' ⊥ C := ⟨fun x => by rw [h1]; exact g1 _, fun x hx => by
        rw [(Submodule.mem_bot _).1 hx]; simp⟩
      obtain ⟨A', hN, -, I, hI, hβ, hq⟩ := ext C gam h1 g1
      let r' : ℕ → Cˣ := fun n => Units.map gam.toMonoidHom (r n)
      have hu' : (r' 1 : C) = gam (algebraMap (PowerSeries O') K PowerSeries.X) := congrArg gam hr1
      have hu1 : ‖(r' 1 : C)‖ < 1 := hu' ▸ g2
      have hpow : r' ((n ^ j) ^ 2) ^ (n ^ j) ^ 2 = r' 1 := by
        rw [← map_pow, hr.pow (pow_pos hm.pos 2), ← hr.1]
      have hn : ‖(n : C)‖ = 1 := by
        obtain ⟨y, hy⟩ := hu.exists_right_inv
        have a1 := hce.1 n
        have a2 := hce.1 y
        have a3 := congrArg (fun x => ‖algebraMap (FractionRing O') C (algebraMap O' _ x)‖) hy
        simp only [map_mul, map_natCast, map_one, norm_mul, norm_one] at a1 a3
        nlinarith [norm_nonneg (n : C)]
      obtain ⟨qf, hq1, hq2⟩ := (_root_.GlobalTheory.Ex.UnitNorm.norms_of_arc_input E H D l Xo c W₀ Y O' b ϖ a hB C hce A' hN).2.2 (r' 1) hu1
      choose p hp' using fun x => (existsUnique_twRel A'.be (r' 1) _ hpow (A'.q _ x)).exists
      obtain ⟨t1, t2, t3⟩ := _root_.GlobalTheory.Ex.arcF_values_add_ker_onto gt E H D O' C A'.arc _ (pow_pos hm.pos 2)
      obtain ⟨c1, c2⟩ := _root_.GlobalTheory.twist_tx_coset_norm_ge C A'.N _ A'.be (r' 1) _ qf n _ j hp ho hn hj hu1 hpow hq1 hq2
        (_root_.GlobalTheory.ValuesTorsion.tors_of_integral hL hL2 (_root_.GlobalTheory.ThetaInValues.brUth_of_laws hL) O' a.D₀ a.even a.bimult C hce A'.N A'.ν hN n hp ho hn)
        D.La (A'.q _) (eq_zero_of_nsmul D hp.ne_zero) t1 t2 t3 p hp'
      have hv := (hsum C gam g1 g2 A'.N I _ A'.be hI hβ (r' 1) (r' ((n ^ j) ^ 2)) (r' 1) hu'
        (by rw [← (hrm _ 1 hm one_pos).1]; rfl) (by rw [← (hrm _ 1 hm one_pos).2]; rfl) (A'.q _) p (hq _) hp').1
      refine ⟨C, inferInstance, gam, ‖(r' 1 : C)‖, norm_pos_iff.2 (r' 1).ne_zero, hu1,
        fun x hx => hu' ▸ g3 _ (hmem x) hx, by simpa only [hv] using c1, fun x => ?_⟩
      simpa only [hv, (hq _ x).1, hβ] using c2 x
    have hlt : ∀ x, S.valuation (v (n ^ j) 1 0 x) ≠ 1 → S.valuation (v (n ^ j) 1 0 x) < 1 := fun x h =>
      lt_of_le_of_ne ((S.valuation_le_one_iff _).2 (hvS x)) h
    refine ⟨hvS, ?_, fun hXu x => ?_⟩
    · obtain ⟨C, _, gam, u, -, -, k1, ⟨x, hx⟩, -⟩ := key 0
      exact ⟨x, not_not.1 fun h => (k1 x (hlt x h)).1.not_ge hx⟩
    · obtain ⟨C, _, gam, u, u0, u1, k1, -, k2⟩ := key ((A₀.be.be (A₀.q ((n ^ j) ^ 2) x).1.1.toAdd
        (A₀.q ((n ^ j) ^ 2) x).1.1.toAdd).toNat + 1)
      obtain ⟨h, hh⟩ := k2 x
      exact ⟨h, not_not.1 fun hne => (hh.trans ((k1 _ (hlt _ hne)).2 hXu)).not_gt
        (pow_lt_pow_right_of_lt_one₀ u0 u1 (Nat.lt_succ_self _))⟩
  · intro C _ _ _ _ _ gam u h1 g1 hu hu1
    obtain ⟨A', hN, hO, I, hI, hβ, hq⟩ := ext C gam h1 g1
    refine ⟨A', fun n => Units.map gam.toMonoidHom (r n), hN, hO, fun _ => rfl, fun m hm p hp => ?_⟩
    have S := fun j z hj => (hlev m j z hm hj).2.2 C gam g1 (by rw [hu] at hu1; exact hu1) A'.N I _ A'.be hI hβ u
      (Units.map gam.toMonoidHom (r (m ^ 2))) (Units.map gam.toMonoidHom (r j)) hu
      (by rw [← (hrm _ j hm hj).1]; rfl) (by rw [← (hrm _ j hm hj).2]; rfl) (A'.q _) p (hq _) hp
    exact ⟨⟨1, fun x => by rw [Units.val_one, _root_.one_mul]; exact (S 1 0 one_pos).1 x⟩,
      fun j hj z q hq' => (S j z hj).2 (A'.q j z) q (hq j z).1 (hq j z).2 hq'⟩

end GlobalTheory.ArcSeries
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSemiAbelianSplitCubicalExtensionClosureStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semiAbelian_split_cubical_extension_closure : Out.Laws → ∀ (C : Core) (T : C.Theta) (n : ℕ), C.HasTests → C.Indep → C.HasCharts → C.TorsSec n → T.Few n → ∃ L : C.Law, letI := L.grp; letI := L.comm; SplitAll C.GG ∧ IsSemiAbelian C.GG ∧ ∃ (PP : RigLB C.GG) (cub : CubicalStr C.GG PP) (m : CubeMap C.A C.GG), m.F = C.a ∧ m.e = C.U.ι ∧ m.IsPullCubical T.cub cub ∧ (T.L.IsSymmetric → PP.IsSymmetric) ∧ (∀ z : C.Z, ∃ (N : C.Z.Opens) (σ : LB.Sec (PP.L.pull (C.GG.hom ⁻¹ᵁ N).ι)), z ∈ N ∧ ∀ z' ∈ N, ∃ x ∈ Out.nonzeroLocus σ, C.GG.hom ((C.GG.hom ⁻¹ᵁ N).ι x) = z') ∧ ∀ z : C.Z, ∃ N : C.Z.Opens, z ∈ N ∧ LBIso (T.O₁.pull (C.GG.hom ⁻¹ᵁ N).ι) ((PP.L.pull (mulN C.GG T.m).left).pull (C.GG.hom ⁻¹ᵁ N).ι) := by
  first | exact @GlobalTheory.ZJ.Assembly.exists_law_splitAll_cubical | exact GlobalTheory.ZJ.Assembly.exists_law_splitAll_cubical | (intros; apply GlobalTheory.ZJ.Assembly.exists_law_splitAll_cubical <;> assumption)
end

