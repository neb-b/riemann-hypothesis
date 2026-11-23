module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGrpPullbackThick
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0071
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianSectionsProportionalOfCoordinates
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory.UT GlobalTheory.ZH.ClassWeight

noncomputable section
namespace GlobalTheory.ZH.SecProp
open GlobalTheory.ZH.CrdCalc

section
variable {F : Type} [Field F] [IsAlgClosed F] {Y : Scheme.{0}} (p : Y ⟶ Sp F) [LocallyOfFiniteType p]

theorem exists_point {Z : Set Y} (hZ : IsLocallyClosed Z) (hn : Z.Nonempty) :
    ∃ r : Sp F ⟶ Y, r ≫ p = 𝟙 _ ∧ ∀ z, r z ∈ Z := by
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace p
  obtain ⟨c, hcW, hc⟩ := nonempty_inter_closedPoints hn hZ
  exact ⟨pointOfClosedPoint p c hc, pointOfClosedPoint_comp p c hc,
    fun z => (congrArg (· ∈ Z) (pointOfClosedPoint_apply p c hc z)).mpr hcW⟩

theorem fn_ext_valR [IsReduced Y] {U : Y.Opens} {a b : Γ(Y, U)}
    (h : ∀ r : Sp F ⟶ Y, r ≫ p = 𝟙 _ → ⊤ ≤ r ⁻¹ᵁ U → valR r U a = valR r U b) : a = b := by
  rw [← sub_eq_zero, ← basicOpen_eq_bot_iff]
  by_contra hne
  have hn : ((Y.basicOpen (a - b) : Y.Opens) : Set Y).Nonempty :=
    Set.nonempty_iff_ne_empty.2 fun e => hne (SetLike.coe_injective e)
  obtain ⟨r, hr, hz⟩ := exists_point p (Y.basicOpen (a - b)).isOpen.isLocallyClosed hn
  have hU : ⊤ ≤ r ⁻¹ᵁ U := fun z _ => Y.basicOpen_le _ (hz z)
  have hu := (isUnit_valR_iff r U hU (a - b)).2 fun z _ => hz z
  have e := h r hr hU
  rw [valR_eq r U hU, valR_eq r U hU, ← sub_eq_zero, ← map_sub] at e
  rw [valR_eq r U hU, e] at hu
  exact not_isUnit_zero hu

variable {H : LB Y} {I : Type} {a b : I → H.Sec}

theorem exists_mem_basicOpen (h : ∀ r : Sp F ⟶ Y, r ≫ p = 𝟙 _ → ∃ w, w ≠ 0 ∧ Crd H b r w) (l : H.ι) (y : Y)
    (hy : y ∈ H.U l) : ∃ i, y ∈ Y.basicOpen ((b i).f l) := by
  by_contra hne
  let V : Y.Opens := ⨆ i, Y.basicOpen ((b i).f l)
  have hyV : y ∉ V := fun e => hne (TopologicalSpace.Opens.mem_iSup.1 e)
  obtain ⟨r, hr, hz⟩ := exists_point p
    ((H.U l).isOpen.isLocallyClosed.inter V.isOpen.isClosed_compl.isLocallyClosed) ⟨y, hy, hyV⟩
  obtain ⟨w, hw, hc⟩ := h r hr
  have hU : ⊤ ≤ r ⁻¹ᵁ H.U l := fun z _ => (hz z).1
  obtain ⟨c, hc'⟩ := crd_unique hc
    (⟨l, 1, hU, fun j => by simp⟩ : Crd H b r (fun i => valR r (H.U l) ((b i).f l)))
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hw
  have hu : IsUnit (valR r (H.U l) ((b i).f l)) := by
    rw [hc' i]
    exact c.isUnit.mul (Ne.isUnit hi)
  have z : Sp F := IsLocalRing.closedPoint F
  exact (hz z).2 (TopologicalSpace.Opens.mem_iSup.2 ⟨i, (isUnit_valR_iff r _ hU _).1 hu (Set.mem_univ z)⟩)

theorem cross_eq [IsReduced Y] (h : ∀ r : Sp F ⟶ Y, r ≫ p = 𝟙 _ → ∃ w, Crd H a r w ∧ Crd H b r w) (l : H.ι)
    (i i' : I) : (a i).f l * (b i').f l = (a i').f l * (b i).f l := by
  refine fn_ext_valR p fun r hr hU => ?_
  obtain ⟨w, ha, hb⟩ := h r hr
  obtain ⟨c, hc⟩ := crd_unique ha
    (⟨l, 1, hU, fun j => by simp⟩ : Crd H a r (fun i => valR r (H.U l) ((a i).f l)))
  obtain ⟨d, hd⟩ := crd_unique hb
    (⟨l, 1, hU, fun j => by simp⟩ : Crd H b r (fun i => valR r (H.U l) ((b i).f l)))
  rw [valR_mul r _ hU, valR_mul r _ hU, hc i, hc i', hd i, hd i']
  ring

end

theorem valR_const {F : Type} [Field F] {Y : Scheme.{0}} (p : Y ⟶ Sp F) (r : Sp F ⟶ Y) (hr : r ≫ p = 𝟙 _)
    (U : Y.Opens) (hU : ⊤ ≤ r ⁻¹ᵁ U) (a : F) :
    valR r U (resG Y le_top (p.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom a))) = a := by
  rw [valR_res r le_top hU, valR_eq r ⊤ le_rfl]
  have e : r.appLE ⊤ ⊤ le_rfl = r.appTop := (Scheme.Hom.app_eq_appLE r).symm
  have e₂ : p.appTop ≫ r.appTop = 𝟙 _ := by rw [← Scheme.Hom.comp_appTop, hr, Scheme.Hom.id_appTop]
  change (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom ((p.appTop ≫ r.appLE ⊤ ⊤ le_rfl).hom _) = a
  rw [e, e₂]
  exact (Scheme.ΓSpecIso (CommRingCat.of F)).inv_hom_id_apply a

theorem proportional_of_crd : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (k : ℕ) (I J : Type) [Fintype J] (t : I → SecA A F k) (s : J → SecA A F k) (b : Matrix I J F), (∀ x : TFK (R := R) F ⟶ A.A, ∃ v : J → F, b.mulVec v ≠ 0 ∧ Crd (LPow A.A A.L (k : ℤ) (TFK (R := R) F)) s (show Sp F ⟶ _ from (ptSecT A.A x).left) v ∧ Crd (LPow A.A A.L (k : ℤ) (TFK (R := R) F)) t (show Sp F ⟶ _ from (ptSecT A.A x).left) (b.mulVec v)) → ∃ c : F, ∀ i, ∑ j, kf R F (b i j) • SecM.ofSec A.A (s j) = kf R F c • SecM.ofSec A.A (t i) := by
  intro hG R _ _ A F _ _ _ k I J _ t s b H
  have hsm := A.isAb.smooth
  let T : Over (Spec (CommRingCat.of (FractionRing R))) := TFK (R := R) F
  let p : (T ⊗ A.A).left ⟶ Sp F := (fst T A.A).left
  have hp : Smooth p := inferInstanceAs (Smooth (pullback.fst T.hom A.A.hom))
  have : IsReduced (T ⊗ A.A).left := GlobalTheory.isReduced_of_smooth_of_isReduced p
  let m : I → SecM A.A A.L (k : ℤ) T := fun i => ∑ j, kf R F (b i j) • SecM.ofSec A.A (s j)
  let t' : I → SecA A F k := fun i => SecM.toSec A.A (m i)
  have key : ∀ r : Sp F ⟶ (T ⊗ A.A).left, r ≫ p = 𝟙 _ →
      ∃ w, w ≠ 0 ∧ Crd (LPow A.A A.L (k : ℤ) T) t' r w ∧ Crd (LPow A.A A.L (k : ℤ) T) t r w := by
    intro r hr
    let r' : T ⟶ T ⊗ A.A := Over.homMk r (by
      rw [← Over.w (fst T A.A), ← Category.assoc]
      exact (congrArg (· ≫ T.hom) hr).trans (Category.id_comp _))
    have er : ptSecT A.A (r' ≫ snd _ _) = r' := by
      refine CartesianMonoidalCategory.hom_ext _ _ ?_ (lift_snd _ _)
      rw [ptSecT, lift_fst]
      exact Over.OverMorphism.ext hr.symm
    obtain ⟨v, hv, hs, ht⟩ := H (r' ≫ snd _ _)
    have er' : (ptSecT A.A (r' ≫ snd _ _)).left = r := congrArg (·.left) er
    replace hs : Crd (LPow A.A A.L (k : ℤ) T) s r v := er' ▸ hs
    replace ht : Crd (LPow A.A A.L (k : ℤ) T) t r (b.mulVec v) := er' ▸ ht
    refine ⟨_, hv, ?_, ht⟩
    obtain ⟨l, c, hl, hc⟩ := hs
    refine ⟨l, c, hl, fun i => ?_⟩
    have e : (t' i).f l = ∑ j, resG _ le_top (p.appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (b i j))) * (s j).f l := by
      change (m i).1 l = _
      simp only [m, Submodule.coe_sum, Finset.sum_apply]
      rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, valR_eq r _ hl, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← valR_eq r _ hl, valR_mul r _ hl, valR_const p r hr _ hl, hc j, mul_left_comm]
  obtain ⟨c₀, hc₀⟩ := SectionRatio.exists_ratio A.isLB (φ := fun _ : Fin 1 => (snd T A.A).left)
    (ε := fun _ => (k : ℤ)) t' t
    (fun y J hJ => by
      have hm := hJ.mem (fun _ : Fin 1 => (snd T A.A).left) (𝟙 _)
      obtain ⟨i, hi⟩ := exists_mem_basicOpen p (H := LPow A.A A.L (k : ℤ) T) (b := t)
        (fun r hr => (key r hr).imp fun w hw => ⟨hw.1, hw.2.2⟩) _ y hm
      exact ⟨i, (SectionRatio.mem_basicOpen_iff_gs _ y hm).1 hi⟩)
    (fun i i' y J hJ => by
      have hm := hJ.mem (fun _ : Fin 1 => (snd T A.A).left) (𝟙 _)
      have e := cross_eq p (H := LPow A.A A.L (k : ℤ) T) (a := t') (b := t)
        (fun r hr => (key r hr).imp fun w hw => hw.2) (fun _ => J (𝟙 _ ≫ (snd T A.A).left)) i i'
      exact (gs_mul _ y _ hm _ _).symm.trans ((congrArg (gs (𝟙 _) y _) e).trans (gs_mul _ y _ hm _ _)))
  obtain ⟨d, hd⟩ := CommPairing.surj_fst hG A.isAb T c₀
  obtain ⟨c, rfl⟩ := (kf_bijective R F).2 d
  refine ⟨c, fun i => ThetaAct.sv_ext A.isLB fun y J hJ => ?_⟩
  refine (hc₀ i y J hJ).trans (Eq.trans ?_ (ThetaAct.sv_smul _ _ _ _ hJ).symm)
  exact congrArg (· * _) ((congrArg (gs (𝟙 _) y ⊤) hd.symm).trans (gs_pull (𝟙 _) _ y ⊤ trivial _))

end GlobalTheory.ZH.SecProp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClosedImmersionBaseChangeProjChart
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

noncomputable section
namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

theorem IsHom.valR_mem_image_ringOn {o Ω Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [Field Ω'] [Algebra o Ω']
    {M : RatModel o Ω} {N : RatModel o Ω'} {φ : Ω →ₐ[o] Ω'} {Y : Scheme.{0}} {j : Y ⟶ M.Z} [IsOpenImmersion j]
    {b : N.Z ⟶ Y} (h : M.IsHom N φ (b ≫ j)) {V : Y.Opens} (hV : ⊤ ≤ (N.pt ≫ b) ⁻¹ᵁ V) (g : Γ(Y, V)) :
    valR (N.pt ≫ b) V g ∈ φ '' (M.ringOn (j ''ᵁ V : M.Z.Opens) : Set Ω) := by
  have hne : ((j ''ᵁ V : M.Z.Opens) : Set M.Z).Nonempty :=
    ⟨_, _, hV (x := IsLocalRing.closedPoint Ω') trivial, rfl⟩
  have hle : V ≤ j ⁻¹ᵁ (j ''ᵁ V) := (j.preimage_image_eq V).ge
  refine ⟨valF M.pt _ ((j.appIso V).inv.hom g), (mem_ringOn_iff_exists hne).2 ⟨_, rfl⟩, ?_⟩
  refine (valR_spMap_comp φ.toRingHom M.pt _ (M.top_le_preimage_pt hne) _).symm.trans ?_
  rw [← show N.pt ≫ b ≫ j = spMap φ.toRingHom ≫ M.pt from h, ← Category.assoc, ← valR_appLE _ j hle hV,
    ← CommRingCat.comp_apply, Scheme.Hom.appIso_inv_appLE]
  exact valR_res _ le_rfl hV g

theorem projChart_of_isPullback : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (φ : Ω →ₐ[o] Ω') (N : RatModel o Ω') (U₀ : M.Z.Opens) (R : Type) [CommRing R] (X : Scheme.{0}) (p : X ⟶ Sp R) (u₀ : U₀.toScheme ⟶ Sp R) (a : N.Z ⟶ X) (b : N.Z ⟶ U₀.toScheme) (H : LB X) (J : Type) (s : J → H.Sec) (t : J → Ω'), IsPullback a b p u₀ → M.IsHom N φ (b ≫ U₀.ι) → ImmBy p H s Set.univ → Crd H s (N.pt ≫ a) t → (∀ (i : J) (z : N.Z), N.Div t i z ↔ a z ∈ nonzeroLocus (s i)) → ∀ W : M.Z.Opens, W ≤ U₀ → IsAffineOpen W → (W : Set M.Z).Nonempty → M.ProjChart N φ (b ≫ U₀.ι) W t := by
  intro o Ω _ _ _ M Ω' _ _ φ N U₀ R _ X p u₀ a b H J s t sq hom imm crd hdiv W hWU hW hne
  obtain ⟨V, rfl⟩ : ∃ V : U₀.toScheme.Opens, U₀.ι ''ᵁ V = W :=
    ⟨U₀.ι ⁻¹ᵁ W, by rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]; exact inf_eq_right.2 hWU⟩
  have hV : IsAffineOpen V := U₀.ι.isAffineOpen_iff_of_isOpenImmersion.1 hW
  have hmem : ∀ z : N.Z, (b ≫ U₀.ι) z ∈ U₀.ι ''ᵁ V ↔ b z ∈ V := fun z =>
    Iff.of_eq (congrArg (b z ∈ ·) (U₀.ι.preimage_image_eq V))
  refine ⟨fun z _ => ?_, fun i hi => ?_⟩
  · have hz : a z ∈ ⨆ i ∈ (Set.univ : Set J), nonzeroLocus (s i) := by rw [imm.1]; trivial
    simp only [Set.mem_univ, iSup_pos, TopologicalSpace.Opens.mem_iSup] at hz
    obtain ⟨i, hi⟩ := hz
    exact ⟨i, (hdiv i z).2 hi⟩
  obtain ⟨hD, r, hr, hgen⟩ := imm.2 i trivial
  have hU : IsAffineOpen (a ⁻¹ᵁ nonzeroLocus (s i) ⊓ b ⁻¹ᵁ V) := by
    have : IsAffine _ := isAffineOpen_top (Sp R)
    have : IsAffine _ := hV
    have : IsAffine _ := hD
    exact .of_isIso (Scheme.Hom.isPullback_resLE sq (US := ⊤) (UT := V) (UX := nonzeroLocus (s i)) le_top le_top
      rfl).isoPullback.hom
  have hset : ((a ⁻¹ᵁ nonzeroLocus (s i) ⊓ b ⁻¹ᵁ V : N.Z.Opens) : Set N.Z) =
      {z' | (b ≫ U₀.ι) z' ∈ U₀.ι ''ᵁ V ∧ N.Div t i z'} :=
    Set.ext fun z => and_comm.trans (and_congr (hmem z).symm (hdiv i z).symm)
  refine ⟨_, hU, hset, le_antisymm (fun x hx => ?_) (Algebra.adjoin_le ?_)⟩
  · have hgp : (b ≫ U₀.ι) (genericPoint N.Z) ∈ U₀.ι ''ᵁ V := by
      have e := congrArg (fun f => f (IsLocalRing.closedPoint Ω')) (show N.pt ≫ b ≫ U₀.ι = _ from hom)
      rw [← N.pt_apply (IsLocalRing.closedPoint Ω')]
      refine (congrArg (· ∈ U₀.ι ''ᵁ V) e).mpr ?_
      exact M.top_le_preimage_pt hne (x := spMap φ.toRingHom (IsLocalRing.closedPoint Ω')) trivial
    have hUne : ((a ⁻¹ᵁ nonzeroLocus (s i) ⊓ b ⁻¹ᵁ V : N.Z.Opens) : Set N.Z).Nonempty :=
      ⟨_, hset.ge ⟨hgp, div_genericPoint hi⟩⟩
    have hpt := N.top_le_preimage_pt hUne
    have ha : ⊤ ≤ (N.pt ≫ a) ⁻¹ᵁ nonzeroLocus (s i) := le_preimage_comp _ a inf_le_left hpt
    have hb : ⊤ ≤ (N.pt ≫ b) ⁻¹ᵁ V := le_preimage_comp _ b inf_le_right hpt
    set A := Algebra.adjoin o (φ '' (M.ringOn (U₀.ι ''ᵁ V : M.Z.Opens) : Set Ω) ∪ Set.range fun j => t j / t i)
    have hB : ∀ g, valR (N.pt ≫ b) V g ∈ A := fun g =>
      Algebra.subset_adjoin (Or.inl (hom.valR_mem_image_ringOn hb g))
    have hA : ∀ g, valR (N.pt ≫ a) (nonzeroLocus (s i)) g ∈ A := fun g => by
      have : Subring.closure (Set.range (constFn p (nonzeroLocus (s i))) ∪ Set.range r) ≤
          A.toSubring.comap (valMap _ _ ha).hom := by
        rw [Subring.closure_le]
        rintro _ (⟨c, rfl⟩ | ⟨j, rfl⟩)
        · show (valMap _ _ ha).hom _ ∈ A
          rw [← valR_eq, valR_constFn _ _ _ ha, Category.assoc, sq.w, ← Category.assoc, ← valR_constFn _ _ _ hb]
          exact hB _
        · show (valMap _ _ ha).hom _ ∈ A
          rw [← valR_eq, eq_div_of_mul_eq hi (CrdCalc.crd_ratio crd (hr j) ha).symm]
          exact Algebra.subset_adjoin (Or.inr ⟨j, rfl⟩)
      rw [valR_eq _ _ ha]
      exact this (hgen.ge (Subring.mem_top g))
    have po := (isIso_pushoutSection_iff sq (US := ⊤) (UT := V) (UX := nonzeroLocus (s i)) le_top le_top rfl).1
      (isIso_pushoutSection_of_isAffineOpen sq _ _ _ (isAffineOpen_top _) hV hD)
    have hcl := CommRingCat.closure_range_union_range_eq_top_of_isPushout po
    have hle : (⊤ : Subring _) ≤ A.toSubring.comap (valMap _ _ hpt).hom := by
      rw [← hcl, Subring.closure_le]
      rintro _ (⟨g, rfl⟩ | ⟨g, rfl⟩)
      · show (valMap _ _ hpt).hom _ ∈ A
        rw [← valR_eq, valR_appLE _ _ _ hpt]
        exact hA g
      · show (valMap _ _ hpt).hom _ ∈ A
        rw [← valR_eq, valR_appLE _ _ _ hpt]
        exact hB g
    obtain ⟨f, rfl⟩ := (mem_ringOn_iff_exists hUne).1 hx
    rw [valF_eq_valR, valR_eq _ _ hpt]
    exact hle (Subring.mem_top f)
  · rintro _ (⟨x, hx, rfl⟩ | ⟨j, rfl⟩)
    · exact mem_ringOn.2 fun z hz => hom.map_mem_O (mem_ringOn.1 hx _ (hset.le hz).1)
    · exact mem_ringOn.2 fun z hz => (hset.le hz).2.2 j

end GlobalTheory.ZH.RatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DivIffMemNonzeroLocus
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

namespace GlobalTheory.ZH.DivCrd

open GlobalTheory.Points CrdCalc

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {N : RatModel o Ω} {X : Scheme.{0}} {a : N.Z ⟶ X}
  {H : LB X} {J : Type} {s : J → H.Sec} {t : J → Ω}

theorem ratio_eq (ht : Crd H s (N.pt ≫ a) t) {k : J} {z : N.Z} (hz : a z ∈ nonzeroLocus (s k)) :
    t k ≠ 0 ∧ ∀ (j : J) (r : Γ(X, nonzeroLocus (s k))), IsRatio (s j) (s k) _ r →
      valF N.pt (a ⁻¹ᵁ nonzeroLocus (s k)) (a.app _ r) = t j / t k := by
  have h : ⊤ ≤ (N.pt ≫ a) ⁻¹ᵁ nonzeroLocus (s k) :=
    N.top_le_preimage_pt (U := a ⁻¹ᵁ nonzeroLocus (s k)) ⟨z, hz⟩
  have hk : t k ≠ 0 := ((crd_isUnit_iff k ht).2 h).ne_zero
  refine ⟨hk, fun j r hr => ?_⟩
  rw [eq_div_iff hk, crd_ratio ht hr h, valR_comp]
  rfl

theorem div_of_mem (hH : H.IsLB) (ht : Crd H s (N.pt ≫ a) t) {k : J} {z : N.Z}
    (hz : a z ∈ nonzeroLocus (s k)) : N.Div t k z := by
  obtain ⟨hk, h⟩ := ratio_eq ht hz
  refine ⟨hk, fun j => ?_⟩
  obtain ⟨r, hr, -⟩ := GlobalTheory.SecRatio.existsUnique_isRatio hH (s j) (s k) _ le_rfl
  exact ⟨a ⁻¹ᵁ nonzeroLocus (s k), a.app _ r, hz, h j r hr⟩

theorem crd_eq_val_mul (hH : H.IsLB) (ht : Crd H s (N.pt ≫ a) t) {K : Type} [Field K] {x : Sp K ⟶ N.Z}
    {v : J → K} {k : J} (hv : Crd H s (x ≫ a) v)
    (hz : a (x (IsLocalRing.closedPoint K)) ∈ nonzeroLocus (s k)) :
    v k ≠ 0 ∧ ∀ j, v j = N.val x (t j / t k) * v k := by
  have hx : ⊤ ≤ x ⁻¹ᵁ (a ⁻¹ᵁ nonzeroLocus (s k)) := (le_preimage_iff x _).2 hz
  have h : ⊤ ≤ (x ≫ a) ⁻¹ᵁ nonzeroLocus (s k) := hx
  refine ⟨((crd_isUnit_iff k hv).2 h).ne_zero, fun j => ?_⟩
  obtain ⟨r, hr, -⟩ := GlobalTheory.SecRatio.existsUnique_isRatio hH (s j) (s k) _ le_rfl
  rw [RatModel.val_eq ((top_le_preimage_iff _ _).1 hx) ((ratio_eq ht hz).2 j r hr), crd_ratio hv hr h,
    valR_comp]
  rfl

theorem mem_of_div_pt (hH : H.IsLB) (hs : ⨆ j, nonzeroLocus (s j) = ⊤) (ht : Crd H s (N.pt ≫ a) t)
    {K : Type} [Field K] (x : Sp K ⟶ N.Z) {i : J} (hi : N.Div t i (x (IsLocalRing.closedPoint K))) :
    a (x (IsLocalRing.closedPoint K)) ∈ nonzeroLocus (s i) := by
  have hm : a (x (IsLocalRing.closedPoint K)) ∈ ⨆ j, nonzeroLocus (s j) := by rw [hs]; trivial
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hm
  obtain ⟨v, hv⟩ := crd_exists hH s (x ≫ a)
  obtain ⟨h0, h1⟩ := crd_eq_val_mul hH ht hv hk
  have hd := div_of_mem hH ht hk
  have hu := (RatModel.val_ne_zero_iff (RatModel.range_eq_singleton x _) _).2 ((hd.div_iff_isUnit i).1 hi)
  have hvi : IsUnit (v i) := isUnit_iff_ne_zero.2 (by rw [h1 i]; exact mul_ne_zero hu h0)
  exact (le_preimage_iff (x ≫ a) _).1 ((crd_isUnit_iff i hv).1 hvi)

theorem mem_of_div (hH : H.IsLB) (hs : ⨆ j, nonzeroLocus (s j) = ⊤) (ht : Crd H s (N.pt ≫ a) t)
    {i : J} {z : N.Z} (hi : N.Div t i z) : a z ∈ nonzeroLocus (s i) := by
  let x : Sp (N.Z.residueField z) ⟶ N.Z := N.Z.fromSpecResidueField z
  have e : x (IsLocalRing.closedPoint (N.Z.residueField z)) = z := Scheme.fromSpecResidueField_apply _ _
  have h := mem_of_div_pt hH hs ht x (i := i) (by rw [e]; exact hi)
  rwa [e] at h

theorem div_iff_mem_nonzeroLocus : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (N : RatModel o Ω) (X : Scheme.{0}) (a : N.Z ⟶ X) (H : LB X) (J : Type) (s : J → H.Sec) (t : J → Ω), H.IsLB → ⨆ j, nonzeroLocus (s j) = ⊤ → Crd H s (N.pt ≫ a) t → (∀ (i : J) (z : N.Z), N.Div t i z ↔ a z ∈ nonzeroLocus (s i)) ∧ ∀ (K : Type) [Field K] (x : Sp K ⟶ N.Z) (v : J → K) (k : J), Crd H s (x ≫ a) v → N.Div t k (x (IsLocalRing.closedPoint K)) → v k ≠ 0 ∧ ∀ j, v j = N.val x (t j / t k) * v k :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hH hs ht =>
    ⟨fun _ _ => ⟨mem_of_div hH hs ht, div_of_mem hH ht⟩,
      fun _ _ x _ _ hv hk => crd_eq_val_mul hH ht hv (mem_of_div_pt hH hs ht x hk)⟩

end GlobalTheory.ZH.DivCrd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsClassicalPointFactorLargeModel
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ZH
open GlobalTheory.Points

theorem ZHPre.exists_testFac_of_large : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Over₀ M U₀ → ∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y → ∃ (y₀ : S.R →+* PadicAlgCl p) (Fs : Finset (PadicAlgCl p)), S.At M y y₀ ∧ (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ ∀ u : ρ.UTest p y₀, (∀ x ∈ Fs, x ∈ Set.range (algebraMap (FractionRing u.V) (PadicAlgCl p))) → ∃ jV yV yK, Q.TestFac y u jV yV yK := by
  intro o Ω _ _ _ hA S ρ M U₀ Q hO z p _ y hy
  let w : Sp (PadicAlgCl p) := IsLocalRing.closedPoint (PadicAlgCl p)
  have hw : (gPt p ≫ y) w ∈ (U₀ : Set M.Z) := hy.2 ⟨w, rfl⟩
  have hle : S.R ≤ M.O ((gPt p ≫ y) w) := hO.le.trans (RatModel.ringOn_le_O hw)
  let y₀ : S.R →+* PadicAlgCl p :=
    (RatModel.valHom (gPt p ≫ y) _ (RatModel.range_eq_singleton _ w)).comp (Subalgebra.inclusion hle).toRingHom
  have hn : ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1 := fun a =>
    RatModel.norm_val_le_one (y := y) rfl (x := algebraMap o Ω a) ((M.O _).algebraMap_mem a)
  have hat : S.At M y y₀ := fun _ => rfl
  obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_le y (le_preimage_top y)
  haveI := hA.ft
  haveI := M.lft
  obtain ⟨t, ht⟩ := exists_finset_closure_eq_top M.s hW
  refine ⟨y₀, t.image (fun f => (((valMap y W hyW).hom f : OO p) : PadicAlgCl p)), hat, hn, fun u hu => ?_⟩
  let j : u.V →+* OO p :=
    ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V))).codRestrict (OO p)
      fun x => (mem_OO_iff _).2 ((u.norm_le _).2 ⟨x, rfl⟩)
  have hj : Function.Injective j := fun a b h =>
    IsFractionRing.injective u.V (FractionRing u.V)
      ((algebraMap (FractionRing u.V) (PadicAlgCl p)).injective (congrArg Subtype.val h))
  obtain ⟨ψ, hψ⟩ := exists_factor_of_closure (valMap y W hyW).hom j hj ht (by
    intro a ha
    obtain ⟨x, hx⟩ := hu _ (Finset.mem_image_of_mem _ ha)
    obtain ⟨v, hv⟩ := (u.norm_le x).1 (by rw [hx]; exact (mem_OO_iff _).1 (Subtype.prop _))
    exact ⟨v, Subtype.ext (by rw [← hx, ← hv]; rfl)⟩)
  let yV : Sp u.V ⟶ M.Z := Spec.map (CommRingCat.ofHom ψ) ≫ hW.fromSpec
  have hfac : spMap j ≫ yV = y := by
    rw [← specMap_valMap_fromSpec hW y hyW, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]
    rfl
  have hg : spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ jK u.V ≫ yV = gPt p ≫ y := by
    have e : spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ jK u.V = gPt p ≫ spMap j := by
      rw [← Spec.map_comp, ← Spec.map_comp]
      rfl
    rw [← hfac, ← Category.assoc, e, Category.assoc]
  have hr : Set.range (jK u.V ≫ yV) ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    rw [Subsingleton.elim x (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) w)]
    rw [← hg] at hw
    exact hw
  refine ⟨j, yV, IsOpenImmersion.lift U₀.ι _ hr, fun _ => rfl, hfac, IsOpenImmersion.lift_fac _ _ _, ?_⟩
  rw [← Spec.map_preimage (IsOpenImmersion.lift U₀.ι _ hr ≫ Q.u₀)]
  congr 1
  ext a
  apply (algebraMap (FractionRing u.V) (PadicAlgCl p)).injective
  have h1 := preimage_comp_eq_val M U₀ hO.ne S.R Q.u₀ Q.u₀_gen
    (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ IsOpenImmersion.lift U₀.ι _ hr) a
  rw [Category.assoc, Category.assoc, IsOpenImmersion.lift_fac, hg, ← hat a, Spec.preimage_comp,
    Spec.preimage_map] at h1
  exact h1.trans (DFunLike.congr_fun u.fac a).symm

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCmpOfIsPullDeg
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.LN.PreBaseChange

theorem exists_cmp_of_isPullDeg (hG : GlobalFnsSt) {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V]
    {I : Ideal R} {I' : Ideal V} {φ : R →+* V} (hI : I.map φ ≤ I') {D : DegPre R} {D₁ D' : DegPre V}
    (hD : IsPullDeg φ D D₁) {A : PolAV (Sp (FractionRing R))} {A' : PolAV (Sp (FractionRing V))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {G' : Over (Spec (CommRingCat.of V))} [GrpObj G']
    [IsCommMonObj G'] (U : PreU I D A G) (U' : PreU I' D' A' G') (F : G'.left ⟶ G.left)
    (pb : IsGrpPullback G' G (spMap φ) F) (wL : LB.Iso U'.P.L.L (U.P.L.L.pull F))
    (hw : IsCPMap U'.P U.P (spMap φ) F pb.1.w wL) :
    ∃ (U₁ : PreU I' D₁ A' G') (C : Cmp φ U U₁ F), U₁.P = U'.P ∧ HEq C.wL wL := by
  obtain ⟨bc, hbc, rfl⟩ := grpPullback_iso pb (isGrpPullback_pullback G (specOf φ))
  choose h q' i' hh hq' using fun e => gtCoord_baseChange_maps R V φ D D₁ hD I I' hI G G' bc hbc e (U.gt e)
  choose g _ hg using fun e => exists_gtCoord_pull hG R V φ D D₁ hD I I' hI G G' bc hbc e (U.gt e) (h e) (q' e)
    (i' e) (hh e) (hq' e)
  have hc := fun e => gtCoord_compat_of_pull R V φ D D₁ hD I I' G G' _ e (U.gt e) (U.gt (e + 1)) (g e) (g (e + 1))
    (h e) (h (e + 1)) (hh e) (hh (e + 1)) (hg e) (hg (e + 1)) (U.gt_q e) (U.gt_t e)
  choose w w_gen sq using fun e => FourthSide.exists_fourth_side _ _ _ _ _ _ D.P.L D₁.P.L U.P.L.L U'.P.L.L D.P.isLB
    D₁.P.isLB U.P.L.isLB U'.P.L.isLB _ _ (U.gt e).pG.left (g e).pG.left (fstG I e G).left (fstG I' e G').left (h e)
    (hg e).1 (hh e) hD.w wL (U.w e) hD.w_gen hw.gen (U.w_gen e)
  have pt : ∀ {Z X Y : Scheme.{0}} {a b : X ⟶ Y} (_ : a = b) (x : Z ⟶ X) (z : Z) {W : Y.Opens},
      a (x z) ∈ W → b (x z) ∈ W := fun e _ _ _ k => e ▸ k
  have compat : ∀ (e : ℕ) (Z : Scheme.{0}) (x : Z ⟶ (thickObj V I' e G').left) (z : Z) (j : D₁.P.L.ι)
      (k : U'.P.L.L.ι), (g e).pG.left (x z) ∈ D₁.P.L.U j → (fstG I' e G').left (x z) ∈ U'.P.L.L.U k →
      gw (w (e + 1)) (x ≫ thickMap V I' e G') z j (fun _ => k) = gw (w e) x z j (fun _ => k) := by
    intro e Z x z j k hj hk
    have := Cmp.mono_fstG I (e + 1) G
    have t := LevelCompat.thickMap_fstG I e G
    have t' := LevelCompat.thickMap_fstG I' e G'
    have hm : thickMap V I' e G' ≫ h (e + 1) = h e ≫ thickMap R I e G := by
      rw [← cancel_mono (fstG I (e + 1) G).left, Category.assoc, hh (e + 1), ← Category.assoc, t', Category.assoc, t,
        hh e]
    obtain ⟨jM, hM⟩ := exists_chart D.P.isLB
      ((hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ((g e).pG.left (x z)))
    obtain ⟨jL, hL⟩ := exists_chart U.P.L.isLB
      ((bc.hom.left ≫ pullback.fst G.hom (specOf φ)) ((fstG I' e G').left (x z)))
    have a₀ := sq e Z x z jM j jL k hM hj hL hk
    have a₁ := sq (e + 1) Z (x ≫ thickMap V I' e G') z jM j jL k
      (pt (congrArg (· ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) (hc e).1).symm x z hM)
      (pt (hc e).1.symm x z hj)
      (pt (congrArg (· ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ)) t').symm x z hL) (pt t'.symm x z hk)
    have b := U.w_compat e Z (x ≫ h e) z jM jL (pt (hg e).1 x z hM) (pt (hh e).symm x z hL)
    rw [Category.assoc x, Category.assoc x, Category.assoc x, (hc e).1, t', hm, ← Category.assoc x (h e), b] at a₁
    exact mul_left_cancel (a₁.trans a₀.symm)
  refine ⟨⟨U'.semi, U'.gen, U'.gen_hom, U'.P, U'.wA, U'.wA_gen, g, fun e => (hc e).1, fun e => (hc e).2, w, w_gen,
      fun e => GlobalTheory.T.fourthSide_respects_rig_symmetry_cube hG R V I I' φ hI D D₁ A G G' U U'.P _ _ wL hw _ _ hD.w (_root_.GlobalTheory.DegPullPackage.isCPMap_of_isPullDeg hG R V φ D D₁ hD) e
        (g e) (h e) (hh e) (hg e).1 (w e) (sq e), compat⟩,
    ⟨pb, wL, hw, _, pull_grp hD, hD.w, hD.w_gen, hD.xe, hD.c_pr, fun e Z x' x hx => ?_, hI⟩, rfl, HEq.rfl⟩
  have := Cmp.mono_fstG I e G
  obtain rfl : x = x' ≫ h e := (cancel_mono (fstG I e G).left).1 (hx.trans (by rw [Category.assoc, hh e]))
  refine ⟨(congrArg (x' ≫ ·) (hg e).1).trans (Category.assoc _ _ _).symm,
    fun z J J' hJ hJ' => ⟨fun χ => ?_, fun k k' hk hk' => ?_⟩⟩
  · refine (CubTransport.val_pmaps ((hg e).2 χ).1 ((hg e).2 χ).2 x' hJ hJ').trans
      ((mul_comm _ _).trans (congrArg _ (Finset.prod_congr rfl fun k _ => ?_)))
    rw [Category.assoc]
  · exact sq e Z x' z _ _ k k' (pt (hg e).1.symm x' z (hJ ((x' ≫ h e) ≫ (U.gt e).pG.left)))
      (hJ' (x' ≫ (g e).pG.left)) (pt (hh e) x' z hk) hk'

theorem exists_cmp_pull : Laws → ∀ (R V : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V] [IsDomain V] (I : Ideal R) (I' : Ideal V) (φ : R →+* V), I.map φ ≤ I' → ∀ (D : DegPre R) (D' : DegPre V) (A : PolAV (Sp (FractionRing R))) (A' : PolAV (Sp (FractionRing V))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (U' : PreU I' D' A' G') (F : G'.left ⟶ G.left) (pb : IsGrpPullback G' G (spMap φ) F) (wL : LB.Iso U'.P.L.L (U.P.L.L.pull F)), IsCPMap U'.P U.P (spMap φ) F pb.1.w wL → ∃ (D₁ : DegPre V) (U₁ : PreU I' D₁ A' G') (C : Cmp φ U U₁ F), U₁.P = U'.P ∧ HEq C.wL wL := by
  intro hL R V _ _ _ _ _ I I' φ hI D D' A A' G _ _ G' _ _ U U' F pb wL hw
  obtain ⟨ψ, h, hW⟩ := _root_.GlobalTheory.PsiTop.exists_setPsi_psiOn_top R D
  obtain ⟨D₁, hD, -⟩ := DegPull.exists_isPullDeg hL.polBaseChange R V φ (setPsi D ψ h) ⊤ hW trivial
  obtain ⟨U₁, C, h₁, h₂⟩ := exists_cmp_of_isPullDeg hL.globalFns hI hD (U.setPsi ψ h) U' F pb wL hw
  exact ⟨D₁, U₁, ⟨C.pb, C.wL, C.wL_map, C.β, C.pbB, C.v, C.v_gen, C.xe, C.c_pr, C.lev, C.map_le⟩, h₁, h₂⟩

end GlobalTheory.LN.PreBaseChange
end
end

