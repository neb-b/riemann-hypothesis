module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0036
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0004
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfHermFormPos
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleKTrivOfFiniteEtaleCover
section
noncomputable section

namespace GlobalTheory.PolDescent

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem kTriv_of_pull {S S' : Scheme.{0}} {f : S' ⟶ S} [IsAffineHom f] [Flat f] [Surjective f]
    {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {φ : A'.left ⟶ A.left} {L : LB A.left} {L' : LB A'.left}
    (h : IsGrpPullback A' A f φ) (hL : L.IsLB) (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ)) (hK : KTriv A' L') :
    KTriv A L := by
  obtain ⟨w, hw⟩ := hw
  intro R _ t x hx
  obtain ⟨R', g, t', hg, sq⟩ : ∃ (R' : CommRingCat.{0}) (g : Spec R' ⟶ Spec (CommRingCat.of R)) (t' : Spec R' ⟶ S'),
      Epi g ∧ g ≫ t = t' ≫ f := by
    have : IsAffine (pullback t f) := isAffine_of_isAffineHom (pullback.fst t f)
    refine ⟨Γ(pullback t f, ⊤), (pullback t f).isoSpec.inv ≫ pullback.fst t f,
      (pullback t f).isoSpec.inv ≫ pullback.snd t f, Flat.epi_of_flat_of_surjective _, ?_⟩
    rw [Category.assoc, Category.assoc, pullback.condition]
  let T : Over S := Over.mk t
  let T' : Over S' := Over.mk t'
  have hxw : (g ≫ x.left) ≫ A.hom = t' ≫ f := by rw [Category.assoc, Over.w x]; exact sq
  let x' : T' ⟶ A' := Over.homMk (h.1.lift _ _ hxw) (h.1.lift_snd _ _ _)
  have hx' : x'.left ≫ φ = g ≫ x.left := h.1.lift_fst _ _ _
  have key : x' = toUnit _ ≫ η[A'] := hK R' t' x' fun p => by
    obtain ⟨V, hV, c, hc⟩ := hx (g p)
    refine ⟨g ⁻¹ᵁ V, hV, ?_⟩
    let a : Over.mk ((T' ⊗ A').hom ≫ f) ⟶ T := Over.homMk ((fst T' A').left ≫ g)
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) sq).trans ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ f) (Over.w (fst T' A'))))))
    let b : Over.mk ((T' ⊗ A').hom ≫ f) ⟶ A := pushPt h.1.w (snd T' A')
    have k₁ : (lift a b).left ≫ (fst T A).left = (fst T' A').left ≫ g := congrArg (fun q => q.left) (lift_fst a b)
    have k₂ : (lift a b).left ≫ (snd T A).left = (snd T' A').left ≫ φ := congrArg (fun q => q.left) (lift_snd a b)
    have k₃ : (lift a b).left ≫ ((fst T A ≫ x) * snd T A).left = ((fst T' A' ≫ x') * snd T' A').left ≫ φ := by
      have e : lift a b ≫ ((fst T A ≫ x) * snd T A) = (a ≫ x) * b := by
        rw [MonObj.comp_mul, lift_fst_assoc, lift_snd]
      refine (congrArg (fun q => q.left) e).trans (h.2 (T' ⊗ A') _ _ _ _ ?_ rfl)
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hx'.symm).trans (Category.assoc _ _ _).symm)
    have le : (fst T' A').left ⁻¹ᵁ g ⁻¹ᵁ V ≤ (lift a b).left ⁻¹ᵁ (fst T A).left ⁻¹ᵁ V := fun y hy =>
      (congrArg (fun q => q y ∈ V) k₁).mpr hy
    have hn := Scheme.Hom.resLE_comp_ι (lift a b).left le
    obtain ⟨c₁, h₁⟩ := gen_chartPull (chartPullIn L _ _ _) c hc
    obtain ⟨c₂, h₂⟩ := gen_chartPull (chartPullSame L (fun k : Fin 2 => (((fst T' A').left ⁻¹ᵁ g ⁻¹ᵁ V).ι ≫
      ![(lift (fst T' A' ≫ x') (snd T' A') ≫ μ[A']).left, (snd T' A').left] k) ≫ φ) _ _
      ((lift a b).left.resLE _ _ le) fun k => by
        rw [← Category.assoc, hn, Category.assoc, Category.assoc]
        fin_cases k
        exacts [congrArg (_ ≫ ·) k₃.symm, congrArg (_ ≫ ·) k₂.symm]) c₁ h₁
    obtain ⟨c₃, h₃⟩ := exists_down ((isGen_iff w).1 hw) hL hL' c₂ h₂
    exact gen_chartPull (chartPullOut L' _ _ _ _ fun _ => rfl) c₃ h₃
  let U : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk g sq
  have e₁ : U ≫ x = pushHom h T' x' := Over.OverMorphism.ext hx'.symm
  have e₂ : U ≫ x = U ≫ (1 : T ⟶ A) := by
    rw [e₁, MonObj.comp_one]
    exact (congrArg (pushHom h T') key).trans (map_one (pushHom h T'))
  exact Over.OverMorphism.ext ((cancel_epi g).1 (congrArg (fun q => q.left) e₂))

theorem relAmple_of_pull {S S' : Scheme.{0}} [IsLocallyNoetherian S] {f : S' ⟶ S} [IsFinite f] [Flat f]
    [Surjective f] {A : Over S} {A' : Over S'} [IsProper A.hom] {φ : A'.left ⟶ A.left} {L : LB A.left}
    {L' : LB A'.left} (h : IsPullback φ A'.hom A.hom f) (hL : L.IsLB) (hL' : L'.IsLB)
    (hw : LBIso L' (L.pull φ)) (hA : RelAmple A' L') : RelAmple A L := by
  have : IsFinite φ := MorphismProperty.of_isPullback (P := @IsFinite) h.flip inferInstance
  have : Flat φ := MorphismProperty.of_isPullback (P := @Flat) h.flip inferInstance
  have : Surjective φ := MorphismProperty.of_isPullback (P := @Surjective) h.flip inferInstance
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  refine relAmple_of_isAmpleLB A hL fun U hU => ?_
  have h₁ := isAmpleLB_of_relAmple A' hL' hA (f ⁻¹ᵁ U) (hU.preimage f)
  have pre : A'.hom ⁻¹ᵁ (f ⁻¹ᵁ U) = φ ⁻¹ᵁ (A.hom ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, ← h.w, Scheme.Hom.comp_preimage]
  rw [pre] at h₁
  have h₂ : IsAmpleLB ((L.pull φ).pull (φ ⁻¹ᵁ (A.hom ⁻¹ᵁ U)).ι) :=
    h₁.of_lbIso (LB.isLB_pull (LB.isLB_pull hL _) _)
      (LBIso.chartPull (GlobalTheory.chartPullPull _ _) (GlobalTheory.chartPullPull _ _) hw.symm)
  have h₃ : IsAmpleLB ((L.pull (A.hom ⁻¹ᵁ U).ι).pull (φ ∣_ (A.hom ⁻¹ᵁ U))) :=
    (isAmpleLB_congr (LB.isLB_pull (LB.isLB_pull hL _) _) (LB.isLB_pull (LB.isLB_pull hL _) _)
      (FiniteAmple.lbIso_pull_pull _ hL (morphismRestrict_ι φ _).symm)).1 h₂
  have : Surjective (φ ∣_ A.hom ⁻¹ᵁ U) := IsZariskiLocalAtTarget.restrict (P := @Surjective) ‹_› _
  exact FiniteAmple.isAmpleLB_of_pull _ (LB.isLB_pull hL _) h₃

end GlobalTheory.PolDescent

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem relAmple_kTriv_of_finite_etale_cover : ∀ (S S' : Scheme.{0}) [IsLocallyNoetherian S] (π : S' ⟶ S) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (φ : G'.left ⟶ G.left) (L : LB G.left) (L' : LB G'.left), IsFinite π → Etale π → Surjective π → IsAbelianScheme G → L.IsLB → L'.IsLB → IsGrpPullback G' G π φ → LBIso L' (L.pull φ) → (Out.RelAmple G' L' → Out.RelAmple G L) ∧ (Out.KTriv G' L' → Out.KTriv G L) := by
  intro S S' _ π G G' _ _ φ L L' _ _ _ hG hL hL' h hw
  have := hG.proper
  exact ⟨PolDescent.relAmple_of_pull h.1 hL hL' hw, PolDescent.kTriv_of_pull h hL hL' hw⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.Rigidity
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.EpsAct

theorem subsingleton_sp_dualNumber (k : Type) [Field k] : Subsingleton (Sp (DualNumber k)) := by
  change Subsingleton (PrimeSpectrum (DualNumber k))
  have key : ∀ (p : PrimeSpectrum (DualNumber k)) (x : DualNumber k), x ∈ p.asIdeal ↔ x.fst = 0 := by
    intro p x
    constructor
    · intro hx
      by_contra h
      exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx
        (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (isUnit_iff_ne_zero.2 h)))
    · intro h
      apply p.isPrime.mem_of_pow_mem 2
      have hx : x = TrivSqZeroExt.inr x.snd := TrivSqZeroExt.ext (by simp [h]) (by simp)
      rw [hx, pow_two]
      simp
  exact ⟨fun p q => PrimeSpectrum.ext (Ideal.ext fun x => (key p x).trans (key q x).symm)⟩

theorem rigidity (hL : Out.Laws) (k : Type) [Field k] {Z : Scheme.{0}} (c₀ : Z ⟶ Sp k)
    (A' G' : Over (Sp (DualNumber k))) [GrpObj A'] [GrpObj G'] (j : Z ⟶ A'.left) (a b : A' ⟶ G')
    (hA : IsAbelianScheme A')
    (hj : IsPullback j c₀ A'.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom))
    (hab : j ≫ a.left = j ≫ b.left) (hη : η[A'] ≫ a = η[A'] ≫ b) : a = b := by
  classical
  have hsurj : Function.Surjective A'.hom.appTop.hom := (hL.globalFns _ A' hA).2
  set d : A' ⟶ G' := a * b⁻¹ with hd
  have hsub : Subsingleton (Sp (DualNumber k)) := subsingleton_sp_dualNumber k
  have hjs : Function.Surjective j.base := by
    have hs0 : Surjective (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) := by
      constructor
      intro y
      obtain ⟨q⟩ : Nonempty (Sp k) := by
        change Nonempty (PrimeSpectrum k)
        infer_instance
      exact ⟨q, Subsingleton.elim _ _⟩
    exact (MorphismProperty.of_isPullback (P := @Surjective) hj.flip hs0).surj
  have key : ∀ {W : Over (Sp (DualNumber k))} (u : W ⟶ A'), u ≫ a = u ≫ b → u ≫ d = 1 := by
    intro W u h
    rw [MonObj.comp_mul, GrpObj.comp_inv, h, mul_inv_cancel]
  have hjd : j ≫ d.left = (toUnit (Over.mk (j ≫ A'.hom))).left ≫ η[G'].left := by
    have h1 := congrArg (fun f => Over.Hom.left f)
      (key (Over.homMk j rfl : Over.mk (j ≫ A'.hom) ⟶ A') (by ext; exact hab))
    simpa [Hom.one_def] using h1
  obtain ⟨pt⟩ : Nonempty ((𝟙_ (Over (Sp (DualNumber k)))).left) := by
    obtain ⟨q⟩ : Nonempty (Sp k) := by
      change Nonempty (PrimeSpectrum k)
      infer_instance
    exact ⟨(spMap (TrivSqZeroExt.fstHom k k k).toRingHom).base q⟩
  have hsub1 : Subsingleton ((𝟙_ (Over (Sp (DualNumber k)))).left) := hsub
  have hy : ∀ x, d.left x = η[G'].left pt := by
    intro x
    obtain ⟨z, rfl⟩ := hjs x
    have h2 := congrArg (fun f : Z ⟶ G'.left => f z) hjd
    simp only [Scheme.Hom.comp_apply] at h2
    rw [h2]
    exact congrArg _ (Subsingleton.elim _ _)
  have hfac := GlobalTheory.DualRigidity.eq_comp_section_of_const A'.hom η[A'].left d.left
    (by simp) hsurj _ hy
  have hη' : η[A'] ≫ d = 1 := key _ hη
  have hd2 : d = toUnit A' ≫ η[A'] ≫ d := by
    ext
    exact hfac
  have hd1 : d = 1 := by
    rw [hd2, hη']
    simp
  exact mul_inv_eq_one.1 hd1

theorem main : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] (T : Scheme.{0}) (t : SAB H T) (x : Sp (DualNumber k) ⟶ T) (t' : SAB H (Sp (DualNumber k))) (ν : SABMap t' t x) (φ : t'.G.left ⟶ t.G.left), IsProper t.G.hom → IsGrpPullback t'.G t.G (constPt x) φ → (∀ (Z : Scheme.{0}) (j : Z ⟶ t'.G.left) (c : Z ⟶ Sp k), j ≫ t'.G.hom = c ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → j ≫ φ = j ≫ ν.φ) → ∀ a, (t'.act.act a).left ≫ φ = φ ≫ (t.act.act a).left := by
  intro hL E _ _ _ H k _ T t x t' ν φ hP hpb hag a
  have hsq := hpb.1
  have hprop : IsProper t'.G.hom := MorphismProperty.of_isPullback (P := @IsProper) hsq hP
  have hs := t'.semi
  have hA : IsAbelianScheme t'.G :=
    { comm := hs.comm, smooth := hs.smooth, proper := hprop, geomConnected := hs.geomConnected }
  have hα : ((t'.act.act a).left ≫ φ) ≫ t.G.hom = t'.G.hom ≫ constPt x := by
    rw [Category.assoc, hsq.w, ← Category.assoc, Over.w]
  have hβ : (φ ≫ (t.act.act a).left) ≫ t.G.hom = t'.G.hom ≫ constPt x := by
    rw [Category.assoc, Over.w, hsq.w]
  let A : t'.G ⟶ t'.G := Over.homMk (hsq.lift _ _ hα) (hsq.lift_snd _ _ _)
  let B : t'.G ⟶ t'.G := Over.homMk (hsq.lift _ _ hβ) (hsq.lift_snd _ _ _)
  have e3 : (t'.act.act a).left ≫ ν.φ = ν.φ ≫ (t.act.act a).left := ν.act a
  have hj := IsPullback.of_hasPullback t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)
  have hab : pullback.fst t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ A.left = pullback.fst t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ B.left := by
    apply hsq.hom_ext
    · simp only [A, B, Over.homMk_left, Category.assoc, IsPullback.lift_fst]
      have e1 := hag _ (pullback.fst t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) (pullback.snd t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) hj.w
      have e2 := hag _ (pullback.fst t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ (t'.act.act a).left) (pullback.snd t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom))
        (by rw [Category.assoc, Over.w]; exact hj.w)
      rw [← Category.assoc, e2, Category.assoc, e3, ← Category.assoc, ← e1, Category.assoc]
    · simp only [A, B, Over.homMk_left, Category.assoc, IsPullback.lift_snd]
  let e : Over.mk ((𝟙_ (Over (Sp (DualNumber k)))).hom ≫ constPt x) ⟶ t.G :=
    Over.homMk (η[t'.G].left ≫ φ) (by rw [Category.assoc, hsq.w, ← Category.assoc, Over.w]; rfl)
  have hη1 : (η[t'.G] : 𝟙_ _ ⟶ t'.G) = 1 := by simp [Hom.one_def]
  have he1 : e = 1 := by
    have hm := hpb.2 _ η[t'.G] η[t'.G] e e rfl rfl
    rw [hη1, _root_.mul_one] at hm
    have hee : e * e = e := by
      ext
      rw [hm, ← hη1]
      rfl
    exact _root_.mul_eq_left.1 hee
  have he2 : e ≫ t.act.act a = e := by
    have := t.act.hom a
    rw [he1, Hom.one_def, Category.assoc, IsMonHom.one_hom]
  have he3 := congrArg Over.Hom.left he2
  have hm1 : η[t'.G] ≫ t'.act.act a = η[t'.G] := by
    have := t'.act.hom a
    exact IsMonHom.one_hom _
  have hm2 := congrArg Over.Hom.left hm1
  have hη : η[t'.G] ≫ A = η[t'.G] ≫ B := by
    ext
    simp only [Over.comp_left]
    apply hsq.hom_ext
    · simp only [A, B, Over.homMk_left, Category.assoc, IsPullback.lift_fst]
      simp only [e, Over.comp_left, Over.homMk_left, Category.assoc] at he3 hm2
      rw [← Category.assoc, hm2, he3]
    · simp only [A, B, Over.homMk_left, Category.assoc, IsPullback.lift_snd]
  have hAB := rigidity hL k (pullback.snd t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) t'.G t'.G (pullback.fst t'.G.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) A B hA hj hab hη
  have hL' := congrArg Over.Hom.left hAB
  simp only [A, B, Over.homMk_left] at hL'
  calc (t'.act.act a).left ≫ φ = hsq.lift _ _ hα ≫ φ := (hsq.lift_fst _ _ _).symm
    _ = hsq.lift _ _ hβ ≫ φ := by rw [hL']
    _ = φ ≫ (t.act.act a).left := hsq.lift_fst _ _ _

end GlobalTheory.EpsAct
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ShapeOfUniformisedThetaObject
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM

theorem map_sum_nsmul_eq_listProd {V G : Type} [AddCommGroup V] [Group G] (E : V → G)
    (hE : ∀ z w, E (z + w) = E z * E w) : ∀ (n : ℕ) (a : Fin n → ℕ) (z : Fin n → V),
    E (∑ i, a i • z i) = (List.ofFn fun i => E (z i) ^ a i).prod := by
  have h0 : E 0 = 1 := by
    have := hE 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have hp : ∀ (m : ℕ) (x : V), E (m • x) = E x ^ m := by
    intro m x
    induction m with
    | zero => rw [zero_smul, pow_zero, h0]
    | succ m ih => rw [succ_nsmul, hE, ih, pow_succ]
  intro n
  induction n with
  | zero => intro a z; simp [h0]
  | succ n ih =>
    intro a z
    rw [Fin.sum_univ_succ, hE, List.ofFn_succ, List.prod_cons, hp, ih]

theorem linearMap_eq_of_span_real {g : ℕ} (s : Set (Fin g → ℂ)) (hs : Submodule.span ℝ s = ⊤)
    (F F' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (h : ∀ z ∈ s, F z = F' z) : F = F' := by
  have : F.restrictScalars ℝ = F'.restrictScalars ℝ := LinearMap.ext_on hs h
  exact LinearMap.restrictScalars_injective ℝ this

theorem level_comb_sub_mem {g n k : ℕ} (hk : (k : ℂ) ≠ 0) {La : Type} [AddCommGroup La] (Q : La →+ (Fin g → ℂ))
    (lam : Fin n → La) (m : Fin n → ℤ) (y : La) :
    ∃ x, (k : ℂ)⁻¹ • Q (∑ i, m i • lam i + k • y) =
      ∑ i, ((m i : ZMod k)).val • ((k : ℂ)⁻¹ • Q (lam i)) + Q x := by
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk
  haveI : NeZero k := ⟨hk0⟩
  refine ⟨∑ i, (m i / k) • lam i + y, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_add (f := _), map_add (f := _), map_sum, map_sum, map_nsmul, smul_add, Finset.smul_sum, ← add_assoc,
    ← Finset.sum_add_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : (((m i : ZMod k).val : ℤ) : ℂ) = ((m i % k : ℤ) : ℂ) := by rw [ZMod.val_intCast]
    have h2 : ((m i : ℤ) : ℂ) = ((m i % k : ℤ) : ℂ) + (k : ℂ) * ((m i / k : ℤ) : ℂ) := by
      exact_mod_cast (Int.emod_add_mul_ediv (m i) k).symm
    rw [map_zsmul, map_zsmul, ← Int.cast_smul_eq_zsmul ℂ, ← Int.cast_smul_eq_zsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ,
      smul_smul, smul_smul, ← add_smul]
    congr 1
    rw [Int.cast_natCast] at h1
    rw [h1]
    conv_lhs => rw [h2]
    field_simp
  · rw [← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ hk]

theorem shape_of_uniformised : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (t : TObj g k J b (spMap em)) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (lam : Fin (2 * g) → La) (ac : J → La → La) (Q : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ), (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q x → χ' l = (-1) ^ EF x (ac w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q (lam i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q (ac j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) → (∀ j i, ∃ y, ac j (lam i) = ∑ i', Mat j i' i • lam i' + k • y) → (∀ j, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q (ac j x)) ∧ ∀ y, y ≠ 0 → (hermForm Hm (F y) (F y)).re < κ * (hermForm Hm y y).re) → t.Shape Mat κ := by
  intro hL hL2 _ hU o _ g k J b em w w' t La _ EF lam ac Q Hm Mat κ ⟨u, χ', hAH, hΛ, _, hpt, hact⟩ hMat hB j
  obtain ⟨F, hFQ, hF⟩ := hact j
  have hk : (k : ℂ) ≠ 0 := by simpa using (b.unit.map em).ne_zero
  refine ⟨fun i => ?_, ?_⟩
  · obtain ⟨y, hy⟩ := hMat j i
    let E : (Fin g → ℂ) → (Out.baseOver (Sp ℂ) ⟶ t.A) := u.ex
    have hE : ∀ z w, E (z + w) = E z * E w := u.ex_add
    have hpt' : ∀ i₀, t.pt i₀ = E ((k : ℂ)⁻¹ • Q (lam i₀)) := fun i₀ => Over.OverMorphism.ext (hpt i₀)
    have hF' : ∀ z, E (F z) = E z ≫ t.act j := hF
    obtain ⟨x, hx⟩ := level_comb_sub_mem hk Q lam (fun i' => Mat j i' i) y
    have h1 : E (Q x) = 1 := (u.ker _).2 ((hΛ _).2 ⟨x, rfl⟩)
    rw [hpt', ← hF', map_smul, hFQ, hy, hx, hE, h1, _root_.mul_one, map_sum_nsmul_eq_listProd E hE]
    simp only [TObj.lab, Out.linComb, hpt']
  · obtain ⟨F', hFQ', hF'⟩ := hB j
    have hFF : F' = F := linearMap_eq_of_span_real _ u.full _ _ fun z hz => by
      obtain ⟨x, rfl⟩ := (hΛ z).1 hz
      rw [hFQ, hFQ']
    subst hFF
    exact GlobalTheory.relAmple_of_hermForm_pos hL hL2 hU t.pol u Hm χ' (t.act j) F' κ hAH (t.hom j) hF hF'

end GlobalTheory.ZM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaSectionsVeryAmplePeriodic
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZV

noncomputable section
namespace GlobalTheory.EmbVA

theorem act_unique (hL : Out.SymLiftSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : Out.PolAV S) (k : ℕ) (z : ℤ)
    (hz : z = k) (ho : Odd k) (hu : IsUnit (k : Γ(S, ⊤))) {T : Over S} (x : T ⟶ P.A) (hx : x ^ k = 1)
    {θ θ' : Out.ThetaGrp P.A P.L z T} (h : Out.SymLift P.A P.L z k x θ) (h' : Out.SymLift P.A P.L z k x θ')
    {s s₁ s₂ : LB.Sec (Out.LPow P.A P.L z T)} (a₁ : Out.IsActOf P.A P.L z θ s s₁)
    (a₂ : Out.IsActOf P.A P.L z θ' s s₂) (j) : s₁.f j = s₂.f j := by
  subst hz
  have hc := (hL S P k ho hu T x hx).2 θ θ' h h'
  refine sec_ext_val P.isLB (s := s₁) (s' := s₂) (fun y J hJ => ?_) j
  have e₁ := GlobalTheory.ThetaPowOrder.act_sval a₁ (𝟙 _) y hJ
  have e₂ := GlobalTheory.ThetaPowOrder.act_sval a₂ (𝟙 _) y hJ
  have e₃ := val_corr hJ hc (𝟙 _)
  have e₄ : θ.pt = θ'.pt := h.pt_eq.trans h'.pt_eq.symm
  refine e₁.trans (Eq.trans ?_ e₂.symm)
  exact congrArg₂ (fun u (p : T ⟶ P.A) => Units.val u * sval (L := P.L) s (𝟙 _ ≫ (Out.translT P.A p).left) y J) e₃ e₄

theorem lbIso_pow {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (n : ℕ) (z : ℤ) (hz : z = n) :
    LBIso (LB.LinComb L (K := Fin 1) (fun _ => f) (fun _ => z)) ((lbPow L n).pull f) := by
  subst hz
  refine LBIso.chartPull (h := f) (A := lbPow L n) (B := lbPow L n) ?_ (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ f f rfl)
    ⟨_, idIso_isGen (LB.isLB_linComb hL _ _)⟩
  have le : ∀ j : Fin 1 → L.ι, LB.wchart L (fun _ : Fin 1 => f) j ≤
      f ⁻¹ᵁ LB.wchart L (fun _ : PUnit => 𝟙 X) (fun _ => j 0) :=
    fun j y hy => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy 0
  refine ⟨fun j _ => j 0, le, fun y j j' hj hj' => ?_⟩
  refine (gm_linComb L _ _ (𝟙 Y) y j j' hj hj').trans (Eq.trans ?_
    (gm_linComb L (fun _ : PUnit => 𝟙 X) (fun _ => (n : ℤ)) f y _ _ (le j hj) (le j' hj')).symm)
  rw [Fin.prod_univ_one, Fintype.prod_unique, Category.id_comp, Category.comp_id]

theorem linComb_pow {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] {r : ℕ} (y : Fin r → (T ⟶ A))
    (a : Fin r → ℕ) (n : ℕ) : Out.linComb y a ^ n = ∏ i, y i ^ (a i * n) := by
  rw [Out.linComb, List.prod_ofFn, ← Finset.prod_pow]
  simp only [pow_mul]

end GlobalTheory.EmbVA

namespace GlobalTheory


open EmbVA in
theorem embSec_veryAmple_periodic : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (K : Type) [Field K] [IsAlgClosed K] (β : o →+* K) (t : TObj g (N' ^ 2) J b (spMap β)) (m : ℕ) σ, Odd N' → m ∣ N' → 2 ≤ m → t.Emb m (Over.mk (𝟙 (Sp K))) σ → IsIso (snd (Over.mk (𝟙 (Sp K))) t.A).left ∧ (Out.LPow t.A t.L ((m : ℤ) ^ 2) (Over.mk (𝟙 (Sp K)))).IsLB ∧ VAmp (fst (Over.mk (𝟙 (Sp K))) t.A).left _ σ ∧ LBIso (Out.LPow t.A t.L ((m : ℤ) ^ 2) (Over.mk (𝟙 (Sp K)))) ((lbPow t.L (m ^ 2)).pull (snd (Over.mk (𝟙 (Sp K))) t.A).left) ∧ (∀ a a' : Ix g (N' ^ 2), (∀ i, (a i).val ≡ (a' i).val [MOD m ^ 2]) → ∀ j, (σ a).f j = (σ a').f j) ∧ TorsBasis t.A (N' ^ 2) t.pt ∧ ∀ x : Out.baseOver (Sp K) ⟶ t.A, x ^ N' = 1 → ∃ h, t.lab h ^ N' = x := by
  intro hL hL2 o _ g N' J b K _ _ β t m σ hN hm h2 hE
  haveI := t.ab.comm
  have hN0 : N' ≠ 0 := by rintro rfl; simp at hN
  haveI : NeZero (N' ^ 2) := ⟨pow_ne_zero _ hN0⟩
  have hid : (Over.homMk (𝟙 (Sp K)) (by simp) : Over.mk (𝟙 (Sp K)) ⟶ Out.baseOver (Sp K)) = 𝟙 _ := rfl
  have hbij : ∀ y : Out.baseOver (Sp K) ⟶ t.A, y ^ (N' ^ 2) = 1 →
      ∃! c : Fin (2 * g) → ZMod (N' ^ 2), Out.linComb t.pt (fun i => (c i).val) = y := fun y hy => by
    have := t.bij K (𝟙 _) y hy
    simpa only [hid, Category.id_comp] using this
  refine ⟨?_, LB.isLB_linComb t.isLB _ _, ?_, lbIso_pow t.isLB _ _ _ (by push_cast; rfl), ?_, ⟨Nat.pos_of_neZero _, t.torsion, hbij⟩, ?_⟩
  · show IsIso (pullback.snd (𝟙 (Sp K)) t.A.hom)
    infer_instance
  · refine _root_.GlobalTheory.ZV.CoordEmbed.vAmp_of_projRep K _ _ _ _ _ _ (_root_.GlobalTheory.FibreEmbed.projRep_fibre hL hL2 _ t.pol K (𝟙 _) _ _ σ (by nlinarith) ?_)
    exact GlobalTheory.EmbSpan.emb_span_eq_top hL hL2 o g N' J b _ _ t m K (𝟙 _) σ hN hm h2 hE
  · intro a a' haa j
    obtain ⟨th, s1, α, U, -, -, -, hU, hact⟩ := hE
    obtain ⟨c, rfl⟩ := hm
    have hm0 : 0 < m := by omega
    have hc : m * c / m = c := Nat.mul_div_cancel_left c hm0
    have hlab : t.lab a ^ (c ^ 2) = t.lab a' ^ (c ^ 2) := by
      rw [TObj.lab, TObj.lab, linComb_pow, linComb_pow]
      refine Finset.prod_congr rfl fun i _ => ?_
      refine pow_eq_pow_of_modEq ?_ (t.torsion i)
      exact ((haa i).mul_right' _).of_dvd (dvd_of_eq (mul_pow m c 2))
    have htor : (t.lab a ^ (c ^ 2)) ^ (m ^ 2) = 1 := by
      rw [← pow_mul, TObj.lab, linComb_pow]
      refine Finset.prod_eq_one fun i _ => ?_
      rw [show (a i).val * (c ^ 2 * m ^ 2) = (m * c) ^ 2 * (a i).val by ring, pow_mul, t.torsion, one_pow]
    have hu : IsUnit ((m ^ 2 : ℕ) : Γ(Sp K, ⊤)) := by
      have h1 := (b.unit.map β).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
      rw [map_natCast, map_natCast, mul_pow, Nat.cast_mul] at h1
      exact isUnit_of_mul_isUnit_left h1
    have h₁ := hU a
    have h₂ := hU a'
    simp only [Over.mk_hom, hid, Category.id_comp, hc] at h₁ h₂
    rw [← hlab] at h₂
    exact act_unique hL.symLift t.pol (m ^ 2) _ (by push_cast; rfl) (Odd.of_dvd_nat hN (Dvd.intro c rfl)).pow hu _ htor
      h₁ h₂ (hact a) (hact a') j
  · intro x hx
    obtain ⟨h1, -, h3, -⟩ := hL.mulN _ t.pol N' (Nat.pos_of_ne_zero hN0)
    obtain ⟨d, hd⟩ := TwistTranslate.exists_root t.pol (𝟙 (Sp K)) N' x
    have hd' : (show Out.baseOver (Sp K) ⟶ t.A from d) ^ N' = x := hd
    obtain ⟨h, hh, -⟩ := hbij d ((congrArg (fun n => (show Out.baseOver (Sp K) ⟶ t.A from d) ^ n) (pow_two N')).trans (by rw [pow_mul, hd', hx]))
    exact ⟨h, (congrArg (· ^ N') hh).trans hd'⟩

end GlobalTheory
end
end

