module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Imports
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocallyTrivialOfIsoPull
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CubeLawCompare

section General

variable {Y T : Scheme.{0}}

def IsGenOn (M : LB Y) (W : Y.Opens) (d : ∀ j, Γ(Y, W ⊓ M.U j)ˣ) : Prop :=
  ∀ j j' (y : Y), y ∈ W → y ∈ M.U j → y ∈ M.U j' →
    gm (𝟙 Y) y (W ⊓ M.U j) (d j) =
      gm (𝟙 Y) y (M.U j ⊓ M.U j') (M.g j j') * gm (𝟙 Y) y (W ⊓ M.U j') (d j')

theorem gen_restrict_iff (M : LB Y) (W : Y.Opens) :
    (∃ c : LB.Gen (M.pull W.ι), c.IsGen) ↔ ∃ d, IsGenOn M W d := by
  constructor
  · rintro ⟨c, hc⟩
    choose b hb using fun j : M.ι =>
      exists_ext_unit W.ι ((M.pull W.ι).U fun _ => j) (c.s fun _ => j)
    have le : ∀ j, W ⊓ M.U j ≤ W.ι ''ᵁ ((M.pull W.ι).U fun _ => j) :=
      fun j y hy => ⟨⟨y, hy.1⟩, mem_pull.2 hy.2, rfl⟩
    refine ⟨fun j => res (le j) (b j), fun j j' y hW hj hj' => ?_⟩
    let z : W.toScheme := ⟨y, hW⟩
    have hz : W.ι z ∈ W ⊓ M.U j ⊓ M.U j' := ⟨⟨hW, hj⟩, hj'⟩
    have l₁ : W ⊓ M.U j ⊓ M.U j' ≤ W ⊓ M.U j := inf_le_left
    have l₂ : W ⊓ M.U j ⊓ M.U j' ≤ M.U j ⊓ M.U j' := fun _ h => ⟨h.1.2, h.2⟩
    have l₃ : W ⊓ M.U j ⊓ M.U j' ≤ W ⊓ M.U j' := fun _ h => ⟨h.1.1, h.2⟩
    have v : ∀ i (hi : y ∈ M.U i), gm W.ι z (W ⊓ M.U i) (res (le i) (b i)) =
        gm (𝟙 _) z ((M.pull W.ι).U fun _ => i) (c.s fun _ => i) := fun i hi => by
      have h := hb i _ (𝟙 _) z (mem_pull.2 hi)
      rw [Category.id_comp] at h
      exact (gm_res W.ι z (le i) ⟨hW, hi⟩ _).trans h
    have m : (𝟙 W.toScheme : _ ⟶ _) z ∈ ((M.pull W.ι).U fun _ => j) ⊓ ((M.pull W.ι).U fun _ => j') :=
      ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
    have e := (gm_res (𝟙 _) z _ m _).symm.trans ((congrArg (gm (𝟙 _) z _) (hc (fun _ => j) (fun _ => j'))).trans
      ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_pull_g M W.ι (𝟙 _) z _ _ m.1 m.2) (gm_res (𝟙 _) z _ m _))))
    rw [Category.id_comp] at e
    have key := gm_inj W.ι z hz hz (a := res l₁ (res (le j) (b j)))
      (b := res l₂ (M.g j j') * res l₃ (res (le j') (b j'))) (by
        rw [map_mul, gm_res W.ι z l₁ hz, gm_res W.ι z l₂ hz, gm_res W.ι z l₃ hz, v j hj, v j' hj']
        exact e)
    rw [map_mul, gm_res (𝟙 Y) (W.ι z) l₁ hz, gm_res (𝟙 Y) (W.ι z) l₂ hz, gm_res (𝟙 Y) (W.ι z) l₃ hz] at key
    exact key
  · rintro ⟨d, hd⟩
    have le : ∀ J : PUnit → M.ι, (M.pull W.ι).U J ≤ W.ι ⁻¹ᵁ (W ⊓ M.U (J PUnit.unit)) :=
      fun J z hz => ⟨z.2, mem_pull.1 hz⟩
    refine ⟨⟨fun J => res (le J) (pullU W.ι _ (d (J PUnit.unit)))⟩, fun J J' => ?_⟩
    have e : res (inf_le_left : W ⊓ M.U (J PUnit.unit) ⊓ M.U (J' PUnit.unit) ≤ _) (d (J PUnit.unit)) =
        res (show W ⊓ M.U (J PUnit.unit) ⊓ M.U (J' PUnit.unit) ≤
            M.U (J PUnit.unit) ⊓ M.U (J' PUnit.unit) from fun _ h => ⟨h.1.2, h.2⟩)
          (M.g (J PUnit.unit) (J' PUnit.unit)) *
        res (show W ⊓ M.U (J PUnit.unit) ⊓ M.U (J' PUnit.unit) ≤
            W ⊓ M.U (J' PUnit.unit) from fun _ h => ⟨h.1.1, h.2⟩)
          (d (J' PUnit.unit)) := unit_ext fun y hy => by
      rw [map_mul, gm_res _ y _ hy, gm_res _ y _ hy, gm_res _ y _ hy]
      exact hd _ _ y hy.1.1 hy.1.2 hy.2
    refine unit_ext fun z hz => ?_
    have hz' : W.ι z ∈ W ⊓ M.U (J PUnit.unit) ⊓ M.U (J' PUnit.unit) :=
      ⟨⟨z.2, mem_pull.1 hz.1⟩, mem_pull.1 hz.2⟩
    have e' := congrArg (gm W.ι z _) e
    rw [map_mul, gm_res _ z _ hz', gm_res _ z _ hz', gm_res _ z _ hz'] at e'
    have v : ∀ I : PUnit → M.ι, z ∈ (M.pull W.ι).U I →
        gm (𝟙 _) z ((M.pull W.ι).U I) (res (le I) (pullU W.ι _ (d (I PUnit.unit)))) =
          gm W.ι z (W ⊓ M.U (I PUnit.unit)) (d (I PUnit.unit)) := fun I hI =>
      (gm_res (𝟙 _) z (le I) hI _).trans ((gm_pull (𝟙 _) W.ι z _ (le I hI) _).trans
        (by rw [Category.id_comp]))
    refine ((gm_res (𝟙 _) z _ hz _).trans (v J hz.1)).trans (e'.trans (Eq.symm ?_))
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_pull_g M W.ι (𝟙 _) z J J' hz.1 hz.2).trans ?_)
      ((gm_res (𝟙 _) z _ hz _).trans (v J' hz.2)))
    rw [Category.id_comp]

theorem locally_trivial_of_iso_pull (p : Y ⟶ T) (M : LB Y) {N : LB T} (hN : N.IsLB)
    (u : LB.Iso (N.pull p) M) (hu : u.IsGen) (t : T) :
    ∃ V : T.Opens, t ∈ V ∧ ∃ c : LB.Gen (M.pull (p ⁻¹ᵁ V).ι), c.IsGen := by
  obtain ⟨i, hi⟩ := exists_chart hN t
  refine ⟨N.U i, hi, (gen_restrict_iff M _).2 ?_⟩
  have le : ∀ j, p ⁻¹ᵁ N.U i ⊓ M.U j ≤ M.U j ⊓ (N.pull p).U fun _ => i :=
    fun j y hy => ⟨hy.2, mem_pull.2 hy.1⟩
  refine ⟨fun j => res (le j) (u.s (j, fun _ => i)), fun j j' y hW hj hj' => ?_⟩
  have hI : (𝟙 Y : Y ⟶ Y) y ∈ (N.pull p).U fun _ => i := mem_pull.2 hW
  have hm : (𝟙 Y : Y ⟶ Y) y ∈ M.U j ⊓ (N.pull p).U (fun _ => i) ⊓ (M.U j' ⊓ (N.pull p).U fun _ => i) :=
    ⟨⟨hj, hI⟩, hj', hI⟩
  have e := (gm_res (𝟙 Y) y _ hm _).symm.trans ((congrArg (gm (𝟙 Y) y _)
    (hu (j, fun _ => i) (j', fun _ => i))).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (gm_div (N.pull p) M (𝟙 Y) y (j, fun _ => i) (j', fun _ => i) hm) (gm_res (𝟙 Y) y _ hm _))))
  rw [gm_self (LB.isLB_pull hN p) (𝟙 Y) y hI, inv_one, _root_.mul_one] at e
  exact (gm_res (𝟙 Y) y (le j) ⟨hW, hj⟩ _).trans
    (e.trans (congrArg _ (gm_res (𝟙 Y) y (le j') ⟨hW, hj'⟩ _).symm))

theorem iso_pull_of_locally_trivial (p : Y ⟶ T) (hp : ∀ V : T.Opens, Function.Bijective (p.app V).hom)
    {M : LB Y} (hM : M.IsLB)
    (h : ∀ t : T, ∃ V : T.Opens, t ∈ V ∧ ∃ c : LB.Gen (M.pull (p ⁻¹ᵁ V).ι), c.IsGen) :
    ∃ N : LB T, N.IsLB ∧ ∃ u : LB.Iso (N.pull p) M, u.IsGen := by
  choose V hV hc using h
  choose d hd using fun t => (gen_restrict_iff M _).1 (hc t)
  have inj : ∀ (O : T.Opens) (a b : Γ(T, O)ˣ),
      (∀ y : Y, p y ∈ O → gm p y O a = gm p y O b) → a = b := fun O a b hab => by
    have e : pullU p O a = pullU p O b := unit_ext fun y hy => by
      rw [gm_pull (𝟙 Y) p y O hy, gm_pull (𝟙 Y) p y O hy, Category.id_comp]
      exact hab y hy
    exact Units.ext ((hp O).1 (congrArg Units.val e))
  have ratio : ∀ t t' : T, ∃ g : Γ(T, V t ⊓ V t')ˣ, ∀ j (y : Y), p y ∈ V t → p y ∈ V t' → y ∈ M.U j →
      gm p y _ g = gm (𝟙 Y) y (p ⁻¹ᵁ V t' ⊓ M.U j) (d t' j) * (gm (𝟙 Y) y (p ⁻¹ᵁ V t ⊓ M.U j) (d t j))⁻¹ := by
    intro t t'
    have l₁ : ∀ j, p ⁻¹ᵁ (V t ⊓ V t') ⊓ M.U j ≤ p ⁻¹ᵁ V t ⊓ M.U j := fun j y hy => ⟨hy.1.1, hy.2⟩
    have l₂ : ∀ j, p ⁻¹ᵁ (V t ⊓ V t') ⊓ M.U j ≤ p ⁻¹ᵁ V t' ⊓ M.U j := fun j y hy => ⟨hy.1.2, hy.2⟩
    have v : ∀ j (y : Y) (hy : y ∈ p ⁻¹ᵁ (V t ⊓ V t') ⊓ M.U j),
        gm (𝟙 Y) y _ (res (l₂ j) (d t' j) * (res (l₁ j) (d t j))⁻¹) =
          gm (𝟙 Y) y (p ⁻¹ᵁ V t' ⊓ M.U j) (d t' j) * (gm (𝟙 Y) y (p ⁻¹ᵁ V t ⊓ M.U j) (d t j))⁻¹ :=
      fun j y hy => by rw [map_mul, map_inv, gm_res _ y _ hy, gm_res _ y _ hy]
    obtain ⟨a, ha⟩ := glue_unit (p ⁻¹ᵁ (V t ⊓ V t')) (fun j => p ⁻¹ᵁ (V t ⊓ V t') ⊓ M.U j)
      (fun _ => inf_le_left) (fun y hy => by
        obtain ⟨j, hj⟩ := exists_chart hM y
        exact Opens.mem_iSup.2 ⟨j, hy, hj⟩)
      (fun j => res (l₂ j) (d t' j) * (res (l₁ j) (d t j))⁻¹) (fun j j' y hy => by
        rw [v j y hy.1, v j' y hy.2, hd t j j' y hy.1.1.1 hy.1.2 hy.2.2,
          hd t' j j' y hy.1.1.2 hy.1.2 hy.2.2, mul_inv, _root_.mul_mul_mul_comm, mul_inv_cancel, _root_.one_mul])
    let E := RingEquiv.ofBijective _ (hp (V t ⊓ V t'))
    let g : Γ(T, V t ⊓ V t')ˣ := Units.map E.symm.toRingHom.toMonoidHom a
    have hg : pullU p _ g = a := Units.ext (E.apply_symm_apply a.val)
    refine ⟨g, fun j y h₁ h₂ hj => ?_⟩
    have hy : (𝟙 Y : Y ⟶ Y) y ∈ p ⁻¹ᵁ (V t ⊓ V t') ⊓ M.U j := ⟨⟨h₁, h₂⟩, hj⟩
    have e := gm_pull (𝟙 Y) p y (V t ⊓ V t') hy.1 g
    rw [Category.id_comp, hg] at e
    rw [← e, ← v j y hy, ← ha j, gm_res _ y _ hy]
  choose g hg using ratio
  let N : LB T := ⟨T, V, g⟩
  have hN : N.IsLB := by
    refine ⟨eq_top_iff.2 fun t _ => Opens.mem_iSup.2 ⟨t, hV t⟩, fun t => inj _ _ _ fun y hy => ?_,
      fun t t' t'' => inj _ _ _ fun y hy => ?_⟩
    · obtain ⟨j, hj⟩ := exists_chart hM y
      exact (gm_res p y _ hy _).trans ((hg t t j y hy hy hj).trans
        ((mul_inv_cancel _).trans (map_one _).symm))
    · obtain ⟨j, hj⟩ := exists_chart hM y
      rw [map_mul, gm_res p y _ hy, gm_res p y _ hy, gm_res p y _ hy]
      refine (congrArg₂ (· * ·) (hg t t' j y hy.1.1 hy.1.2 hj) (hg t' t'' j y hy.1.2 hy.2 hj)).trans
        (Eq.trans ?_ (hg t t'' j y hy.1.1 hy.2 hj).symm)
      rw [mul_comm, _root_.mul_assoc, inv_mul_cancel_left]
  have le : ∀ q : M.ι × (PUnit → T), M.U q.1 ⊓ (N.pull p).U q.2 ≤ p ⁻¹ᵁ V (q.2 PUnit.unit) ⊓ M.U q.1 :=
    fun q y hy => ⟨mem_pull (L := N).1 hy.2, hy.1⟩
  refine ⟨N, hN, ⟨fun q => res (le q) (d (q.2 PUnit.unit) q.1)⟩, fun q q' => unit_ext fun y hy => ?_⟩
  have h₁ : p y ∈ V (q.2 PUnit.unit) := mem_pull (L := N).1 hy.1.2
  have h₂ : p y ∈ V (q'.2 PUnit.unit) := mem_pull (L := N).1 hy.2.2
  have eN := gm_pull_g N p (𝟙 Y) y q.2 q'.2 hy.1.2 hy.2.2
  rw [Category.id_comp] at eN
  refine ((gm_res (𝟙 Y) y _ hy _).trans (gm_res (𝟙 Y) y (le q) hy.1 _)).trans (Eq.symm ?_)
  refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_div (N.pull p) M (𝟙 Y) y q q' hy).trans
    (congrArg (fun w => _ * w⁻¹) (eN.trans (hg _ _ q'.1 y h₁ h₂ hy.2.1))))
    ((gm_res (𝟙 Y) y _ hy _).trans (gm_res (𝟙 Y) y (le q') hy.2 _)))).trans ?_
  rw [hd _ q.1 q'.1 y h₁ hy.1.1 hy.2.1, mul_inv_rev, inv_inv, _root_.mul_assoc, inv_mul_cancel_right]

end General

theorem bijective_app_of_restrict {Y T : Scheme.{0}} (p : Y ⟶ T) (V : T.Opens)
    (h : Function.Bijective (p ∣_ V).appTop.hom) : Function.Bijective (p.app V).hom := by
  have h₁ : IsIso (p ∣_ V).appTop := (ConcreteCategory.isIso_iff_bijective _).2 h
  have h₂ : IsIso (p.app (V.ι ''ᵁ ⊤)) :=
    @IsIso.of_isIso_fac_right _ _ _ _ _ _ _ _
      (by rw [eqToHom_op]; exact Y.presheaf.map_isIso (eqToHom _)) h₁ (morphismRestrict_appTop p V).symm
  have e : V.ι ''ᵁ ⊤ = V := V.ι_image_top
  rw [e] at h₂
  exact ConcreteCategory.bijective_of_isIso (p.app V)


open scoped CategoryTheory.Obj in
theorem bijective_app_fst (hG : GlobalFnsSt) {S : Scheme.{0}} {A : Over S} [GrpObj A]
    (hA : IsAbelianScheme A) (T : Over S) (V : T.left.Opens) :
    Function.Bijective ((fst T A).left.app V).hom := by
  have hB : IsAbelianScheme ((Over.pullback (V.ι ≫ T.hom)).obj A) :=
    { comm := by have := hA.comm; infer_instance
      smooth := by have := hA.smooth; show Smooth (pullback.snd _ _); infer_instance
      proper := by have := hA.proper; show IsProper (pullback.snd _ _); infer_instance
      geomConnected := by
        have := hA.geomConnected; show GeometricallyConnected (pullback.snd _ _); infer_instance }
  have h₁ : Function.Bijective (pullback.snd A.hom (V.ι ≫ T.hom)).appTop.hom := hG _ _ hB
  have sq : IsPullback ((pullback.fst T.hom A.hom ⁻¹ᵁ V).ι ≫ pullback.snd T.hom A.hom)
      (pullback.fst T.hom A.hom ∣_ V) A.hom (V.ι ≫ T.hom) :=
    (isPullback_morphismRestrict (pullback.fst T.hom A.hom) V).flip.paste_horiz
      (IsPullback.of_hasPullback T.hom A.hom).flip
  have h₂ : Function.Bijective (pullback.fst T.hom A.hom ∣_ V).appTop.hom := by
    rw [← sq.isoPullback_hom_snd, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp]
    exact (ConcreteCategory.bijective_of_isIso (sq.isoPullback.hom.app ⊤)).comp h₁
  exact bijective_app_of_restrict _ V h₂

end GlobalTheory.CubeLawCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ThetaGrpActsLinearly
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaAct

open GlobalTheory.CommPairing

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ} {T : Over S}

def sv (v : SecM A L k T) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z)
    (J : (Z ⟶ A.left) → L.ι) : Z.presheaf.stalk z :=
  sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) (SecM.toSec A v) r z J

theorem sv_ext (hL : L.IsLB) {v w : SecM A L k T}
    (h : ∀ y J, Good L y J → sv v (𝟙 _) y J = sv w (𝟙 _) y J) : v = w :=
  Subtype.ext (funext fun j => sec_ext_val hL (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k)
    (s := SecM.toSec A v) (s' := SecM.toSec A w) h j)

theorem sv_add (v w : SecM A L k T) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J} (hJ : Good L z J) :
    sv (v + w) r z J = sv v r z J + sv w r z J :=
  gs_add r z _ (hJ.mem (fun _ : Fin 1 => (snd T A).left) r) _ _

theorem sv_smul (c : Γ(T.left, ⊤)) (v : SecM A L k T) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J}
    (hJ : Good L z J) : sv (c • v) r z J = gs (r ≫ (fst T A).left) z ⊤ c * sv v r z J := by
  have hm := hJ.mem (fun _ : Fin 1 => (snd T A).left) r
  exact (gs_mul r z _ hm _ _).trans (congrArg (· * sv v r z J)
    ((gs_res r z le_top hm _).trans (gs_pull r (fst T A).left z ⊤ trivial c)))

theorem translT_snd (x : T ⟶ A) : (translT A x).left ≫ (snd T A).left = (translPt A x).left := by
  rw [← Over.comp_left, translT, lift_snd]

theorem translT_translPt (x y : T ⟶ A) : translT A x ≫ translPt A y = translPt A (y * x) := by
  show translT A x ≫ ((fst T A ≫ y) * snd T A) = (fst T A ≫ (y * x)) * snd T A
  rw [MonObj.comp_mul, MonObj.comp_mul, ← Category.assoc, translT, lift_fst, lift_snd, _root_.mul_assoc]
  rfl

theorem translT_translT (x y : T ⟶ A) : (translT A x).left ≫ (translT A y).left = (translT A (y * x)).left := by
  rw [← Over.comp_left]
  congr 1
  apply CartesianMonoidalCategory.hom_ext
  · simp [translT]
  · rw [Category.assoc, translT.eq_1 A y, translT.eq_1 A (y * x), lift_snd, lift_snd, translT_translPt]

theorem translPt_one : translPt A (1 : T ⟶ A) = snd T A := by
  show (fst T A ≫ 1) * snd T A = snd T A
  rw [MonObj.comp_one, _root_.one_mul]

theorem translT_one : (translT A (1 : T ⟶ A)).left = 𝟙 _ := by
  rw [translT, translPt_one, lift_fst_snd]; rfl

theorem isActOf_iff (hL : L.IsLB) (θ : ThetaGrp A L k T) (s s' : LB.Sec (LPow A L k T)) :
    IsActOf A L k θ s s' ↔ ∀ y J, Good L y J → sv (SecM.ofSec A s') (𝟙 _) y J =
      (tval θ (𝟙 _) y J).val * sv (SecM.ofSec A s) (𝟙 _ ≫ (translT A θ.pt).left) y J := by
  have key : ∀ (j : Fin 2 → L.ι) (y : (T ⊗ A).left)
      (hy : y ∈ LB.wchart L ![(snd T A).left, (translPt A θ.pt).left] j),
      gs (𝟙 _) y _ (((T ⊗ A).left.presheaf.map (homOfLE (chart_le_zero A L (translPt A θ.pt) j)).op).hom
        (s'.f (fun _ => j 0))) =
        gs (𝟙 _) y (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 0)) (s'.f (fun _ => j 0)) ∧
      gs (𝟙 _) y _ ((show Γ((T ⊗ A).left, LB.wchart L ![(snd T A).left, (translPt A θ.pt).left] j) from
        (θ.φ.s j).val) * ((T ⊗ A).left.presheaf.map (homOfLE
          (chart_le_pull A L (translT A θ.pt) (translPt A θ.pt) (lift_snd _ _) j)).op).hom
          (((translT A θ.pt).left.app _).hom (s.f (fun _ => j 1)))) =
        (gm (𝟙 _) y (LB.wchart L ![(snd T A).left, (translPt A θ.pt).left] j) (θ.φ.s j)).val *
          gs (𝟙 _ ≫ (translT A θ.pt).left) y (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 1))
            (s.f (fun _ => j 1)) := fun j y hy =>
    ⟨gs_res _ y _ hy _, (gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) (gs_unit _ y _ hy _)
      ((gs_res _ y _ hy _).trans (gs_pull (𝟙 _) (translT A θ.pt).left y
        (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => j 1))
        (chart_le_pull A L (translT A θ.pt) (translPt A θ.pt) (lift_snd _ _) j hy) _)))⟩
  have e : (𝟙 _ ≫ (translT A θ.pt).left) ≫ (snd T A).left = 𝟙 _ ≫ (translPt A θ.pt).left := by
    rw [Category.assoc, translT_snd]
  constructor
  · intro H y J hJ
    have hm := hJ.mem ![(snd T A).left, (translPt A θ.pt).left] (𝟙 _)
    obtain ⟨k₁, k₂⟩ := key _ y hm
    have := k₁.symm.trans ((congrArg (gs (𝟙 _) y _) (H _)).trans k₂)
    refine this.trans (congrArg (_ * ·) (Eq.symm ?_))
    exact sval_of (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) s _ y J _ (fun _ => congrArg J e)
  · intro H j
    refine fn_ext fun y hy => ?_
    obtain ⟨k₁, k₂⟩ := key j y hy
    refine k₁.trans (Eq.trans ?_ k₂.symm)
    choose J hJ using fun χ : (T ⊗ A).left ⟶ A.left => exists_chart hL (χ y)
    have hJ' : Good L y J := hJ
    have a₁ := sec_trans (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) s' (𝟙 _) y
      (chart_le_zero A L (translPt A θ.pt) j hy) (hJ'.mem _ _)
    have a₂ := sec_trans (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) s
      (𝟙 _ ≫ (translT A θ.pt).left) y
      (chart_le_pull A L (translT A θ.pt) (translPt A θ.pt) (lift_snd _ _) j hy) (hJ'.mem _ _)
    have a₃ := gen_trans (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.isGen (𝟙 _) y hy
      (hJ'.mem _ _)
    have a₄ : trF (fun _ : Fin 1 => (snd T A).left) (fun _ => k) (𝟙 _) y (fun _ => j 0)
          (fun _ => J (𝟙 _ ≫ (snd T A).left)) =
        trF ![(snd T A).left, (translPt A θ.pt).left] ![k, -k] (𝟙 _) y j
          (fun i => J (𝟙 _ ≫ ![(snd T A).left, (translPt A θ.pt).left] i)) *
        trF (fun _ : Fin 1 => (snd T A).left) (fun _ => k) (𝟙 _ ≫ (translT A θ.pt).left) y (fun _ => j 1)
          (fun _ => J ((𝟙 _ ≫ (translT A θ.pt).left) ≫ (snd T A).left)) := by
      rw [trF, trF, trF, Fin.prod_univ_two, Fin.prod_univ_one, Fin.prod_univ_one, e]
      have h : ∀ a b : ((T ⊗ A).left.presheaf.stalk y)ˣ, a ^ k = a ^ k * b ^ (-k) * b ^ k := fun a b => by
        rw [zpow_neg, inv_mul_cancel_right]
      exact h _ _
    refine a₁.trans (Eq.trans ?_ (congrArg₂ (· * ·) (congrArg Units.val a₃) a₂).symm)
    rw [a₄, Units.val_mul, Units.val_mul, _root_.mul_mul_mul_comm]
    exact congrArg (_ * ·) (H y J hJ')

theorem exists_act (hL : L.IsLB) (θ : ThetaGrp A L k T) (v : SecM A L k T) :
    ∃ w : SecM A L k T, ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
      sv w r z J = (tval θ r z J).val * sv v (r ≫ (translT A θ.pt).left) z J := by
  obtain ⟨w, hw⟩ := exists_sec hL (φ' := fun _ : Fin 1 => (snd T A).left) (ε' := fun _ => k)
    (fun U _ f => by
      refine (Fintype.prod_sum_type _).trans ?_
      simp only [Fin.prod_univ_two, Fin.prod_univ_one, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
        Matrix.cons_val_one, zpow_neg, translT_snd]
      rw [_root_.mul_comm, inv_mul_cancel_right])
    (pullMulSec (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) (SecM.toSec A v) (translT A θ.pt).left
      (φ₃ := ![(snd T A).left, (translPt A θ.pt).left]) (ε₃ := ![k, -k]) θ.φ θ.isGen)
  exact ⟨SecM.ofSec A w, fun Z r z J hJ =>
    (hw Z r z J hJ).trans ((sval_pullMulSec _ _ _ _ r z hJ).trans (_root_.mul_comm _ _))⟩

theorem exists_lin (hL : L.IsLB) (θ : ThetaGrp A L k T) :
    ∃ f : SecM A L k T →ₗ[Γ(T.left, ⊤)] SecM A L k T, ∀ v (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J),
      Good L z J → sv (f v) r z J = (tval θ r z J).val * sv v (r ≫ (translT A θ.pt).left) z J := by
  choose f hf using exists_act hL θ
  refine ⟨⟨⟨f, fun v w => sv_ext hL fun y J hJ => ?_⟩, fun c v => sv_ext hL fun y J hJ => ?_⟩, hf⟩
  · rw [sv_add _ _ _ _ hJ, hf _ _ _ _ _ hJ, hf _ _ _ _ _ hJ, hf _ _ _ _ _ hJ, sv_add _ _ _ _ hJ, mul_add]
  · show sv (f (c • v)) _ y J = sv (c • f v) _ y J
    rw [sv_smul _ (f v) _ _ hJ, hf (c • v) _ _ _ _ hJ, hf v _ _ _ _ hJ, sv_smul _ v _ _ hJ,
      Category.assoc, translT_fst, mul_left_comm]

theorem exists_inv (hL : L.IsLB) (θ : ThetaGrp A L k T) :
    ∃ θ' : ThetaGrp A L k T, θ'.pt = θ.pt⁻¹ ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J),
      Good L z J → tval θ' r z J = (tval θ (r ≫ (translT A θ.pt⁻¹).left) z J)⁻¹ := by
  have e₁ : (translT A θ.pt⁻¹).left ≫ (translPt A θ.pt).left = (snd T A).left := by
    rw [← Over.comp_left, translT_translPt, mul_inv_cancel, translPt_one]
  obtain ⟨t, ht, hv⟩ := exists_gen hL (φ' := ![(snd T A).left, (translPt A θ.pt⁻¹).left]) (ε' := ![k, -k])
    (fun U _ f => by
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, translT_snd, e₁, inv_inv]
      rw [_root_.mul_comm])
    (LB.invGen L _ _ (LB.pullGen L ![(snd T A).left, (translPt A θ.pt).left] ![k, -k] θ.φ (translT A θ.pt⁻¹).left))
    (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ θ.isGen _))
  exact ⟨⟨θ.pt⁻¹, t, ht⟩, rfl, fun Z r z J hJ => (hv Z r z J hJ).trans ((val_inv _ _).trans
    (congrArg (·⁻¹) (val_pull hJ _ _ _)))⟩

theorem exists_mul (hL : L.IsLB) (θx θy : ThetaGrp A L k T) :
    ∃ θ : ThetaGrp A L k T, θ.pt = θy.pt * θx.pt ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J),
      Good L z J → tval θ r z J = tval θx r z J * tval θy (r ≫ (translT A θx.pt).left) z J := by
  have e₁ : (translT A θx.pt).left ≫ (translPt A θy.pt).left = (translPt A (θy.pt * θx.pt)).left := by
    rw [← Over.comp_left, translT_translPt]
  obtain ⟨t, ht, hv⟩ := exists_gen hL (φ' := ![(snd T A).left, (translPt A (θy.pt * θx.pt)).left]) (ε' := ![k, -k])
    (fun U _ f => by
      refine (Fintype.prod_sum_type _).trans ?_
      simp only [Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
        Matrix.cons_val_one, zpow_neg, translT_snd, e₁]
      rw [_root_.mul_assoc, inv_mul_cancel_left])
    (LB.mulGen L ![(snd T A).left, (translPt A θx.pt).left] ![k, -k] _ _ θx.φ
      (LB.pullGen L ![(snd T A).left, (translPt A θy.pt).left] ![k, -k] θy.φ (translT A θx.pt).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ θx.isGen (DVR.pullGen_isGen _ _ _ _ θy.isGen _))
  exact ⟨⟨_, t, ht⟩, rfl, fun Z r z J hJ => (hv Z r z J hJ).trans ((val_mul hJ _ _ _).trans
    (congrArg (tval θx r z J * ·) (val_pull hJ _ _ _)))⟩

theorem exists_equiv (hL : L.IsLB) (θ : ThetaGrp A L k T) :
    ∃ f : SecM A L k T ≃ₗ[Γ(T.left, ⊤)] SecM A L k T, ∀ v (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J),
      Good L z J → sv (f v) r z J = (tval θ r z J).val * sv v (r ≫ (translT A θ.pt).left) z J := by
  obtain ⟨θ', hp, hv⟩ := exists_inv hL θ
  obtain ⟨f, hf⟩ := exists_lin hL θ
  obtain ⟨g, hg⟩ := exists_lin hL θ'
  refine ⟨LinearEquiv.ofLinear f g (LinearMap.ext fun v => sv_ext hL fun y J hJ => ?_)
    (LinearMap.ext fun v => sv_ext hL fun y J hJ => ?_), hf⟩
  · show sv (f (g v)) _ y J = sv v _ y J
    rw [hf _ _ _ _ _ hJ, hg _ _ _ _ _ hJ, hv _ _ _ _ hJ, hp, Category.assoc, translT_translT, inv_mul_cancel,
      translT_one, Category.comp_id, Units.mul_inv_cancel_left]
  · show sv (g (f v)) _ y J = sv v _ y J
    rw [hg _ _ _ _ _ hJ, hf _ _ _ _ _ hJ, hv _ _ _ _ hJ, hp, Category.assoc, translT_translT, mul_inv_cancel,
      translT_one, Category.comp_id, Units.inv_mul_cancel_left]

theorem exists_ratio (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB)
    (θ θ' : ThetaGrp A L k T) (h : θ.pt = θ'.pt) : ∃ c : Γ(T.left, ⊤)ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
        (tval θ' r z J).val = gs (r ≫ (fst T A).left) z ⊤ c.val * (tval θ r z J).val := by
  obtain ⟨a, u, hu⟩ := θ
  obtain ⟨a', u', hu'⟩ := θ'
  obtain rfl : a = a' := h
  obtain ⟨ρ, hρ⟩ := TLinPf.ratio_glue _ (TLinPf.linComb_cover L hL _ _) u' u hu' hu
  obtain ⟨c, hc⟩ := surj_fst hG hA T ρ.val
  obtain ⟨d, hd⟩ := surj_fst hG hA T ρ.inv
  have inj : Function.Injective (fst T A).left.appTop.hom := by
    have e : (ptSecT A a).left ≫ (fst T A).left = 𝟙 _ := by rw [← Over.comp_left, ptSecT, lift_fst]; rfl
    refine Function.LeftInverse.injective (g := (ptSecT A a).left.appTop.hom) fun b => ?_
    have := congrArg (fun q => q.appTop.hom b) e
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, Scheme.Hom.id_appTop,
      CommRingCat.hom_id, RingHom.id_apply] using this
  have hcd : c * d = 1 := inj (by rw [map_mul, map_one, hc, hd]; exact ρ.val_inv)
  refine ⟨⟨c, d, hcd, by rw [_root_.mul_comm]; exact hcd⟩, fun Z r z J hJ => ?_⟩
  have hm := hJ.mem ![(snd T A).left, (translPt A a).left] r
  refine (congrArg Units.val ((congrArg (gm r z _) (hρ _)).trans (map_mul _ _ _))).trans
    ((Units.val_mul _ _).trans (congrArg (· * _) ?_))
  exact (congrArg Units.val (gm_res r z le_top hm _)).trans ((gs_unit r z ⊤ trivial _).symm.trans
      ((congrArg (gs r z ⊤) hc.symm).trans (gs_pull r _ z ⊤ trivial c)))

end GlobalTheory.ThetaAct

namespace GlobalTheory


open ThetaAct CommPairing in
theorem thetaGrp_acts_linearly : GlobalFnsSt → ∀ (S : Scheme.{0}) (P : PolAV S) (k : ℤ) (T : Over S), ∃ ρ : ThetaGrp P.A P.L k T → (SecM P.A P.L k T ≃ₗ[Γ(T.left, ⊤)] SecM P.A P.L k T), (∀ θ s s', IsActOf P.A P.L k θ s s' ↔ ρ θ (SecM.ofSec P.A s) = SecM.ofSec P.A s') ∧ (∀ θx θy c, CommIsOf P.A P.L k θx θy c → ∀ v, ρ θx (ρ θy v) = (c : Γ(T.left, ⊤)) • ρ θy (ρ θx v)) ∧ (∀ θ θ', θ.pt = θ'.pt → ∃ c : Γ(T.left, ⊤)ˣ, ∀ v, ρ θ' v = (c : Γ(T.left, ⊤)) • ρ θ v) ∧ ∀ θx θy, ∃ θ, θ.pt = θx.pt * θy.pt ∧ ∀ v, ρ θ v = ρ θx (ρ θy v) := by
  intro hG S P k T
  have hL := P.isLB
  have := P.isAb.comm
  have cm : ∀ x y : T ⟶ P.A, x * y = y * x := fun x y => _root_.mul_comm x y
  choose ρ hρ using fun θ : ThetaGrp P.A P.L k T => exists_equiv hL θ
  refine ⟨ρ, fun θ s s' => ?_, fun θx θy c H v => sv_ext hL fun y J hJ => ?_, fun θ θ' h => ?_, fun θx θy => ?_⟩
  · rw [isActOf_iff hL]
    exact ⟨fun H => sv_ext hL fun y J hJ => (hρ _ _ _ _ _ _ hJ).trans (H y J hJ).symm,
      fun H y J hJ => H ▸ hρ _ _ _ _ _ _ hJ⟩
  · have e := congrArg Units.val ((commIsOf_iff hL θx θy c).1 H _ (𝟙 _) y J hJ)
    rw [Units.val_mul, Units.val_mul, Units.val_mul, ← gs_unit _ _ ⊤ trivial] at e
    rw [sv_smul _ _ _ _ hJ, hρ _ _ _ _ _ _ hJ, hρ _ _ _ _ _ _ hJ, hρ _ _ _ _ _ _ hJ, hρ _ _ _ _ _ _ hJ,
      Category.assoc, Category.assoc, translT_translT, translT_translT, cm θy.pt, ← _root_.mul_assoc, e]
    ring
  · obtain ⟨c, hc⟩ := exists_ratio hG P.isAb hL θ θ' h
    refine ⟨c, fun v => sv_ext hL fun y J hJ => ?_⟩
    rw [sv_smul _ _ _ _ hJ, hρ _ _ _ _ _ _ hJ, hρ _ _ _ _ _ _ hJ, hc _ _ _ _ hJ, h, _root_.mul_assoc]
  · obtain ⟨θ, hp, hv⟩ := exists_mul hL θx θy
    refine ⟨θ, hp.trans (cm _ _), fun v => sv_ext hL fun y J hJ => ?_⟩
    rw [hρ _ _ _ _ _ _ hJ, hρ _ _ _ _ _ _ hJ, hρ _ _ _ _ _ _ hJ, hv _ _ _ _ hJ, hp, Category.assoc,
      translT_translT, Units.val_mul, _root_.mul_assoc]

end GlobalTheory
end
end

