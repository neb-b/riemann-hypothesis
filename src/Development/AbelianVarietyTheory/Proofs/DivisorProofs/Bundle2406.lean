module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2280
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2183
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0196
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2248
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnitThetaConstantsGenerateIntegralTorsion
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupGaloisMapMul
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.GalMul

open GlobalTheory.ArcPull GlobalTheory.ArcQ GlobalTheory.PsiEvenPull

theorem exists_isPullDeg_of_val {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
    {i : R →+* R'} (hi : Function.Injective i) (D : DegPre R) (D' : DegPre R')
    {W : (Sp R).Opens} (ψW : PsiOn D W) (s : (TK R).left ⟶ W.toScheme) (hs : s ≫ W.ι = jK R)
    {Φ : D'.P.A.left ⟶ D.P.A.left} (gp : IsGrpPullback D'.P.A D.P.A (spMap i) Φ)
    (w : LB.Iso D'.P.L (D.P.L.pull Φ)) (hw : PGen w)
    (hr : PMaps w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => eSec D.P.A) (fun _ => 1) D'.rig D.rig (spMap i))
    (xe : D'.X ≃+ D.X) (hc : ∀ x, (D'.c x).left ≫ Φ = spMap i ≫ (D.c (xe x)).left)
    (hψ : ∀ (x : D'.X) (z : (TK R').left) J J', Good D.P.L z J → Good D'.P.L z J' →
      val (D.psi (xe x)) (genMap hi) z J = (om w z J J' (D'.xK x))⁻¹ * val (D'.psi x) (𝟙 _) z J') :
    ∃ hD : IsPullDeg i D D', proj hD = Φ ∧ hD.xe = xe ∧ HEq hD.w w := by
  obtain ⟨e, e_hom, he⟩ := grpPullback_iso gp (isGrpPullback_pullback D.P.A (specOf i))
  subst he
  have hE : eSec D'.P.A ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) = specOf i ≫ eSec D.P.A :=
    (cubeMapOf gp).e_comm
  obtain ⟨g, sq⟩ : ∃ g : (TK R').left ⟶ (TW W).left, g ≫ W.ι = genMap hi ≫ jK R :=
    ⟨genMap hi ≫ s, (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hs)⟩
  have hg : g ≫ W.ι = jK R' ≫ specOf i := sq.trans ((fracMap_sq hi).symm.trans (Category.id_comp _))
  obtain ⟨lam, l₁, l₂⟩ : ∃ lam : (TK R').left ⟶ (jK R ⁻¹ᵁ W).toScheme, lam ≫ (jK R ⁻¹ᵁ W).ι = genMap hi ∧
      lam ≫ (jK R ∣_ W) = g :=
    ⟨(isPullback_morphismRestrict (jK R) W).lift _ _ sq,
      (isPullback_morphismRestrict (jK R) W).lift_snd _ _ _,
      (isPullback_morphismRestrict (jK R) W).lift_fst _ _ _⟩
  have hx : ∀ x, g ≫ (toUnit (TW W) ≫ D.c (xe x)).left =
      D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) := fun x => by
    show g ≫ W.ι ≫ (D.c (xe x)).left = (jK R' ≫ (D'.c x).left) ≫ _
    rw [Category.assoc, hc, ← Category.assoc, hg, Category.assoc]
  choose b hb vb using fun x => exists_gen D.P.isLB (K' := PUnit)
    (φ' := fun _ => D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i)) (ε' := fun _ => -1)
    (fun U _ h => Finset.prod_congr rfl fun _ _ => congrArg (fun q => h q ^ (-1 : ℤ)) (hx x))
    (LB.pullGen D.P.L _ _ (ψW.psi (xe x)) g) (DVR.pullGen_isGen _ _ _ _ (ψW.psi_gen _) g)
  choose psi hpsi vpsi using fun x => DegPull.exists_down_val hw D.P.isLB D'.P.isLB (K := PUnit)
    (φ' := fun _ => D'.xK x) (ε := fun _ => -1) (fun _ => rfl) (b x) (hb x)
  have eψ : ∀ x, psi x = D'.psi x := fun x => TorusExt.gen_ext_val D'.P.isLB (hpsi x) (D'.psi_gen x) fun y J' hJ' => by
    obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB y
    have v := vpsi x _ (𝟙 _) y _ _ (hJ.mem _ (𝟙 _)) (hJ'.mem _ (𝟙 _))
    have u := (val_pull hJ _ _ _).symm.trans ((val_corr hJ (ψW.psi_eq (xe x)) lam).trans (val_pull hJ _ _ _))
    rw [l₁, l₂, hψ x y J J' hJ hJ'] at u
    have v₁ : val (b x) (𝟙 _) y J = val (ψW.psi (xe x)) g y J :=
      (vb x _ _ y J hJ).trans ((val_pull hJ _ _ _).trans (by rw [Category.id_comp]))
    have v₂ : val (b x) (𝟙 _) y J = (om w y J J' (D'.xK x))⁻¹ * val (psi x) (𝟙 _) y J' := by
      refine v.trans (congrArg₂ (· * ·) ?_ rfl)
      rw [pw, Fintype.prod_unique, zpow_neg_one]
      simp only [om, Category.id_comp]
    exact mul_left_cancel (v₂.symm.trans (v₁.trans u))
  refine ⟨⟨e, e_hom, w, (isGen_iff w).2 hw, hE, ?_, xe, hc, W, ψW, g, hg, fun x => ⟨b x, fun jN jL => ?_,
      corr_of_val D.P.isLB fun y J hJ => vb x _ _ y J hJ⟩⟩, rfl, rfl, HEq.rfl⟩
  · exact (maps_iff w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf i) _
      (rigPull_le (G' := D'.P.A) (G := D.P.A) _ (specOf i) hE D.P.L) (fun _ => rfl)).2 hr
  · rw [← eψ]
    refine unit_ext fun y hy => ?_
    have v := vpsi x _ (𝟙 _) y jN (fun _ => jL) (GeneratorPullback.mapsAt_le_b _ _ _ _ jN jL hy) (GeneratorPullback.mapsAt_le_a _ _ _ _ jN jL hy)
    refine (gm_res _ y _ hy _).trans (v.trans (Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_
      (gm_res _ y _ hy _)))))
    rw [pw, Fintype.prod_unique]
    exact (map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull (𝟙 _) _ y _ hy _))

theorem exists_isPullDeg_comp {R R' R'' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [CommRing R'']
    [IsDomain R''] {i : R →+* R'} {j : R' →+* R''} (hi : Function.Injective i) (hj : Function.Injective j)
    {D : DegPre R} {D' : DegPre R'} {D'' : DegPre R''} (p : IsPullDeg i D D') (q : IsPullDeg j D' D'') :
    ∃ (r : IsPullDeg (j.comp i) D D'') (w : LB.Iso D''.P.L (D.P.L.pull (proj q ≫ proj p))),
      proj r = proj q ≫ proj p ∧ r.xe = q.xe.trans p.xe ∧ HEq r.w w ∧ Tri p.w q.w w := by
  have hji : Function.Injective (j.comp i) := hj.comp hi
  have sc : spMap j ≫ spMap i = spMap (j.comp i) := (spMap_comp i j).symm
  have gp : IsGrpPullback D''.P.A D.P.A (spMap (j.comp i)) (proj q ≫ proj p) :=
    ((pull_grp q).comp (pull_grp p)).congr sc rfl
  have g₁ := (isGen_iff _).1 p.w_gen
  have g₂ := (isGen_iff _).1 q.w_gen
  obtain ⟨w, T⟩ := Geo.Tor.exists_comp D'.P.isLB p.w q.w g₁ g₂ D.P.isLB D''.P.isLB
  have hr := T.pmaps_comp D'.P.isLB (fun _ => q.he) (FieldPull.pmaps_rig p) (FieldPull.pmaps_rig q)
  rw [sc] at hr
  have hc : ∀ x, (D''.c x).left ≫ proj q ≫ proj p = spMap (j.comp i) ≫ (D.c ((q.xe.trans p.xe) x)).left := fun x =>
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ proj p) (q.c_pr x)).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (p.c_pr _)).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) sc)))))
  obtain ⟨s, hs⟩ := GlobalTheory.PullDegComp.exists_generic_lift hi p
  obtain ⟨r, r₁, r₂, r₃⟩ := exists_isPullDeg_of_val hji D D'' p.psiW s hs gp w (T.pgen_comp D'.P.isLB g₁ g₂) hr
    (q.xe.trans p.xe) hc (fun x z J J'' hJ hJ'' => by
      obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB z
      have sj : jK R'' ≫ spMap j = genMap hj ≫ jK R' := (Category.id_comp _).symm.trans (fracMap_sq hj)
      have s' : genMap hj ≫ jK R' ≫ spMap i = genMap hji ≫ jK R :=
        (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) sj.symm).trans ((Category.assoc _ _ _).trans
          ((congrArg (_ ≫ ·) sc).trans ((Category.id_comp _).symm.trans (fracMap_sq hji)))))
      have v₁ := psi_val p _ _ s' hJ hJ' (q.xe x)
      have v₂ := psi_val q _ _ (fracMap_sq hj) hJ' hJ'' x
      have hx : D''.xK x ≫ proj q = genMap hj ≫ D'.xK (q.xe x) := by
        show (jK R'' ≫ (D''.c x).left) ≫ proj q = genMap hj ≫ jK R' ≫ (D'.c (q.xe x)).left
        rw [Category.assoc, q.c_pr, ← Category.assoc, ← Category.assoc, ← sj]
      have t : om w z J J'' (D''.xK x) = om p.w z J J' (D''.xK x ≫ proj q) * om q.w z J' J'' (D''.xK x) :=
        (congrArg (fun u => Geo.Tor.gw w (D''.xK x) z (J u) (J'' (D''.xK x)))
          (Category.assoc (D''.xK x) (proj q) (proj p)).symm).trans
          (T _ _ z _ _ _ (hJ ((D''.xK x ≫ proj q) ≫ proj p)) (hJ' (D''.xK x ≫ proj q)) (hJ'' _))
      rw [v₂, Category.id_comp, ← hx, ← _root_.mul_assoc, ← mul_inv, ← t] at v₁
      exact v₁)
  exact ⟨r, w, r₁, r₂, r₃, T⟩

def Sq {X X' G G' Y Y' : Scheme.{0}} {M : LB X} {M' : LB X'} {L : LB G} {L' : LB G'}
    {F : X' ⟶ X} {B : G' ⟶ G} {p : Y ⟶ X} {p' : Y' ⟶ X'} {f : Y ⟶ G} {f' : Y' ⟶ G'} (h : Y' ⟶ Y)
    (wM : LB.Iso M' (M.pull F)) (wL : LB.Iso L' (L.pull B))
    (w : LB.Iso (L.pull f) (M.pull p)) (w' : LB.Iso (L'.pull f') (M'.pull p')) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (jM : M.ι) (jM' : M'.ι) (jL : L.ι) (jL' : L'.ι),
    F (p' (r z)) ∈ M.U jM → p' (r z) ∈ M'.U jM' → B (f' (r z)) ∈ L.U jL → f' (r z) ∈ L'.U jL' →
    Geo.Tor.gw wM (r ≫ p') z jM jM' * Geo.Tor.gw w' r z jM' (fun _ => jL') =
      Geo.Tor.gw w (r ≫ h) z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ f') z jL jL'

theorem Sq.comp {X X' X'' G G' G'' Y Y' Y'' : Scheme.{0}} {M : LB X} {M' : LB X'} {M'' : LB X''} {L : LB G} {L' : LB G'}
    {L'' : LB G''} {F : X' ⟶ X} {F' : X'' ⟶ X'} {B : G' ⟶ G} {B' : G'' ⟶ G'} {p : Y ⟶ X} {p' : Y' ⟶ X'} {p'' : Y'' ⟶ X''}
    {f : Y ⟶ G} {f' : Y' ⟶ G'} {f'' : Y'' ⟶ G''} {h : Y' ⟶ Y} {h' : Y'' ⟶ Y'}
    {wM : LB.Iso M' (M.pull F)} {wM' : LB.Iso M'' (M'.pull F')} {wM'' : LB.Iso M'' (M.pull (F' ≫ F))}
    {wL : LB.Iso L' (L.pull B)} {wL' : LB.Iso L'' (L'.pull B')} {wL'' : LB.Iso L'' (L.pull (B' ≫ B))}
    {w : LB.Iso (L.pull f) (M.pull p)} {w' : LB.Iso (L'.pull f') (M'.pull p')} {w'' : LB.Iso (L''.pull f'') (M''.pull p'')}
    (hM : M'.IsLB) (hL : L'.IsLB) (TM : Tri wM wM' wM'') (TL : Tri wL wL' wL'')
    (hf : h' ≫ f' = f'' ≫ B') (hp : p'' ≫ F' = h' ≫ p') (H : Sq h wM wL w w') (H' : Sq h' wM' wL' w' w'') :
    Sq (h' ≫ h) wM'' wL'' w w'' := by
  intro Z r z jM jM'' jL jL'' h₁ h₂ h₃ h₄
  have ef : f' (h' (r z)) = B' (f'' (r z)) := congrArg (fun g => g (r z)) hf
  have ep : p' (h' (r z)) = F' (p'' (r z)) := congrArg (fun g => g (r z)) hp.symm
  obtain ⟨jM', m⟩ := exists_chart hM (F' (p'' (r z)))
  obtain ⟨jL', l⟩ := exists_chart hL (B' (f'' (r z)))
  have a := H Z (r ≫ h') z jM jM' jL jL' (by show F (p' (h' (r z))) ∈ _; rw [ep]; exact h₁)
    (by show p' (h' (r z)) ∈ _; rw [ep]; exact m) (by show B (f' (h' (r z))) ∈ _; rw [ef]; exact h₃)
    (by show f' (h' (r z)) ∈ _; rw [ef]; exact l)
  have b := H' Z r z jM' jM'' jL' jL'' m h₂ l h₄
  have c := TM Z (r ≫ p'') z jM jM' jM'' h₁ m h₂
  have d := TL Z (r ≫ f'') z jL jL' jL'' h₃ l h₄
  rw [Category.assoc, hp, ← Category.assoc] at c
  rw [Category.assoc, ← hf, ← Category.assoc] at d
  rw [c, d, _root_.mul_assoc, b, ← _root_.mul_assoc, a, _root_.mul_assoc, Category.assoc]

theorem isPullUnif_comp {R R' R'' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [CommRing R'']
    [IsDomain R''] {I : Ideal R} {I' : Ideal R'} {I'' : Ideal R''} {i : R →+* R'} {j : R' →+* R''}
    {D : DegData R I} {D' : DegData R' I'} {D'' : DegData R'' I''} {p : IsPullDeg i D.toPre D'.toPre}
    {q : IsPullDeg j D'.toPre D''.toPre} {r : IsPullDeg (j.comp i) D.toPre D''.toPre}
    {w : LB.Iso D''.toPre.P.L (D.toPre.P.L.pull (proj q ≫ proj p))} (r₁ : proj r = proj q ≫ proj p)
    (r₂ : r.xe = q.xe.trans p.xe) (r₃ : HEq r.w w) (T : Tri p.w q.w w)
    {A : PolAV (Sp (FractionRing R))} {A' : PolAV (Sp (FractionRing R'))} {A'' : PolAV (Sp (FractionRing R''))}
    {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {G' : Over (Sp R')} [GrpObj G'] [IsCommMonObj G']
    {G'' : Over (Sp R'')} [GrpObj G''] [IsCommMonObj G'']
    {b₁ : G' ≅ (Over.pullback (specOf i)).obj G} {b₂ : G'' ≅ (Over.pullback (specOf j)).obj G'}
    {b : G'' ≅ (Over.pullback (specOf (j.comp i))).obj G}
    (hb : b.hom.left ≫ pullback.fst G.hom (specOf (j.comp i)) =
      (b₂.hom.left ≫ pullback.fst G'.hom (specOf j)) ≫ (b₁.hom.left ≫ pullback.fst G.hom (specOf i)))
    {U : Unif I D A G} {U' : Unif I' D' A' G'} {U'' : Unif I'' D'' A'' G''}
    (H₁ : IsPullUnif i p b₁ U U') (H₂ : IsPullUnif j q b₂ U' U'') : IsPullUnif (j.comp i) r b U U'' := by
  have sc : specOf j ≫ specOf i = specOf (j.comp i) := (spMap_comp i j).symm
  obtain ⟨w₁, g₁, e₁, m₁, K₁⟩ := (isPullUnif_iff_stalks _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).1 H₁
  obtain ⟨w₂, g₂, e₂, m₂, K₂⟩ := (isPullUnif_iff_stalks _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).1 H₂
  replace g₁ := (isGen_iff _).1 g₁
  replace g₂ := (isGen_iff _).1 g₂
  replace m₁ := (maps_iff w₁ _ (fun _ => eSec G) _ U'.LG.rig U.LG.rig (specOf i) _
    (rigPull_le (G' := G') (G := G) _ (specOf i) e₁ U.LG.L) (fun _ => rfl)).1 m₁
  replace m₂ := (maps_iff w₂ _ (fun _ => eSec G') _ U''.LG.rig U'.LG.rig (specOf j) _
    (rigPull_le (G' := G'') (G := G') _ (specOf j) e₂ U'.LG.L) (fun _ => rfl)).1 m₂
  obtain ⟨wL, TL⟩ := Geo.Tor.exists_comp U'.LG.isLB w₁ w₂ g₁ g₂ U.LG.isLB U''.LG.isLB
  have key : ∀ (Φ : D''.toPre.P.A.left ⟶ D.toPre.P.A.left) (u : LB.Iso D''.toPre.P.L (D.toPre.P.L.pull Φ))
      (xe : D''.toPre.X ≃+ D.toPre.X) (B : G''.left ⟶ G.left), Φ = proj q ≫ proj p → HEq u w → xe = q.xe.trans p.xe →
      B = (b₂.hom.left ≫ pullback.fst G'.hom (specOf j)) ≫ (b₁.hom.left ≫ pullback.fst G.hom (specOf i)) →
      ∃ wL : LB.Iso U''.LG.L (U.LG.L.pull B), wL.IsGen ∧ ∃ he : eSec G'' ≫ B = specOf (j.comp i) ≫ eSec G,
        LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G'') (fun _ => 1)) U''.LG.rig
          (rigPullOf B (specOf (j.comp i)) he U.LG.L U.LG.rig) ∧
        ∀ e : ℕ, ∃ h : (thickObj R'' I'' e G'').left ⟶ (thickObj R I e G).left,
          h ≫ (fstG I e G).left = (fstG I'' e G'').left ≫ B ∧
          ((U''.gt e).pG.left ≫ Φ = h ≫ (U.gt e).pG.left ∧ ∀ x : D''.toPre.X,
            (∀ κ : Fin 4, D''.toPre.Oφ (U''.gt e).pG x κ ≫ Φ = h ≫ D.toPre.Oφ (U.gt e).pG (xe x) κ) ∧
            PMaps u (D''.toPre.Oφ (U''.gt e).pG x) (D.toPre.Oφ (U.gt e).pG (xe x)) Oinvε ((U''.gt e).t x)
              ((U.gt e).t (xe x)) h) ∧ Sq h u wL (U.w e) (U''.w e) := by
    rintro _ u _ _ rfl hu rfl rfl
    obtain rfl := eq_of_heq hu
    have he : eSec G'' ≫ (b₂.hom.left ≫ pullback.fst G'.hom (specOf j)) ≫ (b₁.hom.left ≫ pullback.fst G.hom (specOf i)) =
        specOf (j.comp i) ≫ eSec G :=
      (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e₂).trans ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) e₁).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) sc)))))
    have hr := TL.pmaps_comp U'.LG.isLB (fun _ => e₂) m₁ m₂
    rw [sc] at hr
    refine ⟨wL, (isGen_iff _).2 (TL.pgen_comp U'.LG.isLB g₁ g₂), he,
      (maps_iff wL _ (fun _ => eSec G) _ U''.LG.rig U.LG.rig (specOf (j.comp i)) _
        (rigPull_le (G' := G'') (G := G) _ (specOf (j.comp i)) he U.LG.L) (fun _ => rfl)).2 hr, fun e => ?_⟩
    obtain ⟨h₁, f₁, ⟨p₁, t₁⟩, s₁⟩ := K₁ e
    obtain ⟨h₂, f₂, ⟨p₂, t₂⟩, s₂⟩ := K₂ e
    refine ⟨h₂ ≫ h₁, ?_, ⟨?_, fun x => ⟨fun κ => ?_, ?_⟩⟩, Sq.comp D'.toPre.P.isLB U'.LG.isLB T TL f₂ p₂ s₁ s₂⟩
    · exact (Category.assoc _ _ _).trans ((congrArg (h₂ ≫ ·) f₁).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) f₂).trans (Category.assoc _ _ _))))
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) p₂).trans ((Category.assoc _ _ _).trans
        ((congrArg (h₂ ≫ ·) p₁).trans (Category.assoc _ _ _).symm)))
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) ((t₂ x).1 κ)).trans ((Category.assoc _ _ _).trans
        ((congrArg (h₂ ≫ ·) ((t₁ (q.xe x)).1 κ)).trans (Category.assoc _ _ _).symm)))
    · exact T.pmaps_comp D'.toPre.P.isLB (t₂ x).1 (t₁ (q.xe x)).2 (t₂ x).2
  exact (isPullUnif_iff_stalks _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).2 (key _ r.w r.xe _ r₁ r₃ r₂ hb)

end GlobalTheory.Mum.GalMul

namespace GlobalTheory.Mum

theorem galMap_mul : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (σ τ : Gal ρ) (a b : G'.left ⟶ G'.left), GalMap hD U' σ a → GalMap hD U' τ b → GalMap hD U' (σ * τ) (a ≫ b) := by
  intro R _ _ _ _ R' _ _ _ ρ _ D D' hD A' G' _ _ _ U' σ τ a b ⟨ga, q, b₂, ha, H₂, x₂, c₂⟩ ⟨gb, p, b₁, hb, H₁, x₁, c₁⟩
  have gp : IsGrpPullback G' G' (spMap ((Gal.hom σ).comp (Gal.hom τ))) (a ≫ b) :=
    (ga.comp gb).congr (spMap_comp _ _).symm rfl
  obtain ⟨r, w, r₁, r₂, r₃, T⟩ := GalMul.exists_isPullDeg_comp (i := Gal.hom τ) (j := Gal.hom σ) τ.1.injective σ.1.injective p q
  obtain ⟨bc, -, hbc⟩ := grpPullback_iso gp (isGrpPullback_pullback G' (specOf ((Gal.hom σ).comp (Gal.hom τ))))
  refine ⟨gp, r, bc, hbc, GalMul.isPullUnif_comp r₁ r₂ r₃ T (hbc.trans (by rw [ha, hb])) H₁ H₂, fun x => ?_, ?_⟩
  · exact (congrArg (fun e => e x) r₂).trans ((x₁ _).trans (x₂ x))
  · rintro _ _ rfl rfl
    exact (congrArg (· ≫ _) r₁).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (c₁ _ _ rfl rfl)).trans (c₂ _ _ rfl rfl)))

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformizationBaseChangeCompleteDvr
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum


open GlobalTheory.ArcPull GlobalTheory.PullLinear in
theorem isPullDeg_of_trait_unif : ∀ (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsLocalRing R₀], AdmBase R₀ (maximalIdeal R₀) → ∀ (D₀ : DegData R₀ (maximalIdeal R₀)) (A₀ : PolAV (Sp (FractionRing R₀))) (G₀ : Over (Sp R₀)) [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G₀ → ∀ (U₀ : Unif (maximalIdeal R₀) D₀ A₀ G₀) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R₀ →+* W), Function.Injective φ → IsLocalHom φ → ∀ (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (β : GW.left ⟶ G₀.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW), IsGrpPullback GW G₀ (spMap φ) β → LBIso UW.LG.L (U₀.LG.L.pull β) → Nonempty (IsPullDeg φ D₀.toPre DW.toPre) := by
  intro R₀ _ _ _ hR D₀ A₀ G₀ _ _ hG U₀ W _ _ _ hW φ hφ hloc GW _ _ β DW AW UW hβ hLβ
  obtain ⟨hL1, -, -, h4, h5⟩ := GlobalTheory.firstFiveLaws
  have := hW.1
  have hW' : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  obtain ⟨bc, mbc, hbc⟩ := grpPullback_iso hβ (isGrpPullback_pullback G₀ (spMap φ))
  have hbc' : bc.hom.left ≫ pullback.fst G₀.hom (specOf φ) = β := hbc
  have hGW : IsSemiAbelian GW := by
    have := mbc
    exact GlobalTheory.isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback (spMap φ) G₀ hG)

  have sq : spMap (GlobalTheory.ArcPull.fracMap hφ) ≫ jK R₀ = jK W ≫ spMap φ :=
    (GlobalTheory.ArcPull.fracMap_sq hφ).symm.trans (Category.id_comp _)
  obtain ⟨A', gA, pA, dA, mA, tA⟩ := hL1.polBaseChange _ _ (spMap (GlobalTheory.ArcPull.fracMap hφ)) A₀
  have gpA : IsGrpPullback A'.A A₀.A (spMap (GlobalTheory.ArcPull.fracMap hφ)) gA := ⟨pA, fun T x y x₀ y₀ hx hy => by
    have e₁ : x₀ = Out.toBase pA.w x := Over.OverMorphism.ext hx
    have e₂ : y₀ = Out.toBase pA.w y := Over.OverMorphism.ext hy
    rw [e₁, e₂, ← mA]; rfl⟩
  have gpG := GlobalTheory.ThetaBaseChange.grp_generic U₀.toUnifPre
  have gp' : IsGrpPullback ((Over.pullback (jK W)).obj GW) G₀ (spMap (GlobalTheory.ArcPull.fracMap hφ) ≫ jK R₀)
      (pullback.fst GW.hom (jK W) ≫ β) :=
    ((isGrpPullback_pullback GW (jK W)).comp hβ).congr sq.symm rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp' (gpA.comp gpG)
  have hgi : U₀.gen.inv.left ≫ U₀.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have wA : LBIso (A'.L.pull eA.hom.left) (U₀.LG.L.pull (pullback.fst GW.hom (jK W) ≫
      bc.hom.left ≫ pullback.fst G₀.hom (specOf φ))) := by
    refine LBIso.trans (pull_isLB A'.isLB _) (pull_isLB (pull_isLB A₀.isLB gA) eA.hom.left)
      (pull_isLB U₀.LG.isLB _)
      ((LBIso.symm tA).chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull A'.L _ _ rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (A₀.L.pull gA) _ _ rfl)) ?_
    refine LBIso.chartPull (h := eA.hom.left ≫ gA ≫ U₀.gen.inv.left)
      (chartPullLinComb A₀.L gA (fun _ => eA.hom.left) (fun _ => U₀.gen.hom.left) _ _ fun _ => ?_)
      (chartPullSame U₀.LG.L _ (fun _ => pullback.fst G₀.hom (jK R₀)) _ _ fun _ => ?_) U₀.ext
    · rw [Category.assoc, Category.assoc, hgi, Category.comp_id]
    · rw [hbc', ← heA]; simp only [Category.assoc]

  have he : eSec GW ≫ bc.hom.left ≫ pullback.fst G₀.hom (specOf φ) = specOf φ ≫ eSec G₀ := by
    rw [hbc']; exact (cubeMapOf hβ).e_comm
  obtain ⟨wL, hwL, hm⟩ := GlobalTheory.Unif.RigidifyIso.exists_rigidified_iso _ _ (specOf φ) G₀ GW
    (bc.hom.left ≫ pullback.fst G₀.hom (specOf φ)) he U₀.LG UW.LG (by rw [hbc']; exact hLβ)

  obtain ⟨Wo, hWo, hψ⟩ := h5.psiOnExists R₀ _ hR D₀
  have hgen : (specOf φ).base (genericPoint (Spec (CommRingCat.of W))) ∈ Wo := by
    have : (specOf φ).base (genericPoint (Spec (CommRingCat.of W))) = genericPoint (Spec (CommRingCat.of R₀)) := by
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective φ hφ)
    rw [this]; exact hWo

  obtain ⟨D₁, hD₁, U₁, hLG, -, -⟩ := h4.unifBaseChange R₀ W _ _ hR hW' φ (map_maximalIdeal_le φ) D₀ A₀ G₀ hG U₀
    Wo hψ hgen GW bc mbc A' dA eA mE wA UW.LG wL he hwL hm
  obtain ⟨-, w₀, -, g₀, -, m₀, -⟩ := exists_iso_pair_of_eq hLG
  obtain ⟨hDid, -⟩ := GlobalTheory.sixthLaws_and_unifUniq.2 W _ hW' D₁ DW A' AW GW hGW U₁ UW w₀ g₀ m₀
  have h := GlobalTheory.Mum.isPullDeg_unique_and_comp.2 R₀ W W φ (RingHom.id W) hφ Function.injective_id D₀.toPre D₁.toPre
    DW.toPre ⟨hD₁⟩ ⟨hDid⟩
  rwa [RingHom.id_comp] at h

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnimodLatticeBarBar
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem unimodLattice_bar_bar {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (a : 𝓞 E) :
    H.bar (H.bar a) = a := by
  apply RingOfIntegers.ext
  rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]

theorem unimodLattice_bar_rt {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    H.bar H.rt = -H.rt := by
  apply RingOfIntegers.ext
  rw [H.bar_eq]
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply φ.injective
  rw [IsCMField.complexEmbedding_complexConj]
  have hsq : φ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
    have := congrArg (fun x : 𝓞 E => φ (x : E)) H.rt_sq
    simpa using this
  have hd : (7 : ℝ) ≤ H.d := by
    have := H.d_mod
    have : 7 ≤ H.d := by omega
    exact_mod_cast this
  set z := φ (H.rt : E) with hz
  have hre := congrArg Complex.re hsq
  have him := congrArg Complex.im hsq
  simp [pow_two] at hre him
  have hx : z.re = 0 := by
    have hm : z.re * z.im = 0 := by linarith
    rcases mul_eq_zero.1 hm with h | h
    · exact h
    · rw [h] at hre; nlinarith [sq_nonneg z.re]
  have key : starRingEnd ℂ z = -z := by apply Complex.ext <;> simp [hx]
  rw [hz] at key
  simpa using key

theorem unimodLattice_w0_add {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    H.w0 + H.bar H.w0 = 1 := by
  have h1 := H.two_weight_eq_one_add_root
  have h2 : 2 * H.bar H.w0 = 1 - H.rt := by
    have := congrArg H.bar h1
    rw [map_mul, map_add (f := _), map_one, unimodLattice_bar_rt, map_ofNat] at this
    rw [this]; ring
  have h3 : (2 : 𝓞 E) * (H.w0 + H.bar H.w0) = 2 * 1 := by
    rw [mul_add, h1, h2]; ring
  exact mul_left_cancel₀ two_ne_zero h3

theorem unimodLattice :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), ∃ (r : ℕ) (W : Matrix (Fin r) (Fin r) ℤ) (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), 1 ≤ r ∧ ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef ∧ IsUnit (W + W.transpose).det ∧ (∀ a, (ρ a).transpose * (W + W.transpose) = (W + W.transpose) * ρ (H.bar a)) ∧ W = (W + W.transpose) * ρ H.w0 := by
  intro E _ _ _ H
  obtain ⟨m, B0, ρ0, hm, hsym, hpd, hadj⟩ := _root_.GlobalTheory.TraceLattice.exists_traceForm_matrix E H
  obtain ⟨r, b, ρ, hr, hbs, hbpd, hbu, hbadj⟩ :=
    GlobalTheory.T.exists_unimodular_posDef_form_adjoint_rep_of_posDef (𝓞 E) (H.bar : 𝓞 E →+* 𝓞 E) (unimodLattice_bar_bar H) m B0 ρ0 hm hsym hpd hadj
  have hW : b * ρ H.w0 + (b * ρ H.w0).transpose = b := by
    rw [Matrix.transpose_mul, hbs, hbadj, ← Matrix.mul_add, ← map_add (f := _)]
    erw [unimodLattice_w0_add H]
    rw [map_one, Matrix.mul_one]
  refine ⟨r, b * ρ H.w0, ρ, hr, ?_, ?_, ?_, ?_⟩
  · rw [hW]; exact hbpd
  · rw [hW]; exact hbu
  · intro a; rw [hW]; exact hbadj a
  · rw [hW]

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryTraitLabelsSurjectiveKernel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc

theorem uIsLab_onto_and_ker : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X : USetup C) (p : ℕ) [Fact p.Prime] (z : X.M.Z) (ct : UCTrait X p z) (yy : X.S.Gam →+ ModN (X.S.r * X.S.N) ct.T.P.D.toPre.X), UIsLab X ct yy → Function.Surjective yy ∧ yy.ker = X.S.HH X.M z := by
  intro E _ _ _ H Dw _ l Xo cf C X p _ z ct yy hl
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', u', -, -, -, hR', G, _, α, β, -, -, -, y₀, hy₀, u, lb, j, -, hyy, -⟩ := hl
  refine ⟨?_, ?_⟩
  · intro m
    obtain ⟨χ', rfl⟩ := QuotientAddGroup.mk_surjective m
    obtain ⟨a, ha⟩ := lb.yy_onto (QuotientAddGroup.mk (j.symm χ'))
    exact ⟨a, by rw [hyy a _ ha, j.apply_symm_apply]⟩
  have hker : yy.ker = lb.yy.ker := by
    ext a
    simp only [AddMonoidHom.mem_ker]
    obtain ⟨χ, hχ⟩ := QuotientAddGroup.mk_surjective (lb.yy a)
    rw [hyy a χ hχ.symm, ← hχ, QuotientAddGroup.eq_zero_iff, QuotientAddGroup.eq_zero_iff]
    constructor
    · rintro ⟨v, hv⟩
      refine ⟨j.symm v, ?_⟩
      simp only [nsmulAddMonoidHom_apply] at hv ⊢
      rw [← map_nsmul, hv, j.symm_apply_apply]
    · rintro ⟨v, hv⟩
      refine ⟨j v, ?_⟩
      simp only [nsmulAddMonoidHom_apply] at hv ⊢
      rw [← map_nsmul, hv]
  have hint : ∀ a : X.o₁, ‖y₀ (algebraMap X.o₁ R' a)‖ ≤ 1 := fun a => by
    rw [hy₀]
    exact RatModel.norm_val_le_one ct.cen ((X.M.O z).algebraMap_mem a)
  have hcl := GlobalTheory.UnitTheta.closure_unit_theta GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2
    GlobalTheory.ZH.uTors_closed _ _ _ ρ' p y₀ u lb hint
  rw [hker, ← hcl.2]
  obtain ⟨x₀, hx₀⟩ := X.hasDiv z
  set val := X.M.val (gPt p ≫ ct.y) with hval
  have hsp : ∀ w, (gPt p ≫ ct.y) w ⤳ (gPt p ≫ ct.y) (IsLocalRing.closedPoint (PadicAlgCl p)) :=
    RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ _)
  have hgz : (gPt p ≫ ct.y) (IsLocalRing.closedPoint (PadicAlgCl p)) ⤳ z :=
    RatModel.gPt_specializes ct.cen _
  have hy : ∀ x, y₀ ⟨c₀ * X.S.th x, hth x⟩ = val (c₀ * X.S.th x) := fun x => hy₀ _
  have hmul : ∀ x, ‖val (c₀ * X.S.th x)‖ = ‖val (X.S.th x / X.S.th x₀)‖ * ‖val (c₀ * X.S.th x₀)‖ := by
    intro x
    rw [← norm_mul, hval, ← RatModel.val_mul hsp (RatModel.O_le_of_specializes hgz (hx₀.2 x)) (hR' (hth x₀))]
    congr 2
    have := hx₀.1
    field_simp
  have hδ : ‖val (c₀ * X.S.th x₀)‖ = (X.S.rechart c₀ hc R' fg frac hth hev).delta y₀ := by
    apply le_antisymm
    · rw [← hy]
      exact le_ciSup (f := fun x => ‖y₀ ⟨c₀ * X.S.th x, hth x⟩‖) (Set.finite_range _).bddAbove x₀
    · obtain ⟨x₁, hx₁⟩ := exists_eq_ciSup_of_finite (f := fun x => ‖y₀ ⟨c₀ * X.S.th x, hth x⟩‖)
      change ⨆ x, ‖y₀ ⟨c₀ * X.S.th x, hth x⟩‖ ≤ _
      rw [← hx₁, hy, hmul x₁]
      exact mul_le_of_le_one_left (norm_nonneg _) (RatModel.norm_val_le_one ct.cen (hx₀.2 x₁))
  have key : ∀ x, x ∈ X.S.supI X.M z ↔
      ‖y₀ ⟨c₀ * X.S.th x, hth x⟩‖ = (X.S.rechart c₀ hc R' fg frac hth hev).delta y₀ := by
    intro x
    change X.M.Div X.S.th x z ↔ _
    rw [hx₀.div_iff_isUnit x, ← RatModel.norm_val_eq_one_iff ct.cen (hx₀.2 x), hy, hmul x, hδ]
    exact (mul_eq_right₀ hcl.1.ne').symm
  rw [ThetaSys.HH]
  congr 1
  ext x
  exact (key x).symm

end GlobalTheory.UPoinc
end

