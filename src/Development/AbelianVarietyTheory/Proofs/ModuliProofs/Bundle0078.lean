module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.InvariantVectorFieldsBasisVerticalDerivations
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0043

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSchemeMapOfProjectiveCoordinates
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM.RepMap
variable {X : Scheme.{0}} {σ : Type}

theorem gs_one (x : X) (U : X.Opens) (h : x ∈ U) (f : Γ(X, U)) :
    gs (𝟙 X) x U f = (X.presheaf.germ U x h).hom f := by
  rw [gs_eq (𝟙 X) x U h]; rfl

theorem lbIso_of_germs (A B : LB X) (a : σ → A.Sec) (b : σ → B.Sec)
    (H : ∀ (y : X) (j : B.ι) (k : A.ι), y ∈ B.U j → y ∈ A.U k → (∃ i, IsUnit (gs (𝟙 X) y (A.U k) ((a i).f k))) ∧
      ∃ u : (X.presheaf.stalk y)ˣ, ∀ i, gs (𝟙 X) y (B.U j) ((b i).f j) = u * gs (𝟙 X) y (A.U k) ((a i).f k)) :
    LBIso A B := by
  have uniq : ∀ (y : X) (j : B.ι) (k : A.ι), y ∈ B.U j → y ∈ A.U k → ∀ u u' : (X.presheaf.stalk y)ˣ,
      (∀ i, gs (𝟙 X) y (B.U j) ((b i).f j) = u * gs (𝟙 X) y (A.U k) ((a i).f k)) →
      (∀ i, gs (𝟙 X) y (B.U j) ((b i).f j) = u' * gs (𝟙 X) y (A.U k) ((a i).f k)) → u = u' := by
    intro y j k hj hk u u' h h'
    obtain ⟨i, hi⟩ := (H y j k hj hk).1
    exact Units.ext (hi.mul_right_cancel ((h i).symm.trans (h' i)))
  have loc : ∀ (j : B.ι) (k : A.ι) (y : ↥(B.U j ⊓ A.U k : X.Opens)), ∃ (W : X.Opens) (_ : W ≤ B.U j ⊓ A.U k) (c : Γ(X, W)ˣ),
      y.1 ∈ W ∧ ∀ z ∈ W, ∀ i, gs (𝟙 X) z (B.U j) ((b i).f j) = gm (𝟙 X) z W c * gs (𝟙 X) z (A.U k) ((a i).f k) := by
    rintro j k ⟨y, hy⟩
    obtain ⟨⟨i₀, hi₀⟩, u, hu⟩ := H y j k hy.1 hy.2
    let t : Γ(X, B.U j ⊓ A.U k) := resG X inf_le_left ((b i₀).f j) * resG X inf_le_right ((a i₀).f k)
    have hle := X.basicOpen_le t
    have ht : IsUnit (resG X hle t) := RingedSpace.isUnit_res_basicOpen X.toRingedSpace t
    rw [map_mul] at ht
    obtain ⟨c₁, h₁⟩ := isUnit_of_mul_isUnit_left ht
    obtain ⟨c₂, h₂⟩ := isUnit_of_mul_isUnit_right ht
    refine ⟨X.basicOpen t, hle, c₁ * c₂⁻¹, ?_, fun z hz i => ?_⟩
    · rw [X.mem_basicOpen t y hy, ← gs_one y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_res _ y _ hy, hu]
      exact (u.isUnit.mul hi₀).mul hi₀
    · obtain ⟨-, u', hu'⟩ := H z j k (hle hz).1 (hle hz).2
      have e₁ : (gm (𝟙 X) z _ c₁).val = gs (𝟙 X) z (B.U j) ((b i₀).f j) := by
        rw [← gs_unit _ z _ hz, h₁, gs_res _ z _ hz, gs_res _ z _ (hle hz)]
      have e₂ : (gm (𝟙 X) z _ c₂).val = gs (𝟙 X) z (A.U k) ((a i₀).f k) := by
        rw [← gs_unit _ z _ hz, h₂, gs_res _ z _ hz, gs_res _ z _ (hle hz)]
      have e : gm (𝟙 X) z _ c₁ = u' * gm (𝟙 X) z _ c₂ := Units.ext (by rw [Units.val_mul, e₁, e₂, hu'])
      rw [map_mul, map_inv, e, mul_inv_cancel_right, hu']
  choose W hW c hy hc using loc
  have glue : ∀ (j : B.ι) (k : A.ι), ∃ w : Γ(X, B.U j ⊓ A.U k)ˣ, ∀ z ∈ B.U j ⊓ A.U k, ∀ i,
      gs (𝟙 X) z (B.U j) ((b i).f j) = gm (𝟙 X) z _ w * gs (𝟙 X) z (A.U k) ((a i).f k) := by
    intro j k
    obtain ⟨w, hw⟩ := glue_unit (B.U j ⊓ A.U k) (W j k) (hW j k)
      (fun z hz => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨z, hz⟩, hy j k ⟨z, hz⟩⟩) (c j k)
      (fun p q z hz => uniq z j k (hW j k p hz.1).1 (hW j k p hz.1).2 _ _ (hc j k p z hz.1) (hc j k q z hz.2))
    refine ⟨w, fun z hz i => ?_⟩
    rw [← gm_res (𝟙 X) z (hW j k ⟨z, hz⟩) (hy j k ⟨z, hz⟩), hw]
    exact hc j k ⟨z, hz⟩ z (hy j k ⟨z, hz⟩) i
  choose w hw using glue
  refine ⟨⟨fun p => w p.1 p.2⟩, fun p q => unit_ext fun y hy => ?_⟩
  refine (gm_res _ y _ hy _).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div A B (𝟙 X) y p q hy)
    (gm_res _ y _ hy _))).symm)
  refine uniq y p.1 p.2 hy.1.1 hy.1.2 _ _ (hw p.1 p.2 y hy.1) fun i => ?_
  have hB : y ∈ B.U p.1 ⊓ B.U q.1 := ⟨hy.1.1, hy.2.1⟩
  have hA : y ∈ A.U p.2 ⊓ A.U q.2 := ⟨hy.1.2, hy.2.2⟩
  have eB := congrArg (gs (𝟙 X) y _) ((b i).compat p.1 q.1)
  have eA := congrArg (gs (𝟙 X) y _) ((a i).compat p.2 q.2)
  rw [gs_mul _ y _ hB, gs_res _ y _ hB, gs_res _ y _ hB, gs_unit _ y _ hB] at eB
  rw [gs_mul _ y _ hA, gs_res _ y _ hA, gs_res _ y _ hA, gs_unit _ y _ hA] at eA
  rw [eB, eA, hw q.1 q.2 y hy.2 i]
  change _ = ((_ * _ * gm (𝟙 X) y _ (w q.1 q.2) : (X.presheaf.stalk y)ˣ) : X.presheaf.stalk y) * _
  rw [Units.val_mul, Units.val_mul]
  have := (gm (𝟙 X) y _ (A.g p.2 q.2)).inv_mul
  linear_combination (-(gm (𝟙 X) y _ (B.g p.1 q.1)).val * (gm (𝟙 X) y _ (w q.1 q.2)).val *
    gs (𝟙 X) y (A.U q.2) ((a i).f q.2)) * this

theorem coord_germ {M : LB X} {th : σ → M.Sec} {R : Type} [CommRing R] {x : Sp R ⟶ X} {v : σ → R}
    (h : SecCoord M th x v) (p : Sp R) (k : M.ι) (hk : x p ∈ M.U k) :
    ∃ t : ((Sp R).presheaf.stalk p)ˣ, ∀ i, gs x p (M.U k) ((th i).f k) =
      ((Sp R).presheaf.germ ⊤ p trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (v i)) * t := by
  obtain ⟨τ, -, h⟩ := h
  have hp : p ∈ (M.pull x).U (fun _ => k) := mem_pull.2 hk
  refine ⟨gm (𝟙 _) p _ (τ.s fun _ => k), fun i => ?_⟩
  have e := congrArg (gs (𝟙 _) p _) (h i (fun _ => k) (RepBC.pull_le M x _))
  rw [gs_appLE x _ _ _ (𝟙 _) p hp, gs_mul _ p _ hp, gs_res _ p _ hp, gs_one p ⊤ trivial, Category.id_comp] at e
  rw [← gs_unit _ p _ hp]
  exact e

theorem lbIso_of_coord (A B : LB X) (a : σ → A.Sec) (b : σ → B.Sec)
    (H : ∀ y : X, ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ X) (v : σ → R), IsOpenImmersion x ∧ y ∈ Set.range x ∧
      Ideal.span (Set.range v) = ⊤ ∧ SecCoord A a x v ∧ SecCoord B b x v) : LBIso A B := by
  refine lbIso_of_germs A B a b fun y j k hj hk => ?_
  obtain ⟨R, _, x, v, _, ⟨p, rfl⟩, hv, hA, hB⟩ := H y
  obtain ⟨t, ht⟩ := coord_germ hA p k hk
  obtain ⟨t', ht'⟩ := coord_germ hB p j hj
  let e := (asIso (x.stalkMap p)).commRingCatIsoToRingEquiv
  have he : ∀ (U : X.Opens) (_ : x p ∈ U) f, gs x p U f = e (gs (𝟙 X) (x p) U f) := fun U h f => gs_stalkMap x p U h f
  let ψ : R →+* (Sp R).presheaf.stalk p :=
    ((Sp R).presheaf.germ ⊤ p trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  constructor
  · have : ∃ i, IsUnit (ψ (v i)) := by
      by_contra hn
      push_neg at hn
      have : Ideal.span (Set.range v) ≤ (IsLocalRing.maximalIdeal _).comap ψ := by
        rw [Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        exact hn i
      rw [hv, top_le_iff, Ideal.comap_eq_top_iff] at this
      exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top this
    obtain ⟨i, hi⟩ := this
    refine ⟨i, ?_⟩
    rw [← MulEquiv.isUnit_map e, ← he _ hk, ht]
    exact hi.mul t.isUnit
  · refine ⟨Units.map e.symm.toMonoidHom (t' * t⁻¹), fun i => e.injective ?_⟩
    rw [map_mul, ← he _ hk, ← he _ hj, ht, ht']
    have : e (Units.map e.symm.toMonoidHom (t' * t⁻¹)).val = (t' * t⁻¹).val := e.apply_symm_apply _
    rw [this, Units.val_mul]
    linear_combination (-(ψ (v i)) * t'.val) * t.inv_mul

theorem exists_spMap {R R' : Type} [CommRing R] [CommRing R'] (a : Sp R' ⟶ Sp R) : ∃ φ : R →+* R', a = spMap φ :=
  ⟨(Spec.preimage a).hom, (Spec.map_preimage a).symm⟩

theorem exists_factor {U : Scheme.{0}} {R : Type} [CommRing R] (y : Sp R ⟶ X) (u : U ⟶ X) [IsOpenImmersion u]
    (p : Sp R) (h : y p ∈ Set.range u) : ∃ (R' : Type) (_ : CommRing R') (φ : R →+* R') (a : Sp R' ⟶ U),
      IsOpenImmersion (spMap φ) ∧ p ∈ Set.range (spMap φ) ∧ spMap φ ≫ y = a ≫ u := by
  obtain ⟨q, hq⟩ := h
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := y) (g := u) p q hq.symm
  obtain ⟨i, r, hr⟩ := (pullback y u).affineOpenCover.openCover.exists_eq z
  let C := (pullback y u).affineOpenCover.X i
  let w : Sp C ⟶ pullback y u := (pullback y u).affineOpenCover.f i
  have : IsOpenImmersion w := (pullback y u).affineOpenCover.map_prop i
  obtain ⟨φ, hφ⟩ := exists_spMap (w ≫ pullback.fst y u)
  refine ⟨C, inferInstance, φ, w ≫ pullback.snd y u, ?_, ?_, ?_⟩
  · rw [← hφ]; infer_instance
  · rw [← hφ]; refine ⟨r, ?_⟩
    rw [← hz, ← hr]; rfl
  · rw [← hφ, Category.assoc, Category.assoc, pullback.condition]

set_option backward.isDefEq.respectTransparency false in
theorem exists_map_of_coord : ∀ (R σ : Type) [CommRing R] (I : Ideal (MvPolynomial σ R)) (Z Y : Scheme.{0}) (s : Z ⟶ Sp R) (sY : Y ⟶ Sp R) (M : LB Z) (N : LB Y) (th : σ → M.Sec) (ty : σ → N.Sec), ProjRep I s M th → N.IsLB → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (y : Sp R' ⟶ Y) (v : σ → R'), y ≫ sY = spMap β → SecCoord N ty y v → Ideal.span (Set.range v) = ⊤ ∧ ∀ F ∈ I, MvPolynomial.eval₂ β v F = 0) → ∃ f : Y ⟶ Z, f ≫ s = sY ∧ LBIso N (M.pull f) ∧ (∀ (R' : Type) [CommRing R'] (y : Sp R' ⟶ Y) (v : σ → R'), SecCoord N ty y v ↔ SecCoord M th (y ≫ f) v) ∧ ∀ f' : Y ⟶ Z, f' ≫ s = sY → (∀ (R' : Type) [CommRing R'] (y : Sp R' ⟶ Y) (v : σ → R'), SecCoord N ty y v → SecCoord M th (y ≫ f') v) → f' = f := by
  intro R σ _ I Z Y s sY M N th ty ⟨hM, hloc, hpts⟩ hN hY
  have uniq : ∀ (T : Type) [CommRing T] (x x' : Sp T ⟶ Z) (v : σ → T), x ≫ s = x' ≫ s → SecCoord M th x v →
      SecCoord M th x' v → x = x' := by
    intro T _ x x' v e h h'
    obtain ⟨β, hβ⟩ := exists_spMap (x ≫ s)
    obtain ⟨h₁, h₂⟩ := hloc T β x v hβ h
    exact (hpts T β v h₁ h₂).unique ⟨hβ, h⟩ ⟨e.symm.trans hβ, h'⟩
  have uni : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ Y) (v : σ → T), SecCoord N ty y v →
      Ideal.span (Set.range v) = ⊤ ∧ ∃ x : Sp T ⟶ Z, x ≫ s = y ≫ sY ∧ SecCoord M th x v := by
    intro T _ y v h
    obtain ⟨β, hβ⟩ := exists_spMap (y ≫ sY)
    obtain ⟨h₁, h₂⟩ := hY T β y v hβ h
    obtain ⟨x, hx, hx'⟩ := (hpts T β v h₁ h₂).exists
    exact ⟨h₁, x, hx.trans hβ.symm, hx'⟩
  choose A iA u v hu hp hv using (_root_.GlobalTheory.ZM.LocalCoord.secCoord_local Y N σ ty hN).2.2
  choose g hg hgv using fun p => (uni (A p) (u p) (v p) (hv p)).2
  have key : ∀ (p : Y) (T : Type) [CommRing T] (a : Sp T ⟶ Sp (A p)), (∃ w, SecCoord N ty (a ≫ u p) w) ∧
      ∀ w, SecCoord N ty (a ≫ u p) w ↔ SecCoord M th (a ≫ g p) w := by
    intro p T _ a
    obtain ⟨φ, rfl⟩ := exists_spMap a
    have h₁ := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Y N σ ty _ _ _ hN (hv p)).1 T φ
    have h₂ := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Z M σ th _ _ _ hM (hgv p)).1 T φ
    refine ⟨⟨_, h₁⟩, fun w => ⟨fun h => ?_, fun h => ?_⟩⟩
    · obtain ⟨c, hc⟩ := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Y N σ ty _ _ _ hN h₁).2.2 w h
      rw [show w = _ from funext hc]
      exact (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Z M σ th _ _ _ hM h₂).2.1 c
    · obtain ⟨c, hc⟩ := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Z M σ th _ _ _ hM h₂).2.2 w h
      rw [show w = _ from funext hc]
      exact (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Y N σ ty _ _ _ hN h₁).2.1 c
  let 𝒰 : Y.OpenCover := Scheme.Cover.mkOfCovers Y (fun p => Sp (A p)) u (fun p => ⟨p, hp p⟩) hu
  have hglue : ∀ p q : Y, pullback.fst (u p) (u q) ≫ g p = pullback.snd (u p) (u q) ≫ g q := by
    intro p q
    refine Scheme.Cover.hom_ext (pullback (u p) (u q)).affineOpenCover.openCover _ _ fun i => ?_
    let C := (pullback (u p) (u q)).affineOpenCover.X i
    let r : Sp C ⟶ pullback (u p) (u q) := (pullback (u p) (u q)).affineOpenCover.f i
    have e : (r ≫ pullback.fst _ _) ≫ u p = (r ≫ pullback.snd _ _) ≫ u q := by
      rw [Category.assoc, Category.assoc, pullback.condition]
    obtain ⟨⟨w, hw⟩, h⟩ := key p C (r ≫ pullback.fst _ _)
    have := uniq C _ _ w (by rw [Category.assoc, hg, ← Category.assoc, e, Category.assoc _ (g q), hg, Category.assoc _ (u q)])
      ((h w).1 hw) (((key q C (r ≫ pullback.snd _ _)).2 w).1 (e ▸ hw))
    rw [Category.assoc, Category.assoc] at this
    exact this
  let f : Y ⟶ Z := 𝒰.glueMorphisms g hglue
  have hf : ∀ p, u p ≫ f = g p := fun p => Scheme.Cover.ι_glueMorphisms 𝒰 _ hglue p
  have hfs : f ≫ s = sY := by
    refine Scheme.Cover.hom_ext 𝒰 _ _ fun p => ?_
    change u p ≫ _ = u p ≫ _
    rw [← Category.assoc, hf, hg]
  refine ⟨f, hfs, ?_, fun T _ y w => ⟨fun h => ?_, fun h => ?_⟩, fun f' hf' h => ?_⟩
  · refine lbIso_of_coord N (M.pull f) ty (fun i => RepBC.secPull M f (th i)) fun p =>
      ⟨A p, iA p, u p, v p, hu p, hp p, (uni _ _ _ (hv p)).1, hv p, (RepBC.secCoord_pull M th f _ _).2 ?_⟩
    rw [hf]; exact hgv p
  · refine GlobalTheory.T.isSectionCoordinateVector_of_locally_on_ring Z M σ th T _ w hM (uni T y w h).1 fun q => ?_
    have := hu (y q)
    obtain ⟨T', _, φ, a, h₁, h₂, e⟩ := exists_factor y (u (y q)) q (hp _)
    refine ⟨T', inferInstance, φ, h₁, h₂, ?_⟩
    rw [← Category.assoc, e, Category.assoc, hf, ← (key _ T' a).2, ← e]
    exact (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Y N σ ty _ _ _ hN h).1 T' φ
  · obtain ⟨β, hβ⟩ := exists_spMap ((y ≫ f) ≫ s)
    refine GlobalTheory.T.isSectionCoordinateVector_of_locally_on_ring Y N σ ty T _ w hN (hloc T β _ w hβ h).1 fun q => ?_
    have := hu (y q)
    obtain ⟨T', _, φ, a, h₁, h₂, e⟩ := exists_factor y (u (y q)) q (hp _)
    refine ⟨T', inferInstance, φ, h₁, h₂, ?_⟩
    rw [e, (key _ T' a).2, ← hf, ← Category.assoc, ← e, Category.assoc]
    exact (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Z M σ th _ _ _ hM h).1 T' φ
  · refine Scheme.Cover.hom_ext 𝒰 _ _ fun p => ?_
    change u p ≫ _ = u p ≫ _
    rw [hf]
    exact uniq _ _ _ (v p) (by rw [Category.assoc, hf', hg]) (h _ _ _ (hv p)) (hgv p)

end GlobalTheory.ZM.RepMap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSectionsFam
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

noncomputable section
namespace GlobalTheory.ZM.FamOf

theorem spMap_id (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id _

section Unit
variable {S : Scheme.{0}} (A : Over S)

def unitInv : A ⟶ Over.mk (𝟙 S) ⊗ A := lift (Over.homMk A.hom (by simp)) (𝟙 A)

theorem unitInv_snd : (unitInv A).left ≫ (snd (Over.mk (𝟙 S)) A).left = 𝟙 _ := by
  rw [← Over.comp_left, unitInv, lift_snd]; rfl

theorem to_base_ext {T : Over S} (f f' : T ⟶ Over.mk (𝟙 S)) : f = f' :=
  Over.mkIdTerminal.hom_ext f f'

theorem snd_unitInv : (snd (Over.mk (𝟙 S)) A).left ≫ (unitInv A).left = 𝟙 _ := by
  rw [← Over.comp_left]
  have : snd (Over.mk (𝟙 S)) A ≫ unitInv A = 𝟙 _ :=
    CartesianMonoidalCategory.hom_ext _ _ (to_base_ext _ _) (by simp [unitInv])
  rw [this]; rfl

theorem unitInv_fst : (unitInv A).left ≫ (fst (Over.mk (𝟙 S)) A).left = A.hom := by
  rw [← Over.comp_left, unitInv, lift_fst]; rfl

theorem pt_unitInv (z : Over.mk (𝟙 S) ⟶ A) : z.left ≫ (unitInv A).left = (lift (𝟙 (Over.mk (𝟙 S))) z).left := by
  rw [← Over.comp_left]
  congr 1
  exact CartesianMonoidalCategory.hom_ext _ _ (to_base_ext _ _) (by simp [unitInv])

theorem isPullback_unitInv : IsPullback (unitInv A).left A.hom (fst (Over.mk (𝟙 S)) A).left (𝟙 S) := by
  haveI : IsIso (unitInv A).left := ⟨_, unitInv_snd A, snd_unitInv A⟩
  exact IsPullback.of_horiz_isIso ⟨by rw [unitInv_fst, Category.comp_id]⟩

def chartPullUnit (L : LB A.left) (k : ℕ) (a : ℤ) (ha : a = k) :
    ChartPull (lbPow L k) (Out.LPow A L a (Over.mk (𝟙 S))) (unitInv A).left :=
  have le : ∀ j : PUnit → L.ι, LB.wchart L (fun _ : PUnit => 𝟙 A.left) j ≤ (unitInv A).left ⁻¹ᵁ
      LB.wchart L (fun _ : Fin 1 => (snd (Over.mk (𝟙 S)) A).left) (fun _ => j PUnit.unit) :=
    fun j y hy => Set.mem_iInter.2 fun _ => by
      have h1 : y ∈ L.U (j PUnit.unit) := Set.mem_iInter.1 hy PUnit.unit
      show ((unitInv A).left ≫ (snd (Over.mk (𝟙 S)) A).left) y ∈ L.U (j PUnit.unit)
      rw [unitInv_snd]; exact h1
  { idx := fun j _ => j PUnit.unit
    le := le
    g := fun y j j' hj hj' => by
      refine (gm_linComb L (fun _ : PUnit => 𝟙 A.left) (fun _ => (k : ℤ)) (𝟙 _) y j j' hj hj').trans
        (Eq.trans ?_ (gm_linComb L (fun _ : Fin 1 => (snd (Over.mk (𝟙 S)) A).left) (fun _ => a) (unitInv A).left y _ _
          (le j hj) (le j' hj')).symm)
      rw [Fintype.prod_unique, Fintype.prod_unique, unitInv_snd, Category.comp_id, ha] }

end Unit

theorem pt_unique {R σ : Type} [CommRing R] {I : Ideal (MvPolynomial σ R)} {Z : Scheme.{0}} {s : Z ⟶ Sp R}
    {M : LB Z} {th : σ → M.Sec} (hP : ProjRep I s M th) {T : Type} [CommRing T] {β : R →+* T} {y y' : Sp T ⟶ Z}
    {w : σ → T} (hy : y ≫ s = spMap β) (hy' : y' ≫ s = spMap β) (hc : SecCoord M th y w) (hc' : SecCoord M th y' w) :
    y = y' := by
  obtain ⟨h1, h2⟩ := hP.2.1 T β y w hy hc
  exact (hP.2.2 T β w h1 h2).unique ⟨hy, hc⟩ ⟨hy', hc'⟩

theorem fibre_of_unit {R K σ : Type} [CommRing R] [CommRing K] {x : R →+* K} {Z : Scheme.{0}} {s : Z ⟶ Sp R} {M : LB Z}
    {th : σ → M.Sec} (A : Over (Sp K)) (L : LB A.left) (k : ℕ) (a : ℤ) (ha : a = k)
    (th' : σ → (Out.LPow A L a (Over.mk (𝟙 (Sp K)))).Sec) (φ₀ : (Over.mk (𝟙 (Sp K)) ⊗ A).left ⟶ Z)
    (h1 : IsPullback φ₀ (fst (Over.mk (𝟙 (Sp K))) A).left s (spMap x))
    (h2 : LBIso (Out.LPow A L a (Over.mk (𝟙 (Sp K)))) (M.pull φ₀))
    (h3 : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ A).left) (w : σ → T),
      SecCoord _ th' y w ↔ SecCoord M th (y ≫ φ₀) w) :
    ∃ φ : A.left ⟶ Z, IsPullback φ A.hom s (spMap x) ∧
      (∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ A).left) (w : σ → T),
        SecCoord _ th' y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) A).left ≫ φ) w) ∧
      LBIso (lbPow L k) (M.pull φ) ∧
      ∀ (z : Over.mk (𝟙 (Sp K)) ⟶ A) (w : σ → K), SecCoord _ th' (lift (𝟙 (Over.mk (𝟙 (Sp K)))) z).left w →
        SecCoord M th (z.left ≫ φ) w := by
  refine ⟨(unitInv A).left ≫ φ₀, ?_, fun T _ y w => ?_, ?_, fun z w hz => ?_⟩
  · have := (isPullback_unitInv A).paste_horiz h1
    rwa [Category.id_comp] at this
  · have e : (snd (Over.mk (𝟙 (Sp K))) A).left ≫ (unitInv A).left ≫ φ₀ = φ₀ := by
      rw [← Category.assoc, snd_unitInv, Category.id_comp]
    rw [e]
    exact h3 T y w
  · exact LBIso.chartPull (chartPullUnit A L k a ha) (chartPullSame M _ _ _ (unitInv A).left fun _ => rfl) h2
  · have e : z.left ≫ (unitInv A).left ≫ φ₀ = (lift (𝟙 (Over.mk (𝟙 (Sp K)))) z).left ≫ φ₀ := by
      rw [← Category.assoc, pt_unitInv]
    rw [e]
    exact (h3 K _ w).1 hz

theorem exists_section {R σ : Type} [CommRing R] {I : Ideal (MvPolynomial σ R)} {Z : Over (Sp R)}
    {M : LB Z.left} {th : σ → M.Sec} (hP : ProjRep I Z.hom M th) (p : σ → R) {P : Set (Ideal R)} (hd : DenseP P)
    (hu : Ideal.span (Set.range p) = ⊤)
    (h : ∀ q ∈ P, ∃ (K : Type) (_ : Field K) (x : R →+* K) (y : Sp K ⟶ Z.left), RingHom.ker x = q ∧
      y ≫ Z.hom = spMap x ∧ SecCoord M th y (fun a => x (p a))) :
    ∃ sc : Out.baseOver (Sp R) ⟶ Z, SecCoord M th sc.left p := by
  have hF : ∀ F ∈ I, MvPolynomial.eval₂ (RingHom.id R) p F = 0 := by
    intro F hF
    refine hd _ fun q hq _ => ?_
    obtain ⟨K, _, x, y, hx, hy, hc⟩ := h q hq
    have h1 := (hP.2.1 K x y _ hy hc).2 F hF
    rw [← hx, RingHom.mem_ker, MvPolynomial.eval₂_comp_left, RingHom.comp_id]
    exact h1
  obtain ⟨y, ⟨hy, hc⟩, -⟩ := hP.2.2 R (RingHom.id R) p hu hF
  exact ⟨Over.homMk y (hy.trans (spMap_id R)), hc⟩

theorem exists_sections_fam : ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (R : Type) [CommRing R] [IsReduced R] (β : o →+* R) (v : Ix g (N' ^ 2) → R) (m : ℕ) (p : Ix g (N' ^ 2) → Ix g (N' ^ 2) → R) (Hh : Type) (hh : Hh → Ix g (N' ^ 2)) (Q : Polynomial ℚ) (d : ℕ) (Z : Over (Sp R)) (M : LB Z.left) (th : Ix g (N' ^ 2) → M.Sec), DenseP (objPrimes b Mat κ β v) → FibData b Mat κ β v m p hh Q d → (∀ h, Ideal.span (Set.range (p h)) = ⊤) → ProjRep (vanIdeal d (fun h i => p (hh h) i)) Z.hom M th → Flat Z.hom → (∀ (K : Type) [Field K] (x : R →+* K) (I : Ideal (MvPolynomial (Ix g (N' ^ 2)) K)) (X : Scheme.{0}) (s : X ⟶ Sp K) (M' : LB X) (th' : Ix g (N' ^ 2) → M'.Sec), (∀ F ∈ I, ∀ e, MvPolynomial.homogeneousComponent e F ∈ I) → CutBy I Q d (fun h i => x (p (hh h) i)) → ProjRep I s M' th' → ∃ φ : X ⟶ Z.left, IsPullback φ s Z.hom (spMap x) ∧ LBIso M' (M.pull φ) ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ X) (w : Ix g (N' ^ 2) → T), SecCoord M' th' y w ↔ SecCoord M th (y ≫ φ) w) → ∃ sc, Fam b Mat κ β v m M th sc := by
  intro o _ g N' J b Mat κ R _ _ β v m p Hh hh Q d Z M th hd hfib hu hZ hflat hφ
  have key : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (s : Sp K ⟶ Sp o) (t' : TObj g (N' ^ 2) J b s),
      Good b Mat κ β v x t' → ∃ φ : t'.A.left ⟶ Z.left, IsPullback φ t'.A.hom Z.hom (spMap x) ∧
      (∃ σ, t'.Emb m (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T]
        (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g (N' ^ 2) → T),
        SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧
      LBIso (lbPow t'.L (m ^ 2)) (M.pull φ) ∧
      ∀ h, ((t'.lab h ^ N').left ≫ φ) ≫ Z.hom = spMap x ∧
        SecCoord M th ((t'.lab h ^ N').left ≫ φ) (fun a => x (p h a)) := by
    intro K _ _ x s t' ht
    obtain ⟨σ, I, hE, hP, hI, hc, hs⟩ := hfib K x s t' ht
    obtain ⟨φ₀, a1, a2, a3⟩ := hφ K x I _ _ _ σ hI hc hP
    obtain ⟨φ, b1, b2, b3, b4⟩ := fibre_of_unit t'.A t'.L (m ^ 2) _ (Nat.cast_pow m 2).symm σ φ₀ a1 a2 a3
    refine ⟨φ, b1, ⟨σ, hE, b2⟩, b3, fun h => ⟨?_, b4 _ _ (hs h)⟩⟩
    rw [Category.assoc, b1.w, ← Category.assoc, Over.w]
    exact Category.id_comp _
  have hsc : ∀ h, ∃ sc : Out.baseOver (Sp R) ⟶ Z, SecCoord M th sc.left (p h) := fun h =>
    exists_section hZ (p h) hd (hu h) (by
      intro q hq
      obtain ⟨K, _, _, x, s, t', hx, ht⟩ := mem_objPrimes.1 hq
      obtain ⟨φ, -, -, -, h4⟩ := key K x s t' ht
      exact ⟨K, inferInstance, x, _, hx, h4 h⟩)
  choose sc hsc using hsc
  refine ⟨sc, ⟨_, p, hZ, hsc⟩, hflat, fun K _ _ x s t' ht => ?_⟩
  obtain ⟨φ, h1, h2, h3, h4⟩ := key K x s t' ht
  refine ⟨φ, h1, h2, h3, fun h => pt_unique hZ (h4 h).1 ?_ (h4 h).2
    ((Coord.secCoord_bc_scale_unique _ M _ th R _ _ hZ.1 (hsc h)).1 K x)⟩
  rw [Category.assoc, Over.w]
  exact Category.comp_id _

end GlobalTheory.ZM.FamOf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.KsCocLinear
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.LinDir

theorem pbT_id {Y : Scheme.{0}} {O : Y.Opens} (s : Γ(Y, O)) : pbT (𝟙 Y) s O = s := by
  unfold pbT
  rw [dite_eq_left (show O ≤ (𝟙 Y) ⁻¹ᵁ O from le_rfl)]
  have : (𝟙 Y : Y ⟶ Y).appLE O O (show O ≤ (𝟙 Y) ⁻¹ᵁ O from le_rfl) = 𝟙 _ := by
    change 𝟙 _ ≫ Y.presheaf.map (𝟙 (Opposite.op O)) = _
    simp
  rw [this]; rfl

theorem constFn_lin {K : Type} [Field K] {Y : Scheme.{0}} (q : Y ⟶ Sp K) (O : Y.Opens) (c x y : K) :
    constFn q O (c * x + y) - constFn q O c * constFn q O x - constFn q O y = constFn q O 0 := by
  simp [constFn]

theorem locDerK_comb {K : Type} [Field K] {Y X : Scheme.{0}} {R : Type} [CommRing R] {q : Y ⟶ Sp K} {p : X ⟶ Sp R}
    {m : Y ⟶ X} {D D' : R → K} {c : K} {W₀ : X.Opens} {d d' d'' : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)}
    (h : LocDerK q p m D W₀ d) (h' : LocDerK q p m D' W₀ d')
    (h'' : LocDerK q p m (fun r => c * D r + D' r) W₀ d'') :
    LocDerK q p m (fun _ => 0) W₀ (fun W f => d'' W f - constFn q (m ⁻¹ᵁ W) c * d W f - d' W f) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro W hW f f'
    rw [h.add W hW, h'.add W hW, h''.add W hW]; ring
  · intro W hW f f'
    rw [h.mul W hW, h'.mul W hW, h''.mul W hW]; ring
  · intro W W' l hW f
    rw [h.res W W' l hW, h'.res W W' l hW, h''.res W W' l hW, rsT_sub, rsT_sub, rsT_mul,
      rsT_constFn q (m.preimage_mono l)]
  · intro W hW r
    rw [h.base W hW, h'.base W hW, h''.base W hW, constFn_lin]

theorem locDerK_zero {K : Type} [Field K] {Y X : Scheme.{0}} {R : Type} [CommRing R] (q : Y ⟶ Sp K) (p : X ⟶ Sp R)
    (m : Y ⟶ X) (W₀ : X.Opens) : LocDerK q p m (fun _ => 0) W₀ (fun _ _ => 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro W hW f f'
    simp
  · intro W hW f f'
    simp
  · intro W W' l hW f
    rw [rsT_zero]
  · intro W hW r
    simp [constFn]

theorem basis_id (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (g : ℕ) (v : Fin g → (epsR K ⟶ A₀))
    (dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)) (hs : Smooth A₀.hom) (hv : IsLieBasis v)
    (hd : ∀ a, IsInvDer (v a) (dd a)) (R : Type) [CommRing R] (x₀ : R →+* K) (X : Scheme.{0}) (p : X ⟶ Sp R)
    (m : A₀.left ⟶ X) (hp : IsPullback m A₀.hom p (spMap x₀)) (W₀ : X.Opens)
    (d : ∀ W : X.Opens, Γ(X, W) → Γ(A₀.left, m ⁻¹ᵁ W)) (h : LocDerK A₀.hom p m (fun _ => 0) W₀ d) :
    ∃! c : Fin g → Γ(A₀.left, m ⁻¹ᵁ W₀), ∀ W, W ≤ W₀ → ∀ f,
      d W f = ∑ a, rsT (c a) _ * dd a (m ⁻¹ᵁ W) ((m.app W).hom f) := by
  have key : ∀ (y : A₀.left ⟶ A₀.left) (m' : A₀.left ⟶ X) (q' : A₀.left ⟶ Sp K), y ≫ m = m' → y ≫ A₀.hom = q' →
      ∀ (d : ∀ W : X.Opens, Γ(X, W) → Γ(A₀.left, m' ⁻¹ᵁ W)), LocDerK q' p m' (fun _ => 0) W₀ d →
      ∃! c : Fin g → Γ(A₀.left, m' ⁻¹ᵁ W₀), ∀ W, W ≤ W₀ → ∀ f,
        d W f = ∑ a, rsT (c a) _ * pbT y (dd a (m ⁻¹ᵁ W) ((m.app W).hom f)) _ := by
    intro y m' q' e₁ e₂ d h
    subst e₁ e₂
    exact _root_.GlobalTheory.InvFieldBasis.existsUnique_coeff K A₀ g v dd hs hv hd R x₀ X p m hp _ y W₀ d h
  have := key (𝟙 _) m A₀.hom (Category.id_comp _) (Category.id_comp _) d h
  simpa only [pbT_id] using this

theorem ksCoc_linear : ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (g : ℕ) (v : Fin g → (epsR K ⟶ A₀)) (dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)), Smooth A₀.hom → IsLieBasis v → (∀ a, IsInvDer (v a) (dd a)) → ∀ (R : Type) [CommRing R] (x₀ : R →+* K) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : A₀.left ⟶ X), IsPullback m A₀.hom p (spMap x₀) → ∀ (I : Type) (W : I → X.Opens) (D D' : R → K) (c : K) d d' d'' θ θ' θ'', KSCoc A₀.hom p m D W dd d θ → KSCoc A₀.hom p m D' W dd d' θ' → KSCoc A₀.hom p m (fun r => c * D r + D' r) W dd d'' θ'' → ∀ a, IsCob _ (fun i j => θ'' a i j - constFn A₀.hom _ c * θ a i j - θ' a i j) := by
  intro K _ A₀ _ g v dd hs hv hd R _ x₀ X p m hp I W D D' c d d' d'' θ θ' θ'' h h' h'' a
  have hb := basis_id K A₀ g v dd hs hv hd R x₀ X p m hp
  choose b hbb using fun i => (hb (W i) _ (locDerK_comb (h.der i) (h'.der i) (h''.der i))).exists
  refine ⟨fun i => b i a, fun i j => ?_⟩
  have e : m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W j = m ⁻¹ᵁ (W i ⊓ W j) := rfl
  have hu := (hb (W i ⊓ W j) _ (locDerK_zero A₀.hom p m _)).unique
    (y₁ := fun a => rsT (θ'' a i j - constFn A₀.hom _ c * θ a i j - θ' a i j -
      (rsT (b j a) (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W j) - rsT (b i a) (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W j))) _) (y₂ := fun _ => 0)
    (by
      intro O hO f
      have l : m ⁻¹ᵁ O ≤ m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W j := (m.preimage_mono hO).trans e.ge
      have h1 := h.diff i j O hO f
      have h2 := h'.diff i j O hO f
      have h3 := h''.diff i j O hO f
      have h4 := hbb i O (hO.trans inf_le_left) f
      have h5 := hbb j O (hO.trans inf_le_right) f
      have : ∀ a, rsT (rsT (θ'' a i j - constFn A₀.hom _ c * θ a i j - θ' a i j -
          (rsT (b j a) (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W j) - rsT (b i a) (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W j))) (m ⁻¹ᵁ (W i ⊓ W j)))
          (m ⁻¹ᵁ O) * dd a (m ⁻¹ᵁ O) ((m.app O).hom f) =
          rsT (θ'' a i j) (m ⁻¹ᵁ O) * dd a (m ⁻¹ᵁ O) ((m.app O).hom f)
          - constFn A₀.hom (m ⁻¹ᵁ O) c * (rsT (θ a i j) (m ⁻¹ᵁ O) * dd a (m ⁻¹ᵁ O) ((m.app O).hom f))
          - rsT (θ' a i j) (m ⁻¹ᵁ O) * dd a (m ⁻¹ᵁ O) ((m.app O).hom f)
          - (rsT (b j a) (m ⁻¹ᵁ O) * dd a (m ⁻¹ᵁ O) ((m.app O).hom f)
            - rsT (b i a) (m ⁻¹ᵁ O) * dd a (m ⁻¹ᵁ O) ((m.app O).hom f)) := by
        intro a
        rw [rsT_rsT e.ge (m.preimage_mono hO), rsT_sub, rsT_sub, rsT_sub, rsT_sub, rsT_mul,
          rsT_constFn _ l, rsT_rsT inf_le_left l, rsT_rsT inf_le_right l]
        ring
      simp only [this, Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [← h1, ← h2, ← h3, ← h4, ← h5]
      ring)
    (by
      intro O hO f
      simp only [rsT_zero, zero_mul, Finset.sum_const_zero])
  have h0 := congrArg (fun s => rsT s (m ⁻¹ᵁ W i ⊓ m ⁻¹ᵁ W j)) (congrFun hu a)
  simp only [] at h0
  rw [rsT_rsT e.ge e.le, rsT_self, rsT_zero] at h0
  exact sub_eq_zero.1 h0

end GlobalTheory.KS.LinDir
end
end

