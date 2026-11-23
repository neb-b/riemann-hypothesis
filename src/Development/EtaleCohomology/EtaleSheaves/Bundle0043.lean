module

public import Development.EtaleCohomology.EtaleSheaves.KernelLocalization.RangeOfBd
public import Development.EtaleCohomology.EtaleSheaves.Bundle0042
public import Development.EtaleCohomology.EtaleSheaves.Bundle0022
public import Development.EtaleCohomology.EtaleSheaves.Bundle0024
public import Development.EtaleCohomology.EtaleSheaves.Bundle0023
public import Development.EtaleCohomology.EtaleSheaves.Bundle0031
public import Development.EtaleCohomology.EtaleSheaves.Bundle0003
public import Development.EtaleCohomology.EtaleSheaves.Bundle0037
public import Development.EtaleCohomology.EtaleSheaves.Bundle0035
public import Development.EtaleCohomology.EtaleSheaves.Bundle0036
public import Development.EtaleCohomology.TateTwists.Bundle0020
public import Development.EtaleCohomology.EtaleSheaves.LocalDescent.DescLocOf

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.ArchimedeanRelations
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.LeafGhostCut LateralTheory.E.DescIntPf LateralTheory.E.KernelLocalization
namespace LateralTheory.E.RelativeTruncationSingleDegree
theorem sub_of (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (f : U ⟶ E) (n : ℤ) (h : RelZS R F n f)
    (hf : ∀ z : Hrel R f F n, pull R f F n (fgt R f F n z) = 0) : Subsingleton (Hrel R f F n) := by
  refine subsingleton_of_forall_eq 0 fun z => ?_
  have h1 : fgt R f F n z = 0 := (injective_iff_map_eq_zero _).1 h.2 _ (hf z)
  exact (injective_iff_map_eq_zero _).1 (LateralTheory.E.TruncationKernel.fgt_injective_of_pull_surjective R F f n h.1) z h1
theorem pull_fgt (R : Type) [CommRing R] (F : Shv R) {U E : Spc} (f : U ⟶ E) (n : ℤ) (z : Hrel R f F n) :
    pull R f F n (fgt R f F n z) = 0 := by
  obtain ⟨c, rfl⟩ := z.mk_surjective
  exact LateralTheory.E.LeafConeExactPf.pre_inr_eq_zero _ _ c
end LateralTheory.E.RelativeTruncationSingleDegree
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.AugBij
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.TateTwistZeroAugmentationBijective

def Aug : Prop := ∀ q : ℕ, ∃ φ : ∀ T : Scheme.{0}, Sec (tw q 0) T →+ LocallyConstant T (ZMod q),
  (∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec (tw q 0) U), φ V (Sec.res g x) = (φ U x).comap g.base.hom) ∧
  ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), φ U (twGen 0 ζ) = 1

def AugBij : Prop := ∀ (q : ℕ) (φ : ∀ T : Scheme.{0}, Sec (tw q 0) T →+ LocallyConstant T (ZMod q)),
  (∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec (tw q 0) U), φ V (Sec.res g x) = (φ U x).comap g.base.hom) →
  (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), φ U (twGen 0 ζ) = 1) →
  ∀ T : Scheme.{0}, IsUnit (q : Γ(T, ⊤)) → Function.Bijective (φ T)

theorem Tw0_of (hA : Aug) (hB : AugBij) : LateralTheory.E.LCIsoPf.Tw0 := by
  intro q
  obtain ⟨φ, hnat, hgen⟩ := hA q
  have hb := hB q φ hnat hgen
  refine ⟨fun T hT => (AddEquiv.ofBijective (φ T) (hb T hT)).symm, ?_⟩
  intro V U g hV hU a
  apply (hb V hV).1
  have h1 : ∀ (T : Scheme.{0}) (hT : IsUnit (q : Γ(T, ⊤))) (b : LocallyConstant T (ZMod q)),
      φ T ((AddEquiv.ofBijective (φ T) (hb T hT)).symm b) = b := fun T hT b =>
    (AddEquiv.ofBijective (φ T) (hb T hT)).apply_symm_apply b
  rw [hnat, h1 U hU, h1 V hV]

end LateralTheory.E.TateTwistZeroAugmentationBijective
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.CechYoneda
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.CechSigma_xy1Pf_Yo
open LateralTheory.E.CechSigmaProof LateralTheory.E.CechSigma_xy1Pf_Lev

def eW {A B : Scheme.{0}} (p : A ⟶ B) (n : ℕ) :
    yoneda.obj (widePullback B (fun _ : Fin (n + 1) => A) (fun _ => p)) ≅
      widePullback (yoneda.obj B) (fun _ : Fin (n + 1) => yoneda.obj A) (fun _ => yoneda.map p) :=
  preservesLimitIso yoneda (WidePullbackShape.wideCospan B (fun _ : Fin (n + 1) => A) (fun _ => p)) ≪≫
    HasLimit.isoOfNatIso (WidePullbackShape.diagramIsoWideCospan _)

theorem eW_π {A B : Scheme.{0}} (p : A ⟶ B) (n : ℕ) (i : Fin (n + 1)) :
    (eW p n).hom ≫ WidePullback.π _ i = yoneda.map (WidePullback.π _ i) := by
  simp only [eW, Iso.trans_hom, WidePullback.π]
  erw [Category.assoc, HasLimit.isoOfNatIso_hom_π, ← Category.assoc, preservesLimitIso_hom_π]
  simp only [WidePullbackShape.diagramIsoWideCospan, NatIso.ofComponents_hom_app]
  exact Category.comp_id _

theorem eW_base {A B : Scheme.{0}} (p : A ⟶ B) (n : ℕ) :
    (eW p n).hom ≫ WidePullback.base _ = yoneda.map (WidePullback.base _) := by
  simp only [eW, Iso.trans_hom, WidePullback.base]
  erw [Category.assoc, HasLimit.isoOfNatIso_hom_π, ← Category.assoc, preservesLimitIso_hom_π]
  simp only [WidePullbackShape.diagramIsoWideCospan, NatIso.ofComponents_hom_app]
  exact Category.comp_id _

theorem cechYoneda : CechYoneda := by
  intro A B C D p q s n
  refine ⟨(Arrow.isoMk (eW p n) (eW q n) ?_).symm⟩
  apply WidePullback.hom_ext
  · intro i
    simp only [Arrow.mk_hom, Category.assoc]
    erw [Arrow.mapCechNerve_app, WidePullback.lift_π]
    erw [← Category.assoc, eW_π, Category.assoc, eW_π]
    change yoneda.map _ ≫ yoneda.map s.left = yoneda.map _ ≫ yoneda.map _
    simp only [wpMap]
    erw [← Functor.map_comp, ← Functor.map_comp, WidePullback.lift_π]
  · simp only [Arrow.mk_hom, Category.assoc]
    erw [Arrow.mapCechNerve_app, WidePullback.lift_base]
    erw [← Category.assoc, eW_base, Category.assoc, eW_base]
    change yoneda.map _ ≫ yoneda.map s.right = yoneda.map _ ≫ yoneda.map _
    simp only [wpMap]
    erw [← Functor.map_comp, ← Functor.map_comp, WidePullback.lift_base]

end LateralTheory.E.CechSigma_xy1Pf_Yo
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ChasePf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ContPf LateralTheory.E.StepSPf

namespace LateralTheory.E.ChasePf

theorem pp_comp {R : Type} [CommRing R] {F : Shv R} {n : ℤ} {A B C : Scheme.{0}} {f : A ⟶ B} {g : B ⟶ C}
    {h : A ⟶ C} (hfg : f ≫ g = h) (y : H R (sch.obj C) F n) :
    pull R (sch.map f) F n (pull R (sch.map g) F n y) = pull R (sch.map h) F n y := by
  rw [← pull_comp, ← Functor.map_comp, hfg]

theorem pp_id {R : Type} [CommRing R] {F : Shv R} {n : ℤ} {A : Scheme.{0}} {f : A ⟶ A} (hf : f = 𝟙 A)
    (y : H R (sch.obj A) F n) : pull R (sch.map f) F n y = y := by
  rw [hf, CategoryTheory.Functor.map_id, pull_id]

def psi {Z : Scheme.{0}} (A B C : Z.Opens) (hC : C = A ⊓ B) : pullback A.ι B.ι ≅ C.toScheme :=
  IsOpenImmersion.isoOfRangeEq (pullback.fst A.ι B.ι ≫ A.ι) C.ι (by
    rw [IsOpenImmersion.range_pullback_to_base_of_left, Scheme.Opens.range_ι, Scheme.Opens.range_ι,
      Scheme.Opens.range_ι, hC]; rfl)

@[reassoc (attr := simp)]
theorem psi_hom_fst {Z : Scheme.{0}} (A B C : Z.Opens) (hC : C = A ⊓ B) :
    (psi A B C hC).hom ≫ C.ι = pullback.fst A.ι B.ι ≫ A.ι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

theorem psi_inv_fst {Z : Scheme.{0}} (A B C : Z.Opens) (hC : C = A ⊓ B) :
    (psi A B C hC).inv ≫ pullback.fst A.ι B.ι ≫ A.ι = C.ι :=
  IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

@[reassoc (attr := simp)]
theorem psi_inv_snd {Z : Scheme.{0}} (A B C : Z.Opens) (hC : C = A ⊓ B) :
    (psi A B C hC).inv ≫ pullback.snd A.ι B.ι ≫ B.ι = C.ι := by
  rw [← pullback.condition, psi_inv_fst]

theorem cover2 {Y Y' Z : Scheme.{0}} (φ : Y ⟶ Y') (ψ : Y' ⟶ Z) (A B : Z.Opens) (hAB : A ⊔ B = ⊤) :
    Set.range (φ ⁻¹ᵁ (ψ ⁻¹ᵁ A)).ι ∪ Set.range (φ ⁻¹ᵁ (ψ ⁻¹ᵁ B)).ι = Set.univ := by
  rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
  refine Set.eq_univ_of_forall fun y => ?_
  have : ψ.base (φ.base y) ∈ A ⊔ B := by rw [hAB]; trivial
  simpa using this

theorem inf2 {Y Y' Z : Scheme.{0}} (φ : Y ⟶ Y') (ψ : Y' ⟶ Z) (A B : Z.Opens) :
    φ ⁻¹ᵁ (ψ ⁻¹ᵁ (A ⊓ B)) = φ ⁻¹ᵁ (ψ ⁻¹ᵁ A) ⊓ φ ⁻¹ᵁ (ψ ⁻¹ᵁ B) := by
  ext; simp

section
variable {J : Type} [SmallCategory J] (D : J ⥤ Scheme.{0}) (c : Cone D) (j0 : J) (W : (D.obj j0).Opens)

abbrev rL {k : J} (f : k ⟶ j0) : (c.π.app j0 ⁻¹ᵁ W).toScheme ⟶ (D.map f ⁻¹ᵁ W).toScheme :=
  (c.π.app k).resLE (D.map f ⁻¹ᵁ W) (c.π.app j0 ⁻¹ᵁ W) (by rw [← Scheme.Hom.comp_preimage, c.w])

abbrev rT {l k : J} (g : l ⟶ k) (f : k ⟶ j0) (f' : l ⟶ j0) (h : g ≫ f = f') :
    (D.map f' ⁻¹ᵁ W).toScheme ⟶ (D.map f ⁻¹ᵁ W).toScheme :=
  (D.map g).resLE (D.map f ⁻¹ᵁ W) (D.map f' ⁻¹ᵁ W) (by rw [← Scheme.Hom.comp_preimage, ← D.map_comp, h])

theorem rL_rT {l k : J} (g : l ⟶ k) (f : k ⟶ j0) (f' : l ⟶ j0) (h : g ≫ f = f') :
    rL D c j0 W f' ≫ rT D j0 W g f f' h = rL D c j0 W f := by
  rw [← cancel_mono (Scheme.Opens.ι _)]
  simp [rL, rT, Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι_assoc]

end

theorem pp3' {R : Type} [CommRing R] {F : Shv R} {n : ℤ} {A B C E B' C' : Scheme.{0}} {f : A ⟶ B} {g : B ⟶ C}
    {k : C ⟶ E} {f' : A ⟶ B'} {g' : B' ⟶ C'} {k' : C' ⟶ E} (h : f ≫ g ≫ k = f' ≫ g' ≫ k') (y : H R (sch.obj E) F n) :
    pull R (sch.map f) F n (pull R (sch.map g) F n (pull R (sch.map k) F n y)) =
      pull R (sch.map f') F n (pull R (sch.map g') F n (pull R (sch.map k') F n y)) := by
  simp only [← pull_comp, ← Functor.map_comp]; rw [h]

theorem pp3 {R : Type} [CommRing R] {F : Shv R} {n : ℤ} {A B C E : Scheme.{0}} {f : A ⟶ B} {g : B ⟶ C}
    {k : C ⟶ E} {l : A ⟶ E} (h : f ≫ g ≫ k = l) (y : H R (sch.obj E) F n) :
    pull R (sch.map f) F n (pull R (sch.map g) F n (pull R (sch.map k) F n y)) = pull R (sch.map l) F n y := by
  simp only [← pull_comp, ← Functor.map_comp]; rw [h]

theorem pp2' {R : Type} [CommRing R] {F : Shv R} {n : ℤ} {A B E B' : Scheme.{0}} {f : A ⟶ B} {g : B ⟶ E}
    {f' : A ⟶ B'} {g' : B' ⟶ E} (h : f ≫ g = f' ≫ g') (y : H R (sch.obj E) F n) :
    pull R (sch.map f) F n (pull R (sch.map g) F n y) = pull R (sch.map f') F n (pull R (sch.map g') F n y) := by
  simp only [← pull_comp, ← Functor.map_comp]; rw [h]

theorem pp32 {R : Type} [CommRing R] {F : Shv R} {n : ℤ} {A B C E B' : Scheme.{0}} {f : A ⟶ B} {g : B ⟶ C}
    {k : C ⟶ E} {f' : A ⟶ B'} {g' : B' ⟶ E} (h : f ≫ g ≫ k = f' ≫ g') (y : H R (sch.obj E) F n) :
    pull R (sch.map f) F n (pull R (sch.map g) F n (pull R (sch.map k) F n y)) =
      pull R (sch.map f') F n (pull R (sch.map g') F n y) := by
  simp only [← pull_comp, ← Functor.map_comp]; rw [h]

theorem pp24 {R : Type} [CommRing R] {F : Shv R} {n : ℤ} {A B E B' C' E' : Scheme.{0}} {f : A ⟶ B} {g : B ⟶ E}
    {f' : A ⟶ B'} {g' : B' ⟶ C'} {k' : C' ⟶ E'} {l' : E' ⟶ E} (h : f ≫ g = f' ≫ g' ≫ k' ≫ l')
    (y : H R (sch.obj E) F n) :
    pull R (sch.map f) F n (pull R (sch.map g) F n y) = pull R (sch.map f') F n (pull R (sch.map g') F n
      (pull R (sch.map k') F n (pull R (sch.map l') F n y))) := by
  simp only [← pull_comp, ← Functor.map_comp]; rw [h]

theorem Chase_of : DiagramChase₂ := by
  intro hH hmv q J _ _ D c hc ha hcs hqs hu j0 X e U V hUV pU pV pW n i
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, n = m + 1 := ⟨n - 1, by ring⟩
  intro x
  obtain ⟨δ, hex, hnat⟩ := hmv hH (ZMod q) (tw q i)
  have cov : ∀ {Y : Scheme.{0}} (φ : Y ⟶ D.obj j0),
      Set.range (φ ⁻¹ᵁ (e.hom ⁻¹ᵁ U)).ι ∪ Set.range (φ ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι = Set.univ :=
    fun φ => cover2 φ e.hom U V hUV
  have hinf : ∀ {Y : Scheme.{0}} (φ : Y ⟶ D.obj j0),
      φ ⁻¹ᵁ (e.hom ⁻¹ᵁ (U ⊓ V)) = φ ⁻¹ᵁ (e.hom ⁻¹ᵁ U) ⊓ φ ⁻¹ᵁ (e.hom ⁻¹ᵁ V) :=
    fun φ => inf2 φ e.hom U V

  obtain ⟨k1, f1, a1, ha1⟩ := (pU (m + 1) i).1 (pull _ (sch.map (c.π.app j0 ⁻¹ᵁ (e.hom ⁻¹ᵁ U)).ι) _ _ x)
  obtain ⟨k2, f2, b1, hb1⟩ := (pV (m + 1) i).1 (pull _ (sch.map (c.π.app j0 ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι) _ _ x)
  obtain ⟨k3, g1, g2, hg⟩ := IsCofiltered.cospan f1 f2

  obtain ⟨a2, ha2d⟩ : ∃ a2, a2 = pull _ (sch.map (rT D j0 (e.hom ⁻¹ᵁ U) g1 f1 (g1 ≫ f1) rfl)) (tw q i) (m + 1) a1 :=
    ⟨_, rfl⟩
  obtain ⟨b2, hb2d⟩ : ∃ b2, b2 = pull _ (sch.map (rT D j0 (e.hom ⁻¹ᵁ V) g2 f2 (g1 ≫ f1) hg.symm)) (tw q i) (m + 1) b1 :=
    ⟨_, rfl⟩
  have ha2 : pull _ (sch.map (rL D c j0 (e.hom ⁻¹ᵁ U) (g1 ≫ f1))) (tw q i) (m + 1) a2 =
      pull _ (sch.map (c.π.app j0 ⁻¹ᵁ (e.hom ⁻¹ᵁ U)).ι) _ _ x := by
    rw [ha2d, pp_comp (rL_rT D c j0 _ g1 f1 _ rfl)]; exact ha1
  have hb2 : pull _ (sch.map (rL D c j0 (e.hom ⁻¹ᵁ V) (g1 ≫ f1))) (tw q i) (m + 1) b2 =
      pull _ (sch.map (c.π.app j0 ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι) _ _ x := by
    rw [hb2d, pp_comp (rL_rT D c j0 _ g2 f2 _ hg.symm)]; exact hb1

  obtain ⟨dC, hdC⟩ : ∃ dC, dC = pull _ (sch.map (psi _ _ _ (hinf (D.map (g1 ≫ f1)))).inv) (tw q i) (m + 1)
      (pull _ (sch.map (pullback.fst _ _)) _ _ a2 - pull _ (sch.map (pullback.snd _ _)) _ _ b2) := ⟨_, rfl⟩
  have hd : pull _ (sch.map (rL D c j0 (e.hom ⁻¹ᵁ (U ⊓ V)) (g1 ≫ f1))) (tw q i) (m + 1) dC = 0 := by
    rw [hdC, map_sub, map_sub,
      pp3' (f' := (psi _ _ _ (hinf (c.π.app j0))).inv) (g' := pullback.fst _ _) (k' := rL D c j0 (e.hom ⁻¹ᵁ U) (g1 ≫ f1)) (by
        apply (cancel_mono (Scheme.Opens.ι _)).1
        simp [Category.assoc, rL, rT, Scheme.Hom.resLE_comp_ι_assoc, psi_inv_fst, (reassoc_of% psi_inv_fst), psi_inv_snd, pullback.condition_assoc, Cone.w]
        all_goals simp [← Category.assoc, psi_inv_fst, pullback.condition]),
      pp3' (f' := (psi _ _ _ (hinf (c.π.app j0))).inv) (g' := pullback.snd _ _) (k' := rL D c j0 (e.hom ⁻¹ᵁ V) (g1 ≫ f1)) (by
        apply (cancel_mono (Scheme.Opens.ι _)).1
        simp [Category.assoc, rL, rT, Scheme.Hom.resLE_comp_ι_assoc, psi_inv_fst, (reassoc_of% psi_inv_fst), psi_inv_snd, pullback.condition_assoc, Cone.w]
        all_goals simp [← Category.assoc, psi_inv_fst, pullback.condition]),
      ha2, hb2, pp3 (psi_inv_fst _ _ _ _), pp3 (psi_inv_snd _ _ _ _), sub_self]
  obtain ⟨k4, g4, hk4⟩ := (pW (m + 1) i).2 k3 (g1 ≫ f1) dC hd

  obtain ⟨a3, ha3d⟩ : ∃ a3, a3 = pull _ (sch.map (rT D j0 (e.hom ⁻¹ᵁ U) g4 (g1 ≫ f1) (g4 ≫ g1 ≫ f1) rfl))
      (tw q i) (m + 1) a2 := ⟨_, rfl⟩
  obtain ⟨b3, hb3d⟩ : ∃ b3, b3 = pull _ (sch.map (rT D j0 (e.hom ⁻¹ᵁ V) g4 (g1 ≫ f1) (g4 ≫ g1 ≫ f1) rfl))
      (tw q i) (m + 1) b2 := ⟨_, rfl⟩
  have hab : pull _ (sch.map (pullback.fst _ _)) _ _ a3 = pull _ (sch.map (pullback.snd (D.map (g4 ≫ g1 ≫ f1) ⁻¹ᵁ
      (e.hom ⁻¹ᵁ U)).ι (D.map (g4 ≫ g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι)) (tw q i) (m + 1) b3 := by
    have key : pull _ (sch.map (pullback.fst _ _)) _ _ a3 - pull _ (sch.map (pullback.snd (D.map (g4 ≫ g1 ≫ f1) ⁻¹ᵁ
        (e.hom ⁻¹ᵁ U)).ι (D.map (g4 ≫ g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι)) (tw q i) (m + 1) b3 =
        pull _ (sch.map (psi _ _ _ (hinf (D.map (g4 ≫ g1 ≫ f1)))).hom) _ _
          (pull _ (sch.map (rT D j0 (e.hom ⁻¹ᵁ (U ⊓ V)) g4 (g1 ≫ f1) (g4 ≫ g1 ≫ f1) rfl)) _ _ dC) := by
      have E3 : (pullback.fst (D.map (g4 ≫ g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ U)).ι (D.map (g4 ≫ g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι ≫ rT D j0 (e.hom ⁻¹ᵁ U) g4 (g1 ≫ f1) (g4 ≫ g1 ≫ f1) rfl =
        (psi _ _ _ (hinf (D.map (g4 ≫ g1 ≫ f1)))).hom ≫ rT D j0 (e.hom ⁻¹ᵁ (U ⊓ V)) g4 (g1 ≫ f1) (g4 ≫ g1 ≫ f1) rfl ≫
          (psi _ _ _ (hinf (D.map (g1 ≫ f1)))).inv ≫ pullback.fst (D.map (g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ U)).ι (D.map (g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι) := by
        apply (cancel_mono (Scheme.Opens.ι _)).1
        simp [Category.assoc, rL, rT, Scheme.Hom.resLE_comp_ι_assoc, psi_inv_fst, (reassoc_of% psi_inv_fst), psi_inv_snd, pullback.condition_assoc, Cone.w]
      have E4 : (pullback.snd (D.map (g4 ≫ g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ U)).ι (D.map (g4 ≫ g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι ≫ rT D j0 (e.hom ⁻¹ᵁ V) g4 (g1 ≫ f1) (g4 ≫ g1 ≫ f1) rfl =
        (psi _ _ _ (hinf (D.map (g4 ≫ g1 ≫ f1)))).hom ≫ rT D j0 (e.hom ⁻¹ᵁ (U ⊓ V)) g4 (g1 ≫ f1) (g4 ≫ g1 ≫ f1) rfl ≫
          (psi _ _ _ (hinf (D.map (g1 ≫ f1)))).inv ≫ pullback.snd (D.map (g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ U)).ι (D.map (g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι) := by
        apply (cancel_mono (Scheme.Opens.ι _)).1
        simp [Category.assoc, rL, rT, Scheme.Hom.resLE_comp_ι_assoc, psi_inv_fst, (reassoc_of% psi_inv_fst), psi_inv_snd, pullback.condition_assoc, Cone.w]
      rw [hdC, ha3d, hb3d]; simp only [map_sub]; rw [pp24 E3, pp24 E4]
    rw [hk4, map_zero] at key
    exact sub_eq_zero.mp key
  obtain ⟨xk, hxa, hxb⟩ := (hex (D.map (g4 ≫ g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ U)).ι (D.map (g4 ≫ g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι
    (cov _) (m + 1)).1 a3 b3 hab

  obtain ⟨x', hx'⟩ : ∃ x' : Ht q (sch.obj c.pt) (m + 1) i, x' = x -
      (show Ht q (sch.obj c.pt) (m + 1) i from pull _ (sch.map (c.π.app k4)) (tw q i) (m + 1) xk) := ⟨_, rfl⟩
  have h1 : pull _ (sch.map (c.π.app j0 ⁻¹ᵁ (e.hom ⁻¹ᵁ U)).ι) _ _ x' = 0 := by
    rw [hx', map_sub, pp2' (f' := rL D c j0 _ (g4 ≫ g1 ≫ f1)) (g' := (D.map (g4 ≫ g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ U)).ι) (by simp [rL]), hxa, ha3d,
      pp_comp (rL_rT D c j0 _ g4 (g1 ≫ f1) _ rfl), ha2, sub_self]
  have h2 : pull _ (sch.map (c.π.app j0 ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι) _ _ x' = 0 := by
    rw [hx', map_sub, pp2' (f' := rL D c j0 _ (g4 ≫ g1 ≫ f1)) (g' := (D.map (g4 ≫ g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι) (by simp [rL]), hxb, hb3d,
      pp_comp (rL_rT D c j0 _ g4 (g1 ≫ f1) _ rfl), hb2, sub_self]
  obtain ⟨w, hw⟩ := ((hex (c.π.app j0 ⁻¹ᵁ (e.hom ⁻¹ᵁ U)).ι (c.π.app j0 ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι (cov _) m).2.2 x').mp
    ⟨h1, h2⟩

  obtain ⟨k5, f5, w5, hw5⟩ := (pW m i).1 (pull _ (sch.map (psi _ _ _ (hinf (c.π.app j0))).inv) _ _ w)
  obtain ⟨k6, h4, h5, hh⟩ := IsCofiltered.cospan (g4 ≫ g1 ≫ f1) f5
  obtain ⟨w6, hw6⟩ : ∃ w6, w6 = pull _ (sch.map (psi _ _ _ (hinf (D.map (h4 ≫ g4 ≫ g1 ≫ f1)))).hom) (tw q i) m
      (pull _ (sch.map (rT D j0 (e.hom ⁻¹ᵁ (U ⊓ V)) h5 f5 (h4 ≫ g4 ≫ g1 ≫ f1) hh.symm)) _ _ w5) := ⟨_, rfl⟩
  have hn := hnat (c.π.app j0 ⁻¹ᵁ (e.hom ⁻¹ᵁ U)).ι (c.π.app j0 ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι
    (D.map (h4 ≫ g4 ≫ g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ U)).ι (D.map (h4 ≫ g4 ≫ g1 ≫ f1) ⁻¹ᵁ (e.hom ⁻¹ᵁ V)).ι (cov _) (cov _)
    (rL D c j0 _ (h4 ≫ g4 ≫ g1 ≫ f1)) (rL D c j0 _ (h4 ≫ g4 ≫ g1 ≫ f1)) (c.π.app k6)
    (by simp [rL]) (by simp [rL]) m w6
  have hpb : pull _ (sch.map (pullback.map _ _ _ _ (rL D c j0 (e.hom ⁻¹ᵁ U) (h4 ≫ g4 ≫ g1 ≫ f1))
      (rL D c j0 (e.hom ⁻¹ᵁ V) (h4 ≫ g4 ≫ g1 ≫ f1)) (c.π.app k6) (by simp [rL]) (by simp [rL]))) (tw q i) m w6 = w := by
    rw [hw6, pp32 (f' := (psi _ _ _ (hinf (c.π.app j0))).hom) (g' := rL D c j0 _ f5) (by
      rw [← cancel_mono (Scheme.Opens.ι _)]
      simp only [Category.assoc, rT, rL, Scheme.Hom.resLE_comp_ι, psi_hom_fst_assoc]
      simp [Scheme.Hom.resLE_comp_ι_assoc, Cone.w]), hw5,
      pp_comp (Iso.hom_inv_id _), pp_id rfl]
  refine ⟨k6, δ _ _ m w6 + pull _ (sch.map (D.map h4)) _ _ xk, ?_⟩
  rw [map_add (f := _), ← hn, hpb, hw, pp_comp (c.w h4), hx', sub_add_cancel]

end LateralTheory.E.ChasePf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ChernClassCocycleFirst
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.ChernCocycleEdgeCoboundary


open LateralTheory.E.ChernClassRootLocalization in
theorem sec_dd (q : ℕ) {V : Scheme.{0}} (y : Sec ((res _ (tw q 1)).X 0) V) :
    Sec.map ((res _ (tw q 1)).d 1 2) (Sec.map ((res _ (tw q 1)).d 0 1) y) = 0 := by
  have h : (res _ (tw q 1)).d 0 1 ≫ (res _ (tw q 1)).d 1 2 = 0 := HomologicalComplex.d_comp_d _ _ _ _
  change ((((res _ (tw q 1)).d 0 1 ≫ (res _ (tw q 1)).d 1 2).hom.app (op V)).hom y) = 0
  rw [h]
  rfl

theorem etale_kummer_chern_cochain_coboundary_vanishes_on_edges_of_local_roots (hr : LateralTheory.E.ChernClassRootLocalization.LeafRootLoc) : LateralTheory.E.ChernClassExistence.EtaleKummerChernCochainCoboundaryVanishesOnEdges := by
  intro q _ E L hi α hα U x
  have key : ∀ (V : Scheme.{0}) (x' : Sx E 1 V), ev (δ 2 3 α) 1 2 (by simp) V x' =
      Sec.map ((res _ (tw q 1)).d 1 2) (ev α 1 1 (by simp) V x') := by
    intro V x'
    have := (LateralTheory.E.ChernClassEvaluation.evDelta_pf (ZMod q) (I := res _ (tw q 1)) (n := 2) (m := 3) (by norm_num) α V).2
      0 1 2 (by simp) (by simp) x'
    rw [this]
    simp [hα.1]
  apply LateralTheory.E.ChernClassRootLocalization.sec_sep
  refine LateralTheory.EtaleFoundations.FirstChernUniqueness.loc_imp (LateralTheory.EtaleFoundations.FirstChernUniqueness.root_line hr q L hi U x) fun V g hv => ?_
  obtain ⟨v, hv⟩ := hv
  rw [← LateralTheory.E.ChernClassRootLocalization.ev_res, key, hα.2.1 V _ v hv, sec_dd]
  exact (map_zero ((res _ (tw q 1)).X 2 |>.obj.map g.op).hom).symm

end LateralTheory.E.ChernCocycleEdgeCoboundary
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ChernClassCocycleSecond
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.ChernCocycleFaceFormulas

lemma δ0_eq : (SimplexCategory.δ (0 : Fin 3) : SimplexCategory.mk 1 ⟶ SimplexCategory.mk 2) =
    SimplexCategory.subinterval 1 1 (by omega) := by
  ext i; fin_cases i <;> rfl

lemma δ2_eq : (SimplexCategory.δ (2 : Fin 3) : SimplexCategory.mk 1 ⟶ SimplexCategory.mk 2) =
    SimplexCategory.subinterval 0 1 (by omega) := by
  ext i; fin_cases i <;> rfl

lemma face0 {E : Spc} {U : Scheme.{0}} (x : Sx E 2 U) : x.face 0 = x.sub 1 1 (by omega) := by
  unfold Sx.face Sx.sub SimplicialObject.δ; rw [δ0_eq]

lemma face2 {E : Spc} {U : Scheme.{0}} (x : Sx E 2 U) : x.face 2 = x.sub 0 1 (by omega) := by
  unfold Sx.face Sx.sub SimplicialObject.δ; rw [δ2_eq]

lemma glMat_face1 {U : Scheme.{0}} (y : Sx (ofCat (glCat 1)) 2 U) :
    glMat (y.face 1) = glMat (y.sub 1 1 (by omega)) * glMat (y.sub 0 1 (by omega)) := by
  let z : ComposableArrows (SingleObj (GL (Fin 1) Γ(U, ⊤))) 2 := y
  have h1 : glMat (y.face 1) = z.map' 0 2 := rfl
  have h2 : glMat (y.sub 1 1 (by omega)) = z.map' 1 2 := rfl
  have h3 : glMat (y.sub 0 1 (by omega)) = z.map' 0 1 := rfl
  rw [h1, h2, h3, ← SingleObj.comp_as_mul, ← z.map'_comp 0 1 2]

lemma L_map {E : Spc} (L : E ⟶ ofCat (glCat 1)) {U : Scheme.{0}} {m n : ℕ}
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) (x : Sx E n U) :
    (L.app (op (SimplexCategory.mk m))).app (op U) ((E.map θ.op).app (op U) x) =
      ((ofCat (glCat 1)).map θ.op).app (op U) ((L.app (op (SimplexCategory.mk n))).app (op U) x) :=
  congrArg (fun φ => φ.app (op U) x) (L.naturality θ.op)

lemma lineUnit_face1 {E : Spc} (L : E ⟶ ofCat (glCat 1)) {U : Scheme.{0}} (x : Sx E 2 U) :
    lineUnit L (x.face 1) = lineUnit L (x.sub 0 1 (by omega)) * lineUnit L (x.sub 1 1 (by omega)) := by
  have key := glMat_face1 ((L.app (op (SimplexCategory.mk 2))).app (op U) x)
  unfold lineUnit
  unfold Sx.face Sx.sub SimplicialObject.δ at *
  rw [L_map, L_map, L_map, key, map_mul, mul_comm]

open LateralTheory.E.ChernClassRootLocalization in
lemma etale_kummer_chern_cochain_coboundary_triangle_eq_zero_of_qth_roots (q : ℕ) {E : Spc} (L : E ⟶ ofCat (glCat 1))
    (α : Cochain ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2) (hα : LateralTheory.EtaleFoundations.IsEtaleKummerChernClassCochainOfLineBundle q L α)
    (V : Scheme.{0}) (y : Sx E 2 V) (v w : (Γ(V, ⊤))ˣ) (hv : v ^ q = lineUnit L (y.sub 0 1 (by omega)))
    (hw : w ^ q = lineUnit L (y.sub 1 1 (by omega))) : ev (δ 2 3 α) 2 1 (by simp) V y = 0 := by
  have hd := (LateralTheory.E.ChernClassEvaluation.evDelta_pf (ZMod q) (show (2:ℤ) + 1 = 3 by norm_num) α V).2 1 0 1
    (by norm_num) (by norm_num) y
  have e0 : ev α 1 1 (by omega) V (y.face 0) = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q V w) :=
    hα.2.1 V _ w (by rw [face0]; exact hw)
  have e2 : ev α 1 1 (by omega) V (y.face 2) = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q V v) :=
    hα.2.1 V _ v (by rw [face2]; exact hv)
  have e1 : ev α 1 1 (by omega) V (y.face 1) = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q V (v * w)) :=
    hα.2.1 V _ (v * w) (by rw [lineUnit_face1, mul_pow, hv, hw])
  have e3 := hα.2.2 V y v w hv hw
  refine hd.trans ?_
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, add_zero]
  have e3' : ev α (1 + 1) 0 (by omega) V y = kumT q V v + kumT q V w - kumT q V (v * w) := e3
  have hn : (3 : ℤ).negOnePow = -1 := by rw [Int.negOnePow_odd]; decide
  rw [e3', e0, e1, e2, hn]
  simp only [Sec.map, map_add (f := _), map_sub]
  simp
  abel

open LateralTheory.E.ChernClassRootLocalization in
theorem etale_kummer_chern_cochain_coboundary_vanishes_on_triangles_of_local_r (hr : LateralTheory.E.ChernClassRootLocalization.LeafRootLoc) : LateralTheory.E.ChernClassExistence.EtaleKummerChernCochainCoboundaryVanishesOnTriangles := by
  intro q _ E L hi α hα U x
  apply sec_sep
  refine LateralTheory.EtaleFoundations.FirstChernUniqueness.loc_imp (LateralTheory.EtaleFoundations.FirstChernUniqueness.loc_and
    (LateralTheory.EtaleFoundations.FirstChernUniqueness.root_line hr q L hi U (x.sub 0 1 (by omega)))
    (LateralTheory.EtaleFoundations.FirstChernUniqueness.root_line hr q L hi U (x.sub 1 1 (by omega)))) fun V g hvw => ?_
  obtain ⟨⟨v, hv⟩, ⟨w, hw⟩⟩ := hvw
  rw [← LateralTheory.EtaleFoundations.FirstChernUniqueness.sub_res] at hv hw
  rw [← ev_res]
  exact (etale_kummer_chern_cochain_coboundary_triangle_eq_zero_of_qth_roots q L α hα V _ v w hv hw).trans (map_zero ((_ : Sec _ U →ₗ[_] Sec _ V))).symm

end LateralTheory.E.ChernCocycleFaceFormulas
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ChernClassValueSecond
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.ChernClassTriangleValuesFromKummerTorsor

theorem etale_kummer_chern_triangle_values_exist_of_local_roots_and_kummer_tor (hr : LateralTheory.E.ChernClassRootLocalization.LeafRootLoc) (hk : LateralTheory.E.CupProductRingLaws.LeafKumTExists) :
    LateralTheory.E.ChernClassExistence.EtaleKummerChernTriangleValuesExistNatural :=
  LateralTheory.EtaleFoundations.exists_natural_etale_kummer_degree_two_value_of_roots_kummer_gluing (LateralTheory.E.ChernClassEdgeValuesFromKummerTorsor.prim_loc_of hr) (LateralTheory.E.ChernClassEdgeValuesFromKummerTorsor.kumT_ex_of hk)
    LateralTheory.EtaleFoundations.etale_sheaf_sections_glue_of_forget_isSheaf

end LateralTheory.E.ChernClassTriangleValuesFromKummerTorsor
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.CokernelKilling
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.DescLocPf

namespace LateralTheory.E.KillCokPf

def Pointwise : Prop := B1 → ∀ (q : ℕ) [NeZero q] (i : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ (D : CommRingCat.{0}) (d : A ⟶ D) (O : CommRingCat.{0}) (o : D ⟶ O), IE o → BC q i φ (d ≫ o) →
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : D ⟶ Y'), IsPushout φ d w φ' →
  ∀ (m : ℤ) (y : H (ZMod q) (sch.obj (Spec Y')) (tw q i) m) (Q : Ideal O), Q.IsPrime →
  ∃ (D₁ : CommRingCat.{0}) (e : D ⟶ D₁) (Q₁ : Ideal D₁), Et e ∧ Q₁.IsPrime ∧ Q₁.comap e.hom = Q.comap o.hom ∧
    ∃ (Y₁ : CommRingCat.{0}) (u : Y' ⟶ Y₁) (φ₁ : D₁ ⟶ Y₁), IsPushout φ' e u φ₁ ∧
      pull _ (sch.map (Spec.map u)) (tw q i) m y ∈ Set.range (pull _ (sch.map (Spec.map φ₁)) (tw q i) m)

def Assemble : Prop := Coprod → ∀ (q : ℕ) [NeZero q] (i : ℤ) {D Y' : CommRingCat.{0}} (φ' : D ⟶ Y') (m : ℤ)
  (y : H (ZMod q) (sch.obj (Spec Y')) (tw q i) m),
  (∀ r : Ideal D, r.IsPrime → ∃ (D₁ : CommRingCat.{0}) (e : D ⟶ D₁) (Q₁ : Ideal D₁), Et e ∧ Q₁.IsPrime ∧ Q₁.comap e.hom = r ∧
    ∃ (Y₁ : CommRingCat.{0}) (u : Y' ⟶ Y₁) (φ₁ : D₁ ⟶ Y₁), IsPushout φ' e u φ₁ ∧
      pull _ (sch.map (Spec.map u)) (tw q i) m y ∈ Set.range (pull _ (sch.map (Spec.map φ₁)) (tw q i) m)) →
  ∃ (E : CommRingCat.{0}) (e : D ⟶ E) (Y'' : CommRingCat.{0}) (u : Y' ⟶ Y'') (φ'' : E ⟶ Y''),
    Et e ∧ SpS e ∧ IsPushout φ' e u φ'' ∧
    pull _ (sch.map (Spec.map u)) (tw q i) m y ∈ Set.range (pull _ (sch.map (Spec.map φ'')) (tw q i) m)

theorem KillCok_of (hC : Coprod) (hP : Pointwise) (hA : Assemble) : LateralTheory.E.DescLocPf.Fine.KillCok := by
  intro hH q _ i n A Y φ hq P _ het _ D d hD hpts Y' w φ' hpo m _ y
  have hB1 : B1 := hH.2.2.2.2.2.2.1
  have hloc : ∀ r : Ideal D, r.IsPrime → ∃ (D₁ : CommRingCat.{0}) (e : D ⟶ D₁) (Q₁ : Ideal D₁), Et e ∧ Q₁.IsPrime ∧
      Q₁.comap e.hom = r ∧ ∃ (Y₁ : CommRingCat.{0}) (u : Y' ⟶ Y₁) (φ₁ : D₁ ⟶ Y₁), IsPushout φ' e u φ₁ ∧
      pull _ (sch.map (Spec.map u)) (tw q i) m y ∈ Set.range (pull _ (sch.map (Spec.map φ₁)) (tw q i) m) := by
    intro r hr
    obtain ⟨O, o, Q, hIE, hQ, hQr, hBC⟩ := hpts r hr
    obtain ⟨D₁, e, Q₁, he, hQ₁, hc, rest⟩ := hP hB1 q i φ hq D d O o hIE hBC Y' w φ' hpo m y Q hQ
    exact ⟨D₁, e, Q₁, he, hQ₁, hc.trans hQr, rest⟩
  obtain ⟨E, e, Y'', u, φ'', he, hs, hpo', hy⟩ := hA hC q i φ' m y hloc
  exact ⟨E, e, Y'', u, φ'', he, hs, het d e hD he, hpo', hy⟩

end LateralTheory.E.KillCokPf
end
end

