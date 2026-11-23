module

public import Development.EtaleCohomology.TateTwists.Bundle0004
public import Development.EtaleCohomology.TateTwists.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.EtaleCohomology.TateTwists.Bundle0001

@[expose] public section

-- bundled from Development.EtaleCohomology.TateTwists.EtaleKInjectiveExtensionAlongQuasiIsoFromSingle
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.EtaleKInjectiveExtensionAlongQuasiIsoFromSingle : Prop :=
  ∀ (R : Type) [CommRing R] (F : Shv R) (T I : Cx R) [I.IsKInjective] [I.IsStrictlyGE 0] (ε : sgl F ⟶ T) [QuasiIso ε],
    (∀ a : sgl F ⟶ I, ∃ m : T ⟶ I, ε ≫ m = a) ∧ ∀ m m' : T ⟶ I, ε ≫ m = ε ≫ m' → Nonempty (Homotopy m m')

def LateralTheory.EtaleFoundations.EtaleSheafInjectiveResolutionProperties : Prop :=
  ∀ (R : Type) [CommRing R] (F : Shv R), (res R F).IsKInjective ∧ (∀ n, Injective ((res R F).X n)) ∧
    (res R F).IsStrictlyGE 0 ∧ QuasiIso (resAug F) ∧ sglι F ≫ (resAug F).f 0 = resι R F

def LateralTheory.EtaleFoundations.EtaleTateTwistHomDeterminedByGenerators : Prop :=
  ∀ (q : ℕ) [NeZero q] (i : ℤ) (M : Shv (ZMod q)) (φ ψ : tw q i ⟶ M),
    (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), Sec.map φ (twGen i ζ) = Sec.map ψ (twGen i ζ)) → φ = ψ

def LateralTheory.EtaleFoundations.EtaleZModInjectiveSheafFlat : Prop :=
  ∀ (q : ℕ) [NeZero q] (M : Shv (ZMod q)) [Injective M], FlatS M

def LateralTheory.EtaleFoundations.EtaleInjectiveSheafSectionsInjective : Prop :=
  ∀ (R : Type) [CommRing R] (M : Shv R) [Injective M] (U : Scheme.{0}), Module.Injective (ULift.{1} R) (Sec M U)

def LateralTheory.EtaleFoundations.ZModInjectiveModuleFlat : Prop :=
  ∀ (q : ℕ) [NeZero q] (N : Type 1) [AddCommGroup N] [Module (ULift.{1} (ZMod q)) N],
    Module.Injective (ULift.{1} (ZMod q)) N → Module.Flat (ULift.{1} (ZMod q)) N

theorem LateralTheory.EtaleFoundations.etale_zmod_injective_sheaf_flat_of_sections_injective_and_zmod_flat (hS : LateralTheory.EtaleFoundations.EtaleInjectiveSheafSectionsInjective)
    (hQ : LateralTheory.EtaleFoundations.ZModInjectiveModuleFlat) : LateralTheory.EtaleFoundations.EtaleZModInjectiveSheafFlat := by
  intro q _ M _
  refine ⟨M.obj, 𝟙 _, fun U y => ?_, fun U x hx => ?_, fun U _ => hQ q _ (hS _ M U)⟩
  · exact ⟨⊤, GrothendieckTopology.top_mem _ _, fun V g _ => ⟨Sec.res g y, rfl⟩⟩
  · refine ⟨⊤, GrothendieckTopology.top_mem _ _, fun V g _ => ?_⟩
    have hx0 : x = 0 := hx
    subst hx0
    exact map_zero _

namespace LateralTheory.EtaleFoundations.TwResExt

variable {C : Type*} [Category C] [Abelian C]

attribute [local instance] HasDerivedCategory.standard in
theorem qh_iso {S T : CochainComplex C ℤ} (ε : S ⟶ T) [QuasiIso ε] :
    IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map ε)) := by
  have : IsIso (DerivedCategory.Q.map ε) := inferInstance
  exact (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso C) ε).2 this

attribute [local instance] HasDerivedCategory.standard in
theorem kinj_lift {S T I : CochainComplex C ℤ} [I.IsKInjective] (ε : S ⟶ T) [QuasiIso ε] (a : S ⟶ I) :
    ∃ m : T ⟶ I, Nonempty (Homotopy (ε ≫ m) a) := by
  have := qh_iso ε
  set qt := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective (qt.obj T) I).2
    (inv (DerivedCategory.Qh.map (qt.map ε)) ≫ DerivedCategory.Qh.map (qt.map a))
  obtain ⟨m, rfl⟩ := qt.map_surjective g
  refine ⟨m, ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
  apply (CochainComplex.IsKInjective.Qh_map_bijective (qt.obj S) I).1
  rw [Functor.map_comp, Functor.map_comp]
  erw [hg]
  exact IsIso.hom_inv_id_assoc _ _

attribute [local instance] HasDerivedCategory.standard in
theorem kinj_uniq {S T I : CochainComplex C ℤ} [I.IsKInjective] (ε : S ⟶ T) [QuasiIso ε] (m m' : T ⟶ I)
    (h : ε ≫ m = ε ≫ m') : Nonempty (Homotopy m m') := by
  have := qh_iso ε
  set qt := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  refine ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩
  apply (CochainComplex.IsKInjective.Qh_map_bijective (qt.obj T) I).1
  rw [← cancel_epi (DerivedCategory.Qh.map (qt.map ε)), ← Functor.map_comp, ← Functor.map_comp,
    ← Functor.map_comp, ← Functor.map_comp, h]

theorem homotopy_single_eq {F : C} {I : CochainComplex C ℤ} [I.IsStrictlyGE 0]
    (f g : (CochainComplex.singleFunctor C 0).obj F ⟶ I) (h : Homotopy f g) : f = g := by
  have hz : ∀ i j, h.hom i j = 0 := by
    intro i j
    by_cases hi : i = 0
    · subst hi
      by_cases hr : (ComplexShape.up ℤ).Rel j 0
      · have hj : j < 0 := by simp [ComplexShape.up_Rel] at hr; omega
        exact (I.isZero_of_isStrictlyGE 0 j hj).eq_of_tgt _ _
      · exact h.zero _ _ hr
    · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi).eq_of_src _ _
  apply HomologicalComplex.hom_ext
  intro n
  rw [h.comm n]
  have : h.hom = 0 := by funext i j; exact hz i j
  simp [this]

theorem sec_map_comp {R : Type} [CommRing R] {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}}
    (x : Sec F U) : Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

theorem ext_hom_pf : LateralTheory.EtaleFoundations.EtaleKInjectiveExtensionAlongQuasiIsoFromSingle := by
  intro R _ F T I _ _ ε _
  refine ⟨fun a => ?_, fun m m' h => kinj_uniq ε m m' h⟩
  obtain ⟨m, ⟨hm⟩⟩ := kinj_lift ε a
  exact ⟨m, homotopy_single_eq _ _ hm⟩

theorem res_pf : LateralTheory.EtaleFoundations.EtaleSheafInjectiveResolutionProperties := by
  intro R _ F
  refine ⟨?_, fun n => ?_, ?_, ?_, rfl⟩
  · exact inferInstanceAs ((injectiveResolution F).cochainComplex.IsKInjective)
  · exact inferInstanceAs (Injective ((injectiveResolution F).cochainComplex.X n))
  · exact inferInstanceAs ((injectiveResolution F).cochainComplex.IsStrictlyGE 0)
  · exact inferInstanceAs (QuasiIso (injectiveResolution F).ι')

end LateralTheory.EtaleFoundations.TwResExt

theorem LateralTheory.EtaleFoundations.TwResExt.linearMap_comp_eq_on_smul_of_eq {S A B C : Type*} [Ring S] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module S A] [Module S B] [Module S C] (t : A →ₗ[S] B) (f g : B →ₗ[S] C) (x : A) (b : S)
    (h : f (t x) = g (t x)) : f (t (b • x)) = g (t (b • x)) := by
  rw [map_smul, map_smul, map_smul, h]

theorem LateralTheory.EtaleFoundations.TwResExt.twuniq_pf : LateralTheory.EtaleFoundations.EtaleTateTwistHomDeterminedByGenerators := by
  intro q _ i M φ ψ h
  apply Sheaf.hom_ext
  refine CategoryTheory.sheafify_hom_ext (J := Scheme.etaleTopology) (P := Scheme.Γ ⋙ twF q i) φ.hom ψ.hom M.property ?_
  refine NatTrans.ext (funext fun U => ModuleCat.hom_ext (Submodule.linearMap_qext _ (Finsupp.lhom_ext fun ζ b => ?_)))
  have h1 := h (unop U) ζ
  change (φ.hom.app U).hom ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i) |>.app U).hom
      (Submodule.Quotient.mk (Finsupp.single ζ b))) = (ψ.hom.app U).hom ((toSheafify Scheme.etaleTopology
      (Scheme.Γ ⋙ twF q i) |>.app U).hom (Submodule.Quotient.mk (Finsupp.single ζ b)))
  rw [← Finsupp.smul_single_one, Submodule.Quotient.mk_smul]
  exact LateralTheory.EtaleFoundations.TwResExt.linearMap_comp_eq_on_smul_of_eq _ _ _ _ b h1

open LateralTheory.EtaleFoundations.TwResExt in
theorem LateralTheory.EtaleFoundations.etale_tate_twist_resolution_universal_of_injective_sections_and_zmod_f (hS : LateralTheory.EtaleFoundations.EtaleInjectiveSheafSectionsInjective) (hQ : LateralTheory.EtaleFoundations.ZModInjectiveModuleFlat) :
    LateralTheory.EtaleFoundations.EtaleTwistResolutionUniversalExtension := by
  have hF := LateralTheory.EtaleFoundations.etale_zmod_injective_sheaf_flat_of_sections_injective_and_zmod_flat hS hQ
  have hE := ext_hom_pf
  have hR := res_pf
  have hU := twuniq_pf
  intro q _ i
  obtain ⟨hK, hInj, hGE, hQ, hι⟩ := hR (ZMod q) (tw q i)
  have hgen : ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)),
      Sec.map ((resAug (tw q i)).f 0) (Sec.map (sglι (tw q i)) (twGen i ζ)) = resGen i ζ := by
    intro U ζ
    rw [← sec_map_comp, hι]
    rfl
  refine ⟨⟨hGE, resAug _, hQ, hgen⟩, fun t => ?_, ?_⟩
  · haveI := hInj t
    exact hF q _
  · intro T e hT
    obtain ⟨_, ε, hε, he⟩ := hT
    have := hε
    have := hK
    have := hGE
    obtain ⟨hex, huniq⟩ := hE (ZMod q) (tw q i) T (res _ (tw q i)) ε
    refine ⟨?_, ?_⟩
    · obtain ⟨m, hm⟩ := hex (resAug _)
      refine ⟨m, fun U ζ => ?_⟩
      rw [← he, ← sec_map_comp, ← HomologicalComplex.comp_f, hm]
      exact hgen U ζ
    · intro u u' h
      apply huniq
      apply HomologicalComplex.from_single_hom_ext
      have hφ : sglι (tw q i) ≫ (ε ≫ u).f 0 = sglι (tw q i) ≫ (ε ≫ u').f 0 := by
        apply hU q i
        intro U ζ
        simp only [sec_map_comp, HomologicalComplex.comp_f]
        have h1 := h U ζ
        rw [← he] at h1
        exact h1
      have hiso : IsIso (sglι (tw q i)) := Iso.isIso_inv _
      exact (cancel_epi (sglι (tw q i))).1 hφ
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleLocallyExistsQthRootOfUnitWhenQInvertible
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.FirstChernUniqueness

lemma sec_sub {q : ℕ} {F : Shv (ZMod q)} (hF : IsZero F) (U : Scheme.{0}) (a b : Sec F U) : a = b := by
  have h1 : IsZero F.obj := (sheafToPresheaf _ _).map_isZero hF
  have h2 : IsZero (F.obj.obj (op U)) := h1.obj (op U)
  have := (ModuleCat.isZero_iff_subsingleton.mp h2)
  exact Subsingleton.elim _ _

lemma res_zero_neg (q : ℕ) (s : ℤ) (hs : s < 0) : IsZero ((res _ (tw q 1)).X s) := by
  unfold res
  exact CochainComplex.isZero_of_isStrictlyGE _ 0 _ (by omega)

lemma sub_res {E : Spc} {N : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E N U) (j l : ℕ) (h : j + l ≤ N) :
    (x.res g).sub j l h = (x.sub j l h).res g := by
  unfold Sx.sub Sx.res
  exact (NatTrans.naturality_apply (E.map (SimplexCategory.subinterval j l h).op) g.op x)

lemma loc_imp {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P)
    (h : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hSP⟩ := hP
  exact ⟨S, hS, fun V g hg => h V g (hSP V g hg)⟩

def EtaleLocallyExistsQthRootOfUnitWhenQInvertible : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ u : (Γ(U, ⊤))ˣ,
  Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u

lemma glMat_res {V U : Scheme.{0}} (g : V ⟶ U) (y : Sx (ofCat (glCat 1)) 1 U) :
    (glMat (y.res g) : Matrix (Fin 1) (Fin 1) Γ(V, ⊤)) = g.appTop.hom.mapMatrix (glMat y : Matrix (Fin 1) (Fin 1) Γ(U, ⊤)) := by
  rfl

lemma lineUnit_res {E : Spc} (L : E ⟶ ofCat (glCat 1)) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E 1 U) :
    lineUnit L (x.res g) = Units.map g.appTop.hom.toMonoidHom (lineUnit L x) := by
  unfold lineUnit
  have hn : (L.app (op (SimplexCategory.mk 1))).app (op V) (x.res g) =
      Sx.res g ((L.app (op (SimplexCategory.mk 1))).app (op U) x) := by
    unfold Sx.res; rw [NatTrans.naturality_apply]
  rw [hn]
  ext
  simp only [Units.coe_map, Matrix.GeneralLinearGroup.val_det_apply, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  rw [glMat_res, RingHom.map_det]

lemma root_line (hr : EtaleLocallyExistsQthRootOfUnitWhenQInvertible) (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)) (hi : Inv q E)
    (U : Scheme.{0}) (x : Sx E 1 U) : Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = lineUnit L (x.res g) := by
  refine loc_imp (hr q U (hi U ⟨x.sub 0 0 (by omega)⟩) (lineUnit L x)) fun V g hv => ?_
  obtain ⟨v, hv⟩ := hv
  exact ⟨v, by rw [lineUnit_res]; exact hv⟩

lemma loc_and {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P) (hQ : Loc U Q) :
    Loc U fun V g => P V g ∧ Q V g := by
  obtain ⟨S, hS, hSP⟩ := hP
  obtain ⟨T, hT, hTQ⟩ := hQ
  exact ⟨S ⊓ T, Scheme.etaleTopology.intersection_covering hS hT, fun V g hg => ⟨hSP V g hg.1, hTQ V g hg.2⟩⟩

end LateralTheory.EtaleFoundations.FirstChernUniqueness
end

-- bundled from Development.EtaleCohomology.TateTwists.EtalePrismAlexanderWhitneyHomotopyOfRelations
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.SteenPf

def leaf_acyc : Prop := ∀ (N k : ℕ) (c : Pr N →₀ ℤ), Pr.Deg (k + 1) c → Pr.d N c = 0 →
  ∃ b : Pr N →₀ ℤ, Pr.Deg (k + 2) b ∧ Pr.d N b = c

def leaf_dbd : Prop := ∀ (N : ℕ) (c : Pr N →₀ ℤ), Pr.d (N + 1) (Pr.bd c) = Pr.bd (Pr.d N c)

def leaf_bdbd : Prop := ∀ (N : ℕ) (c : Pr N →₀ ℤ), Pr.bd (Pr.bd c) = 0

def leaf_aw : Prop := ∀ N : ℕ, Pr.d (N + 1) (Pr.aw (N + 1)) = Pr.bd (Pr.aw N)

def leaf_wa : Prop := ∀ N : ℕ, Pr.d (N + 1) (Pr.wa (N + 1)) = Pr.bd (Pr.wa N)

lemma deg_zero {N k : ℕ} : Pr.Deg k (0 : Pr N →₀ ℤ) := by
  intro z hz; simp at hz

lemma deg_sub {N k : ℕ} {a b : Pr N →₀ ℤ} (ha : Pr.Deg k a) (hb : Pr.Deg k b) : Pr.Deg k (a - b) := by
  intro z hz
  rcases Finset.mem_union.1 (Finsupp.support_sub hz) with h | h
  · exact ha z h
  · exact hb z h

lemma deg_bd {N k : ℕ} {c : Pr N →₀ ℤ} (hc : Pr.Deg k c) : Pr.Deg k (Pr.bd c) := by
  intro z hz
  unfold Pr.bd at hz
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum hz)
  have h2 := Finsupp.support_smul hi
  unfold Pr.push at h2
  simp only [Finsupp.lmapDomain_apply] at h2
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support h2)
  exact hc w hw

lemma deg_aw (N : ℕ) : Pr.Deg N (Pr.aw N) := by
  intro z hz
  unfold Pr.aw at hz
  obtain ⟨p, -, hp⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum hz)
  have := Finsupp.support_single_subset hp
  rw [Finset.mem_singleton] at this
  subst this
  have := p.isLt
  show (p : ℕ) + (N - p) = N
  omega

lemma deg_wa (N : ℕ) : Pr.Deg N (Pr.wa N) := by
  intro z hz
  unfold Pr.wa at hz
  obtain ⟨p, -, hp⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum hz)
  have := Finsupp.support_single_subset hp
  rw [Finset.mem_singleton] at this
  subst this
  have := p.isLt
  show (N - p) + (p : ℕ) = N
  omega

lemma bd_sub {N : ℕ} (a b : Pr N →₀ ℤ) : Pr.bd (a - b) = Pr.bd a - Pr.bd b := by
  unfold Pr.bd
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sub, smul_sub]

lemma bd_zero {N : ℕ} : Pr.bd (0 : Pr N →₀ ℤ) = 0 := by
  simpa using bd_sub (0 : Pr N →₀ ℤ) 0

lemma aw_zero_eq : Pr.aw 0 = Pr.wa 0 := by
  simp [Pr.aw, Pr.wa]

def Good (N : ℕ) (x : Pr N →₀ ℤ) : Prop :=
  Pr.Deg (N + 1) x ∧ Pr.bd (Pr.aw N - Pr.wa N - Pr.d N x) = 0

lemma step (hA : leaf_acyc) (hD : leaf_dbd) (hB : leaf_bdbd) (hAW : leaf_aw) (hWA : leaf_wa)
    (N : ℕ) (x : Pr N →₀ ℤ) (hx : Good N x) :
    ∃ y : Pr (N + 1) →₀ ℤ, Good (N + 1) y ∧ Pr.d (N + 1) y + Pr.bd x = Pr.aw (N + 1) - Pr.wa (N + 1) := by
  set c := Pr.aw (N + 1) - Pr.wa (N + 1) - Pr.bd x with hcdef
  have hcdeg : Pr.Deg (N + 1) c := deg_sub (deg_sub (deg_aw _) (deg_wa _)) (deg_bd hx.1)
  have hcyc : Pr.d (N + 1) c = 0 := by
    rw [hcdef, map_sub, map_sub, hAW, hWA, hD, ← bd_sub, ← bd_sub]
    exact hx.2
  obtain ⟨b, hbdeg, hb⟩ := hA (N + 1) N c hcdeg hcyc
  refine ⟨b, ⟨hbdeg, ?_⟩, ?_⟩
  · have : Pr.aw (N + 1) - Pr.wa (N + 1) - Pr.d (N + 1) b = Pr.bd x := by
      rw [hb, hcdef]; abel
    rw [this]; exact hB N x
  · rw [hb, hcdef]; abel

lemma good_zero : Good 0 0 := by
  refine ⟨deg_zero, ?_⟩
  rw [aw_zero_eq, map_zero, sub_self, sub_zero, bd_zero]

end LateralTheory.EtaleFoundations.SteenPf

open LateralTheory.EtaleFoundations.SteenPf in
theorem LateralTheory.EtaleFoundations.etale_prism_alexander_whitney_homotopy_of_relations (hA : leaf_acyc) (hD : leaf_dbd) (hB : leaf_bdbd)
    (hAW : leaf_aw) (hWA : leaf_wa) : LateralTheory.EtaleFoundations.PrismAlexanderWhitneySwapChainHomotopy := by
  classical
  let seq : ∀ N, {x : Pr N →₀ ℤ // Good N x} := fun N =>
    Nat.rec (motive := fun N => {x : Pr N →₀ ℤ // Good N x}) ⟨0, good_zero⟩
      (fun N x => ⟨Classical.choose (step hA hD hB hAW hWA N x.1 x.2),
        (Classical.choose_spec (step hA hD hB hAW hWA N x.1 x.2)).1⟩) N
  refine ⟨fun N => (seq N).1, fun N => (seq N).2.1, ?_, fun N => ?_⟩
  · show Pr.d 0 0 = _
    rw [map_zero, aw_zero_eq, sub_self]
  · exact (Classical.choose_spec (step hA hD hB hAW hWA N (seq N).1 (seq N).2)).2
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleSemilinearCohomologyOperationExistsOfEvalua
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.pp_ev_basic : Prop :=
  ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}, (∀ (α β : Cochain ((chains R).obj E) I n) p s h U x, ev (R := R) (α + β) p s h U x = ev (R := R) α p s h U x + ev (R := R) β p s h U x ∧ ev (R := R) (α - β) p s h U x = ev (R := R) α p s h U x - ev (R := R) β p s h U x ∧ ev (R := R) (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 ∧ ∀ c : ℤ, ev (R := R) (c • α) p s h U x = c • ev (R := R) α p s h U x) ∧ (∀ (α : Cochain ((chains R).obj E) I n) p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (ev (R := R) α p s h U x) = ev (R := R) α p s h V (x.res g)) ∧ (∀ α β : Cochain ((chains R).obj E) I n, (∀ p s h U x, ev (R := R) α p s h U x = ev (R := R) β p s h U x) → α = β) ∧ (∀ {E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) p s h U (x : Sx E' p U), ev (R := R) ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev (R := R) α p s h U (x.map f)) ∧ ∀ {J : Cx R} (m : I ⟶ J) (α : Cochain ((chains R).obj E) I n) p s h U x, ev (R := R) (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev (R := R) α p s h U x)

def LateralTheory.EtaleFoundations.pp_ev_mk : Prop :=
  ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U), (∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g)) → ∃ α : Cochain ((chains R).obj E) I n, ∀ p s h U x, ev (R := R) α p s h U x = a p s h U x

def LateralTheory.EtaleFoundations.pp_ev_delta : Prop :=
  ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n m : ℤ} (hm : n + 1 = m) (α : Cochain ((chains R).obj E) I n) (U : Scheme.{0}), (∀ (x : Sx E 0 U), ev (R := R) (δ n m α) 0 m (by simp) U x = Sec.map (I.d n m) (ev (R := R) α 0 n (by simp) U x)) ∧ ∀ (p : ℕ) (s t : ℤ) (hs : -((p + 1 : ℕ) : ℤ) + n = s) (ht : -((p + 1 : ℕ) : ℤ) + m = t) (x : Sx E (p + 1) U), ev (R := R) (δ n m α) (p + 1) t ht U x = Sec.map (I.d s t) (ev (R := R) α (p + 1) s hs U x) + m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ev (R := R) α p t (by omega) U (x.face i)

namespace LateralTheory.EtaleFoundations.OpPf
variable {S R : Type} [CommRing S] [CommRing R] {I : Cx S} {J : Cx R}

theorem img_ex (hB : LateralTheory.EtaleFoundations.pp_ev_basic) (hM : LateralTheory.EtaleFoundations.pp_ev_mk) (ρ : SemiMap I J) {E : Spc} {n : ℤ}
    (α : Cochain ((chains S).obj E) I n) : ∃ β, ρ.IsImage α β := by
  obtain ⟨β, hβ⟩ := hM R (E := E) (I := J) (n := n) (fun p s h U x => ρ.app U s (ev (R := S) α p s h U x)) (by
    intro p s h V U g x
    rw [ρ.nat, (hB S).2.1])
  exact ⟨β, fun p s h U x => hβ p s h U x⟩

theorem img_unique (hB : LateralTheory.EtaleFoundations.pp_ev_basic) (ρ : SemiMap I J) {E : Spc} {n : ℤ}
    {α : Cochain ((chains S).obj E) I n} {β β' : Cochain ((chains R).obj E) J n}
    (h : ρ.IsImage α β) (h' : ρ.IsImage α β') : β = β' :=
  (hB R).2.2.1 β β' (fun p s hh U x => by rw [h, h'])

theorem img_delta (hD : LateralTheory.EtaleFoundations.pp_ev_delta) (ρ : SemiMap I J) {E : Spc} {n m : ℤ} (hm : n + 1 = m)
    {α : Cochain ((chains S).obj E) I n} {β : Cochain ((chains R).obj E) J n}
    (h : ρ.IsImage α β) : ρ.IsImage (δ n m α) (δ n m β) := by
  intro p t ht U x
  cases p with
  | zero =>
    obtain rfl : t = m := by omega
    rw [(hD R hm β U).1 x, (hD S hm α U).1 x, h, ρ.comm]
  | succ p =>
    rw [(hD R hm β U).2 p _ t rfl ht x, (hD S hm α U).2 p _ t rfl ht x]
    rw [map_add (f := _), ← ρ.comm, ← h]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Units.smul_def, Units.smul_def, map_zsmul, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, ← h]

theorem img_cocycle (hB : LateralTheory.EtaleFoundations.pp_ev_basic) (hM : LateralTheory.EtaleFoundations.pp_ev_mk) (hD : LateralTheory.EtaleFoundations.pp_ev_delta)
    (ρ : SemiMap I J) {E : Spc} {n : ℤ} (α : Cocycle ((chains S).obj E) I n) :
    ∃ β : Cocycle ((chains R).obj E) J n, ρ.IsImage α.1 β.1 := by
  obtain ⟨β, hβ⟩ := img_ex hB hM ρ α.1
  refine ⟨Cocycle.mk β (n + 1) rfl ?_, hβ⟩
  have h1 := img_delta hD ρ rfl hβ
  rw [Cocycle.δ_eq_zero] at h1
  have h0 : ρ.IsImage (0 : Cochain ((chains S).obj E) I (n + 1)) (0 : Cochain ((chains R).obj E) J (n + 1)) := by
    intro p s h U x
    rw [((hB R).1 0 0 p s h U x).2.2.1, ((hB S).1 0 0 p s h U x).2.2.1, map_zero]
  exact img_unique hB ρ h1 h0

noncomputable def img (hB : LateralTheory.EtaleFoundations.pp_ev_basic) (hM : LateralTheory.EtaleFoundations.pp_ev_mk) (hD : LateralTheory.EtaleFoundations.pp_ev_delta)
    (ρ : SemiMap I J) {E : Spc} {n : ℤ} (α : Cocycle ((chains S).obj E) I n) : Cocycle ((chains R).obj E) J n :=
  (img_cocycle hB hM hD ρ α).choose

theorem img_spec (hB : LateralTheory.EtaleFoundations.pp_ev_basic) (hM : LateralTheory.EtaleFoundations.pp_ev_mk) (hD : LateralTheory.EtaleFoundations.pp_ev_delta)
    (ρ : SemiMap I J) {E : Spc} {n : ℤ} (α : Cocycle ((chains S).obj E) I n) : ρ.IsImage α.1 (img hB hM hD ρ α).1 :=
  (img_cocycle hB hM hD ρ α).choose_spec

theorem img_eq (hB : LateralTheory.EtaleFoundations.pp_ev_basic) (hM : LateralTheory.EtaleFoundations.pp_ev_mk) (hD : LateralTheory.EtaleFoundations.pp_ev_delta)
    (ρ : SemiMap I J) {E : Spc} {n : ℤ} (α : Cocycle ((chains S).obj E) I n) (β : Cocycle ((chains R).obj E) J n)
    (h : ρ.IsImage α.1 β.1) : img hB hM hD ρ α = β :=
  Cocycle.ext (img_unique hB ρ (img_spec hB hM hD ρ α) h)

noncomputable def zmap (hB : LateralTheory.EtaleFoundations.pp_ev_basic) (hM : LateralTheory.EtaleFoundations.pp_ev_mk) (hD : LateralTheory.EtaleFoundations.pp_ev_delta)
    (ρ : SemiMap I J) (E : Spc) (n : ℤ) : Cocycle ((chains S).obj E) I n →+ CohomologyClass ((chains R).obj E) J n :=
  AddMonoidHom.mk' (fun α => CohomologyClass.mk (img hB hM hD ρ α)) (fun a b => by
    rw [← CohomologyClass.mk_add]
    congr 1
    apply img_eq
    intro p s h U x
    have ha := img_spec hB hM hD ρ a p s h U x
    have hb := img_spec hB hM hD ρ b p s h U x
    change ev (R := R) ((img hB hM hD ρ a).1 + (img hB hM hD ρ b).1) p s h U x = ρ.app U s (ev (R := S) (a.1 + b.1) p s h U x)
    rw [((hB R).1 _ _ p s h U x).1, ((hB S).1 _ _ p s h U x).1, map_add (f := _), ha, hb])

noncomputable def theOp (hB : LateralTheory.EtaleFoundations.pp_ev_basic) (hM : LateralTheory.EtaleFoundations.pp_ev_mk) (hD : LateralTheory.EtaleFoundations.pp_ev_delta)
    (ρ : SemiMap I J) : NatOp I J where
  app E n := CohomologyClass.descAddMonoidHom (zmap hB hM hD ρ E n) (by
    intro α hα
    obtain ⟨γ, hγ⟩ := (mem_coboundaries_iff α (n - 1) (by omega)).1 hα
    obtain ⟨γ', hγ'⟩ := img_ex hB hM ρ γ
    have h1 := img_delta hD ρ (by omega : n - 1 + 1 = n) hγ'
    rw [hγ] at h1
    have h2 := img_eq hB hM hD ρ α (Cocycle.mk (δ (n - 1) n γ') (n + 1) rfl (δ_δ _ _ _ _)) h1
    change CohomologyClass.mk (img hB hM hD ρ α) = 0
    rw [h2, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
    exact ⟨γ', rfl⟩)
  nat := by
    intro E E' f n x
    obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective x
    change CohomologyClass.mk (zcomp _ (img hB hM hD ρ α) (zero_add n)) =
      CohomologyClass.mk (img hB hM hD ρ (zcomp _ α (zero_add n)))
    congr 1
    symm
    apply img_eq
    intro p s h U y
    change ev (R := R) ((Cochain.ofHom ((chains R).map f)).comp (img hB hM hD ρ α).1 (zero_add n)) p s h U y =
      ρ.app U s (ev (R := S) ((Cochain.ofHom ((chains S).map f)).comp α.1 (zero_add n)) p s h U y)
    rw [(hB R).2.2.2.1, (hB S).2.2.2.1, img_spec hB hM hD ρ α]

end LateralTheory.EtaleFoundations.OpPf

open LateralTheory.EtaleFoundations.OpPf in
theorem LateralTheory.EtaleFoundations.etale_semilinear_cohomology_operation_exists_of_evaluation (hB : LateralTheory.EtaleFoundations.pp_ev_basic) (hM : LateralTheory.EtaleFoundations.pp_ev_mk)
    (hD : LateralTheory.EtaleFoundations.pp_ev_delta) : LateralTheory.EtaleFoundations.EtaleCochainSemilinearMapOnClasses := by
  intro S R _ _ I J ρ
  refine ⟨fun E n α => img_cocycle hB hM hD ρ α, fun E n α β h => ?_⟩
  have hc : ∃ c : NatOp I J, ∀ (E : Spc) (n : ℤ) (α : Cocycle ((chains S).obj E) I n) (β : Cocycle ((chains R).obj E) J n),
      (∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U), ev (R := R) β.1 p s h U x = ρ.app U s (ev (R := S) α.1 p s h U x)) →
      c.app E n (CohomologyClass.mk α) = CohomologyClass.mk β := by
    refine ⟨theOp hB hM hD ρ, fun E n α β h => ?_⟩
    change CohomologyClass.mk (img hB hM hD ρ α) = CohomologyClass.mk β
    rw [img_eq hB hM hD ρ α β h]
  exact pick_spec hc E n α β h
end

