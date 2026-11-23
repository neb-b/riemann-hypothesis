module

public import Development.EtaleCohomology.EtaleSheaves.LineHigh
public import Development.EtaleCohomology.EtaleSheaves.Bundle0005
public import Development.EtaleCohomology.EtaleSheaves.Bundle0004
public import Development.EtaleCohomology.TateTwists.Bundle0009

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.AICAcycPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.AICAcycPf

theorem acyc_of_iso (q : ℕ) {X Y : Scheme.{0}} (e : X ≅ Y) (h : Acyc q (sch.obj Y)) : Acyc q (sch.obj X) := by
  intro n i hn
  have := h n i hn
  constructor
  intro a b
  have key : ∀ a : Ht q (sch.obj X) n i,
      a = pull _ (sch.map e.hom) _ n (pull _ (sch.map e.inv) _ n a) := by
    intro a
    rw [← pull_comp, ← CategoryTheory.Functor.map_comp, e.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]
  rw [key a, key b, Subsingleton.elim (pull _ (sch.map e.inv) _ n a) (pull _ (sch.map e.inv) _ n b)]

theorem aff (hB5 : B5) (q : ℕ) (Z : Scheme.{0}) [IsAffine Z] (hZ : AICSch Z) (hq : IsUnit (q : Γ(Z, ⊤))) :
    Acyc q (sch.obj Z) := by
  have : IsIntegral Z := hZ.1
  have hA : AIC Γ(Z, ⊤) := hZ.2 ⊤ (isAffineOpen_top Z) ⟨Nonempty.some inferInstance, by simp⟩
  have h5 := hB5 q Γ(Z, ⊤) hA hq
  exact acyc_of_iso q Z.isoSpec h5

def Step : Prop := Hyp → MV → HZero → ∀ (q : ℕ) {U V X : Scheme.{0}} (f : U ⟶ X) (g : V ⟶ X) [IsOpenImmersion f]
  [IsOpenImmersion g], Set.range f ∪ Set.range g = Set.univ → AICSch X → AICSch U → AICSch V → IsUnit (q : Γ(X, ⊤)) →
  Acyc q (sch.obj U) → Acyc q (sch.obj V) → (Nonempty ↥(pullback f g : Scheme.{0}) → Acyc q (sch.obj (pullback f g))) → Acyc q (sch.obj X)

def Cov : Prop := ∀ (q : ℕ) (P : Scheme.{0} → Prop), (∀ {X Y : Scheme.{0}}, (X ≅ Y) → P Y → P X) →
  (∀ Z : Scheme.{0}, IsAffine Z → AICSch Z → IsUnit (q : Γ(Z, ⊤)) → P Z) →
  (∀ {U V X : Scheme.{0}} (f : U ⟶ X) (g : V ⟶ X) [IsOpenImmersion f] [IsOpenImmersion g],
    Set.range f ∪ Set.range g = Set.univ → AICSch X → AICSch U → AICSch V → IsUnit (q : Γ(X, ⊤)) →
    P U → P V → (Nonempty ↥(pullback f g : Scheme.{0}) → P (pullback f g)) → P X) →
  ∀ (Z : Scheme.{0}) [CompactSpace Z] [QuasiSeparatedSpace Z], AICSch Z → IsUnit (q : Γ(Z, ⊤)) → P Z

theorem AICAcyc_of (hZ : HZero) (hMV : MV) (hStep : Step) (hCov : Cov) : AICAcyc := by
  intro hyp q Z _ _ hZs hq
  refine hCov q (fun W => Acyc q (sch.obj W)) ?_ ?_ ?_ Z hZs hq
  · intro X Y e h
    exact acyc_of_iso q e h
  · intro W hA hW hWq
    exact aff hyp.b5 q W hW hWq
  · intro U V X f g _ _ hc hX hU hV hq' hPU hPV hPW
    exact hStep hyp hMV hZ q f g hc hX hU hV hq' hPU hPV hPW

end LateralTheory.E.AICAcycPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.AICSHPf
section
noncomputable section
open Polynomial GlobalTheory.EtC

namespace LateralTheory.E.AICSHPf

theorem root_near {T : Type} [CommRing T] [IsDomain T] (hA : ∀ p : Polynomial T, p.Monic → 0 < p.natDegree → ∃ a, p.eval a = 0)
    (P : Ideal T) [P.IsPrime] (a₀ : T) :
    ∀ (n : ℕ) (f : T[X]), f.natDegree = n → f.Monic → f.eval a₀ ∈ P → ∃ a, f.IsRoot a ∧ a - a₀ ∈ P := by
  intro n
  induction n with
  | zero =>
    intro f hd hm hv
    have : f = 1 := Polynomial.eq_one_of_monic_natDegree_zero hm hd
    subst this
    simp only [eval_one] at hv
    exact absurd ((Ideal.eq_top_iff_one P).2 hv) (Ideal.IsPrime.ne_top inferInstance)
  | succ n ih =>
    intro f hd hm hv
    obtain ⟨r, hr⟩ := hA f hm (by omega)
    have hroot : f.IsRoot r := hr
    set q := f /ₘ (X - C r) with hq
    have hfac : (X - C r) * q = f := (Polynomial.mul_divByMonic_eq_iff_isRoot).2 hroot
    have hqm : q.Monic := Polynomial.Monic.of_mul_monic_left (monic_X_sub_C r) (by rw [hfac]; exact hm)
    have hdeg : q.natDegree = n := by
      have := (monic_X_sub_C r).natDegree_mul hqm
      rw [hfac, natDegree_X_sub_C] at this; omega
    have hv' : (a₀ - r) * q.eval a₀ ∈ P := by
      rw [← hfac] at hv; simpa [eval_mul] using hv
    rcases (inferInstance : P.IsPrime).mem_or_mem hv' with h | h
    · refine ⟨r, hroot, ?_⟩
      have := P.neg_mem_iff.2 h; simpa using this
    · obtain ⟨a, ha, ha'⟩ := ih q hdeg hqm h
      refine ⟨a, ?_, ha'⟩
      rw [← hfac]; simp [IsRoot, eval_mul, ha.eq_zero]

theorem henselian {T : Type} [CommRing T] [IsDomain T] [IsLocalRing T] (hA : AIC T) : HenselianLocalRing T where
  is_henselian f hf a₀ h₀ _ := root_near hA (IsLocalRing.maximalIdeal T) a₀ _ f rfl hf h₀

theorem algClosed {T : Type} [CommRing T] [IsDomain T] [IsLocalRing T] (hA : AIC T) :
    IsAlgClosed (IsLocalRing.ResidueField T) := by
  refine IsAlgClosed.of_exists_root _ ?_
  intro p hpm hirr
  obtain ⟨P, hPl, hPd, hPm⟩ := Polynomial.lifts_and_degree_eq_and_monic
    (Polynomial.lifts_iff_coeff_lifts p |>.2 fun n => IsLocalRing.residue_surjective _) hpm
  have hpos : 0 < P.natDegree := by
    rw [Polynomial.natDegree_eq_of_degree_eq hPd]; exact Irreducible.natDegree_pos hirr
  obtain ⟨a, ha⟩ := hA P hPm hpos
  refine ⟨IsLocalRing.residue T a, ?_⟩
  rw [← hPl, Polynomial.eval_map, Polynomial.eval₂_at_apply, ha, map_zero]

end LateralTheory.E.AICSHPf

namespace LateralTheory.E.t_E3Cut

theorem AICSH_of : AICSH := by
  intro T _ _ _ hA
  let _ := LateralTheory.E.AICSHPf.henselian hA
  have := LateralTheory.E.AICSHPf.algClosed hA
  exact ⟨inferInstance, inferInstance⟩

end LateralTheory.E.t_E3Cut
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.AlgResPropsPf
section
noncomputable section
open CategoryTheory Limits

namespace LateralTheory.E.AlgResPropsPf
open LateralTheory.E.t_E3Cut

theorem cancel {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C) (h : AlgRes (f ≫ g)) : AlgRes g := by
  intro Q hQ c
  obtain ⟨p, ⟨n, hn⟩, hp⟩ := h Q hQ c
  refine ⟨p.map f.hom, ⟨n, ?_⟩, ?_⟩
  · rw [Polynomial.coeff_map]; simpa using hn
  · rw [Polynomial.eval₂_map]; simpa using hp

theorem integral {A B : CommRingCat.{0}} (f : A ⟶ B) (h : f.hom.IsIntegral) : AlgRes f := by
  intro Q hQ c
  obtain ⟨p, hm, hp⟩ := h c
  refine ⟨p, ⟨p.natDegree, ?_⟩, ?_⟩
  · rw [← Polynomial.leadingCoeff, hm.leadingCoeff, map_one]
    exact fun h1 => hQ.ne_top ((Ideal.eq_top_iff_one Q).2 h1)
  · rw [hp]; exact Q.zero_mem

theorem loc (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (S : Submonoid A) [IsLocalization S B] :
    AlgRes (CommRingCat.ofHom (algebraMap A B)) := by
  intro Q hQ c
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective S c
  refine ⟨Polynomial.C (s : A) * Polynomial.X - Polynomial.C a, ⟨1, ?_⟩, ?_⟩
  · have hu : IsUnit (algebraMap A B s) := IsLocalization.map_units B s
    intro hm
    apply hQ.ne_top
    apply Q.eq_top_of_isUnit_mem hm
    simpa [Polynomial.coeff_C, Polynomial.coeff_X] using hu
  · have := IsLocalization.mk'_spec B a s
    simp only [CommRingCat.hom_ofHom, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X]
    rw [mul_comm, this, sub_self]; exact Q.zero_mem

def Comp : Prop :=
  ∀ {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C), AlgRes f → AlgRes g → AlgRes (f ≫ g)

def Push : Prop :=
  ∀ {A B C D : CommRingCat.{0}} (f : A ⟶ B) (g : A ⟶ C) (u : B ⟶ D) (v : C ⟶ D), IsPushout f g u v → AlgRes f → AlgRes v

def EtAlg : Prop := ∀ {A B : CommRingCat.{0}} (f : A ⟶ B), Et f → AlgRes f

theorem AlgResProps_of (h1 : Comp) (h2 : Push) (h3 : EtAlg) : LateralTheory.E.t_E3Cut.AlgResProps :=
  ⟨fun f g hf hg => h1 f g hf hg, fun f g h => cancel f g h, fun f g u v h hf => h2 f g u v h hf,
    fun f h => h3 f h, fun f h => integral f h, fun A B _ _ _ S _ => loc A B S⟩

end LateralTheory.E.AlgResPropsPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.BasePf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut

namespace LateralTheory.E.BasePf

theorem polyPO {A C : CommRingCat.{0}} (f : A ⟶ C) :
    IsPushout (pC A) f (CommRingCat.ofHom (Polynomial.mapRingHom f.hom)) (pC C) := by
  algebraize [f.hom, Polynomial.mapRingHom f.hom]
  exact (CommRingCat.isPushout_of_isPushout A C (Polynomial A) (Polynomial C)).flip

theorem et_map {A C : CommRingCat.{0}} (f : A ⟶ C) (hf : Et f) :
    Et (CommRingCat.ofHom (Polynomial.mapRingHom f.hom)) := by
  have : (RingHom.toMorphismProperty RingHom.Etale).IsStableUnderCobaseChange :=
    RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.mpr RingHom.Etale.isStableUnderBaseChange
  exact (RingHom.toMorphismProperty RingHom.Etale).of_isPushout (polyPO f) hf

theorem Base_of (h : LateralTheory.E.t_E3Cut.EtaleBaseChangeFractionFieldIndEtaleOverPolynomial) : LateralTheory.E.t_E3Cut.Base := by
  intro H q _ i T _ _ _ hT hq B c hc Y' w φ' hpo
  rw [Category.id_comp] at hpo
  have hc4 : C4 := H.2.2.2.2.2.2.2.2.2.2
  have hqB : IsUnit (q : B) := by simpa using hq.map c.hom
  have hqY : IsUnit (q : Y') := by simpa using hqB.map φ'.hom
  have sq := hpo.flip.paste_horiz (polyPO φ')
  have e1 : c ≫ pC B = pC (CommRingCat.of T) ≫ CommRingCat.ofHom (Polynomial.mapRingHom c.hom) := by
    ext x; simp
  rw [e1] at sq
  have hIE : IE (CommRingCat.ofHom (Polynomial.mapRingHom c.hom)) :=
    MorphismProperty.le_ind _ _ (et_map c hc)
  have r2 : RE q i (CommRingCat.ofHom (Polynomial.mapRingHom φ'.hom)) :=
    h H q i T (FractionRing T) hT hq _ _ hIE _ _ _ sq.flip
  have r1 : RE q i (pC B) := hc4 q B hqB i
  have r3 : RE q i (pC Y') := hc4 q Y' hqY i
  have e2 : pC B ≫ CommRingCat.ofHom (Polynomial.mapRingHom φ'.hom) = φ' ≫ pC Y' := by
    ext x; simp
  have r4 : RE q i (φ' ≫ pC Y') := e2 ▸ r1.comp r2
  exact RE.of_comp_right r3 r4

end LateralTheory.E.BasePf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.CechFiltPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.CechFiltPf

def Piece : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {E₀ E : Spc} (g : E₀ ⟶ E) (p : ℕ) (n : ℤ),
  Subsingleton (Hrel R (disc.map (g.app (op (SimplexCategory.mk p)))) F (n - p)) →
  Subsingleton (HK R (mappingCone ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).map
    (((chains R).map g).f (-(p : ℤ))))) F n)

universe u v

theorem chains_isZero (R : Type) [CommRing R] (E : Spc) (j : ℤ) (hj : 0 < j) : IsZero (((chains R).obj E).X j) := by
  unfold chains
  exact HomologicalComplex.isZero_extend_X _ _ _ (fun i => by
    show -(i : ℤ) ≠ j
    omega)

theorem res_isZero (R : Type) [CommRing R] (F : Shv R) (j : ℤ) (hj : j < 0) : IsZero ((res R F).X j) := by
  unfold res InjectiveResolution.cochainComplex
  exact HomologicalComplex.isZero_extend_X _ _ _ (fun i => by
    show (i : ℤ) ≠ j
    omega)

def DiscLvl : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {P Q : PSh} (h : P ⟶ Q) (m : ℤ),
  Subsingleton (Hrel R (disc.map h) F m) →
  Subsingleton (HK R (mappingCone ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map ((free R).map h))) F m)

def ShiftLvl : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {E₀ E : Spc} (g : E₀ ⟶ E) (p : ℕ) (n : ℤ),
  Subsingleton (HK R (mappingCone ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).map
    ((free R).map (g.app (op (SimplexCategory.mk p)))))) F (n - p)) →
  Subsingleton (HK R (mappingCone ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).map
    (((chains R).map g).f (-(p : ℤ))))) F n)

theorem Piece_of (hD : DiscLvl) (hS : ShiftLvl) : Piece := by
  intro R _ F E₀ E g p n h
  exact hS R F g p n (hD R F _ _ h)

end LateralTheory.E.CechFiltPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ChernClassRootLocalization
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.ChernClassRootLocalization

open LateralTheory.E.CupProductRingLaws LateralTheory.E.ChernCocycleExistenceAndUniqueness

theorem sec_sep {R : Type} [CommRing R] (F : Shv R) (U : Scheme.{0}) (a b : Sec F U)
    (h : Loc U fun _ g => Sec.res g a = Sec.res g b) : a = b := by
  obtain ⟨S, hS, hab⟩ := h
  have hF := ((sheafCompose Scheme.etaleTopology (forget (ModuleCat.{1} (ULift.{1} R)))).obj F).property
  rw [isSheaf_iff_isSheaf_of_type] at hF
  exact (hF S hS).isSeparatedFor.ext (fun V g hg => hab V g hg)

variable {R : Type} [CommRing R] in
theorem freeGen_res (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    freeGen R P V (P.map g.op x) = Sec.res g (freeGen R P U x) := by
  have key := NatTrans.naturality_apply (toSheafify Scheme.etaleTopology ((freeP R).obj P)) g.op
    (ModuleCat.freeMk (R := ULift.{1} R) (show uliftFunctor.{1, 0}.obj (P.obj (op U)) from ULift.up x))
  refine Eq.trans ?_ key
  unfold freeGen
  congr 1
  simp only [freeP, Functor.whiskeringRight_obj_obj, Functor.comp_map]
  erw [ModuleCat.free_map_apply]
  rfl

variable {R : Type} [CommRing R] in
theorem ev_res {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s)
    {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E p U) : ev α p s h V (x.res g) = Sec.res g (ev α p s h U x) := by
  unfold ev Sx.res
  rw [freeGen_res]
  exact NatTrans.naturality_apply (((chainsXIso R E p).inv ≫ α.v _ _ h).hom) g.op _

def LeafRootLoc : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ u : (Γ(U, ⊤))ˣ,
  Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u

theorem evUnique_of (hr : LeafRootLoc) : EtaleKummerChernCocycleEvaluationsUnique := by
  intro q _ E L hq γ γ' h h'
  constructor
  · intro U x
    apply sec_sep
    refine LateralTheory.EtaleFoundations.FirstChernUniqueness.loc_imp (LateralTheory.EtaleFoundations.FirstChernUniqueness.root_line hr q L hq U x) fun V g hv => ?_
    obtain ⟨v, hv⟩ := hv
    rw [← ev_res, ← ev_res, h.2.1 V _ v hv, h'.2.1 V _ v hv]
  · intro U x
    apply sec_sep
    refine LateralTheory.EtaleFoundations.FirstChernUniqueness.loc_imp (LateralTheory.EtaleFoundations.FirstChernUniqueness.loc_and (LateralTheory.EtaleFoundations.FirstChernUniqueness.root_line hr q L hq U (x.sub 0 1 (by omega)))
      (LateralTheory.EtaleFoundations.FirstChernUniqueness.root_line hr q L hq U (x.sub 1 1 (by omega)))) fun V g hv => ?_
    obtain ⟨⟨v, hv⟩, ⟨w, hw⟩⟩ := hv
    rw [← LateralTheory.EtaleFoundations.FirstChernUniqueness.sub_res] at hv hw
    rw [← ev_res, ← ev_res, h.2.2 V _ v w hv hw, h'.2.2 V _ v w hv hw]

theorem etale_first_chern_class_represented_of_cocycle_exists_and_evaluations_unique (hE : EtaleKummerChernCocycleExists) (hr : LeafRootLoc) : EtaleFirstChernClassRepresentedByChernCocycle :=
  LateralTheory.E.ChernCocycleExistenceAndUniqueness.etale_first_chern_class_represented_of_cocycle_exists_and_evaluations_unique hE (evUnique_of hr)

end LateralTheory.E.ChernClassRootLocalization
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ChowCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut

namespace LateralTheory.E.ChowCut

def Img : Prop := ∀ (A : Type) [CommRing A] {Z X : Scheme.{0}} (h : Z ⟶ X) (p : X ⟶ Spec (CommRingCat.of A)) [IsProper p],
  IsIntegralHom h → IsIntegral Z → ∃ (X₁ : Scheme.{0}) (h₁ : Z ⟶ X₁) (p₁ : X₁ ⟶ Spec (CommRingCat.of A)),
    IsIntegral X₁ ∧ IsProper p₁ ∧ IsIntegralHom h₁ ∧ IsDominant h₁ ∧ h₁ ≫ p₁ = h ≫ p

def ChowL : Prop := ∀ (A : Type) [CommRing A] {X₁ : Scheme.{0}} (p₁ : X₁ ⟶ Spec (CommRingCat.of A)) [IsProper p₁],
  IsIntegral X₁ → ∃ (X' : Scheme.{0}) (π : X' ⟶ X₁) (U : X₁.Opens) (s : U.toScheme ⟶ X'),
    (U : Set X₁).Nonempty ∧ s ≫ π = U.ι ∧ IT π ∧ IT (π ≫ p₁)

def Norm : Prop := ∀ {Z W : Scheme.{0}} (f : W ⟶ Z) [QuasiSeparated f], AICSch Z →
  (∃ (U : Z.Opens) (s : U.toScheme ⟶ W), (U : Set Z).Nonempty ∧ s ≫ f = U.ι) →
  ∃ (Z' : Scheme.{0}) (v : Z' ⟶ W), IsIntegralHom v ∧ AICSch Z' ∧ IsDominant (v ≫ f)

theorem goal_of (hI : Img) (hC : ChowL) (hN : Norm) : LateralTheory.E.t_E2Cut.Chow := by
  intro A _ Z X h p _ hh hZ
  obtain ⟨X₁, h₁, p₁, hX₁, hp₁, hh₁, hd₁, e⟩ := hI A h p hh hZ.1
  have := hp₁
  have := hh₁
  have := hd₁
  obtain ⟨X', π, U, s, hU, hs, hπ, hπp⟩ := hC A p₁ hX₁
  obtain ⟨_, _⟩ := (hπ.bc h₁ (IsPullback.of_hasPullback h₁ π).flip).qc
  have hU' : ((h₁ ⁻¹ᵁ U : Z.Opens) : Set Z).Nonempty := by
    obtain ⟨x, hxU, y, rfl⟩ := h₁.denseRange.inter_open_nonempty _ U.isOpen hU
    exact ⟨y, hxU⟩
  have sec : ∃ (V : Z.Opens) (t : V.toScheme ⟶ pullback h₁ π), (V : Set Z).Nonempty ∧ t ≫ pullback.fst h₁ π = V.ι :=
    ⟨h₁ ⁻¹ᵁ U, pullback.lift (h₁ ⁻¹ᵁ U).ι ((h₁ ∣_ U) ≫ s) (by rw [Category.assoc, hs, morphismRestrict_ι]), hU',
      pullback.lift_fst _ _ _⟩
  obtain ⟨Z', v, hv, hZ', hd⟩ := hN (pullback.fst h₁ π) hZ sec
  refine ⟨Z', v ≫ pullback.fst h₁ π, hZ', hd, hπ.bc h₁ (IsPullback.of_hasPullback h₁ π).flip |>.pre v hv, ?_⟩
  have : (v ≫ pullback.fst h₁ π) ≫ h ≫ p = (v ≫ pullback.snd h₁ π) ≫ π ≫ p₁ := by
    rw [← e, Category.assoc, reassoc_of% pullback.condition, Category.assoc]
  rw [this]
  exact hπp.pre _ inferInstance

end LateralTheory.E.ChowCut

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ContPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.ContPf

def PC (X0 : Scheme.{0}) : Prop := ∀ (q : ℕ) {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D),
  IsLimit c → (∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)) → (∀ j, CompactSpace (D.obj j)) →
  (∀ j, QuasiSeparatedSpace (D.obj j)) → (∀ j, IsUnit (q : Γ(D.obj j, ⊤))) → ∀ j0 : J, Nonempty (D.obj j0 ≅ X0) →
  ∀ n i : ℤ,
  (∀ x : Ht q (sch.obj c.pt) n i, ∃ j y, pull _ (sch.map (c.π.app j)) _ _ y = x) ∧
  ∀ j (y : Ht q (sch.obj (D.obj j)) n i), pull _ (sch.map (c.π.app j)) _ _ y = 0 →
    ∃ (k : J) (f : k ⟶ j), pull _ (sch.map (D.map f)) _ _ y = 0

def ContAff : Prop := Hyp → ∀ (X : Scheme.{0}) [IsAffine X], PC X

def ContStep : Prop := Hyp → MV → ∀ (X : Scheme.{0}) (U V : X.Opens), IsCompact (U : Set X) → IsCompact (V : Set X) →
  U ⊔ V = ⊤ → PC U.toScheme → PC V.toScheme → PC (U ⊓ V).toScheme → PC X

def ContInd : Prop := ∀ (P : Scheme.{0} → Prop), (∀ (X : Scheme.{0}) [IsAffine X], P X) →
  (∀ (X : Scheme.{0}) (U V : X.Opens), IsCompact (U : Set X) → IsCompact (V : Set X) → U ⊔ V = ⊤ →
    P U.toScheme → P V.toScheme → P (U ⊓ V).toScheme → P X) →
  ∀ (X : Scheme.{0}) [CompactSpace X] [QuasiSeparatedSpace X], P X

theorem Cont_of (hMV : MV) (hA : ContAff) (hS : ContStep) (hI : ContInd) : Cont := by
  intro h q J _ _ D c hc ha hcs hqs hu n i
  obtain ⟨j0⟩ := IsCofiltered.nonempty (C := J)
  have := hcs j0
  have := hqs j0
  have key : PC (D.obj j0) := hI PC (fun X _ => hA h X) (fun X U V hU hV hUV pU pV pW => hS h hMV X U V hU hV hUV pU pV pW)
    (D.obj j0)
  exact key q D c hc ha hcs hqs hu j0 ⟨Iso.refl _⟩ n i

end LateralTheory.E.ContPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.CoprodPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.CoprodPf

def FreeCoprod : Prop := ∀ (R : Type) [CommRing R] {ι : Type} (X : ι → Scheme.{0}),
  Nonempty (IsColimit (Cofan.mk ((free R).obj (yoneda.obj (∐ X))) fun j => (free R).map (yoneda.map (Sigma.ι X j))))

def ChainsDiscCoprod : Prop := ∀ (R : Type) [CommRing R] {ι : Type} (P : ι → PSh) (Q : PSh) (p : ∀ j, P j ⟶ Q),
  Nonempty (IsColimit (Cofan.mk ((free R).obj Q) fun j => (free R).map (p j))) →
  Nonempty (IsColimit (Cofan.mk ((chains R).obj (disc.obj Q)) fun j => (chains R).map (disc.map (p j))))

def HKCoprod : Prop := ∀ (R : Type) [CommRing R] {ι : Type} (K : ι → Cx R) (c : Cofan K), IsColimit c →
  ∀ (F : Shv R) (n : ℤ), Function.Bijective fun (x : HK R c.pt F n) (j : ι) => HK.pull R (c.inj j) F n x

theorem Coprod_of (h1 : FreeCoprod) (h2 : ChainsDiscCoprod) (h3 : HKCoprod) : LateralTheory.E.t_E3Cut.Coprod := by
  intro R _ F ι X n
  obtain ⟨hc⟩ := h2 R (fun j => yoneda.obj (X j)) (yoneda.obj (∐ X)) (fun j => yoneda.map (Sigma.ι X j)) (h1 R X)
  exact h3 R _ _ hc F n

end LateralTheory.E.CoprodPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.CoverCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.CoverCut

def ClopenSys {Y : Scheme.{0}} (y : Y) {J : Type} [SmallCategory J] (D : J ⥤ Scheme.{0}) (c : Cone D)
    (ι : ∀ j, D.obj j ⟶ Y) : Prop :=
  Nonempty (IsLimit c) ∧ (∀ j, IsOpenImmersion (ι j) ∧ IsClosedImmersion (ι j) ∧ y ∈ Set.range (ι j)) ∧
    ∀ {j k : J} (f : j ⟶ k), D.map f ≫ ι k = ι j ∧ IsAffineHom (D.map f)

def Build : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P],
  ∃ (Y : Scheme.{0}) (k : Y ⟶ P), IsIntegralHom k ∧ Surjective k ∧
    ∀ y : Y, ∃ (J : Type) (_ : SmallCategory J) (_ : IsCofiltered J) (D : J ⥤ Scheme.{0}) (c : Cone D) (ι : ∀ j, D.obj j ⟶ Y),
      ClopenSys y D c ι ∧ AICSch c.pt ∧ ∀ j, IsIntegralHom ((c.π.app j ≫ ι j) ≫ k)

def ProEqv : Prop := Hyp → ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], IsUnit (q : A) →
  ∀ {Y : Scheme.{0}} [CompactSpace Y] [QuasiSeparatedSpace Y] (g : Y ⟶ Spec (CommRingCat.of A)),
  (∀ y : Y, ∃ (J : Type) (_ : SmallCategory J) (_ : IsCofiltered J) (D : J ⥤ Scheme.{0}) (c : Cone D) (ι : ∀ j, D.obj j ⟶ Y),
      ClopenSys y D c ι ∧ ∀ j, PB q i ((c.π.app j ≫ ι j) ≫ g)) →
  PB q i g

theorem goal_of (hB : Build) (hP : ProEqv) : Cover := by
  intro H q i A _ _ hq P _ _ p hZ
  obtain ⟨Y, k, hk, hs, hY⟩ := hB (P := P)
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace k
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated k
  refine ⟨Y, k, hk, hs, hP H q i A hq (k ≫ p) fun y => ?_⟩
  obtain ⟨J, _, _, D, c, ι, hc, hA, hint⟩ := hY y
  refine ⟨J, inferInstance, inferInstance, D, c, ι, hc, fun j => ?_⟩
  have := hZ c.pt ((c.π.app j ≫ ι j) ≫ k) (hint j) hA
  simpa only [Category.assoc] using this

end LateralTheory.E.CoverCut
end
end

