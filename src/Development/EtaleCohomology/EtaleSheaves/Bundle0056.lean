module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0049
public import Development.EtaleCohomology.EtaleSheaves.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.EtaleCohomology.EtaleSheaves.Bundle0050
public import Development.EtaleCohomology.EtaleSheaves.Bundle0048

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafActSheafPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafActSheafPf
open LateralTheory.E.CupProductRingLaws LateralTheory.E.LeafUnitActPfAug LateralTheory.E.LeafUnitPairPf LateralTheory.E.LeafUnitActPf

section Basic
variable {R : Type} [CommRing R]

theorem res_comp (F : Shv R) {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (y : Sec F U) :
    Sec.res k (Sec.res g y) = Sec.res (k ≫ g) y := by
  change (F.obj.map k.op).hom ((F.obj.map g.op).hom y) = (F.obj.map (k ≫ g).op).hom y
  rw [op_comp, Functor.map_comp]
  rfl

theorem res_smul (F : Shv R) {V U : Scheme.{0}} (g : V ⟶ U) (c : ULift.{1} R) (y : Sec F U) :
    Sec.res g (c • y) = c • Sec.res g y := map_smul (F.obj.map g.op).hom c y

theorem res_add (F : Shv R) {V U : Scheme.{0}} (g : V ⟶ U) (y z : Sec F U) :
    Sec.res g (y + z) = Sec.res g y + Sec.res g z := map_add (F.obj.map g.op).hom y z

theorem map_res {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (y : Sec F U) :
    Sec.res g (Sec.map φ y) = Sec.map φ (Sec.res g y) := by
  have h := congrArg (fun f => f.hom y) (φ.hom.naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h.symm

theorem map_smul' {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (c : ULift.{1} R) (y : Sec F U) :
    Sec.map φ (c • y) = c • Sec.map φ y := map_smul (φ.hom.app (op U)).hom c y

theorem sec_res (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) {V U : Scheme.{0}} (g : V ⟶ U) (x : M.obj Γ(U, ⊤)) :
    Sec.res (F := ofRings R M) g (ofRings.sec M U x) = ofRings.sec M V ((M.map g.appTop).hom x) := by
  have h := congrArg (fun f => f.hom x) ((toSheafify Scheme.etaleTopology.{0} (Scheme.Γ ⋙ M)).naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h.symm

theorem loc_and {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P) (hQ : Loc U Q) :
    Loc U fun V g => P V g ∧ Q V g := by
  obtain ⟨S, hS, h1⟩ := hP
  obtain ⟨T, hT, h2⟩ := hQ
  exact ⟨S ⊓ T, Scheme.etaleTopology.intersection_covering hS hT, fun V g hg => ⟨h1 V g hg.1, h2 V g hg.2⟩⟩

theorem glue (F : Shv R) {U : Scheme.{0}} (S : Sieve U) (hS : S ∈ Scheme.etaleTopology.{0} U)
    (s : ∀ ⦃V : Scheme.{0}⦄ (g : V ⟶ U), S.arrows g → Sec F V)
    (hs : ∀ ⦃V W : Scheme.{0}⦄ (g : V ⟶ U) (hg : S.arrows g) (h : W ⟶ V),
      Sec.res h (s g hg) = s (h ≫ g) (S.downward_closed hg h)) :
    ∃ t : Sec F U, ∀ (V : Scheme.{0}) (g : V ⟶ U) (hg : S.arrows g), Sec.res g t = s g hg := by
  have hsh := F.property (ModuleCat.of (ULift.{1} R) (ULift.{1} R)) S hS
  let x : Presieve.FamilyOfElements (F.obj ⋙ coyoneda.obj (op (ModuleCat.of (ULift.{1} R) (ULift.{1} R)))) S.arrows :=
    fun V g hg => ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ (s g hg))
  have hx : x.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro V W g h hg
    refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
    change (LinearMap.toSpanSingleton _ _ (s (h ≫ g) _)) 1 = (F.obj.map h.op).hom ((LinearMap.toSpanSingleton _ _ (s g hg)) 1)
    simp only [LinearMap.toSpanSingleton_apply, one_smul]
    exact (hs g hg h).symm
  obtain ⟨t, ht, -⟩ := hsh x hx
  refine ⟨t.hom 1, fun V g hg => ?_⟩
  have h1 := congrArg (fun f => f.hom (1 : ULift.{1} R)) (ht g hg)
  change (F.obj.map g.op).hom (t.hom 1) = (LinearMap.toSpanSingleton _ _ (s g hg)) 1 at h1
  simpa [LinearMap.toSpanSingleton_apply] using h1

end Basic

variable {q : ℕ}

theorem etaleTwistZero_sheafifiedSection_of_ring_restrict {V U : Scheme.{0}} (g : V ⟶ U) (x : (twF q 0).obj Γ(U, ⊤)) :
    Sec.res (F := tw q 0) g (ofRings.sec (twF q 0) U x) = ofRings.sec (twF q 0) V (((twF q 0).map g.appTop).hom x) :=
  sec_res (twF q 0) g x

theorem etaleTwistZero_sheafifiedSection_of_ring_add {U : Scheme.{0}} (x y : (twF q 0).obj Γ(U, ⊤)) :
    ofRings.sec (twF q 0) U (x + y) = ofRings.sec (twF q 0) U x + ofRings.sec (twF q 0) U y := by
  unfold ofRings.sec; exact map_add _ x y

theorem sec_smul0 {U : Scheme.{0}} (c : ULift.{1} (ZMod q)) (x : (twF q 0).obj Γ(U, ⊤)) :
    ofRings.sec (twF q 0) U (c • x) = c • ofRings.sec (twF q 0) U x := by
  unfold ofRings.sec; exact map_smul _ c x

theorem etaleTwistZero_augmentation_map_add {V : Scheme.{0}} (x y : (twF q 0).obj Γ(V, ⊤)) :
    aug q Γ(V, ⊤) (x + y) = aug q Γ(V, ⊤) x + aug q Γ(V, ⊤) y := map_add _ _ _

theorem aug_smul0 {V : Scheme.{0}} (c : ULift.{1} (ZMod q)) (x : (twF q 0).obj Γ(V, ⊤)) :
    aug q Γ(V, ⊤) (c • x) = c • aug q Γ(V, ⊤) x := map_smul _ _ _

theorem aug_smul_eq (F : Shv (ZMod q)) {W : Scheme.{0}} (x y : (twF q 0).obj Γ(W, ⊤))
    (h : ofRings.sec (twF q 0) W x = ofRings.sec (twF q 0) W y) (z : Sec F W) :
    aug q Γ(W, ⊤) x • z = aug q Γ(W, ⊤) y • z := by
  apply sec_eq_of_loc
  obtain ⟨S, hS, hP⟩ := etale_tate_twist_zero_sections_eq_locally_of_sheafified_eq q x y h
  refine ⟨S, hS, fun V g hg => ?_⟩
  beta_reduce
  rw [res_smul, res_smul, ← aug_map q g.appTop x, ← aug_map q g.appTop y, hP V g hg]

def Good (F : Shv (ZMod q)) {U : Scheme.{0}} (a : Sec (tw q 0) U) (b t : Sec F U) : Prop :=
  ∀ (V : Scheme.{0}) (g : V ⟶ U) (x : (twF q 0).obj Γ(V, ⊤)), Sec.res g a = ofRings.sec (twF q 0) V x →
    Sec.res g t = aug q Γ(V, ⊤) x • Sec.res g b

theorem good_of_loc (F : Shv (ZMod q)) {U : Scheme.{0}} (a : Sec (tw q 0) U) (b t : Sec F U)
    (h : Loc U fun V g => ∃ x : (twF q 0).obj Γ(V, ⊤), Sec.res g a = ofRings.sec (twF q 0) V x ∧
      Sec.res g t = aug q Γ(V, ⊤) x • Sec.res g b) : Good F a b t := by
  intro V g x hx
  obtain ⟨S, hS, hP⟩ := h
  refine sec_eq_of_loc F _ _ ⟨S.pullback g, Scheme.etaleTopology.pullback_stable g hS, fun W k hk => ?_⟩
  obtain ⟨x', hx', ht⟩ := hP W (k ≫ g) hk
  rw [res_comp, ht, res_smul, res_comp, ← aug_map q k.appTop x]
  apply aug_smul_eq
  rw [← hx', ← res_comp, hx, etaleTwistZero_sheafifiedSection_of_ring_restrict]

theorem good_unique (F : Shv (ZMod q)) {U : Scheme.{0}} (a : Sec (tw q 0) U) (b t₁ t₂ : Sec F U)
    (h₁ : Good F a b t₁) (h₂ : Good F a b t₂) : t₁ = t₂ := by
  obtain ⟨S, hS, hP⟩ := etale_tate_twist_zero_section_locally_lifts_to_ring_value q a
  refine sec_eq_of_loc F t₁ t₂ ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨x, hx⟩ := hP V g hg
  rw [h₁ V g x hx, h₂ V g x hx]

theorem good_exists (F : Shv (ZMod q)) {U : Scheme.{0}} (a : Sec (tw q 0) U) (b : Sec F U) : ∃ t, Good F a b t := by
  obtain ⟨S, hS, hP⟩ := etale_tate_twist_zero_section_locally_lifts_to_ring_value q a
  have key : ∀ {V W : Scheme.{0}} (g : V ⟶ U) (h : W ⟶ V) (x : (twF q 0).obj Γ(V, ⊤)) (x' : (twF q 0).obj Γ(W, ⊤)),
      Sec.res g a = ofRings.sec (twF q 0) V x → Sec.res (h ≫ g) a = ofRings.sec (twF q 0) W x' →
      Sec.res h (aug q Γ(V, ⊤) x • Sec.res g b) = aug q Γ(W, ⊤) x' • Sec.res (h ≫ g) b := by
    intro V W g h x x' e1 e2
    rw [res_smul, res_comp, ← aug_map q h.appTop x]
    apply aug_smul_eq
    rw [← etaleTwistZero_sheafifiedSection_of_ring_restrict, ← e1, res_comp, e2]
  obtain ⟨t, ht⟩ := glue F S hS (fun V g hg => aug q Γ(V, ⊤) (hP V g hg).choose • Sec.res g b)
    (fun V W g hg h => key g h _ _ (hP V g hg).choose_spec (hP W (h ≫ g) (S.downward_closed hg h)).choose_spec)
  exact ⟨t, good_of_loc F a b t ⟨S, hS, fun V g hg => ⟨_, (hP V g hg).choose_spec, ht V g hg⟩⟩⟩

def act (F : Shv (ZMod q)) {U : Scheme.{0}} (a : Sec (tw q 0) U) (b : Sec F U) : Sec F U := (good_exists F a b).choose

theorem act_good (F : Shv (ZMod q)) {U : Scheme.{0}} (a : Sec (tw q 0) U) (b : Sec F U) : Good F a b (act F a b) :=
  (good_exists F a b).choose_spec

theorem act_add_left (F : Shv (ZMod q)) {U : Scheme.{0}} (a₁ a₂ : Sec (tw q 0) U) (b : Sec F U) :
    act F (a₁ + a₂) b = act F a₁ b + act F a₂ b := by
  refine good_unique F _ b _ _ (act_good F _ b) (good_of_loc F _ b _ ?_)
  obtain ⟨S, hS, hP⟩ := loc_and (etale_tate_twist_zero_section_locally_lifts_to_ring_value q a₁) (etale_tate_twist_zero_section_locally_lifts_to_ring_value q a₂)
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨⟨x₁, h₁⟩, ⟨x₂, h₂⟩⟩ := hP V g hg
  refine ⟨x₁ + x₂, by rw [res_add, h₁, h₂]; exact (etaleTwistZero_sheafifiedSection_of_ring_add x₁ x₂).symm, ?_⟩
  rw [res_add, act_good F a₁ b V g x₁ h₁, act_good F a₂ b V g x₂ h₂, etaleTwistZero_augmentation_map_add, add_smul]

theorem act_smul_left (F : Shv (ZMod q)) {U : Scheme.{0}} (c : ULift.{1} (ZMod q)) (a : Sec (tw q 0) U) (b : Sec F U) :
    act F (c • a) b = c • act F a b := by
  refine good_unique F _ b _ _ (act_good F _ b) (good_of_loc F _ b _ ?_)
  obtain ⟨S, hS, hP⟩ := etale_tate_twist_zero_section_locally_lifts_to_ring_value q a
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨x, h⟩ := hP V g hg
  refine ⟨c • x, by rw [res_smul, h]; exact (sec_smul0 c x).symm, ?_⟩
  rw [res_smul, act_good F a b V g x h, aug_smul0, smul_eq_mul, mul_smul]

theorem act_add_right (F : Shv (ZMod q)) {U : Scheme.{0}} (a : Sec (tw q 0) U) (b₁ b₂ : Sec F U) :
    act F a (b₁ + b₂) = act F a b₁ + act F a b₂ := by
  refine good_unique F a _ _ _ (act_good F a _) (fun V g x hx => ?_)
  rw [res_add, res_add, act_good F a b₁ V g x hx, act_good F a b₂ V g x hx, smul_add]

theorem act_smul_right (F : Shv (ZMod q)) {U : Scheme.{0}} (c : ULift.{1} (ZMod q)) (a : Sec (tw q 0) U) (b : Sec F U) :
    act F a (c • b) = c • act F a b := by
  refine good_unique F a _ _ _ (act_good F a _) (fun V g x hx => ?_)
  rw [res_smul, res_smul, act_good F a b V g x hx, smul_comm]

theorem act_res (F : Shv (ZMod q)) {V U : Scheme.{0}} (g : V ⟶ U) (a : Sec (tw q 0) U) (b : Sec F U) :
    Sec.res g (act F a b) = act F (Sec.res g a) (Sec.res g b) := by
  refine good_unique F _ _ _ _ (fun W k x hx => ?_) (act_good F _ _)
  rw [res_comp, res_comp]
  exact act_good F a b W (k ≫ g) x (by rw [← res_comp]; exact hx)

theorem act_map {F G : Shv (ZMod q)} (φ : F ⟶ G) {U : Scheme.{0}} (a : Sec (tw q 0) U) (b : Sec F U) :
    Sec.map φ (act F a b) = act G a (Sec.map φ b) := by
  refine good_unique G a _ _ _ (fun V g x hx => ?_) (act_good G a _)
  rw [map_res, act_good F a b V g x hx, map_smul', map_res]

theorem act_gen (F : Shv (ZMod q)) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) (b : Sec F U) : act F (twGen 0 ζ) b = b := by
  refine good_unique F _ b _ _ (act_good F _ b) (fun V g x hx => ?_)
  let y : (twF q 0).obj Γ(U, ⊤) := Submodule.Quotient.mk (Finsupp.single ζ 1)
  have e : aug q Γ(V, ⊤) (((twF q 0).map g.appTop).hom y) = 1 := (aug_map q g.appTop y).trans (aug_mk_single q ζ)
  have hs : ofRings.sec (twF q 0) V (((twF q 0).map g.appTop).hom y) = ofRings.sec (twF q 0) V x := by
    rw [← hx]; exact (etaleTwistZero_sheafifiedSection_of_ring_restrict g y).symm
  exact (one_smul _ _).symm.trans ((congrArg (· • Sec.res g b) e).symm.trans (aug_smul_eq F _ x hs _))

theorem LeafActSheaf_of : LeafActSheaf := by
  intro q _
  refine ⟨fun F U => LinearMap.mk₂ (ULift.{1} (ZMod q)) (fun a b => act F a b)
    (act_add_left F) (act_smul_left F) (act_add_right F) (act_smul_right F), ?_, ?_, ?_⟩
  · intro F V U g a b
    exact act_res F g a b
  · intro F G φ U a b
    exact act_map φ a b
  · intro F U ζ b
    exact act_gen F ζ b

end LateralTheory.E.LeafActSheafPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafDimOpenPf
section
open AlgebraicGeometry CategoryTheory LateralTheory.E.E4 Topology

namespace LateralTheory.E.LeafDimOpenPf

theorem dim_mono {X : Type*} [TopologicalSpace X] {S T : Set X} (h : S ⊆ T) :
    topologicalKrullDim S ≤ topologicalKrullDim T :=
  (IsEmbedding.inclusion h).isInducing.topologicalKrullDim_le

theorem dim_basicOpen (k A : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] (g : A) (hg : g ≠ 0) {n : ℕ} (hn : Algebra.trdeg k A = n) :
    topologicalKrullDim (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A)) = n := by
  let B := Localization.Away g
  have hle : Submonoid.powers g ≤ nonZeroDivisors A := powers_le_nonZeroDivisors_of_noZeroDivisors hg
  have : IsDomain B := IsLocalization.isDomain_localization hle
  have : Algebra.FiniteType A B := inferInstance
  have : Algebra.FiniteType k B := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  have : FaithfulSMul A B :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsLocalization.injective B hle)
  have : Algebra.IsAlgebraic A B := IsLocalization.isAlgebraic B (Submonoid.powers g)
  have htr : Algebra.trdeg k B = n := by
    rw [GlobalTheory.trdeg_eq_of_isAlgebraic_top k A B, hn]
  rw [GlobalTheory.topologicalKrullDim_eq_of_isEmbedding
      (PrimeSpectrum.localization_away_isOpenEmbedding B g).isEmbedding
      (PrimeSpectrum.localization_away_comap_range B g),
    PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, GlobalTheory.ringKrullDim_eq_of_trdeg_eq k B htr]

theorem LeafDimOpen_of : LateralTheory.E.LeafCloseBCut.LeafDimOpen := by
  intro k _ X b _ hX U hU hne
  obtain ⟨x0, hx0⟩ := hne
  obtain ⟨A0, _, _, _, _, _, j0, _, ⟨p0, hp0⟩, -, htr0⟩ := GlobalTheory.exists_affine_chart_trdeg_eq b x0
  obtain ⟨n, -, htn⟩ := GlobalTheory.exists_ringKrullDim_eq_and_trdeg_eq k A0
  have hK := htr0.symm.trans htn
  have hup : topologicalKrullDim X ≤ n := by
    refine GlobalTheory.topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_
    obtain ⟨A, _, _, _, _, _, j, _, hx, -, htr⟩ := GlobalTheory.exists_affine_chart_trdeg_eq b x
    refine ⟨Set.range j, j.isOpenEmbedding.isOpen_range, hx, le_of_eq ?_⟩
    rw [GlobalTheory.topologicalKrullDim_eq_of_isEmbedding j.isOpenEmbedding.isEmbedding rfl]
    exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A).trans
      (GlobalTheory.ringKrullDim_eq_of_trdeg_eq k A (htr.trans hK))
  refine hup.trans ?_
  have hVo : IsOpen (j0 ⁻¹' U) := hU.preimage j0.isOpenEmbedding.continuous
  have hpV : p0 ∈ j0 ⁻¹' U := by simpa [Set.mem_preimage, hp0] using hx0
  obtain ⟨_, ⟨g, rfl⟩, hpg, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hpV hVo
  have hg : g ≠ 0 := by
    rintro rfl; exact (PrimeSpectrum.mem_basicOpen _ _).mp hpg (Ideal.zero_mem _)
  have hd := dim_basicOpen k A0 g hg htn
  calc (n : WithBot ℕ∞) = topologicalKrullDim (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A0)) := hd.symm
    _ = topologicalKrullDim (j0 '' (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum A0))) :=
      (GlobalTheory.topologicalKrullDim_eq_of_isEmbedding
        (j0.isOpenEmbedding.isEmbedding.comp IsEmbedding.subtypeVal)
        (by rw [Set.range_comp]; exact congrArg _ Subtype.range_coe)).symm
    _ ≤ topologicalKrullDim U := dim_mono (by rintro _ ⟨q, hq, rfl⟩; exact hsub hq)

end LateralTheory.E.LeafDimOpenPf
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafExtTensPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafExtTensPf

theorem res_isKInjective (R : Type) [CommRing R] (F : Shv R) : (res R F).IsKInjective := by
  unfold res; infer_instance

theorem res_injective (R : Type) [CommRing R] (F : Shv R) (n : ℤ) : Injective ((res R F).X n) := by
  unfold res
  rw [InjectiveResolution.cochainComplex]
  by_cases h : ∃ k : ℕ, ComplexShape.embeddingUpNat.f k = n
  · obtain ⟨k, hk⟩ := h
    exact Injective.of_iso (HomologicalComplex.extendXIso _ _ hk).symm inferInstance
  · push_neg at h
    exact (HomologicalComplex.isZero_extend_X _ _ n h).injective

section
variable {C : Type*} [Category C] [Abelian C]

theorem exact_lift {S T L : CochainComplex C ℤ} (ι : S ⟶ T) [∀ n, Mono (ι.f n)] [∀ n, Injective (L.X n)]
    (u : S ⟶ L) (g0 : T ⟶ L) (H : Homotopy u (ι ≫ g0)) : ∃ g : T ⟶ L, ι ≫ g = u := by
  let h' : ∀ i j, T.X i ⟶ L.X j := fun i j => Injective.factorThru (H.hom i j) (ι.f i)
  have hh : (fun i j => ι.f i ≫ h' i j) = H.hom := by
    funext i j; exact Injective.comp_factorThru _ _
  refine ⟨g0 + Homotopy.nullHomotopicMap h', ?_⟩
  rw [Preadditive.comp_add, Homotopy.comp_nullHomotopicMap, hh]
  ext n
  rw [H.comm n]
  simp only [HomologicalComplex.add_f_apply]
  change _ + (dNext n H.hom + prevD n H.hom) = _
  abel

theorem homotopy_lift {S T L : CochainComplex C ℤ} (ι : S ⟶ T) [QuasiIso ι] [L.IsKInjective]
    (u : S ⟶ L) : ∃ g0 : T ⟶ L, Nonempty (Homotopy u (ι ≫ g0)) := by
  let _ := HasDerivedCategory.standard C
  let qt := (HomotopyCategory.quotient C (ComplexShape.up ℤ))
  have hi : IsIso (DerivedCategory.Qh.map (qt.map ι)) := by
    have e := (DerivedCategory.quotientCompQhIso C).hom.naturality ι
    have : IsIso (DerivedCategory.Q.map ι) := by
      rw [DerivedCategory.isIso_Q_map_iff_quasiIso]; infer_instance
    have e2 : DerivedCategory.Qh.map (qt.map ι) = (DerivedCategory.quotientCompQhIso C).hom.app S ≫
        DerivedCategory.Q.map ι ≫ (DerivedCategory.quotientCompQhIso C).inv.app T := by
      simp only [Functor.comp_map] at e
      rw [← reassoc_of% e]; simp [qt]
    rw [e2]; infer_instance
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective (qt.obj T) L).surjective
    (inv (DerivedCategory.Qh.map (qt.map ι)) ≫ DerivedCategory.Qh.map (qt.map u))
  obtain ⟨g0, rfl⟩ := qt.map_surjective g
  refine ⟨g0, ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
  apply (CochainComplex.IsKInjective.Qh_map_bijective (qt.obj S) L).injective
  rw [Functor.map_comp, Functor.map_comp, hg, IsIso.hom_inv_id_assoc]

theorem extAlongQIso {S T L : CochainComplex C ℤ} (ι : S ⟶ T) (hm : ∀ n, Mono (ι.f n)) (hq : QuasiIso ι)
    (hk : L.IsKInjective) (hinj : ∀ n, Injective (L.X n)) (u : S ⟶ L) : ∃ g : T ⟶ L, ι ≫ g = u := by
  obtain ⟨g0, ⟨H⟩⟩ := homotopy_lift ι u
  exact exact_lift ι u g0 H
end

def LeafTensMono : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) {S T : Cx (ZMod q)} (σ : Pair (sgl (tw q 0)) (res _ (tw q i)) S)
  (τ : Pair (res _ (tw q 0)) (res _ (tw q i)) T), σ.IsTensor → τ.IsTensor → ∀ ι : S ⟶ T,
  (∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec ((sgl (tw q 0)).X s) U) (b : Sec ((res _ (tw q i)).X t) U),
    Sec.map (ι.f w) (σ.mul U s t w h a b) = τ.mul U s t w h (Sec.map ((resAug (tw q 0)).f s) a) b) →
  ∀ n, Mono (ι.f n)

def LeafTensQIso : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) {S T : Cx (ZMod q)} (σ : Pair (sgl (tw q 0)) (res _ (tw q i)) S)
  (τ : Pair (res _ (tw q 0)) (res _ (tw q i)) T), σ.IsTensor → τ.IsTensor → ∀ ι : S ⟶ T,
  (∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec ((sgl (tw q 0)).X s) U) (b : Sec ((res _ (tw q i)).X t) U),
    Sec.map (ι.f w) (σ.mul U s t w h a b) = τ.mul U s t w h (Sec.map ((resAug (tw q 0)).f s) a) b) →
  QuasiIso ι

theorem LeafExtTens_of (hmono : LeafTensMono) (hqiso : LeafTensQIso) : LateralTheory.E.LeafPairExtPf2.LeafExtTens := by
  intro q _ i S T σ τ hσ hτ ι hι u
  exact extAlongQIso ι (hmono q i σ τ hσ hτ ι hι) (hqiso q i σ τ hσ hτ ι hι) (res_isKInjective _ _)
    (res_injective _ _) u

end LateralTheory.E.LeafExtTensPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafGlueExtendPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Topology

namespace LateralTheory.E.LeafGlueExtendPf

lemma dominant_of_generic {C W : Scheme.{0}} (e : W ⟶ C) [IsOpenImmersion e] (x : C)
    (hx : IsGenericPoint x (⊤ : Set C)) (g : Spec (C.presheaf.stalk x) ⟶ W)
    (hg : g ≫ e = C.fromSpecStalk x) : IsDominant g := by
  constructor
  rw [denseRange_iff_closure_range, Set.eq_univ_iff_forall]
  intro w
  obtain ⟨pt, hpt⟩ : ∃ pt : Spec (C.presheaf.stalk x), C.fromSpecStalk x pt = x :=
    ⟨_, Scheme.fromSpecStalk_closedPoint⟩
  rw [← hg] at hpt
  have he : e (g pt) = x := hpt
  have hmem : g pt ∈ Set.range g := ⟨_, rfl⟩
  have h1 : closure ({g pt} : Set W) ⊆ closure (Set.range g) :=
    closure_mono (Set.singleton_subset_iff.mpr hmem)
  apply h1
  rw [e.isOpenEmbedding.isEmbedding.closure_eq_preimage_closure_image, Set.image_singleton, he]
  show e w ∈ closure {x}
  rw [show closure ({x} : Set C) = (⊤ : Set C) from hx]
  trivial

theorem LeafGlueExtend_of : LateralTheory.E.LeafExtendCut.LeafGlueExtend := by
  intro C X S _ sC p _ x hx ψ H
  choose U hyU hxU f hf1 hf2 using H
  let 𝒰 : C.OpenCover := Scheme.Cover.mkOfCovers C (fun y => (U y).toScheme) (fun y => (U y).ι)
    (fun y => ⟨y, ⟨y, hyU y⟩, rfl⟩)
  have hcompat0 : ∀ i j : C,
      pullback.fst (U i).ι (U j).ι ≫ f i = pullback.snd (U i).ι (U j).ι ≫ f j := by
    intro i j
    have : IsReduced (pullback (U i).ι (U j).ι) :=
      isReduced_of_isOpenImmersion (pullback.fst (U i).ι (U j).ι ≫ (U i).ι)
    let g := pullback.lift ((U i).fromSpecStalkOfMem x (hxU i))
      ((U j).fromSpecStalkOfMem x (hxU j))
      (by rw [Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.Opens.fromSpecStalkOfMem_ι])
    have : IsDominant g :=
      dominant_of_generic (pullback.fst (U i).ι (U j).ι ≫ (U i).ι) x hx g
        (by simp only [g, pullback.lift_fst_assoc, Scheme.Opens.fromSpecStalkOfMem_ι])
    refine ext_of_isDominant_of_isSeparated p ?_ g ?_
    · simp only [Category.assoc, hf2]; rw [pullback.condition_assoc]
    · rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc, hf1, hf1]
  have hcompat : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ f i = pullback.snd _ _ ≫ f j :=
    fun i j => hcompat0 i j
  refine ⟨𝒰.glueMorphisms f hcompat, ?_, ?_⟩
  · have := 𝒰.ι_glueMorphisms f hcompat x
    rw [← (U x).fromSpecStalkOfMem_ι x (hxU x), Category.assoc]
    change _ ≫ 𝒰.f x ≫ _ = _
    rw [this]
    exact hf1 x
  · refine Scheme.Cover.hom_ext 𝒰 _ _ (fun y => ?_)
    rw [𝒰.ι_glueMorphisms_assoc f hcompat y]
    exact hf2 y

end LateralTheory.E.LeafGlueExtendPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafInj0Of
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafInj0Pf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut

theorem cov_of_pts {B : Scheme.{0}} {U : B.Etale} {P : ∀ U' : B.Etale, (U' ⟶ U) → Prop}
    (h : ∀ x : U.left, ∃ (U' : B.Etale) (a : U' ⟶ U) (y : U'.left), a.left y = x ∧
      Cov U' (fun U'' b => P U'' (b ≫ a))) : Cov U P := by
  choose U' a y hy hC using h
  choose T hT hP using hC
  let R : Sieve U :=
    { arrows := fun {Z} g => ∃ x, ∃ b : Z ⟶ U' x, T x b ∧ g = b ≫ a x
      downward_closed := by
        rintro Z W g ⟨x, b, hb, rfl⟩ h
        exact ⟨x, h ≫ b, (T x).downward_closed hb h, by simp⟩ }
  refine ⟨R, ?_, ?_⟩
  · have h0 : Sieve.ofArrows U' a ∈ (EtTop B) U := by
      rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
      ext z
      simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
      exact ⟨z, y z, hy z⟩
    refine (EtTop B).transitive h0 R ?_
    intro Z f hf
    obtain ⟨W, g, f', hf', rfl⟩ := hf
    cases hf' with
    | mk x =>
      refine (EtTop B).superset_covering ?_ ((EtTop B).pullback_stable g (hT x))
      intro V c hc
      exact ⟨x, c ≫ g, hc, by simp⟩
  · rintro Z g ⟨x, b, hb, rfl⟩
    exact hP x Z b hb

def LeafInj0W : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale), ∀ c : Hrel (ZMod q) (sch.map (prB ι U)) (tw q i) 0,
  ∀ x : U.left, U.hom x ∈ Set.range ι →
  ∃ (U' : B.Etale) (a : U' ⟶ U) (y : U'.left), a.left y = x ∧ Cov U' (fun U'' b => rB q i ι (b ≫ a) 0 c = 0)

def LeafInj0V : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  SHV q i V p g1 g2 → ∀ (U : B.Etale), ∀ c : Hrel (ZMod q) (sch.map (prB ι U)) (tw q i) 0,
  Cov U (fun U' a => rY q i (g2 ≫ g1 ≫ p) ι a 0 (bY q i (g2 ≫ g1 ≫ p) ι U 0 c) = 0) →
  ∀ x : U.left, U.hom x ∉ Set.range ι →
  ∃ (U' : B.Etale) (a : U' ⟶ U) (y : U'.left), a.left y = x ∧ Cov U' (fun U'' b => rB q i ι (b ≫ a) 0 c = 0)

theorem LeafInj0_of (hW : LeafInj0W) (hV : LeafInj0V) : LateralTheory.E.LeafDegCut.LeafInj0 := by
  intro hH q _ k _ hq i B W Y0 Y1 Y2 s ι _ V hV' p g1 g2 hp1 hp2 hp3 hS U c hc
  apply cov_of_pts
  intro x
  by_cases hx : U.hom x ∈ Set.range ι
  · exact hW hH q k hq i s ι V hV' p g1 g2 hp1 hp2 hp3 hS U c x hx
  · exact hV hH q k hq i s ι V hV' p g1 g2 hp1 hp2 hp3 hS U c hc x hx
end LateralTheory.E.LeafInj0Pf
end
end

