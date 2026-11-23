module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
public import Development.EtaleCohomology.EtaleSheaves.Bundle0056

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafStalkSmoothClosedPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 Order

namespace LateralTheory.E.LeafStalkSmoothClosedPf

theorem coheight_le_topDim {X : Scheme.{0}} (x : X) :
    (coheight x : WithBot ℕ∞) ≤ topologicalKrullDim X := by
  let := specializationOrder X
  have h := coheight_le_krullDim
    (irreducibleSetEquivPoints.symm x : TopologicalSpace.IrreducibleCloseds X)
  rwa [coheight_orderIso] at h

theorem stalk_not_isField {X : Scheme.{0}} [IsIntegral X] (y : X) (hy : y ≠ genericPoint X) :
    ¬ IsField (X.presheaf.stalk y) := by
  intro hF
  let := hF.toField
  have h0 : ringKrullDim (X.presheaf.stalk y) = 0 := ringKrullDim_eq_zero_of_field _
  rw [ringKrullDim_stalk_eq_coheight] at h0
  have hc : coheight y = 0 := by exact_mod_cast h0
  rw [coheight_eq_zero] at hc
  have h1 : y ≤ genericPoint X := genericPoint_specializes y
  have h2 : genericPoint X ≤ y := hc h1
  exact hy (Specializes.antisymm (h2 : y ⤳ genericPoint X) (h1 : genericPoint X ⤳ y)).eq

theorem stalk_dvr {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (y : X)
    (hn : IsIntegrallyClosed (X.presheaf.stalk y)) (hd : topologicalKrullDim X = 1)
    (hy : y ≠ genericPoint X) : IsDiscreteValuationRing (X.presheaf.stalk y) := by
  have hc : coheight y ≤ 1 := by
    have := (coheight_le_topDim y).trans hd.le
    exact_mod_cast this
  have : Ring.KrullDimLE 1 (X.presheaf.stalk y) := krullDimLE_of_coheight_le hc
  have : Ring.DimensionLEOne (X.presheaf.stalk y) :=
    ⟨fun hp hprime => hprime.isMaximal_of_ne_bot hp⟩
  have : IsDedekindDomain (X.presheaf.stalk y) := {}
  exact ((IsDiscreteValuationRing.TFAE _ (stalk_not_isField y hy)).out 3 1).mp this

set_option backward.isDefEq.respectTransparency false in
theorem LeafStalkSmoothClosed_of : LateralTheory.E.LeafSmoothOfNormalPf.LeafStalkSmoothClosed := by
  intro Ω _ _ C c _ hc hn hd y hy
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian c
  have := hn y
  have : IsDiscreteValuationRing (C.presheaf.stalk y) := stalk_dvr y (hn y) hd hy
  have hE := LocallyOfFiniteType.stalkMap c y
  algebraize [(c.stalkMap y).hom]
  let p : Spec (CommRingCat.of Ω) := c y
  let K' := (Spec.structureSheaf Ω).presheaf.stalk p
  let e : Ω ≃ₐ[Ω] K' := IsLocalization.atUnits _ p.asIdeal.primeCompl
      (fun x hx ↦ by aesop (add simp IsUnit.mem_submonoid_iff))
  have : Algebra.IsAlgebraic Ω K' := .of_injective e.symm.toAlgHom e.symm.injective
  let : Field K' := (e.toRingEquiv.symm.isField (Field.toIsField Ω)).toField
  let : Field ((Sp Ω).presheaf.stalk (c y)) := this
  have : PerfectField ((Sp Ω).presheaf.stalk (c y)) :=
    Algebra.IsAlgebraic.perfectField (K := Ω) (L := (Spec.structureSheaf Ω).presheaf.stalk p)
  exact GlobalTheory.formallySmooth_of_isRegularLocalRing_of_perfectField _ _

end LateralTheory.E.LeafStalkSmoothClosedPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafTensMonoPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafTensMonoPf
open LateralTheory.E.LeafTwPairExistsPf LateralTheory.E.LeafPairExtPf2

section
variable {R : Type} [CommRing R]

theorem res_comp {F : Shv R} {W V U : Scheme.{0}} (h : W ⟶ V) (g : V ⟶ U) (y : Sec F U) :
    Sec.res (h ≫ g) y = Sec.res h (Sec.res g y) := by
  simp [Sec.res]

theorem loc_trans {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Loc V fun W k => Q W (k ≫ g)) : Loc U Q := by
  classical
  obtain ⟨S, hS, hP⟩ := h
  let T : ∀ ⦃V : Scheme.{0}⦄ ⦃f : V ⟶ U⦄, S.arrows f → Sieve V := fun V f hf =>
    Classical.choose (hPQ V f (hP V f hf))
  refine ⟨Sieve.bind S.arrows T, (Scheme.etaleTopology.{0}).bind_covering hS
    (fun V f hf => (Classical.choose_spec (hPQ V f (hP V f hf))).1), ?_⟩
  rintro W _ ⟨V, k, f, hf, hk, rfl⟩
  exact (Classical.choose_spec (hPQ V f (hP V f hf))).2 W k hk

theorem eq_zero_of_loc {F : Shv R} {U : Scheme.{0}} (y : Sec F U) (h : Loc U fun _ g => Sec.res g y = 0) : y = 0 := by
  obtain ⟨S, hS, hP⟩ := h
  let e : ModuleCat.of (ULift.{1} R) (ULift.{1} R) ⟶ F.obj.obj (op U) :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ y)
  have := F.property.hom_ext ⟨S, hS⟩ e 0 (fun I => by
    ext1; apply LinearMap.ext_ring
    have := hP _ I.f I.hf
    simpa [e] using this)
  have h2 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom this) 1
  simpa [e] using h2

theorem mono_of_loc {F G : Shv R} (f : F ⟶ G)
    (h : ∀ (U : Scheme.{0}) (y : Sec F U), Sec.map f y = 0 → Loc U fun _ g => Sec.res g y = 0) : Mono f := by
  have : Mono ((sheafToPresheaf _ _).map f) := by
    have hm : ∀ U, Mono (((sheafToPresheaf Scheme.etaleTopology (ModuleCat (ULift.{1, 0} R))).map f).app U) := by
      intro U
      rw [ModuleCat.mono_iff_injective, injective_iff_map_eq_zero]
      intro y hy
      exact eq_zero_of_loc y (h U.unop y hy)
    exact NatTrans.mono_of_mono_app _
  exact (sheafToPresheaf _ _).mono_of_mono_map this

theorem lift_res {I J K : Cx R} (μ : Pair I J K) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens I J U w) :
    μ.lift V w (Tens.res g w x) = Sec.res g (μ.lift U w x) := by
  have : (μ.lift V w).comp (Tens.res g w) = ((K.X w).obj.map g.op).hom.comp (μ.lift U w) := by
    apply DirectSum.linearMap_ext; intro p
    apply TensorProduct.ext'; intro a b
    simp [Pair.lift, Tens.res]
    exact (μ.nat g _ _ _ p.2 a b).symm
  exact LinearMap.congr_fun this x

theorem lift_compat {I J K K' : Cx R} (σ : Pair I J K) (ν : Pair I J K') (ι : K ⟶ K')
    (h : ∀ (U : Scheme.{0}) (s t w : ℤ) (hw : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
      Sec.map (ι.f w) (σ.mul U s t w hw a b) = ν.mul U s t w hw a b) (U : Scheme.{0}) (w : ℤ) (x : Tens I J U w) :
    Sec.map (ι.f w) (σ.lift U w x) = ν.lift U w x := by
  have : ((ι.f w).hom.app (op U)).hom.comp (σ.lift U w) = ν.lift U w := by
    apply DirectSum.linearMap_ext; intro p
    apply TensorProduct.ext'; intro a b
    simp [Pair.lift]
    exact h U _ _ _ p.2 a b
  exact LinearMap.congr_fun this x
end

def LeafTw0LocSplit : Prop := ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (n : ℕ) (a : Fin n → Sec ((sgl (tw q 0)).X 0) U),
  Loc U fun V g => ∃ (e : Sec ((sgl (tw q 0)).X 0) V) (c : Fin n → ULift.{1} (ZMod q)),
    (∀ k, Sec.res g (a k) = c k • e) ∧
    (e = 0 ∨ ∃ r : Sec ((res _ (tw q 0)).X 0) V →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q),
      r (Sec.map ((resAug (tw q 0)).f 0) e) = 1)

def LeafPreTensLocInj : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) {T : Cx (ZMod q)} (τ : Pair (res _ (tw q 0)) (res _ (tw q i)) T),
  τ.IsTensor → ∀ (U : Scheme.{0}) (w : ℤ) (x : Tens (sgl (tw q 0)) (res _ (tw q i)) U w),
  (pre τ (resAug (tw q 0))).lift U w x = 0 → Loc U fun _ g => Tens.res g w x = 0

theorem LeafTensMono_of (hL : LeafPreTensLocInj) : LateralTheory.E.LeafExtTensPf.LeafTensMono := by
  intro q _ i S T σ τ hσ hτ ι hι n
  apply mono_of_loc
  intro U y hy
  have hc := lift_compat σ (pre τ (resAug (tw q 0))) ι (fun U s t w hw a b => hι U s t w hw a b)
  refine loc_trans (hσ.1 U n y) ?_
  rintro V g ⟨x, hx⟩
  have h0 : (pre τ (resAug (tw q 0))).lift V n x = 0 := by
    rw [← hc, hx, ← res_map, hy]; simp
  obtain ⟨S', hS', hP'⟩ := hL q i τ hτ V n x h0
  exact ⟨S', hS', fun W k hk => by
    show Sec.res (k ≫ g) y = 0
    have hk' : Tens.res k n x = 0 := hP' W k hk
    rw [res_comp, ← hx, ← lift_res, hk', map_zero]⟩

end LateralTheory.E.LeafTensMonoPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafTensQIsoPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafTensQIsoPf

def LeafSecInj : Prop := ∀ (R : Type) [CommRing R] (F : Shv R), Injective F → ∀ U : Scheme.{0},
  Module.Injective (ULift.{1} R) (Sec F U)

def LeafZModInjFlat : Prop := ∀ (q : ℕ) [NeZero q] (M : Type 1) [AddCommGroup M] [Module (ULift.{1} (ZMod q)) M],
  Module.Injective (ULift.{1} (ZMod q)) M → Module.Flat (ULift.{1} (ZMod q)) M

def LeafTensQIsoGen : Prop := ∀ (R : Type) [CommRing R] {I I' J S T : Cx R} (f : I ⟶ I'), QuasiIso f →
  I.IsStrictlyGE 0 → I'.IsStrictlyGE 0 → J.IsStrictlyGE 0 →
  (∀ (n : ℤ) (U : Scheme.{0}), Module.Flat (ULift.{1} R) (Sec (J.X n) U)) →
  ∀ (σ : Pair I J S) (τ : Pair I' J T), σ.IsTensor → τ.IsTensor → ∀ ι : S ⟶ T,
  (∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
    Sec.map (ι.f w) (σ.mul U s t w h a b) = τ.mul U s t w h (Sec.map (f.f s) a) b) →
  QuasiIso ι

theorem resAug_quasiIso (R : Type) [CommRing R] (F : Shv R) : QuasiIso (resAug F) := by
  unfold resAug; exact @InjectiveResolution.instQuasiIsoIntι' _ _ _ _ _

theorem res_strictlyGE (R : Type) [CommRing R] (F : Shv R) : (res R F).IsStrictlyGE 0 := by
  unfold res; infer_instance

theorem sgl_strictlyGE (R : Type) [CommRing R] (F : Shv R) : (sgl F).IsStrictlyGE 0 := by
  infer_instance

theorem LeafTensQIso_of (hgen : LeafTensQIsoGen) (hinj : LeafSecInj) (hflat : LeafZModInjFlat) :
    LateralTheory.E.LeafExtTensPf.LeafTensQIso := by
  intro q _ i S T σ τ hσ hτ ι hι
  exact hgen (ZMod q) (resAug (tw q 0)) (resAug_quasiIso _ _) (sgl_strictlyGE _ _) (res_strictlyGE _ _)
    (res_strictlyGE _ _) (fun n U => hflat q _ (hinj _ _ (LateralTheory.E.LeafExtTensPf.res_injective _ _ n) U)) σ τ hσ hτ ι hι

end LateralTheory.E.LeafTensQIsoPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafVanVPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.LeafVanVPf

theorem free_empty (R : Type) [CommRing R] (X : Scheme.{0}) [IsEmpty X] : IsZero ((free R).obj (yoneda.obj X)) := by
  have key : ∀ (F : Shv R) (f g : (freeP R).obj (yoneda.obj X) ⟶ F.obj), f = g := by
    intro F f g
    ext1
    funext U
    by_cases hU : IsEmpty U.unop
    · have hb : ⊥ ∈ Scheme.etaleTopology U.unop := Scheme.bot_mem_grothendieckTopology _
      exact (Sheaf.isTerminalOfBotCover F U.unop hb).hom_ext _ _
    · apply ModuleCat.free_hom_ext
      rintro ⟨x⟩
      exfalso
      apply hU
      exact ⟨fun u => IsEmpty.false ((show U.unop ⟶ X from x) u)⟩
  rw [IsZero.iff_id_eq_zero]
  apply ((sheafificationAdjunction Scheme.etaleTopology (ModuleCat.{1} (ULift.{1} R))).homEquiv _ _).injective
  exact key _ _ _

theorem chains_empty (R : Type) [CommRing R] (X : Scheme.{0}) [IsEmpty X] (n : ℤ) :
    IsZero (((chains R).obj (sch.obj X)).X n) := by
  by_cases h : n ≤ 0
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, n = -(p : ℤ) := ⟨(-n).toNat, by omega⟩
    exact (free_empty R X).of_iso (chainsXIso R _ p)
  · refine HomologicalComplex.isZero_extend_X ((chainsN R).obj (sch.obj X)) ComplexShape.embeddingDownNat n ?_
    intro i hi
    change -(i : ℤ) = n at hi
    omega

theorem isIso_inr {C : Type*} [Category C] [Abelian C] {K L : CochainComplex C ℤ} (φ : K ⟶ L)
    (h : ∀ n, IsZero (K.X n)) : IsIso (mappingCone.inr φ) := by
  have : ∀ n, IsIso ((mappingCone.inr φ).f n) := fun n =>
    ⟨(mappingCone.snd φ).v n n (add_zero n), by simp, by
      rw [← mappingCone.id_X φ n (n + 1) rfl, (h (n + 1)).eq_of_tgt ((mappingCone.fst φ).1.v n (n + 1) rfl) 0]
      simp⟩
  exact HomologicalComplex.Hom.isIso_of_components _

theorem subsingleton_of_iso {R : Type} [CommRing R] {K L : Cx R} (f : K ⟶ L) [IsIso f] (F : Shv R) (m : ℤ)
    (h : Subsingleton (HK R K F m)) : Subsingleton (HK R L F m) := by
  have key : ∀ x : HK R L F m, HK.pull R (inv f) F m (HK.pull R f F m x) = x := by
    intro x
    obtain ⟨x, rfl⟩ := x.mk_surjective
    refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
    simp only [zcomp, Cocycle.mk_coe, Cocycle.ofHom_coe]
    rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp, IsIso.inv_hom_id, Cochain.id_comp]
  exact ⟨fun x y => by rw [← key x, ← key y, Subsingleton.elim (HK.pull R f F m x) (HK.pull R f F m y)]⟩

theorem LeafVanV_of : LateralTheory.E.LeafVan0Pf.LeafVanV := by
  intro _ q _ i B W Y S ι p s hs m hm
  have he : IsEmpty ↥(pullback (pullback.snd p s ≫ s) ι : Scheme.{0}) := ⟨fun z => by
    refine hs (pullback.snd p s (pullback.fst (pullback.snd p s ≫ s) ι z)) ⟨pullback.snd (pullback.snd p s ≫ s) ι z, ?_⟩
    have hc := congrArg (fun f => f z) (pullback.condition (f := pullback.snd p s ≫ s) (g := ι))
    simpa using hc.symm⟩
  have := isIso_inr ((chains (ZMod q)).map (sch.map (LateralTheory.E.LeafVan0Pf.prS p ι s))) (chains_empty _ _)
  exact subsingleton_of_iso (mappingCone.inr _) _ m hm

end LateralTheory.E.LeafVanVPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafVanWPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.LeafVanWPf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.LeafVan0Pf

section Cone
variable {C : Type*} [Category C] [Preadditive C] {K L M : CochainComplex C ℤ} (φ : K ⟶ L) [HomologicalComplex.HasHomotopyCofiber φ]

theorem desc_δ {n m : ℤ} (α : Cochain K M m) (β : Cochain L M n) (h : m + 1 = n) (n' : ℤ) (hn' : n + 1 = n') :
    δ n n' (mappingCone.descCochain φ α β h) =
      mappingCone.descCochain φ (δ m n α + n'.negOnePow • (Cochain.ofHom φ).comp β (zero_add n)) (δ n n' β) hn' := by
  rw [mappingCone.δ_descCochain φ α β h n' hn']; rfl

theorem desc_eq_zero {n m : ℤ} {α : Cochain K M m} {β : Cochain L M n} {h : m + 1 = n}
    (H : mappingCone.descCochain φ α β h = 0) : α = 0 ∧ β = 0 := by
  constructor
  · have := mappingCone.inl_descCochain φ α β h
    rw [H, Cochain.comp_zero] at this; exact this.symm
  · have := mappingCone.inr_descCochain φ α β h
    rw [H, Cochain.comp_zero] at this; exact this.symm

theorem units_mul_self' (u : ℤˣ) : u * u = 1 := Int.units_mul_self u

theorem cone_zero
    (hinj : ∀ (n : ℤ) (x : Cocycle L M n),
      CohomologyClass.mk (zcomp (Cocycle.ofHom φ) x (zero_add n)) = 0 → CohomologyClass.mk x = 0)
    (hsurj : ∀ (n : ℤ) (y : Cocycle K M n), ∃ x : Cocycle L M n,
      CohomologyClass.mk (zcomp (Cocycle.ofHom φ) x (zero_add n)) = CohomologyClass.mk y)
    (n : ℤ) (z : Cocycle (mappingCone φ) M n) : CohomologyClass.mk z = 0 := by
  set a : Cochain K M (n - 1) := (mappingCone.inl φ).comp z.1 (by omega) with ha
  set b : Cochain L M n := (Cochain.ofHom (mappingCone.inr φ)).comp z.1 (zero_add n) with hb
  have hz : z.1 = mappingCone.descCochain φ a b (by omega) := by
    rw [mappingCone.ext_cochain_from_iff φ (n - 1) n (by omega)]
    simp [ha, hb]
  have h0 := Cocycle.δ_eq_zero z (n + 1)
  rw [hz, desc_δ φ a b _ (n + 1) rfl] at h0
  obtain ⟨h1, h2⟩ := desc_eq_zero φ h0
  have hda : δ (n - 1) n a = -((n + 1).negOnePow • (Cochain.ofHom φ).comp b (zero_add n)) := eq_neg_of_add_eq_zero_left h1
  let bc : Cocycle L M n := Cocycle.mk b (n + 1) rfl h2
  have hb0 : CohomologyClass.mk bc = 0 := by
    apply hinj
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
    refine ⟨-((n + 1).negOnePow • a), ?_⟩
    rw [δ_neg, δ_units_smul, hda, smul_neg, neg_neg, smul_smul, units_mul_self', one_smul]
    simp [zcomp, bc]
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at hb0
  obtain ⟨γ, hγ⟩ := hb0
  change δ (n - 1) n γ = b at hγ
  set a' : Cochain K M (n - 1) := a - n.negOnePow • (Cochain.ofHom φ).comp γ (zero_add _) with ha'
  let w : Cochain (mappingCone φ) M (n - 1) := mappingCone.descCochain φ (0 : Cochain K M (n - 1 - 1)) γ (by omega)
  have hw : δ (n - 1) n w = mappingCone.descCochain φ (n.negOnePow • (Cochain.ofHom φ).comp γ (zero_add _)) b (by omega) := by
    simp only [w]; rw [desc_δ φ _ γ _ n (by omega), hγ, δ_zero, zero_add]
  have hda' : δ (n - 1) n a' = 0 := by
    have e : mappingCone.descCochain φ a' (0 : Cochain L M n) (by omega) = z.1 - δ (n - 1) n w := by
      rw [hz, hw, mappingCone.ext_cochain_from_iff φ (n - 1) n (by omega)]
      simp [ha']
    have e2 := congrArg (δ n (n + 1)) e
    rw [δ_sub, δ_δ, sub_zero, Cocycle.δ_eq_zero, desc_δ φ _ _ _ (n + 1) rfl] at e2
    have := (desc_eq_zero φ e2).1
    simpa using this
  obtain ⟨x, hx⟩ := hsurj (n - 1) (Cocycle.mk a' n (by omega) hda')
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ (n - 1 - 1) (by omega)] at hx
  obtain ⟨γ', hγ'⟩ := hx
  change δ (n - 1 - 1) (n - 1) γ' = (Cochain.ofHom φ).comp x.1 (zero_add _) - a' at hγ'
  have hdx := Cocycle.δ_eq_zero x n
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨w + n.negOnePow • mappingCone.descCochain φ (0 : Cochain K M (n - 1 - 1)) x.1 (by omega) -
    mappingCone.descCochain φ γ' (0 : Cochain L M (n - 1)) (by omega), ?_⟩
  rw [δ_sub, δ_add, δ_units_smul, hw, desc_δ φ _ _ _ n (by omega), desc_δ φ _ _ _ n (by omega), hγ', hdx]
  change _ = z.1
  rw [hz, mappingCone.ext_cochain_from_iff φ (n - 1) n (by omega)]
  constructor
  · simp only [mappingCone.inl_descCochain, Cochain.comp_add, Cochain.comp_sub, Cochain.comp_units_smul, δ_zero, zero_add,
      Cochain.comp_zero, smul_zero, add_zero, smul_smul, units_mul_self', one_smul, ha']
    abel
  · simp
end Cone

section Geo
variable {R : Type} [CommRing R] (F : Shv R)

theorem hrel_sub {U E : Spc} (f : U ⟶ E) (h : Eqv R f F) (n : ℤ) : Subsingleton (Hrel R f F n) := by
  have hinj : ∀ (n : ℤ) (x : Cocycle ((chains R).obj E) (res R F) n),
      CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map f)) x (zero_add n)) = 0 → CohomologyClass.mk x = 0 := by
    intro n x hx
    apply (h n).1
    change CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map f)) x (zero_add n)) = pull R f F n 0
    rw [map_zero]; exact hx
  have hsurj : ∀ (n : ℤ) (y : Cocycle ((chains R).obj U) (res R F) n), ∃ x : Cocycle ((chains R).obj E) (res R F) n,
      CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map f)) x (zero_add n)) = CohomologyClass.mk y := by
    intro n y
    obtain ⟨c, hc⟩ := (h n).2 (CohomologyClass.mk y)
    obtain ⟨x, rfl⟩ := c.mk_surjective
    exact ⟨x, hc⟩
  refine ⟨fun y y' => ?_⟩
  obtain ⟨z, rfl⟩ := y.mk_surjective
  obtain ⟨z', rfl⟩ := y'.mk_surjective
  change CohomologyClass.mk z = CohomologyClass.mk z'
  rw [cone_zero _ hinj hsurj n z, cone_zero _ hinj hsurj n z']

theorem eqv_of_iso {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIso f] : Eqv R (sch.map f) F := by
  intro n
  refine Function.bijective_iff_has_inverse.2 ⟨pull R (sch.map (inv f)) F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, ← Functor.map_comp, IsIso.inv_hom_id, CategoryTheory.Functor.map_id, pull_id]
  · rw [← pull_comp, ← Functor.map_comp, IsIso.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]

theorem eqv_of_square {P Q X Y : Scheme.{0}} (a : P ⟶ X) (f : X ⟶ Y) (h : P ⟶ Q) (c : Q ⟶ Y) (w : a ≫ f = h ≫ c)
    (ha : Eqv R (sch.map a) F) (hh : Eqv R (sch.map h) F) (hc : Eqv R (sch.map c) F) : Eqv R (sch.map f) F := by
  intro n
  have key : ∀ y, pull R (sch.map a) F n (pull R (sch.map f) F n y) = pull R (sch.map h) F n (pull R (sch.map c) F n y) := by
    intro y; rw [← pull_comp, ← pull_comp, ← Functor.map_comp, ← Functor.map_comp, w]
  constructor
  · intro y y' e
    apply (hc n).1; apply (hh n).1
    rw [← key, ← key, e]
  · intro x
    obtain ⟨u, hu⟩ := (hh n).2 (pull R (sch.map a) F n x)
    obtain ⟨v, rfl⟩ := (hc n).2 u
    refine ⟨v, (ha n).1 ?_⟩
    rw [key, hu]
end Geo

theorem commGroup_inv_eq_conj_twist_identity {B W S X T : Scheme.{0}} (pA : X ⟶ S) (s : S ⟶ B) (ι : W ⟶ B) [Mono ι] (r : T ⟶ S) (w : T ⟶ W)
    (hw : w ≫ ι = r ≫ s) (hc : (pullback.fst (pullback.fst (pA ≫ s) ι ≫ pA) r ≫ pullback.fst (pA ≫ s) ι) ≫ pA =
      pullback.snd (pullback.fst (pA ≫ s) ι ≫ pA) r ≫ r) :
    IsIso (pullback.lift (pullback.fst (pullback.fst (pA ≫ s) ι ≫ pA) r ≫ pullback.fst (pA ≫ s) ι)
      (pullback.snd (pullback.fst (pA ≫ s) ι ≫ pA) r) hc) := by
  have c1 : pullback.fst pA r ≫ pA ≫ s = (pullback.snd pA r ≫ w) ≫ ι := by
    simp only [Category.assoc, hw]; exact pullback.condition_assoc s
  have c2 : pullback.lift (pullback.fst pA r) (pullback.snd pA r ≫ w) c1 ≫ pullback.fst (pA ≫ s) ι ≫ pA =
      pullback.snd pA r ≫ r := by
    rw [← Category.assoc, pullback.lift_fst, pullback.condition]
  refine ⟨⟨pullback.lift (pullback.lift (pullback.fst pA r) (pullback.snd pA r ≫ w) c1) (pullback.snd pA r) c2, ?_, ?_⟩⟩
  · apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
          pullback.lift_snd_assoc]
      · rw [← cancel_mono ι]
        simp only [Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
          pullback.lift_snd_assoc, hw]
        have e3 : pullback.fst (pA ≫ s) ι ≫ pA ≫ s = pullback.snd (pA ≫ s) ι ≫ ι := pullback.condition
        have e4 := pullback.condition_assoc (f := pullback.fst (pA ≫ s) ι ≫ pA) (g := r) s
        simp only [Category.assoc] at e4
        rw [← e3]
        first | exact e4 | exact e4.symm
    · simp only [Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
          pullback.lift_snd_assoc]
  · apply pullback.hom_ext
    · simp only [Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
          pullback.lift_snd_assoc]
    · simp only [Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
          pullback.lift_snd_assoc]

theorem closed_eq {A : Type} [CommRing A] [IsLocalRing A] (x : Sp A) (hx : ∀ z : Sp A, z ⤳ x) :
    x = IsLocalRing.closedPoint A :=
  ((IsLocalRing.specializes_closedPoint x).antisymm (hx _)).eq

theorem LeafVanW_of : LeafVanW := by
  intro hH q _ k _ hq i B W Y b ι _ p hp A _ s hA hx m
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hE2, -⟩ := hH
  obtain ⟨hHen, hsep⟩ := hA
  haveI : IsProper p := hp
  have hqA : IsUnit (q : A) := by
    have := hq.map (Spec.preimage (s ≫ b)).hom
    simpa using this

  obtain ⟨x, hx1, w0, hw0⟩ := hx
  have hxc := closed_eq x hx1
  have hrpt : (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) (IsLocalRing.closedPoint (IsLocalRing.ResidueField A)) =
      IsLocalRing.closedPoint A := IsLocalRing.comap_closedPoint (IsLocalRing.residue A)
  haveI : Surjective (pullback.fst (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ s) ι) := by
    constructor
    intro t
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ s) (g := ι)
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField A)) w0 (by
        have := congrArg s hrpt
        rw [← hxc, ← hw0] at this
        exact this)
    exact ⟨z, hz.trans (Subsingleton.elim _ _)⟩
  haveI := isIso_of_isClosedImmersion_of_surjective (pullback.fst (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ s) ι)
  have hw : (inv (pullback.fst (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ s) ι) ≫ pullback.snd _ _) ≫ ι =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ s := by
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]

  have e1 := hE2 q A ⟨hHen, hsep⟩ hqA (pullback.snd p s) i
  have e2 := hE2 q A ⟨hHen, hsep⟩ hqA (pullback.fst (pullback.snd p s ≫ s) ι ≫ pullback.snd p s) i
  have hc : (pullback.fst (pullback.fst (pullback.snd p s ≫ s) ι ≫ pullback.snd p s) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫
      pullback.fst (pullback.snd p s ≫ s) ι) ≫ pullback.snd p s =
      pullback.snd (pullback.fst (pullback.snd p s ≫ s) ι ≫ pullback.snd p s) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) := by
    rw [Category.assoc, pullback.condition]
  haveI := commGroup_inv_eq_conj_twist_identity (pullback.snd p s) s ι _ _ hw hc
  have heqv : Eqv (ZMod q) (sch.map (prS p ι s)) (tw q i) :=
    eqv_of_square _ _ _ _ _ (pullback.lift_fst _ _ _).symm e2 (eqv_of_iso _ (pullback.lift (pullback.fst (pullback.fst (pullback.snd p s ≫ s) ι ≫ pullback.snd p s)
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫ pullback.fst (pullback.snd p s ≫ s) ι) _ hc)) e1
  exact hrel_sub _ _ heqv m

end LateralTheory.E.LeafVanWPf
end
end

