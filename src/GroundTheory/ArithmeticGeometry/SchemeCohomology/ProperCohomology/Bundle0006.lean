module

public import Mathlib
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ChowGraph
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle0003
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle0005
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.ImmersionPush
public import GroundTheory.ArithmeticGeometry.EtaleCompletion.Bundle0001

@[expose] public section

-- bundled from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ChowMulti
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u

noncomputable section

theorem exists_chow_multiProj {A : Type u} [CommRing A] [IsNoetherianRing A] (X : Scheme.{u})
    [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] [IrreducibleSpace X] :
    ∃ (k : ℕ) (n : Fin (k + 1) → ℕ) (X' : Scheme.{u}) (q : X' ⟶ ProjSpace.MP A k n)
      (π : X' ⟶ X) (U : X.Opens), IsClosedImmersion q ∧
      q ≫ ProjSpace.mpStr A k n = π ≫ (X ↘ Spec (.of A)) ∧ genericPoint X ∈ U ∧
      IsIso (π ∣_ U) := by
  classical
  set s := X ↘ Spec (.of A)
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  have : IsNoetherian X := ⟨⟩

  have hex : ∀ x : X, ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V := fun x => by
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨V, hV, hxV⟩
  choose V hVaff hxV using hex
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : X => (V x : Set X))
    (fun x => (V x).2) (fun x _ => Set.mem_iUnion.2 ⟨x, hxV x⟩)
  have htne : t.Nonempty := by
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    obtain ⟨y, hy, -⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact ⟨y, hy⟩
  obtain ⟨k, hk⟩ : ∃ k, t.card = k + 1 := ⟨t.card - 1, by have := htne.card_pos; omega⟩
  let e : Fin (k + 1) ≃ t := (Fintype.equivFinOfCardEq (by simpa using hk)).symm
  let U : Fin (k + 1) → X.Opens := fun j => V (e j)
  have hUaff : ∀ j, IsAffineOpen (U j) := fun j => hVaff _
  have hU : iSup U = ⊤ := by
    refine top_le_iff.1 fun x _ => ?_
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact Opens.mem_iSup.2 ⟨e.symm ⟨y, hy⟩, by simpa [U] using hxy⟩
  have hc := fun j => ProjSpace.exists_closedImmersion_stdOpen (A := A) s (hUaff j)
  choose n c hccl hcc using hc
  have : ∀ j, IsClosedImmersion (c j) := hccl
  have hη : genericPoint X ∈ ChowGraph.W U := by
    rw [ChowGraph.W, ← SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter]
    intro j
    exact ((genericPoint_spec X).mem_open_set_iff (U j).2).2
      ⟨e j, Set.mem_univ _, hxV _⟩
  have : NoetherianSpace (ChowGraph.W U).toScheme :=
    NoetherianSpace.set ((ChowGraph.W U : X.Opens) : Set X)
  have : QuasiCompact (ChowGraph.g s n U c hcc) := ⟨fun _ _ _ => NoetherianSpace.isCompact _⟩
  refine ⟨k, n, ChowGraph.X' s n U c hcc, ChowGraph.q s n U c hcc, ChowGraph.π s n U c hcc,
    ChowGraph.W U, ChowGraph.isClosedImmersion_q s n U c hcc hU, ?_, hη,
    ChowGraph.isIso_π_restrict s n U c hcc⟩
  simp only [ChowGraph.q, ChowGraph.π, Category.assoc, pullback.condition]

end

end GroundTheory.Arith.SchemeCoh
end

-- bundled from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.PullbackUnit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

section Affine

variable {X : Scheme.{u}}

lemma isIso_of_bijective_app_affine {M N : X.Modules} (f : M ⟶ N)
    (h : ∀ U : X.Opens, IsAffineOpen U → Function.Bijective (f.app U)) : IsIso f := by
  have hB : Opens.IsBasis (Set.range fun U : X.affineOpens => (U : X.Opens)) := by
    rw [Subtype.range_coe]
    exact X.isBasis_affineOpens
  let φ : modulesAb M ⟶ modulesAb N := ⟨f.mapPresheaf⟩
  have : IsIso φ := TopCat.Sheaf.isIso_iff_isIso_basis hB fun U => by
    change IsIso (f.mapPresheaf.app (op U.1))
    rw [Scheme.Modules.mapPresheaf_app]
    exact (ConcreteCategory.isIso_iff_bijective _).2 (h U.1 U.2)
  have : IsIso ((Scheme.Modules.toPresheaf X).map f) := by
    rw [Scheme.Modules.toPresheaf_map]
    exact Functor.map_isIso (sheafToPresheaf _ _) φ
  exact isIso_of_reflects_iso f (Scheme.Modules.toPresheaf X)

lemma bijective_app_of_bijective_app_affine {M N : X.Modules} (f : M ⟶ N) (W : X.Opens)
    (h : ∀ V : X.Opens, IsAffineOpen V → V ≤ W → Function.Bijective (f.app V)) :
    ∀ V ≤ W, Function.Bijective (f.app V) := by
  have hR : IsIso ((Scheme.Modules.restrictFunctor W.ι).map f) :=
    isIso_of_bijective_app_affine _ fun V' hV' =>
      h _ (hV'.image_of_isOpenImmersion W.ι) ((W.ι.image_le_opensRange V').trans (by simp))
  intro V hV
  have hE : W.ι ''ᵁ (W.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.2 hV
  rw [← hE]
  exact ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.restrictFunctor W.ι).map f).app (W.ι ⁻¹ᵁ V))

end Affine

section Section

variable {T U : Scheme.{u}}

theorem bijective_pullbackSection_of_surjective (g : T ⟶ U) [IsAffine T] [IsAffine U]
    (N : U.Modules) [N.IsQuasicoherent] (hg : Function.Surjective g.appTop)
    (hker : ∀ a : Γ(U, ⊤), g.appTop a = 0 → ∀ n : Γ(N, ⊤), a • n = 0) :
    Function.Bijective (Etale.pullbackSection g N) := by
  constructor
  · let K := RingHom.ker g.appTop.hom
    have hM : Module.IsTorsionBySet Γ(U, ⊤) Γ(N, ⊤) (K : Set Γ(U, ⊤)) :=
      fun n a => hker a.1 a.2 n
    let _ : Module (Γ(U, ⊤) ⧸ K) Γ(N, ⊤) := hM.module
    let e := RingHom.quotientKerEquivOfSurjective (f := g.appTop.hom) hg
    let _ : Module Γ(T, ⊤) Γ(N, ⊤) := Module.compHom _ e.symm.toRingHom
    obtain ⟨ψ', hψ', -⟩ := Etale.existsUnique_pullbackSection g N Γ(N, ⊤) (AddMonoidHom.id _)
      (fun a n => by
        change a • n = e.symm (g.appTop a) • n
        have he : e.symm (g.appTop a) = Ideal.Quotient.mk K a :=
          e.symm_apply_eq.2 (RingHom.quotientKerEquivOfSurjective_apply_mk hg a).symm
        rw [he, hM.mk_smul])
    intro x y hxy
    have := congrArg ψ' hxy
    rwa [hψ', hψ'] at this
  · intro p
    let P := Γ((Scheme.Modules.pullback g).obj N, ⊤)
    let L : Submodule Γ(T, ⊤) P := Submodule.span Γ(T, ⊤) (Set.range (Etale.pullbackSection g N))
    have hL : L = ⊤ := by
      obtain ⟨ψ', -, huniq⟩ := Etale.existsUnique_pullbackSection g N (P ⧸ L) 0
        (fun a n => by simp)
      have h0 : (0 : P →ₗ[Γ(T, ⊤)] (P ⧸ L)) = ψ' := huniq 0 (fun n => by simp)
      have h1 : L.mkQ = ψ' := huniq L.mkQ (fun n => by
        simpa using (Submodule.Quotient.mk_eq_zero L).2 (Submodule.subset_span ⟨n, rfl⟩))
      rw [eq_top_iff]
      intro q _
      have := LinearMap.congr_fun (h1.trans h0.symm) q
      exact (Submodule.Quotient.mk_eq_zero L).1 this
    have hp : p ∈ L := hL ▸ Submodule.mem_top
    induction hp using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => exact ⟨0, map_zero _⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, map_add _ _ _⟩
    | smul s x _ hx =>
      obtain ⟨n, rfl⟩ := hx
      obtain ⟨a, rfl⟩ := hg s
      exact ⟨a • n, Etale.pullbackSection_smul g N a n⟩

end Section

section Move

variable {V T U : Scheme.{u}}

lemma bijective_pullbackUnitApp_comp_left_iff (f : V ⟶ T) [IsOpenImmersion f] (g : T ⟶ U)
    (N : U.Modules) (O : U.Opens) (hO : g ⁻¹ᵁ O ≤ f.opensRange) :
    Function.Bijective (Etale.pullbackUnitApp (f ≫ g) N O) ↔
      Function.Bijective (Etale.pullbackUnitApp g N O) := by
  have hc := ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.pullbackComp f g).inv.app N).app ((f ≫ g) ⁻¹ᵁ O))
  have hf := Etale.pullbackUnitApp_bijective f ((Scheme.Modules.pullback g).obj N) hO
  have e : ⇑(ConcreteCategory.hom
      (((Scheme.Modules.pullbackComp f g).inv.app N).app ((f ≫ g) ⁻¹ᵁ O))) ∘
        ⇑(Etale.pullbackUnitApp (f ≫ g) N O) =
      ⇑(Etale.pullbackUnitApp f _ (g ⁻¹ᵁ O)) ∘ ⇑(Etale.pullbackUnitApp g N O) :=
    funext (Etale.pullbackUnitApp_comp f g N O)
  rw [← Function.Bijective.of_comp_iff' hc, e]
  exact Function.Bijective.of_comp_iff' hf _

lemma bijective_pullbackUnitApp_comp_right_iff (g : V ⟶ T) (h : T ⟶ U) [IsOpenImmersion h]
    (N : U.Modules) (O : U.Opens) (hO : O ≤ h.opensRange) :
    Function.Bijective (Etale.pullbackUnitApp (g ≫ h) N O) ↔
      Function.Bijective (Etale.pullbackUnitApp g ((Scheme.Modules.pullback h).obj N) (h ⁻¹ᵁ O)) := by
  have hc := ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.pullbackComp g h).inv.app N).app ((g ≫ h) ⁻¹ᵁ O))
  have hh := Etale.pullbackUnitApp_bijective h N hO
  have e : ⇑(ConcreteCategory.hom
      (((Scheme.Modules.pullbackComp g h).inv.app N).app ((g ≫ h) ⁻¹ᵁ O))) ∘
        ⇑(Etale.pullbackUnitApp (g ≫ h) N O) =
      ⇑(Etale.pullbackUnitApp g _ (h ⁻¹ᵁ O)) ∘ ⇑(Etale.pullbackUnitApp h N O) :=
    funext (Etale.pullbackUnitApp_comp g h N O)
  rw [← Function.Bijective.of_comp_iff' hc, e]
  exact Function.Bijective.of_comp_iff _ hh

lemma bijective_pullbackUnitApp_congr (g : T ⟶ U) (N : U.Modules) {O O' : U.Opens} (h : O = O') :
    Function.Bijective (Etale.pullbackUnitApp g N O) ↔
      Function.Bijective (Etale.pullbackUnitApp g N O') := by
  subst h
  rfl

end Move

section Unit

variable {X Y : Scheme.{u}}

theorem bijective_pullbackUnitApp_of_isClosedImmersion (ψ : Y ⟶ X) (F : X.Modules)
    [F.IsQuasicoherent] {V : X.Opens} (hV : IsAffineOpen V) [IsClosedImmersion (ψ ∣_ V)]
    (hkill : ∀ a : Γ(X, V.ι ''ᵁ ⊤), ψ.app (V.ι ''ᵁ ⊤) a = 0 →
      ∀ m : Γ(F, V.ι ''ᵁ ⊤), a • m = 0) :
    Function.Bijective (Etale.pullbackUnitApp ψ F V) := by
  rw [← bijective_pullbackUnitApp_comp_left_iff (ψ ⁻¹ᵁ V).ι ψ F V (by simp),
    ← morphismRestrict_ι ψ V, bijective_pullbackUnitApp_comp_right_iff (ψ ∣_ V) V.ι F V (by simp),
    bijective_pullbackUnitApp_congr _ _ (Scheme.Opens.ι_preimage_self V)]
  have : IsAffine V := hV
  obtain ⟨hT, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine (ψ ∣_ V)
  let e := (Scheme.Modules.restrictFunctorIsoPullback V.ι).app F
  have : ((Scheme.Modules.pullback V.ι).obj F).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf).prop_of_iso e inferInstance
  refine bijective_pullbackSection_of_surjective (ψ ∣_ V) _ hsurj fun a ha n => ?_

  have ha' : ψ.app (V.ι ''ᵁ ⊤) a = 0 := by
    rw [morphismRestrict_appTop] at ha
    have hinj := (ConcreteCategory.bijective_of_isIso
      (Y.presheaf.map (eqToHom (image_morphismRestrict_preimage ψ V ⊤)).op)).1
    exact hinj (by rw [map_zero]; exact ha)
  have key : ∀ n' : Γ(F.restrict V.ι, ⊤), a • n' = 0 := fun n' => by
    have hi := ConcreteCategory.bijective_of_isIso (F.restrictAppIso V.ι ⊤).hom
    apply hi.1
    have hs := congrArg (fun φ : Γ(F.restrict V.ι, ⊤) ⟶ Γ(F, V.ι ''ᵁ ⊤) => φ n')
      (Scheme.Modules.smul_restrictAppIso_hom V.ι F ⊤ a)
    simp only [ConcreteCategory.comp_apply, Scheme.Opens.ι_appIso, Iso.refl_inv] at hs
    change (F.restrictAppIso V.ι ⊤).hom (a • n') = _
    rw [map_zero]
    refine (show _ = _ from hs).trans ?_
    exact hkill a ha' _
  have h1 : n = e.hom.app ⊤ (e.inv.app ⊤ n) := by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.inv_hom_id]
    rfl
  rw [h1, ← Scheme.Modules.Hom.app_smul, key, map_zero]

theorem bijective_unit_app_of_le (ψ : Y ⟶ X) (F : X.Modules) [F.IsQuasicoherent] (W : X.Opens)
    [IsClosedImmersion (ψ ∣_ W)]
    (hkill : ∀ V : X.Opens, IsAffineOpen V → V ≤ W → ∀ a : Γ(X, V), ψ.app V a = 0 →
      ∀ m : Γ(F, V), a • m = 0) :
    ∀ V ≤ W, Function.Bijective
      (((Scheme.Modules.pullbackPushforwardAdjunction ψ).unit.app F).app V) := by
  refine bijective_app_of_bijective_app_affine _ W fun V hV hVW => ?_
  have hE : W.ι ''ᵁ (W.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.2 hVW
  have hci : IsClosedImmersion (ψ ∣_ V) := by
    have e := morphismRestrictRestrict ψ W (W.ι ⁻¹ᵁ V)
    have h := (MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion e).1 inferInstance
    rwa [hE] at h
  have hVtop : V.ι ''ᵁ ⊤ = V := Scheme.Opens.ι_image_top V
  exact bijective_pullbackUnitApp_of_isClosedImmersion ψ F hV fun a ha m =>
    hkill _ (by rw [hVtop]; exact hV) (hVtop.le.trans hVW) a ha m

end Unit

end

end GroundTheory.Arith.SchemeCoh
end

-- bundled from GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.QcqsPushforward
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

variable {Y : Scheme.{u}} (G : Y.Modules)

lemma eq_of_forall_resF {κ : Type u} (W : κ → Y.Opens) {U : Y.Opens} (hle : ∀ k, W k ≤ U)
    (hcov : U ≤ iSup W) (m m' : Γ(G, U)) (h : ∀ k, resF G (hle k) m = resF G (hle k) m') :
    m = m' :=
  TopCat.Sheaf.eq_of_locally_eq' (modulesAb G) W U (fun k => homOfLE (hle k)) hcov m m' h

lemma exists_resF_eq_of_compatible {κ : Type u} (W : κ → Y.Opens) {U : Y.Opens}
    (hle : ∀ k, W k ≤ U) (hcov : U ≤ iSup W) (σ : ∀ k, Γ(G, W k))
    (hσ : ∀ k l, resF G (inf_le_left : W k ⊓ W l ≤ W k) (σ k) =
      resF G (inf_le_right : W k ⊓ W l ≤ W l) (σ l)) :
    ∃ m : Γ(G, U), ∀ k, resF G (hle k) m = σ k := by
  obtain ⟨m, hm, -⟩ := TopCat.Sheaf.existsUnique_gluing' (modulesAb G) W U
    (fun k => homOfLE (hle k)) hcov σ
    (fun k l => hσ k l)
  exact ⟨m, hm⟩

variable [G.IsQuasicoherent]

lemma basicOpen_resO_le {U W : Y.Opens} (hWU : W ≤ U) (h : Γ(Y, U)) :
    Y.basicOpen (resO hWU h) ≤ Y.basicOpen h := by
  rw [Scheme.basicOpen_res]
  exact inf_le_right

theorem qcoh_exists_pow_smul_eq_zero_of_isCompact {U : Y.Opens} (hU : IsCompact (U : Set Y))
    (h : Γ(Y, U)) (m : Γ(G, U)) (hm : resF G (Y.basicOpen_le h) m = 0) :
    ∃ e : ℕ, h ^ e • m = 0 := by
  classical
  obtain ⟨Us, hUs, hfin, hUeq⟩ := Y.isBasis_affineOpens.exists_finite_of_isCompact hU
  have := hfin.to_subtype
  have hle : ∀ k : Us, (k : Y.Opens) ≤ U := fun k => hUeq ▸ le_sSup k.2
  have key : ∀ k : Us, ∃ e : ℕ, resO (hle k) h ^ e • resF G (hle k) m = 0 := fun k =>
    qcoh_exists_pow_smul_eq_zero G (hUs k.2) (resO (hle k) h) (resF G (hle k) m) (by
      rw [resF_resF, ← resF_resF G (Y.basicOpen_le h) (basicOpen_resO_le (hle k) h), hm, map_zero])
  choose e he using key
  have := Fintype.ofFinite Us
  refine ⟨Finset.univ.sup e, eq_of_forall_resF G (fun k : Us => (k : Y.Opens)) hle
    (by rw [hUeq, sSup_eq_iSup']) _ _ fun k => ?_⟩
  have hk : e k ≤ Finset.univ.sup e := Finset.le_sup (Finset.mem_univ k)
  rw [map_zero, resF_smul, map_pow, ← Nat.sub_add_cancel hk, pow_add, mul_smul, he k, smul_zero]

theorem qcoh_exists_res_eq_of_qcqs {U : Y.Opens} (hU : IsCompact (U : Set Y))
    (hU' : IsQuasiSeparated (U : Set Y)) (h : Γ(Y, U)) (m : Γ(G, Y.basicOpen h)) :
    ∃ (e : ℕ) (m' : Γ(G, U)), resF G (Y.basicOpen_le h) m' = resO (Y.basicOpen_le h) h ^ e • m := by
  classical
  obtain ⟨Us, hUs, hfin, hUeq⟩ := Y.isBasis_affineOpens.exists_finite_of_isCompact hU
  have := hfin.to_subtype
  have := Fintype.ofFinite Us
  let W : Us → Y.Opens := fun k => k
  have hle : ∀ k, W k ≤ U := fun k => hUeq ▸ le_sSup k.2
  have hcov : U ≤ iSup W := by rw [hUeq, sSup_eq_iSup']

  have loc : ∀ k, ∃ (e : ℕ) (mk : Γ(G, W k)),
      resF G (Y.basicOpen_le (resO (hle k) h)) mk =
        resO (Y.basicOpen_le (resO (hle k) h)) (resO (hle k) h) ^ e •
          resF G (basicOpen_resO_le (hle k) h) m := fun k =>
    qcoh_exists_res_eq G (hUs k.2) (resO (hle k) h) (resF G (basicOpen_resO_le (hle k) h) m)
  choose e mk hmk using loc
  set N := Finset.univ.sup e
  obtain ⟨σ, hσ⟩ : ∃ σ : ∀ k, Γ(G, W k), ∀ k,
      resF G (Y.basicOpen_le (resO (hle k) h)) (σ k) =
        resO ((basicOpen_resO_le (hle k) h).trans (Y.basicOpen_le h)) h ^ N •
          resF G (basicOpen_resO_le (hle k) h) m := by
    refine ⟨fun k => resO (hle k) h ^ (N - e k) • mk k, fun k => ?_⟩
    have hk : e k ≤ N := Finset.le_sup (Finset.mem_univ k)
    rw [resF_smul, hmk, smul_smul]
    simp only [map_pow, resO_resO]
    rw [← pow_add, Nat.sub_add_cancel hk]

  have pair : ∀ k l, ∃ e' : ℕ, resO (inf_le_left.trans (hle k) : W k ⊓ W l ≤ U) h ^ e' •
      (resF G (inf_le_left : W k ⊓ W l ≤ W k) (σ k) -
        resF G (inf_le_right : W k ⊓ W l ≤ W l) (σ l)) = 0 := by
    intro k l
    have hkl : IsCompact ((W k ⊓ W l : Y.Opens) : Set Y) :=
      hU' _ _ (hle k) (W k).2 (hUs k.2).isCompact (hle l) (W l).2 (hUs l.2).isCompact
    refine qcoh_exists_pow_smul_eq_zero_of_isCompact G hkl _ _ ?_
    have hb : Y.basicOpen (resO (inf_le_left.trans (hle k) : W k ⊓ W l ≤ U) h) ≤
        Y.basicOpen (resO (hle k) h) := by
      rw [Scheme.basicOpen_res, Scheme.basicOpen_res]
      exact inf_le_inf_right _ inf_le_left
    have hb' : Y.basicOpen (resO (inf_le_left.trans (hle k) : W k ⊓ W l ≤ U) h) ≤
        Y.basicOpen (resO (hle l) h) := by
      rw [Scheme.basicOpen_res, Scheme.basicOpen_res]
      exact inf_le_inf_right _ inf_le_right
    rw [map_sub, resF_resF, resF_resF, sub_eq_zero,
      ← resF_resF G (Y.basicOpen_le (resO (hle k) h)) hb,
      ← resF_resF G (Y.basicOpen_le (resO (hle l) h)) hb', hσ k, hσ l, resF_smul, resF_smul,
      resF_resF, resF_resF, map_pow, map_pow, resO_resO, resO_resO]
  choose e' he' using pair
  set N' := Finset.univ.sup (fun kl : Us × Us => e' kl.1 kl.2)
  obtain ⟨τ, hτdef⟩ : ∃ τ : ∀ k, Γ(G, W k), ∀ k, τ k = resO (hle k) h ^ N' • σ k :=
    ⟨fun k => resO (hle k) h ^ N' • σ k, fun _ => rfl⟩
  have hτ : ∀ k l, resF G (inf_le_left : W k ⊓ W l ≤ W k) (τ k) =
      resF G (inf_le_right : W k ⊓ W l ≤ W l) (τ l) := by
    intro k l
    have hkl : e' k l ≤ N' := Finset.le_sup (f := fun kl : Us × Us => e' kl.1 kl.2)
      (Finset.mem_univ (k, l))
    rw [hτdef, hτdef, resF_smul, resF_smul, map_pow, map_pow, resO_resO, resO_resO, ← sub_eq_zero,
      ← smul_sub, ← Nat.sub_add_cancel hkl, pow_add, mul_smul, he' k l, smul_zero]
  obtain ⟨m', hm'⟩ := exists_resF_eq_of_compatible G W hle hcov τ hτ
  refine ⟨N' + N, m', ?_⟩

  refine eq_of_forall_resF G (fun k => Y.basicOpen (resO (hle k) h))
    (fun k => basicOpen_resO_le (hle k) h) ?_ _ _ fun k => ?_
  · intro x hx
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (hcov (Y.basicOpen_le h hx))
    refine Opens.mem_iSup.2 ⟨k, ?_⟩
    rw [Scheme.basicOpen_res]
    exact ⟨hk, hx⟩
  · rw [resF_resF, ← resF_resF G (hle k) (Y.basicOpen_le (resO (hle k) h)), hm', hτdef, resF_smul,
      hσ k, resF_smul, smul_smul]
    simp only [map_pow, resO_resO, ← pow_add]

theorem isQuasicoherent_pushforward_of_qcqs {X : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    [QuasiSeparated f] (F : X.Modules) [F.IsQuasicoherent] :
    ((Scheme.Modules.pushforward f).obj F).IsQuasicoherent := by
  refine isQuasicoherent_of_affineCover _ (fun V : Y.affineOpens => (V : Y.Opens))
    (fun V => V.2) (iSup_affineOpens_eq_top Y) ?_ ?_
  · intro V g
    have hc : IsCompact ((f ⁻¹ᵁ (V : Y.Opens) : X.Opens) : Set X) := f.isCompact_preimage V.2.isCompact
    have hqs : IsQuasiSeparated ((f ⁻¹ᵁ (V : Y.Opens) : X.Opens) : Set X) :=
      f.isQuasiSeparated_preimage V.2.isQuasiSeparated
    have hb : f ⁻¹ᵁ Y.basicOpen g = X.basicOpen (f.app V g) := Scheme.preimage_basicOpen f g
    show ∀ m : Γ(F, f ⁻¹ᵁ Y.basicOpen g), ∃ (e : ℕ) (m' : Γ(F, f ⁻¹ᵁ (V : Y.Opens))),
      resF F ((Opens.map f.base).monotone (Y.basicOpen_le g)) m' =
        f.app (Y.basicOpen g) (resO (Y.basicOpen_le g) g ^ e) • m
    intro m
    obtain ⟨e, m', hm'⟩ := qcoh_exists_res_eq_of_qcqs F hc hqs (f.app V g) (resF F hb.ge m)
    refine ⟨e, m', ?_⟩
    have h2 := congrArg (resF F hb.le) hm'
    rw [resF_resF, resF_smul, resF_resF, resF_self, map_pow, resO_resO] at h2
    rw [h2, map_pow, app_resO]
  · intro V g
    have hc : IsCompact ((f ⁻¹ᵁ (V : Y.Opens) : X.Opens) : Set X) := f.isCompact_preimage V.2.isCompact
    have hb : f ⁻¹ᵁ Y.basicOpen g = X.basicOpen (f.app V g) := Scheme.preimage_basicOpen f g
    show ∀ m : Γ(F, f ⁻¹ᵁ (V : Y.Opens)),
      resF F ((Opens.map f.base).monotone (Y.basicOpen_le g)) m = 0 →
        ∃ e : ℕ, f.app V (g ^ e) • m = 0
    intro m hm
    obtain ⟨e, he⟩ := qcoh_exists_pow_smul_eq_zero_of_isCompact F hc (f.app V g) m (by
      have h2 := congrArg (resF F hb.ge) hm
      rw [resF_resF, map_zero] at h2
      exact h2)
    exact ⟨e, by rw [map_pow]; exact he⟩

end

end GroundTheory.Arith.SchemeCoh
end

