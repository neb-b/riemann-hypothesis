module

public import Development.EtaleCohomology.CohomologicalPurity.Bundle0006
public import Development.EtaleCohomology.CohomologicalPurity.Bundle0005
public import Development.EtaleCohomology.CohomologicalPurity.LeafDescPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafDictPf
public import Development.EtaleCohomology.CohomologicalPurity.LeafClCut
public import Development.EtaleCohomology.KummerTheory.Bundle0012

@[expose] public section

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafBdAddPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Cl.Flq

theorem etale_section_boundary_of_mem_addSubgroup_closure {R : Type} [CommRing R] (K : Cx R) {Y : Scheme.{0}} (U' : Y.Opens) (n : ℤ)
    (a : Sec (K.X n) Y) (ha : a ∈ AddSubgroup.closure {a | Bd K U' n a}) : Bd K U' n a := by
  induction ha using AddSubgroup.closure_induction with
  | mem x hx => exact hx
  | zero => exact ⟨0, map_zero _, map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨b, hb0, hb⟩ := hx
    obtain ⟨c, hc0, hc⟩ := hy
    refine ⟨b + c, ?_, ?_⟩
    · show ((K.X (n-1)).obj.map U'.ι.op).hom (b + c) = 0
      rw [map_add (f := _), show ((K.X (n-1)).obj.map U'.ι.op).hom b = 0 from hb0, show ((K.X (n-1)).obj.map U'.ι.op).hom c = 0 from hc0, add_zero]
    · show ((K.d (n - 1) n).hom.app (op Y)).hom (b + c) = x + y
      rw [map_add (f := _)]; rw [← hb, ← hc]
  | neg x _ hx =>
    obtain ⟨b, hb0, hb⟩ := hx
    refine ⟨-b, ?_, ?_⟩
    · show ((K.X (n-1)).obj.map U'.ι.op).hom (-b) = 0
      rw [map_neg]; rw [show ((K.X (n-1)).obj.map U'.ι.op).hom b = 0 from hb0, neg_zero]
    · show ((K.d (n - 1) n).hom.app (op Y)).hom (-b) = -x
      rw [map_neg]; rw [← hb]

theorem LeafBdAdd_of : LeafBdAdd := by
  intro R _ K X U n W a ha
  exact etale_section_boundary_of_mem_addSubgroup_closure K _ n a ha

end LateralTheory.CohomologicalPurity.Cl.Flq
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafCmpPfId
section
noncomputable section
open CategoryTheory AlgebraicGeometry

namespace LateralTheory.CohomologicalPurity.Cl

theorem le_map_of {d : ℕ} {P : SP d} (F F₀ : Frame P) (C : Type) [CommRing C] (φ : F.B →+* C) (ψ : F₀.B →+* C)
    (e : Spec.map (CommRingCat.ofHom φ) ≫ F.w = Spec.map (CommRingCat.ofHom ψ) ≫ F₀.w) : F.I.map φ ≤ F₀.I.map ψ := by
  let J := F₀.I.map ψ
  let π : C →+* C ⧸ J := Ideal.Quotient.mk J
  let ψ' : F₀.B ⧸ F₀.I →+* C ⧸ J := Ideal.Quotient.lift F₀.I (π.comp ψ)
    (fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem ψ ha))
  have hψ : ψ'.comp (Ideal.Quotient.mk F₀.I) = π.comp ψ := RingHom.ext fun a => rfl
  have hw : (Spec.map (CommRingCat.ofHom π) ≫ Spec.map (CommRingCat.ofHom φ)) ≫ F.w =
      (Spec.map (CommRingCat.ofHom ψ') ≫ F₀.z) ≫ P.ι := by
    rw [Category.assoc, e, Category.assoc, ← F₀.cart.w, ← Category.assoc, ← Category.assoc,
      ← spec_comp_ofHom, ← spec_comp_ofHom, hψ]
  let t := F.cart.lift _ _ hw
  have ht : t ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk F.I)) =
      Spec.map (CommRingCat.ofHom π) ≫ Spec.map (CommRingCat.ofHom φ) := F.cart.lift_fst _ _ _
  let τ : F.B ⧸ F.I →+* C ⧸ J := (Spec.preimage t).hom
  have h1 : Spec.map (CommRingCat.ofHom (τ.comp (Ideal.Quotient.mk F.I))) =
      Spec.map (CommRingCat.ofHom (π.comp φ)) := by
    rw [spec_comp_ofHom, spec_comp_ofHom, ← ht]
    congr 1
    exact Spec.map_preimage t
  have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
  change (π.comp φ) a = 0
  rw [← show (τ.comp (Ideal.Quotient.mk F.I)) = π.comp φ from h2, RingHom.comp_apply,
    Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]

theorem LeafCmpId_pf : LeafCmpId := fun _ _ F F₀ C _ φ ψ e =>
  le_antisymm (le_map_of F F₀ C φ ψ e) (le_map_of F₀ F C ψ φ e.symm)

end LateralTheory.CohomologicalPurity.Cl
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafCmpPfNb
section
noncomputable section
open CategoryTheory AlgebraicGeometry

namespace LateralTheory.CohomologicalPurity.Cl

theorem LeafCmpNb_pf : LeafCmpNb := by
  intro X B B₀ _ _ w w₀ h₀ y hy
  let W : (Spec (CommRingCat.of B)).Opens := w ⁻¹ᵁ w₀.opensRange
  have hs : IsOpen (X := PrimeSpectrum B) (W : Set (Spec (CommRingCat.of B))) := W.2
  have hyW : (y : PrimeSpectrum B) ∈ (W : Set (Spec (CommRingCat.of B))) := hy
  obtain ⟨_, ⟨g, rfl⟩, hyg, hsub⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := B)).exists_subset_of_mem_open hyW hs
  let l : B →+* Localization.Away g := algebraMap B (Localization.Away g)
  have hr : Set.range (PrimeSpectrum.comap l) = PrimeSpectrum.basicOpen g :=
    PrimeSpectrum.localization_away_comap_range (Localization.Away g) g
  have H : Set.range (Spec.map (CommRingCat.ofHom l) ≫ w) ⊆ Set.range w₀ := by
    rintro _ ⟨t, rfl⟩
    have : (Spec.map (CommRingCat.ofHom l)) t ∈ W :=
      hsub (by
        have h1 : PrimeSpectrum.comap l t ∈ Set.range (PrimeSpectrum.comap l) := ⟨t, rfl⟩
        rw [hr] at h1; exact h1)
    exact this
  let u := IsOpenImmersion.lift w₀ _ H
  refine ⟨Localization.Away g, inferInstance, l, (Spec.preimage u).hom, ?_, ?_, ?_⟩
  · exact Scheme.isOpenImmersion_SpecMap_localizationAway (R := CommRingCat.of B) g
  · have h2 : (y : PrimeSpectrum B) ∈ Set.range (PrimeSpectrum.comap l) := by rw [hr]; exact hyg
    obtain ⟨t, ht⟩ := h2
    exact ⟨show Spec (CommRingCat.of (Localization.Away g)) from t, ht⟩
  · rw [CommRingCat.ofHom_hom, Spec.map_preimage]
    exact (IsOpenImmersion.lift_fac w₀ _ H).symm

end LateralTheory.CohomologicalPurity.Cl
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafDescOSepPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Cl

theorem sres_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (f : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res f (Sec.res g x) = Sec.res (f ≫ g) x := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem sres_zero {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (f : V ⟶ U) :
    Sec.res (F := F) f 0 = 0 := map_zero ((F.obj.map f.op).hom)

theorem smap_zero {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} :
    Sec.map φ (0 : Sec F U) = 0 := map_zero ((φ.hom.app (op U)).hom)

theorem smap_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (f : V ⟶ U) (x : Sec F U) :
    Sec.map φ (Sec.res f x) = Sec.res f (Sec.map φ x) := by
  have := congrArg (fun h => h.hom x) (φ.hom.naturality f.op)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using this

theorem le_comp' {Y Z X : Scheme.{0}} {W : Y.Opens} (f : Y ⟶ Z) (g : Z ⟶ X) (U : X.Opens) (k : Y ⟶ X)
    (hk : f ≫ g = k) (hW : W ≤ k ⁻¹ᵁ U) : W ≤ f ⁻¹ᵁ (g ⁻¹ᵁ U) := by
  subst hk; intro w hw; exact hW hw

theorem zc_res {R : Type} [CommRing R] {K : Cx R} {n : ℤ} {X' X : Scheme.{0}} (f : X' ⟶ X) (U' : X'.Opens)
    (U : X.Opens) (h : U' ≤ f ⁻¹ᵁ U) (a : Sec (K.X n) X) (ha : a ∈ Zc K U n) : Sec.res f a ∈ Zc K U' n := by
  rw [mem_Zc] at ha ⊢
  refine ⟨?_, ?_⟩
  · rw [sres_comp, ← Scheme.Hom.resLE_comp_ι f h, ← sres_comp, ha.1, sres_zero]
  · rw [smap_res, ha.2, sres_zero]

theorem res_inj (q : ℕ) (i : ℤ) : ∀ s, Injective ((res _ (tw q i)).X s) := fun s => by
  unfold res; infer_instance

theorem res_neg (q : ℕ) (i : ℤ) : ∀ s < 0, IsZero ((res _ (tw q i)).X s) := fun s hs => by
  unfold res; exact CochainComplex.isZero_of_isStrictlyGE _ 0 s hs

theorem LeafDescOSep_of : LeafDescOSep := by
  intro hD hF q X U m i hL s hs
  have h1 : ∀ n < m, ∀ (W : X.Opens), ∀ a ∈ Zc (res _ (tw q i)) (W.ι ⁻¹ᵁ U) n, ∀ x ∈ W,
      ∃ (V : X.Opens) (h : V ≤ W), x ∈ V ∧ Bd (res _ (tw q i)) (V.ι ⁻¹ᵁ U) n (rs h a) := by
    intro n hn W a ha x hx
    obtain ⟨V, hVW, hxV, hV⟩ := hL x W hx
    obtain ⟨cls, -, hker, -⟩ := hD q n i
    have hz : rs hVW a ∈ Zc (res _ (tw q i)) (V.ι ⁻¹ᵁ U) n :=
      zc_res _ _ _ (le_comp' _ _ U _ (Scheme.homOfLE_ι _ _) le_rfl) a ha
    refine ⟨V, hVW, hxV, (hker _ ⟨_, hz⟩).1 ?_⟩
    have := hV n hn
    exact Subsingleton.elim _ _
  obtain ⟨cls, hsurj, hker, hnat⟩ := hD q m i
  obtain ⟨a, rfl⟩ := hsurj U s
  have hFl := (hF _ (res _ (tw q i)) (res_inj q i) (res_neg q i) X U m h1).1
  have hza' : Sec.res (⊤ : X.Opens).ι a.1 ∈ Zc (res _ (tw q i)) ((⊤ : X.Opens).ι ⁻¹ᵁ U) m :=
    zc_res _ _ _ le_rfl a.1 a.2
  have hB : Bd (res _ (tw q i)) ((⊤ : X.Opens).ι ⁻¹ᵁ U) m (Sec.res (⊤ : X.Opens).ι a.1) := by
    apply hFl ⊤
    intro x _
    by_cases hxU : x ∈ U
    · refine ⟨U, le_top, hxU, ⟨0, sres_zero _, ?_⟩⟩
      have e : rs (le_top : U ≤ ⊤) (Sec.res (⊤ : X.Opens).ι a.1) = 0 := by
        unfold rs; rw [sres_comp, Scheme.homOfLE_ι]; exact a.2.1
      rw [e]; exact smap_zero _
    · obtain ⟨V, hxV, hV0⟩ := hs x hxU
      refine ⟨V, le_top, hxV, ?_⟩
      have e : rs (le_top : V ≤ ⊤) (Sec.res (⊤ : X.Opens).ι a.1) = Sec.res V.ι a.1 := by
        unfold rs; rw [sres_comp, Scheme.homOfLE_ι]
      have hz : Sec.res V.ι a.1 ∈ Zc (res _ (tw q i)) (V.ι ⁻¹ᵁ U) m := zc_res _ _ _ le_rfl a.1 a.2
      rw [e]
      refine (hker _ (⟨_, hz⟩ : Zc _ _ _)).1 ?_
      rw [← hnat V.ι (V.ι ⁻¹ᵁ U) U le_rfl a ⟨_, hz⟩ rfl]
      exact hV0
  have h0 := (hker _ (⟨_, hza'⟩ : Zc _ _ _)).2 hB
  rw [← hnat (⊤ : X.Opens).ι _ U le_rfl a ⟨_, hza'⟩ rfl] at h0
  have hle : U ≤ X.topIso.inv ⁻¹ᵁ ((⊤ : X.Opens).ι ⁻¹ᵁ U) :=
    le_comp' _ _ U (𝟙 X) (Scheme.toIso_inv_ι X) (fun x hx => hx)
  have hid : U ≤ (𝟙 X) ⁻¹ᵁ U := fun x hx => hx
  have key := pull_pull X.topIso.inv (⊤ : X.Opens).ι (Scheme.toIso_inv_ι X) U _ U hle le_rfl hid m i (cls U a)
  rw [h0, map_zero, Hs_pull_id] at key
  exact key.symm

end LateralTheory.CohomologicalPurity.Cl
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafDescPfGlue
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Cl

theorem le_of_comp {Y Z X : Scheme.{0}} {W : Y.Opens} {V : Z.Opens} (f : Y ⟶ Z) (g : Z ⟶ X) (U : X.Opens)
    (hV : V = g ⁻¹ᵁ U) (k : Y ⟶ X) (hk : f ≫ g = k) (hW : W ≤ k ⁻¹ᵁ U) : W ≤ f ⁻¹ᵁ V := by
  subst hV hk; intro w hw; exact hW hw

theorem pre_comp {Y Z X : Scheme.{0}} (f : Y ⟶ Z) (g : Z ⟶ X) (V : Z.Opens) (U : X.Opens) (hV : V = g ⁻¹ᵁ U) :
    f ⁻¹ᵁ V = (f ≫ g) ⁻¹ᵁ U := by
  subst hV; ext; rfl

theorem LeafPcGlue_pf : LeafPcGlue := by
  intro q X U m i hG A p s hcov H
  let E := fun a => Equiv.ofBijective _ (pc_bij (q := q) (p a) m i)
  obtain ⟨c, hc⟩ := hG A (fun a => (p a).j.opensRange) (fun a => (E a).symm (s a)) (fun x hx => hcov x hx) (by
    intro a b x hxa hxb hxU
    obtain ⟨y, rfl⟩ : x ∈ Set.range (p a).j := hxa
    obtain ⟨t, u, h, hcomm, ⟨z, rfl⟩, heq⟩ := H a b y hxU hxb
    let P : Pc U := ⟨t.Y, t.j ≫ (p a).j, inferInstance, t.V, t.hV.trans (pre_comp _ _ _ U (p a).hV)⟩
    have ha : P.j.opensRange ≤ (p a).j.opensRange := by rintro _ ⟨w, rfl⟩; exact ⟨t.j w, rfl⟩
    have hb : P.j.opensRange ≤ (p b).j.opensRange := by
      rintro _ ⟨w, rfl⟩
      refine ⟨u w, ?_⟩
      change (u ≫ (p b).j) w = (t.j ≫ (p a).j) w
      rw [hcomm]
    have ea : P.j.isoOpensRange.hom ≫ X.homOfLE ha = t.j ≫ (p a).j.isoOpensRange.hom := by
      rw [← cancel_mono ((p a).j.opensRange.ι)]
      simp only [Category.assoc, Scheme.homOfLE_ι, Scheme.Hom.isoOpensRange_hom_ι]; rfl
    have eb : P.j.isoOpensRange.hom ≫ X.homOfLE hb = u ≫ (p b).j.isoOpensRange.hom := by
      rw [← cancel_mono ((p b).j.opensRange.ι)]
      simp only [Category.assoc, Scheme.homOfLE_ι, Scheme.Hom.isoOpensRange_hom_ι]
      exact hcomm
    have hPV : P.V ≤ P.j ⁻¹ᵁ U := P.hV.le
    have ha' : P.j.opensRange.ι ⁻¹ᵁ U ≤ X.homOfLE ha ⁻¹ᵁ ((p a).j.opensRange.ι ⁻¹ᵁ U) :=
      le_of_comp _ _ U rfl _ (Scheme.homOfLE_ι _ _) le_rfl
    have hb' : P.j.opensRange.ι ⁻¹ᵁ U ≤ X.homOfLE hb ⁻¹ᵁ ((p b).j.opensRange.ι ⁻¹ᵁ U) :=
      le_of_comp _ _ U rfl _ (Scheme.homOfLE_ι _ _) le_rfl
    refine ⟨P.j.opensRange, ha, hb, ha', hb', ⟨z, rfl⟩, ?_⟩
    apply (pc_bij P m i).1
    have k1 : P.V ≤ (t.j ≫ (p a).j.isoOpensRange.hom) ⁻¹ᵁ ((p a).j.opensRange.ι ⁻¹ᵁ U) :=
      le_of_comp _ _ U rfl _ (by rw [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι]) hPV
    have k2 : P.V ≤ (u ≫ (p b).j.isoOpensRange.hom) ⁻¹ᵁ ((p b).j.opensRange.ι ⁻¹ᵁ U) :=
      le_of_comp _ _ U rfl _ (by rw [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, ← hcomm]) hPV
    rw [pull_pull _ _ ea _ _ _ _ _ k1, pull_pull _ _ eb _ _ _ _ _ k2,
      ← pull_pull t.j _ rfl _ _ _ t.hV.le (pc_le (p a)) k1, ← pull_pull u _ rfl _ _ _ h (pc_le (p b)) k2]
    change Hs.pull q _ m i (E a ((E a).symm (s a))) = Hs.pull q _ m i (E b ((E b).symm (s b)))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact heq)
  refine ⟨c, fun a => ?_⟩
  rw [pc_res, hc a]
  exact (E a).apply_symm_apply (s a)

theorem LeafDesc_of' (hD : LeafDict) (hF : LeafFlq) (hS : LeafDescOSep) (hG : LeafDescOGlue) : LeafDesc :=
  LeafDesc_of hD hF hS hG LeafPcGlue_pf

end LateralTheory.CohomologicalPurity.Cl
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafDictPfDbl
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.DictPf

theorem LeafDbl_pf : LeafDbl := by
  refine ⟨fun U => (PreservesPushout.iso disc (yoneda.map U.ι) (yoneda.map U.ι)).symm, ?_, ?_, ?_⟩
  · intro X U
    exact PreservesPushout.inl_iso_inv disc _ _
  · intro X U
    exact PreservesPushout.inr_iso_inv disc _ _
  · intro X' X f U' U h
    dsimp only
    refine (Iso.inv_comp_eq _).1 ?_
    set_option synthInstance.maxHeartbeats 200000 in
      apply pushout.hom_ext
    · have a1 : pushout.inl (opn U').hom (opn U').hom ≫ (PreservesPushout.iso disc (yoneda.map U'.ι) (yoneda.map U'.ι)).hom =
          disc.map (pushout.inl _ _) := PreservesPushout.inl_iso_hom disc _ _
      have a2 : disc.map (pushout.inl (yoneda.map U.ι) (yoneda.map U.ι)) ≫
          (PreservesPushout.iso disc (yoneda.map U.ι) (yoneda.map U.ι)).symm.hom = pushout.inl (opn U).hom (opn U).hom :=
        PreservesPushout.inl_iso_inv disc _ _
      have il : pushout.inl _ _ ≫ Qmap f U' U h = yoneda.map f ≫ pushout.inl _ _ := pushout.inl_desc _ _ _
      show pushout.inl (opn U').hom (opn U').hom ≫ (PreservesPushout.iso disc (yoneda.map U'.ι) (yoneda.map U'.ι)).hom ≫
        disc.map (Qmap f U' U h) ≫ (PreservesPushout.iso disc (yoneda.map U.ι) (yoneda.map U.ι)).symm.hom = _
      erw [← Category.assoc, a1, ← Category.assoc, ← Functor.map_comp, il, Functor.map_comp, Category.assoc, a2]
      exact (pushout.inl_desc _ _ _).symm
    · have a1 : pushout.inr (opn U').hom (opn U').hom ≫ (PreservesPushout.iso disc (yoneda.map U'.ι) (yoneda.map U'.ι)).hom =
          disc.map (pushout.inr _ _) := PreservesPushout.inr_iso_hom disc _ _
      have a2 : disc.map (pushout.inr (yoneda.map U.ι) (yoneda.map U.ι)) ≫
          (PreservesPushout.iso disc (yoneda.map U.ι) (yoneda.map U.ι)).symm.hom = pushout.inr (opn U).hom (opn U).hom :=
        PreservesPushout.inr_iso_inv disc _ _
      have il : pushout.inr _ _ ≫ Qmap f U' U h = yoneda.map f ≫ pushout.inr _ _ := pushout.inr_desc _ _ _
      show pushout.inr (opn U').hom (opn U').hom ≫ (PreservesPushout.iso disc (yoneda.map U'.ι) (yoneda.map U'.ι)).hom ≫
        disc.map (Qmap f U' U h) ≫ (PreservesPushout.iso disc (yoneda.map U.ι) (yoneda.map U.ι)).symm.hom = _
      erw [← Category.assoc, a1, ← Category.assoc, ← Functor.map_comp, il, Functor.map_comp, Category.assoc, a2]
      exact (pushout.inr_desc _ _ _).symm

theorem LeafDict_of' (hD : Cl.LeafDisc) (hE : LeafEv) (hP : LeafPair) : Cl.LeafDict := LeafDict_of hD hE hP LeafDbl_pf

end LateralTheory.CohomologicalPurity.DictPf
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafDiscPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Cl.DiscPf

variable {R : Type} [CommRing R]

abbrev Cd (R : Type) [CommRing R] (P : PSh) : Cx R := (chains R).obj (disc.obj P)

abbrev e0 (R : Type) [CommRing R] (P : PSh) : (Cd R P).X (-((0 : ℕ) : ℤ)) ≅ (free R).obj P := chainsXIso R (disc.obj P) 0

theorem isZero_pos (P : PSh) (j : ℤ) (hj : 0 < j) : IsZero ((Cd R P).X j) :=
  HomologicalComplex.isZero_extend_X ((chainsN R).obj (disc.obj P)) ComplexShape.embeddingDownNat j
    (fun i h => by change (-(i : ℤ)) = j at h; omega)

theorem d_one (P : PSh) : (Cd R P).d (-1) (-((0 : ℕ) : ℤ)) = 0 := by
  have h := LateralTheory.KummerTheory.chains_d R (disc.obj P) 0
  have hs : (∑ i : Fin (0 + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (SimplicialObject.δ (disc.obj P) i)) = 0 := by
    have : ∀ i : Fin (0 + 2), (free R).map (SimplicialObject.δ (disc.obj P) i) = 𝟙 _ := fun i => (free R).map_id _
    simp only [this]
    simp
  rw [hs, zero_comp] at h
  have : (chainsXIso R (disc.obj P) (0 + 1)).hom ≫ (chainsXIso R (disc.obj P) (0 + 1)).inv ≫
      (Cd R P).d (-((0 + 1 : ℕ) : ℤ)) (-((0 : ℕ) : ℤ)) = 0 := by rw [h, comp_zero]
  simpa using this

def coch {K : Cx R} {n : ℤ} (P : PSh) (a : (free R).obj P ⟶ K.X n) : Cochain (Cd R P) K n :=
  Cochain.single (p := -((0 : ℕ) : ℤ)) (q := n) ((e0 R P).hom ≫ a) n

theorem coch_add {K : Cx R} {n : ℤ} (P : PSh) (a b : (free R).obj P ⟶ K.X n) : coch P (a + b) = coch P a + coch P b := by
  ext p q hpq
  by_cases hp : p = -((0 : ℕ) : ℤ)
  · subst hp
    obtain rfl : q = n := by omega
    simp [coch, Cochain.single_v]
  · simp [coch, Cochain.single_v_eq_zero _ _ _ _ _ hp]

theorem delta_coch {K : Cx R} {n : ℤ} (P : PSh) (a : (free R).obj P ⟶ K.X n) :
    δ n (n + 1) (coch P a) = Cochain.single (p := -((0 : ℕ) : ℤ)) ((e0 R P).hom ≫ a ≫ K.d n (n + 1)) (n + 1) := by
  rw [coch, Cochain.δ_single _ n (n + 1) rfl (-1) (n + 1) (by simp) rfl, d_one, zero_comp, Cochain.single_zero, smul_zero,
    add_zero, Category.assoc]

theorem coch_cocycle {K : Cx R} {n : ℤ} (P : PSh) (a : (free R).obj P ⟶ K.X n) (ha : a ≫ K.d n (n + 1) = 0) :
    δ n (n + 1) (coch P a) = 0 := by
  rw [delta_coch, ha, comp_zero, Cochain.single_zero]

def cz {K : Cx R} {n : ℤ} (P : PSh) (a : (free R).obj P ⟶ K.X n) (ha : a ≫ K.d n (n + 1) = 0) : Cocycle (Cd R P) K n :=
  ⟨coch P a, (Cocycle.mem_iff n (n + 1) rfl _).2 (coch_cocycle P a ha)⟩

open Classical in
def cl (K : Cx R) (n : ℤ) (P : PSh) (a : (free R).obj P ⟶ K.X n) : CohomologyClass (Cd R P) K n :=
  if ha : a ≫ K.d n (n + 1) = 0 then CohomologyClass.mk (cz P a ha) else 0

theorem cl_eq {K : Cx R} {n : ℤ} (P : PSh) (a : (free R).obj P ⟶ K.X n) (ha : a ≫ K.d n (n + 1) = 0) :
    cl K n P a = CohomologyClass.mk (cz P a ha) := dif_pos ha

theorem cl_add {K : Cx R} {n : ℤ} (P : PSh) (a b : (free R).obj P ⟶ K.X n) (ha : a ≫ K.d n (n + 1) = 0)
    (hb : b ≫ K.d n (n + 1) = 0) : cl K n P (a + b) = cl K n P a + cl K n P b := by
  have hab : (a + b) ≫ K.d n (n + 1) = 0 := by rw [Preadditive.add_comp, ha, hb, add_zero]
  rw [cl_eq _ _ ha, cl_eq _ _ hb, cl_eq _ _ hab, ← CohomologyClass.mk_add]
  congr 1
  exact Cocycle.ext (coch_add P a b)

theorem cl_zero_iff {K : Cx R} {n : ℤ} (P : PSh) (a : (free R).obj P ⟶ K.X n) (ha : a ≫ K.d n (n + 1) = 0) :
    cl K n P a = 0 ↔ ∃ b, b ≫ K.d (n - 1) n = a := by
  rw [cl_eq _ _ ha, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
  constructor
  · rintro ⟨β, hβ⟩
    refine ⟨(e0 R P).inv ≫ β.v (-((0 : ℕ) : ℤ)) (n - 1) (by omega), ?_⟩
    have h1 := Cochain.congr_v hβ (-((0 : ℕ) : ℤ)) n (by omega)
    rw [δ_v (n - 1) n (by omega) β _ n _ (n - 1) (-((0 : ℕ) : ℤ) + 1) (by omega) rfl,
      (isZero_pos P (-((0 : ℕ) : ℤ) + 1) (by omega)).eq_of_tgt ((Cd R P).d (-((0 : ℕ) : ℤ)) _) 0, zero_comp, smul_zero, add_zero] at h1
    have h2 : (cz P a ha).1.v (-((0 : ℕ) : ℤ)) n (by omega) = (e0 R P).hom ≫ a := Cochain.single_v _ _ _
    rw [h2] at h1
    rw [Category.assoc, h1, Iso.inv_hom_id_assoc]
  · rintro ⟨b, rfl⟩
    refine ⟨Cochain.single (p := -((0 : ℕ) : ℤ)) (q := n - 1) ((e0 R P).hom ≫ b) (n - 1), ?_⟩
    rw [Cochain.δ_single _ (n - 1) n (by omega) (-1) n (by simp) (by omega), d_one, zero_comp, Cochain.single_zero, smul_zero,
      add_zero, Category.assoc]
    rfl

theorem etale_discrete_chains_degree_zero_iso_free_naturality (P' P : PSh) (f : P' ⟶ P) :
    ((chains R).map (disc.map f)).f (-((0 : ℕ) : ℤ)) ≫ (e0 R P).hom = (e0 R P').hom ≫ (free R).map f := by
  dsimp only [chains, e0, chainsXIso, Functor.comp_map, Functor.comp_obj]
  erw [HomologicalComplex.extendMap_f _ _ (i := 0) rfl]
  erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

theorem cl_nat {K : Cx R} {n : ℤ} (P' P : PSh) (f : P' ⟶ P) (a : (free R).obj P ⟶ K.X n) (ha : a ≫ K.d n (n + 1) = 0) :
    cpre (Cocycle.ofHom ((chains R).map (disc.map f))) K n n (zero_add n) (cl K n P a) = cl K n P' ((free R).map f ≫ a) := by
  have ha' : ((free R).map f ≫ a) ≫ K.d n (n + 1) = 0 := by rw [Category.assoc, ha, comp_zero]
  rw [cl_eq _ _ ha, cl_eq _ _ ha', cpre_mk]
  congr 1
  apply Cocycle.ext
  refine Cochain.ext _ _ (fun p q hpq => ?_)
  change ((Cochain.ofHom ((chains R).map (disc.map f))).comp (coch P a) (zero_add n)).v p q hpq = (coch P' _).v p q hpq
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  by_cases hp : p = -((0 : ℕ) : ℤ)
  · subst hp
    obtain rfl : q = n := by omega
    simp only [coch, Cochain.single_v]
    rw [← Category.assoc, etale_discrete_chains_degree_zero_iso_free_naturality, Category.assoc]
  · simp only [coch, Cochain.single_v_eq_zero _ _ _ _ _ hp, comp_zero]

end LateralTheory.CohomologicalPurity.Cl.DiscPf

namespace LateralTheory.CohomologicalPurity.Cl


open DiscPf in
def LeafDiscNrm : Prop := ∀ (R : Type) [CommRing R] (K : Cx R) (n : ℤ) (P : PSh)
  (z : Cocycle ((chains R).obj (disc.obj P)) K n),
  ∃ (a : (free R).obj P ⟶ K.X n) (β : Cochain ((chains R).obj (disc.obj P)) K (n - 1)),
    z.1 = Cochain.single (p := -((0 : ℕ) : ℤ)) (q := n) ((chainsXIso R (disc.obj P) 0).hom ≫ a) n + δ (n - 1) n β

open DiscPf in
theorem LeafDisc_of (hN : LeafDiscNrm) : LeafDisc := by
  intro R _ K n
  refine ⟨cl K n, fun P a b ha hb => cl_add P a b ha hb, ?_, fun P a ha => cl_zero_iff P a ha,
    fun P' P f a ha => cl_nat P' P f a ha⟩
  intro P x
  obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
  obtain ⟨a, β, hz⟩ := hN R K n P z
  have hz0 : δ n (n + 1) z.1 = 0 := (Cocycle.mem_iff n (n + 1) rfl z.1).1 z.2
  have hc : δ n (n + 1) (coch P a) = 0 := by
    have := hz0
    rw [hz, δ_add, δ_δ, add_zero] at this
    exact this
  have ha : a ≫ K.d n (n + 1) = 0 := by
    rw [delta_coch] at hc
    have h1 := Cochain.congr_v hc (-((0 : ℕ) : ℤ)) (n + 1) (by omega)
    rw [Cochain.single_v, Cochain.zero_v] at h1
    exact (cancel_epi (e0 R P).hom).1 (h1.trans (comp_zero).symm)
  refine ⟨a, ha, ?_⟩
  rw [cl_eq _ _ ha, ← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨-β, ?_⟩
  rw [δ_neg]
  change _ = coch P a - z.1
  rw [hz]
  unfold coch
  abel

end LateralTheory.CohomologicalPurity.Cl
end
end

