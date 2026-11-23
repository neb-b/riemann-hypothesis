module

public import Development.EtaleCohomology.CohomologicalPurity.Bundle0003
public import Development.EtaleCohomology.CohomologicalPurity.LeafClCut
public import Development.EtaleCohomology.CohomologicalPurity.Bundle0004

@[expose] public section

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafExcFormalPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity

theorem chainsInrSq (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P) :
    (chains (ZMod q)).map (dbl.inr P') ≫ (chains (ZMod q)).map (dbl.map φ) =
      (chains (ZMod q)).map φ.right ≫ (chains (ZMod q)).map (dbl.inr P) := by
  rw [← Functor.map_comp, ← Functor.map_comp, dbl.inr_map]

abbrev cokC (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P) :=
  cokernel.map ((chains (ZMod q)).map (dbl.inr P')) ((chains (ZMod q)).map (dbl.inr P))
    ((chains (ZMod q)).map φ.right) ((chains (ZMod q)).map (dbl.map φ)) (chainsInrSq q φ)

theorem HK.pull_comp' (R : Type) [CommRing R] {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (F : Shv R) (n : ℤ)
    (x : HK R M F n) : HK.pull R (f ≫ g) F n x = HK.pull R f F n (HK.pull R g F n x) := by
  rcases x.mk_surjective with ⟨z, rfl⟩
  simp only [HK.pull, HK.pre, cpre_mk]
  congr 1
  ext1
  simp [zcomp, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]

theorem HK.pull_id' (R : Type) [CommRing R] (K : Cx R) (F : Shv R) (n : ℤ) (x : HK R K F n) :
    HK.pull R (𝟙 K) F n x = x := by
  rcases x.mk_surjective with ⟨z, rfl⟩
  simp only [HK.pull, HK.pre, cpre_mk]
  congr 1
  ext1
  simp [zcomp]

theorem HK.pull_bij (R : Type) [CommRing R] {K L : Cx R} (f : K ⟶ L) [IsIso f] (F : Shv R) (n : ℤ) :
    Function.Bijective (HK.pull R f F n) := by
  refine Function.bijective_iff_has_inverse.2 ⟨HK.pull R (inv f) F n, fun x => ?_, fun x => ?_⟩
  · rw [← HK.pull_comp', IsIso.inv_hom_id, HK.pull_id']
  · rw [← HK.pull_comp', IsIso.hom_inv_id, HK.pull_id']

def LeafExcIdent : Prop := ∀ (q : ℕ) (n i : ℤ), ∃ e : ∀ P : Arrow Spc,
    HK (ZMod q) (cokernel ((chains (ZMod q)).map (dbl.inr P))) (tw q i) n ≃+ Hs q P n i,
  ∀ {P' P : Arrow Spc} (φ : P' ⟶ P) (x : HK (ZMod q) (cokernel ((chains (ZMod q)).map (dbl.inr P))) (tw q i) n),
    Hs.pull q φ n i (e P x) = e P' (HK.pull (ZMod q) (cokC q φ) (tw q i) n x)

def LeafExcCx : Prop := ∀ (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P), IsIso (cokC q φ) → Exc q φ

theorem LeafExcCx_of (hI : LeafExcIdent) : LeafExcCx := by
  intro q P' P φ hφ n i
  obtain ⟨e, he⟩ := hI q n i
  have hfun : ⇑(Hs.pull q φ n i) = ⇑(e P') ∘ ⇑(HK.pull (ZMod q) (cokC q φ) (tw q i) n) ∘ ⇑(e P).symm := by
    funext y
    obtain ⟨x, rfl⟩ := (e P).surjective y
    simp [he]
  rw [hfun]
  exact (e P').bijective.comp ((HK.pull_bij _ _ _ _).comp (e P).symm.bijective)

def LeafExcDeg : Prop := ∀ (q : ℕ) {P' P : Arrow Spc} (φ : P' ⟶ P),
  (∀ p : SimplexCategoryᵒᵖ, IsIso (cokernel.map ((free (ZMod q)).map (P'.hom.app p)) ((free (ZMod q)).map (P.hom.app p))
    ((free (ZMod q)).map (φ.left.app p)) ((free (ZMod q)).map (φ.right.app p)) (freeSq _ φ p))) → IsIso (cokC q φ)

theorem LeafExcFormal_of (hI : LeafExcIdent) (hD : LeafExcDeg) : LeafExcFormal := by
  intro q P' P φ h
  exact LeafExcCx_of hI q φ (hD q φ h)

end LateralTheory.CohomologicalPurity
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafFlqPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Cl.Flq

abbrev ZN {R : Type} [CommRing R] (K : Cx R) {X : Scheme.{0}} (U : X.Opens) (n : ℤ) (W : X.Opens) :
    AddSubgroup (Sec (K.X n) W.toScheme) := Zc K (W.ι ⁻¹ᵁ U) n

def BN {R : Type} [CommRing R] (K : Cx R) {X : Scheme.{0}} (U : X.Opens) (n : ℤ) (W : X.Opens) :
    AddSubgroup (Sec (K.X n) W.toScheme) := AddSubgroup.closure {a | Bd K (W.ι ⁻¹ᵁ U) n a}

abbrev OK {R : Type} [CommRing R] {G : Shv R} {X : Scheme.{0}} (N : ∀ W : X.Opens, AddSubgroup (Sec G W.toScheme)) : Prop :=
  (∀ (V W : X.Opens) (h : V ≤ W), ∀ a ∈ N W, rs h a ∈ N V) ∧
  (∀ (W : X.Opens) (a : Sec G W.toScheme), (∀ x ∈ W, ∃ (V : X.Opens) (h : V ≤ W), x ∈ V ∧ rs h a ∈ N V) → a ∈ N W) ∧
  (∀ (V W : X.Opens) (h : V ≤ W), ∀ a ∈ N V, ∃ b ∈ N W, rs h b = a)

def LeafBdAdd : Prop := ∀ (R : Type) [CommRing R] (K : Cx R) (X : Scheme.{0}) (U : X.Opens) (n : ℤ) (W : X.Opens)
  (a : Sec (K.X n) W.toScheme), a ∈ BN K U n W → Bd K (W.ι ⁻¹ᵁ U) n a

def LeafBZ : Prop := ∀ (R : Type) [CommRing R] (K : Cx R) (X : Scheme.{0}) (U : X.Opens) (n : ℤ) (W : X.Opens)
  (a : Sec (K.X n) W.toScheme), Bd K (W.ι ⁻¹ᵁ U) n a → a ∈ ZN K U n W

def LeafZloc : Prop := ∀ (R : Type) [CommRing R] (K : Cx R) (X : Scheme.{0}) (U : X.Opens) (n : ℤ),
  (∀ (V W : X.Opens) (h : V ≤ W), ∀ a ∈ ZN K U n W, rs h a ∈ ZN K U n V) ∧
  (∀ (W : X.Opens) (a : Sec (K.X n) W.toScheme), (∀ x ∈ W, ∃ (V : X.Opens) (h : V ≤ W), x ∈ V ∧ rs h a ∈ ZN K U n V) →
    a ∈ ZN K U n W)

def LeafZero : Prop := ∀ (R : Type) [CommRing R] (K : Cx R) (X : Scheme.{0}) (U : X.Opens) (n : ℤ),
  IsZero (K.X n) → OK (ZN K U n)

def LeafStep : Prop := ∀ (R : Type) [CommRing R] (K : Cx R), LateralTheory.CohomologicalPurity.Cl.LeafZorn → (∀ s, Injective (K.X s)) →
  ∀ (X : Scheme.{0}) (U : X.Opens) (n : ℤ), OK (ZN K U (n - 1)) → OK (BN K U n)

def LeafTop : Prop := ∀ (R : Type) [CommRing R] (K : Cx R) (X : Scheme.{0}) (U : X.Opens) (n : ℤ)
  (c' : Sec (K.X n) (⊤ : X.Opens).toScheme), c' ∈ ZN K U n ⊤ →
  ∃ c ∈ Zc K U n, ∀ V : X.Opens, Sec.res V.ι c = rs le_top c'

def LeafRs : Prop := ∀ (R : Type) [CommRing R] (G : Shv R) (X : Scheme.{0}) (T V W : X.Opens) (h : V ≤ W) (h' : T ≤ V)
  (a b : Sec G W.toScheme), rs h (a - b) = rs h a - rs h b ∧ rs h' (rs h a) = rs (h'.trans h) a

theorem LeafRs_of : LeafRs := by
  intro R _ G X T V W h h' a b
  refine ⟨?_, ?_⟩
  · show ((G.obj.map (X.homOfLE h).op).hom (a - b)) = _
    exact map_sub _ a b
  · show ((G.obj.map (X.homOfLE h').op).hom ((G.obj.map (X.homOfLE h).op).hom a)) = (G.obj.map (X.homOfLE (h'.trans h)).op).hom a
    have e : X.homOfLE (h'.trans h) = X.homOfLE h' ≫ X.homOfLE h := (Scheme.homOfLE_homOfLE X h' h).symm
    rw [e, op_comp, Functor.map_comp]
    rfl

theorem LeafFlq_of (hZ : LateralTheory.CohomologicalPurity.Cl.LeafZorn) (hA : LeafBdAdd) (hBZ : LeafBZ) (hL : LeafZloc) (h0 : LeafZero)
    (hS : LeafStep) (hT : LeafTop) : LateralTheory.CohomologicalPurity.Cl.LeafFlq := by
  intro R _ K hinj hneg X U m H
  have hR := LeafRs_of
  have key : ∀ n, n < m → OK (ZN K U (n - 1)) → OK (ZN K U n) := by
    intro n hn hprev
    have hB := hS R K hZ hinj X U n hprev
    have eq : ZN K U n = BN K U n := by
      funext W; ext a; constructor
      · intro ha; apply hB.2.1 W a; intro x hx
        obtain ⟨V, h, hxV, hb⟩ := H n hn W a ha x hx
        exact ⟨V, h, hxV, AddSubgroup.subset_closure hb⟩
      · intro ha; exact hBZ R K X U n W a (hA R K X U n W a ha)
    rw [eq]; exact hB
  have P : ∀ k : ℕ, (k : ℤ) < m → OK (ZN K U (k : ℤ)) := by
    intro k
    induction k with
    | zero => intro h; exact key _ h (h0 R K X U _ (hneg _ (by norm_num)))
    | succ k ih =>
      intro h
      apply key _ h
      have e : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by push_cast; ring
      rw [e]; exact ih (by omega)
  have hm : OK (ZN K U (m - 1)) := by
    by_cases hc : m - 1 < 0
    · exact h0 R K X U _ (hneg _ hc)
    · have e : ((m - 1).toNat : ℤ) = m - 1 := Int.toNat_of_nonneg (by omega)
      have := P (m - 1).toNat (by omega)
      rw [e] at this; exact this
  have hBm := hS R K hZ hinj X U m hm
  refine ⟨fun W a hloc => hA R K X U m W a (hBm.2.1 W a fun x hx => ?_), ?_⟩
  · obtain ⟨V, h, hxV, hb⟩ := hloc x hx
    exact ⟨V, h, hxV, AddSubgroup.subset_closure hb⟩
  intro A V a ha hcov hagree
  obtain ⟨c', hc'⟩ := hZ R (K.X m) X (BN K U m) hBm.1 hBm.2.1 hBm.2.2 ⊤ A V (fun _ => le_top) a
    (fun x _ => hcov x) (by
      intro k l
      apply hBm.2.1
      intro x hx
      obtain ⟨hxk, hxl⟩ := hx
      obtain ⟨T, hk, hl, hxT, hb⟩ := hagree k l x hxk hxl
      refine ⟨T, le_inf hk hl, hxT, ?_⟩
      have e : rs (le_inf hk hl) (rs (inf_le_left : V k ⊓ V l ≤ V k) (a k) - rs (inf_le_right : V k ⊓ V l ≤ V l) (a l))
          = rs hk (a k) - rs hl (a l) := by
        have rsub : ∀ {V W : X.Opens} (h : V ≤ W) (x y : Sec (K.X m) W.toScheme), rs h (x - y) = rs h x - rs h y :=
          fun {V W} h x y => (hR R _ X V V W h le_rfl x y).1
        have rrs : ∀ {T V W : X.Opens} (h : V ≤ W) (h' : T ≤ V) (x : Sec (K.X m) W.toScheme),
            rs h' (rs h x) = rs (h'.trans h) x := fun {T V W} h h' x => (hR R _ X T V W h h' x x).2
        rw [rsub, rrs, rrs]
      rw [e]; exact AddSubgroup.subset_closure hb)
  have hmem : c' ∈ ZN K U m ⊤ := by
    apply (hL R K X U m).2 ⊤ c'
    intro x _
    obtain ⟨k, hk⟩ := hcov x
    refine ⟨V k, le_top, hk, ?_⟩
    have h1 := hBZ R K X U m (V k) _ (hA R K X U m (V k) _ (hc' k))
    have h2 : a k ∈ ZN K U m (V k) := ha k
    simpa using add_mem h1 h2
  obtain ⟨c, hc, hcV⟩ := hT R K X U m c' hmem
  refine ⟨c, hc, fun k => ?_⟩
  rw [hcV]; exact hA R K X U m (V k) _ (hc' k)

end LateralTheory.CohomologicalPurity.Cl.Flq
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafGenPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.CohomologicalPurity.Cl

def LeafGenCart : Prop := ∀ {X Z : Scheme.{0}} (ι : Z ⟶ X) [IsClosedImmersion ι] (V : X.affineOpens) (r : Γ(X, V.1)),
  ∃ z : Spec (CommRingCat.of (Localization.Away r ⧸ (ι.ker.ideal V).map (algebraMap Γ(X, V.1) (Localization.Away r)))) ⟶ Z,
    IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _))) z
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1) (Localization.Away r))) ≫ V.2.fromSpec) ι

def LeafGenKer : Prop := ∀ {X Z : Scheme.{0}} (ι : Z ⟶ X) [IsClosedImmersion ι] (V : X.affineOpens) (r : Γ(X, V.1)),
  (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      ((ι.ker.ideal V).map (algebraMap Γ(X, V.1) (Localization.Away r)))))).ker =
    ι.ker.comap (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1) (Localization.Away r))) ≫ V.2.fromSpec)

theorem LeafGenCart_of (hK : LeafGenKer) : LeafGenCart := by
  intro X Z ι _ V r
  have hK' := hK ι V r
  have hm : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      ((ι.ker.ideal V).map (algebraMap Γ(X, V.1) (Localization.Away r)))))) :=
    IsClosedImmersion.spec_of_quotient_mk (R := CommRingCat.of (Localization.Away r)) _
  have hfst := Scheme.IdealSheafData.ker_fst_of_isClosedImmersion ι
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1) (Localization.Away r))) ≫ V.2.fromSpec)
  let e := IsClosedImmersion.lift (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V.1)
    (Localization.Away r))) ≫ V.2.fromSpec) ι) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      ((ι.ker.ideal V).map (algebraMap Γ(X, V.1) (Localization.Away r)))))) (by rw [hfst, hK'])
  refine ⟨e ≫ pullback.snd _ _, isPullback_of_isClosedImmersion _ ι _ _ ?_ hK'.symm⟩
  rw [Category.assoc, ← pullback.condition, IsClosedImmersion.lift_fac_assoc]

theorem span_loc {d : ℕ} {A : Type} [CommRing A] (I : Ideal A) (a : Fin d → A) (r : A) (ha : ∀ j, a j ∈ I)
    (hra : ∀ y ∈ I, r * y ∈ Ideal.span (Set.range a)) :
    Ideal.span (Set.range (algebraMap A (Localization.Away r) ∘ a)) = I.map (algebraMap A (Localization.Away r)) := by
  rw [Set.range_comp, ← Ideal.map_span]
  apply le_antisymm
  · exact Ideal.map_mono (Ideal.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact ha j))
  · rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [Ideal.mem_comap]
    have hu : IsUnit (algebraMap A (Localization.Away r) r) := IsLocalization.Away.algebraMap_isUnit r
    have h1 : algebraMap A (Localization.Away r) (r * y) ∈ (Ideal.span (Set.range a)).map (algebraMap A (Localization.Away r)) :=
      Ideal.mem_map_of_mem _ (hra y hy)
    rw [map_mul] at h1
    obtain ⟨u, hu'⟩ := hu
    have := Ideal.mul_mem_left _ (↑u⁻¹ : Localization.Away r) h1
    rwa [← hu', ← mul_assoc, Units.inv_mul, one_mul] at this

theorem LeafGen_of (hC : LeafChart) (hGR : LeafGenRing) (hKer : LeafGenKer) : LeafGen := by
  have hCart : LeafGenCart := LeafGenCart_of @hKer
  intro d P x hx
  obtain ⟨V, hxV, -, hfg, hch⟩ := hC d P x ⊤ trivial
  obtain ⟨a, r, hr1, ha, hra⟩ := hGR d Γ(P.X, V.1) (P.ι.ker.ideal V) hfg hch
  have := P.cl
  obtain ⟨z, hz⟩ := hCart P.ι V r
  have hxr : x ∈ Set.range P.ι := by
    by_contra h; exact hx (by rw [← SetLike.mem_coe, P.hU]; exact h)
  refine ⟨⟨Localization.Away r, (P.ι.ker.ideal V).map (algebraMap _ _), algebraMap _ _ ∘ a,
    span_loc _ a r ha hra, Spec.map (CommRingCat.ofHom (algebraMap _ _)) ≫ V.2.fromSpec, z, ?_, hz⟩, ?_, ?_⟩
  · intro y hy
    change (_ ≫ V.2.fromSpec) y ∈ P.U
    rw [← SetLike.mem_coe, P.hU]
    rintro ⟨t, ht⟩
    obtain ⟨s, hs, -⟩ := Scheme.exists_preimage_of_isPullback hz y t ht.symm
    apply hy
    rw [← hs]
    intro g hg
    change Ideal.Quotient.mk _ g ∈ s.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hg]; exact zero_mem _
  · change IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap _ _)) ≫ V.2.fromSpec)
    have h1 := Scheme.isOpenImmersion_SpecMap_localizationAway (R := Γ(P.X, V.1)) r
    have h2 := V.2.isOpenImmersion_fromSpec
    infer_instance
  · have hxV' : x ∈ (V.1 : Set P.X) := hxV
    rw [← V.2.range_fromSpec] at hxV'
    obtain ⟨p, hp⟩ := hxV'
    have hz0 : x ∈ P.X.zeroLocus (U := V.1) (P.ι.ker.ideal V) := by
      rw [← Scheme.IdealSheafData.mem_support_iff_of_mem hxV, ← SetLike.mem_coe, Scheme.Hom.support_ker]; exact subset_closure hxr
    have hIp : ∀ g ∈ P.ι.ker.ideal V, g ∈ p.asIdeal := by
      intro g hg
      have h1 := (Scheme.mem_zeroLocus_iff _ _ _).1 hz0 g hg
      by_contra h2
      apply h1
      rw [← hp]
      change p ∈ V.2.fromSpec ⁻¹ᵁ P.X.basicOpen g
      rw [V.2.fromSpec_preimage_basicOpen]; exact h2
    have hr : p ∈ PrimeSpectrum.basicOpen r := by
      intro h; apply p.2.ne_top; rw [Ideal.eq_top_iff_one]
      have := p.asIdeal.sub_mem h (hIp _ hr1); simpa using this
    have hr' : p ∈ Set.range (PrimeSpectrum.comap (algebraMap Γ(P.X, V.1) (Localization.Away r))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]; exact hr
    obtain ⟨q, hq⟩ := hr'
    refine ⟨q, ?_⟩
    show V.2.fromSpec ((Spec.map (CommRingCat.ofHom (algebraMap Γ(P.X, V.1) (Localization.Away r)))) q) = x
    rw [← hp]
    exact congrArg V.2.fromSpec hq

end LateralTheory.CohomologicalPurity.Cl
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafGenRingPf
section
noncomputable section

namespace LateralTheory.CohomologicalPurity.GenRingPf

open LateralTheory.CohomologicalPurity

theorem inj_sq {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A) (h : Nbhd φ I) (y : A)
    (hy : φ y ∈ (I ^ 2).map φ) : y ∈ I ^ 2 := by
  let _ := φ.toAlgebra
  have _ : Algebra.Etale A B := h.1
  let e := RingEquiv.ofBijective _ h.2
  let f : B →ₐ[A] A ⧸ I :=
    { toRingHom := e.symm.toRingHom.comp (Ideal.Quotient.mk (I.map φ))
      commutes' := fun a => by
        change e.symm (Ideal.Quotient.mk _ (φ a)) = Ideal.Quotient.mk I a
        rw [e.symm_apply_eq]
        rfl }
  let g : A ⧸ I ^ 2 →ₐ[A] A ⧸ I := Ideal.Quotient.factorₐ A (Ideal.pow_le_self two_ne_zero)
  have hg : Function.Surjective g := Ideal.Quotient.factor_surjective (Ideal.pow_le_self two_ne_zero)
  have hn : IsNilpotent (RingHom.ker (g : A ⧸ I ^ 2 →+* A ⧸ I)) := by
    refine ⟨2, ?_⟩
    rw [Ideal.zero_eq_bot, ← le_bot_iff]
    refine le_trans (le_of_eq (pow_two _)) ?_
    refine Ideal.mul_le.mpr fun x hx z hz => ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hx' : x ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hx
    have hz' : z ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hz
    rw [Ideal.mem_bot, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, pow_two]
    exact Ideal.mul_mem_mul hx' hz'
  let σ := Algebra.FormallySmooth.liftOfSurjective f g hg hn
  have hσ : ∀ a, σ (φ a) = Ideal.Quotient.mk (I ^ 2) a := fun a => σ.commutes a
  have hc : (σ : B →+* A ⧸ I ^ 2).comp φ = Ideal.Quotient.mk (I ^ 2) := RingHom.ext hσ
  have h0 := Ideal.mem_map_of_mem (σ : B →+* A ⧸ I ^ 2) hy
  rw [Ideal.map_map, hc, Ideal.map_quotient_self, Ideal.mem_bot] at h0
  change σ (φ y) = 0 at h0
  rw [hσ] at h0
  exact Ideal.Quotient.eq_zero_iff_mem.mp h0

theorem approx {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A)
    (hs : ∀ b : B, ∃ c : A, b - φ c ∈ I.map φ) (J : Ideal A) (T : Set B)
    (hT : ∀ t ∈ T, t ∈ I.map φ ∧ ∃ c ∈ J, t - φ c ∈ I.map φ ^ 2) :
    ∀ z ∈ Ideal.span T, ∃ c ∈ J, z - φ c ∈ I.map φ ^ 2 := by
  have hle : Ideal.span T ≤ I.map φ := Ideal.span_le.mpr fun t ht => (hT t ht).1
  intro z hz
  induction hz using Submodule.span_induction with
  | mem t ht => exact (hT t ht).2
  | zero => exact ⟨0, J.zero_mem, by simp⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨c, hc, hxc⟩ := ihx
    obtain ⟨c', hc', hyc⟩ := ihy
    refine ⟨c + c', J.add_mem hc hc', ?_⟩
    have : x + y - φ (c + c') = (x - φ c) + (y - φ c') := by rw [map_add (f := _)]; ring
    rw [this]; exact Ideal.add_mem _ hxc hyc
  | smul b x hx ih =>
    obtain ⟨c, hc, hxc⟩ := ih
    obtain ⟨c', hbc⟩ := hs b
    refine ⟨c' * c, J.mul_mem_left _ hc, ?_⟩
    have : b • x - φ (c' * c) = (b - φ c') * x + φ c' * (x - φ c) := by
      rw [map_mul, smul_eq_mul]; ring
    rw [this]
    refine Ideal.add_mem _ ?_ (Ideal.mul_mem_left _ _ hxc)
    rw [pow_two]
    exact Ideal.mul_mem_mul hbc (hle hx)

end LateralTheory.CohomologicalPurity.GenRingPf

open LateralTheory.CohomologicalPurity.GenRingPf in
theorem LateralTheory.CohomologicalPurity.Cl.LeafGenRing_of : LateralTheory.CohomologicalPurity.Cl.LeafGenRing := by
  intro d A _ I hI hC
  obtain ⟨B, _, φ, ψ, hN, _, hspan, _⟩ := hC
  have hs : ∀ b : B, ∃ c : A, b - φ c ∈ I.map φ := by
    intro b
    obtain ⟨x, hx⟩ := hN.2.2 (Ideal.Quotient.mk _ b)
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨c, ?_⟩
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq] at hx
    have := (I.map φ).neg_mem hx
    rwa [neg_sub] at this
  have hI1 : ∀ z ∈ I.map φ, ∃ c ∈ I, z - φ c ∈ I.map φ ^ 2 :=
    approx φ I hs I (φ '' I) (fun t ht => by
      obtain ⟨i, hi, rfl⟩ := ht
      exact ⟨Ideal.mem_map_of_mem _ hi, i, hi, by simp⟩)
  have hX : ∀ j, ∃ c ∈ I, ψ (MvPolynomial.X j) - φ c ∈ I.map φ ^ 2 := fun j =>
    hI1 _ (hspan ▸ Ideal.subset_span ⟨j, rfl⟩)
  choose a ha hax using hX
  have hle : I ≤ Ideal.span (Set.range a) ⊔ I • I := by
    intro y hy
    have hy' : φ y ∈ Ideal.span (Set.range fun j => ψ (MvPolynomial.X j)) := hspan ▸ Ideal.mem_map_of_mem _ hy
    obtain ⟨c, hc, hyc⟩ := approx φ I hs (Ideal.span (Set.range a)) _ (fun t ht => by
      obtain ⟨j, rfl⟩ := ht
      exact ⟨hspan ▸ Ideal.subset_span ⟨j, rfl⟩, a j, Ideal.subset_span ⟨j, rfl⟩, hax j⟩) _ hy'
    have h2 : y - c ∈ I ^ 2 := inj_sq φ I hN _ (by rw [map_sub, Ideal.map_pow]; exact hyc)
    have : y = c + (y - c) := by ring
    rw [this]
    refine Submodule.add_mem_sup hc ?_
    rw [Ideal.smul_eq_mul, ← pow_two]; exact h2
  obtain ⟨r, hr, hrle⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup hI le_rfl hle
  refine ⟨a, r, hr, ha, fun y hy => ?_⟩
  have := hrle (Submodule.smul_mem_pointwise_smul y r I hy)
  simpa [smul_eq_mul] using this
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafGoodPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Bd

theorem pb_v {R : Type} [CommRing R] {A B I : Cx R} (f : A ⟶ B) {n : ℤ} (c : Cochain B I n) (p q : ℤ) (hpq : p + n = q) :
    (pb f c).v p q hpq = f.f p ≫ c.v p q hpq := by
  simp [pb, Cochain.zero_cochain_comp_v, Cochain.ofHom_v]

theorem LeafGood_of : LeafGood := by
  intro R _ A B D i l r I hm hp hI
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply HomologicalComplex.hom_ext
    intro p
    simpa using (hp p).w
  · intro n a
    refine ⟨Cochain.mk (fun p q hpq => Injective.factorThru (a.v p q hpq) (i.f p)), ?_⟩
    refine Cochain.ext _ _ (fun p q hpq => ?_)
    rw [pb_v]
    simp [Cochain.mk_v]
  · intro n c c' h
    refine ⟨Cochain.mk (fun p q hpq => (hp p).desc (c.v p q hpq) (c'.v p q hpq) (by
      have := congrArg (fun x => x.v p q hpq) h
      simpa only [pb_v] using this)), ?_, ?_⟩
    · refine Cochain.ext _ _ (fun p q hpq => ?_); rw [pb_v]; simp [Cochain.mk_v]
    · refine Cochain.ext _ _ (fun p q hpq => ?_); rw [pb_v]; simp [Cochain.mk_v]
  · intro n b b' h1 h2
    refine Cochain.ext _ _ (fun p q hpq => ?_)
    apply (hp p).hom_ext
    · have := congrArg (fun x => x.v p q hpq) h1
      simpa only [pb_v] using this
    · have := congrArg (fun x => x.v p q hpq) h2
      simpa only [pb_v] using this

end LateralTheory.CohomologicalPurity.Bd
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafHsContPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity

def HtOffCont (q : ℕ) {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A) {J : Type} [SmallCategory J]
    (D : J ⥤ CommRingCat.{0}) (s : (Functor.const J).obj (CommRingCat.of A) ⟶ D)
    (t : D ⟶ (Functor.const J).obj (CommRingCat.of B)) (n i : ℤ) : Prop :=
  (∀ x : Ht q (opn (off B (I.map φ))).left n i, ∃ j h, ∃ y,
    pull _ (opnMap (Spec.map (t.app j)) (off B (I.map φ)) (off (D.obj j) (I.map (s.app j).hom)) h).left (tw q i) n y = x) ∧
  (∀ j h y, pull _ (opnMap (Spec.map (t.app j)) (off B (I.map φ)) (off (D.obj j) (I.map (s.app j).hom)) h).left
      (tw q i) n y = 0 →
    ∃ (k : J) (f : j ⟶ k) (h' : _), pull _ (opnMap (Spec.map (D.map f)) (off (D.obj k) (I.map (s.app k).hom))
      (off (D.obj j) (I.map (s.app j).hom)) h').left (tw q i) n y = 0)

def LeafOffCont : Prop := A1 → A4 → B1 → LeafBd → LeafExc → ∀ (q : ℕ) {A B : Type} [CommRing A] [CommRing B]
  (φ : A →+* B) (I : Ideal A), I.FG → IsUnit (q : A) → ∀ (J : Type) [SmallCategory J] [IsFiltered J]
  (D : J ⥤ CommRingCat.{0}) (s : (Functor.const J).obj (CommRingCat.of A) ⟶ D)
  (t : D ⟶ (Functor.const J).obj (CommRingCat.of B)),
  IsColimit (Cocone.mk _ t) → (∀ j, s.app j ≫ t.app j = CommRingCat.ofHom φ) → ∀ n i : ℤ, HtOffCont q φ I D s t n i

def LeafHsFive : Prop := A1 → B1 → LeafBd → ∀ (q : ℕ) {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B)
  (I : Ideal A), IsUnit (q : A) → ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0})
  (s : (Functor.const J).obj (CommRingCat.of A) ⟶ D) (t : D ⟶ (Functor.const J).obj (CommRingCat.of B)),
  IsColimit (Cocone.mk _ t) → (∀ j, s.app j ≫ t.app j = CommRingCat.ofHom φ) → ∀ i : ℤ,
  (∀ m : ℤ, HtOffCont q φ I D s t m i) → ∀ n : ℤ,
  (∀ x : Hs q (opn (off B (I.map φ))) n i, ∃ j h, ∃ y,
    Hs.pull q (opnMap (Spec.map (t.app j)) (off B (I.map φ)) (off (D.obj j) (I.map (s.app j).hom)) h) n i y = x) ∧
  (∀ j h y, Hs.pull q (opnMap (Spec.map (t.app j)) (off B (I.map φ)) (off (D.obj j) (I.map (s.app j).hom)) h) n i y = 0 →
    ∃ (k : J) (f : j ⟶ k) (h' : _), Hs.pull q (opnMap (Spec.map (D.map f)) (off (D.obj k) (I.map (s.app k).hom))
      (off (D.obj j) (I.map (s.app j).hom)) h') n i y = 0)

theorem opn_mono {X : Scheme.{0}} (U : X.Opens) : Mono (opn U).hom := by
  change Mono (sch.map U.ι)
  unfold sch
  infer_instance

theorem spec_cont (b1 : B1) (q : ℕ) {B : Type} [CommRing B] {J : Type} [SmallCategory J] [IsFiltered J]
    (D : J ⥤ CommRingCat.{0}) (t : D ⟶ (Functor.const J).obj (CommRingCat.of B)) (hc : IsColimit (Cocone.mk _ t))
    (hq : IsUnit (q : B)) (hqj : ∀ j, IsUnit (q : D.obj j)) (n i : ℤ) :
    (∀ x : Ht q (sp B) n i, ∃ j, ∃ y, pull _ (sch.map (Spec.map (t.app j))) (tw q i) n y = x) ∧
    ∀ j (y : Ht q (sch.obj (Spec (D.obj j))) n i), pull _ (sch.map (Spec.map (t.app j))) (tw q i) n y = 0 →
      ∃ (k : J) (f : j ⟶ k), pull _ (sch.map (Spec.map (D.map f))) (tw q i) n y = 0 := by
  have h := b1 q D _ hc n i
  exact ⟨fun x => h.1 x hq, fun j y hy => h.2 j y (hqj j) hy⟩

theorem leafHsCont_of (hB : LeafBd) (hE : LeafExc) (hO : LeafOffCont) (hF : LeafHsFive) : LeafHsCont := by
  intro a1 a4 b1 q A B _ _ φ I hI hq J _ _ D s t hc he n i
  exact hF a1 b1 hB q φ I hq J D s t hc he i (fun m => hO a1 a4 b1 hB hE q φ I hI hq J D s t hc he m i) n

end LateralTheory.CohomologicalPurity
end
end

