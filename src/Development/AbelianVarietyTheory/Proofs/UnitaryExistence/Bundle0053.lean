module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.AppCompatGeneric

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenConnectedComponentOfNoetherianSpace
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TopologicalSpace

noncomputable section

namespace GlobalTheory

universe u v

theorem isOpen_connectedComponent_of_noetherianSpace {X : Type u} [TopologicalSpace X]
    [NoetherianSpace X] (x : X) : IsOpen (connectedComponent x) := by
  have h : (connectedComponent x)ᶜ =
      ⋃ Z ∈ {Z ∈ irreducibleComponents X | ¬ Z ⊆ connectedComponent x}, Z := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    constructor
    · intro hy
      exact ⟨irreducibleComponent y, ⟨irreducibleComponent_mem_irreducibleComponents y,
        fun h => hy (h mem_irreducibleComponent)⟩, mem_irreducibleComponent⟩
    · rintro ⟨Z, ⟨hZ, hZ'⟩, hy⟩ hyx
      apply hZ'
      rw [connectedComponent_eq hyx]
      exact hZ.1.isConnected.subset_connectedComponent hy
  rw [← isClosed_compl_iff, h]
  refine Set.Finite.isClosed_biUnion
    (NoetherianSpace.finite_irreducibleComponents.subset (by exact fun Z hZ => hZ.1)) fun Z hZ => ?_
  exact isClosed_of_mem_irreducibleComponents Z hZ.1

theorem geometricallyConnected_of_isAlgClosed {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [ConnectedSpace X] :
    GeometricallyConnected f := by
  refine ⟨fun K _ y Z p q h => ?_⟩
  have := LocallyOfFiniteType.jacobsonSpace f
  have hy : Surjective y := ⟨fun a => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  have hs : Surjective p := MorphismProperty.of_isPullback h.flip hy
  have ho : UniversallyOpen p := MorphismProperty.of_isPullback h.flip
    (inferInstance : UniversallyOpen y)

  have fib : ∀ x : X, IsClosed {x} → ∀ a b : Z, p a = x → p b = x → a = b := by
    intro x hx a b ha hb
    let s := pointOfClosedPoint f x hx
    have hs : s ≫ f = 𝟙 _ := pointOfClosedPoint_comp f x hx
    let t : Spec (.of K) ⟶ Z := h.lift (y ≫ s) (𝟙 _) (by simp [hs])
    have ht : IsPullback t y p s := by
      refine IsPullback.of_right (h₁₂ := q) (v₁₃ := y) (h₂₂ := f) ?_ (by simp [t]) h.flip
      rw [hs, show t ≫ q = 𝟙 _ by simp [t]]
      exact IsPullback.of_id_fst
    obtain ⟨a', rfl, -⟩ := Scheme.exists_preimage_of_isPullback ht a (IsLocalRing.closedPoint k)
      (ha.trans (pointOfClosedPoint_apply f x hx _).symm)
    obtain ⟨b', rfl, -⟩ := Scheme.exists_preimage_of_isPullback ht b (IsLocalRing.closedPoint k)
      (hb.trans (pointOfClosedPoint_apply f x hx _).symm)
    rw [Subsingleton.elim a' b']
  have hne : Nonempty Z := (p.surjective (Classical.arbitrary X)).nonempty
  have : PreconnectedSpace Z := by
    refine preconnectedSpace_iff_clopen.2 fun U hU => ?_
    by_contra hc
    push Not at hc
    have h₁ : (p '' U).Nonempty := hc.1.image _
    have h₂ : (p '' Uᶜ).Nonempty := (Set.nonempty_compl.2 hc.2).image _
    have o₁ : IsOpen (p '' U) := p.isOpenMap _ hU.isOpen
    have o₂ : IsOpen (p '' Uᶜ) := p.isOpenMap _ hU.compl.isOpen
    have hcov : p '' U ∪ p '' Uᶜ = Set.univ := by
      rw [← Set.image_union, Set.union_compl_self, Set.image_univ, p.surjective.range_eq]
    obtain ⟨x, ⟨⟨a, ha, hax⟩, ⟨b, hb, hbx⟩⟩, hx⟩ := nonempty_inter_closedPoints
      (nonempty_inter o₁ o₂ hcov h₁ h₂) (o₁.inter o₂).isLocallyClosed
    exact hb (fib x hx a b hax hbx ▸ ha)
  exact ⟨hne⟩

section Sub

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] {A N : C} [GrpObj N]

theorem exists_grpObj_of_mono_of_fac (n : A ⟶ N) [Mono n] (e : 𝟙_ C ⟶ A) (m : A ⊗ A ⟶ A) (i : A ⟶ A)
    (he : e ≫ n = η[N]) (hm : m ≫ n = (n ⊗ₘ n) ≫ μ[N]) (hi : i ≫ n = n ≫ ι[N]) :
    ∃ _ : GrpObj A, IsMonHom n := by
  have he' : ∀ {T : C} (t : T ⟶ 𝟙_ C), t ≫ e ≫ n = 1 := fun t => by
    rw [he, Hom.one_def, toUnit_unique t (toUnit _)]
  have hm' : ∀ {T : C} (t : T ⟶ A ⊗ A), t ≫ m ≫ n = (t ≫ fst _ _ ≫ n) * (t ≫ snd _ _ ≫ n) :=
    fun t => by
      rw [hm, Hom.mul_def, ← Category.assoc]
      congr 1
      ext <;> simp
  have hm'' : m ≫ n = (fst _ _ ≫ n) * (snd _ _ ≫ n) := by simpa using hm' (𝟙 _)
  have hi' : i ≫ n = n⁻¹ := by rw [hi, Hom.inv_def]
  letI : GrpObj A :=
    { one := e
      mul := m
      inv := i
      one_mul := by
        rw [← cancel_mono n, Category.assoc, hm', whiskerRight_fst_assoc, whiskerRight_snd_assoc,
          he', _root_.one_mul, leftUnitor_hom]
      mul_one := by
        rw [← cancel_mono n, Category.assoc, hm', whiskerLeft_fst_assoc, whiskerLeft_snd_assoc,
          he', _root_.mul_one, rightUnitor_hom]
      mul_assoc := by
        rw [← cancel_mono n, Category.assoc, hm', Category.assoc, Category.assoc,
          hm' (A ◁ m), whiskerRight_fst_assoc, whiskerRight_snd_assoc, whiskerLeft_fst_assoc,
          whiskerLeft_snd_assoc, hm', hm', MonObj.comp_mul, MonObj.comp_mul, _root_.mul_assoc]
        simp
      left_inv := by
        rw [← cancel_mono n, Category.assoc, Category.assoc, hm', he', lift_fst_assoc,
          lift_snd_assoc, hi', Category.id_comp, inv_mul_cancel]
      right_inv := by
        rw [← cancel_mono n, Category.assoc, Category.assoc, hm', he', lift_fst_assoc,
          lift_snd_assoc, hi', Category.id_comp, mul_inv_cancel] }
  exact ⟨this, ⟨he, hm⟩⟩

end Sub

theorem finite_points_of_isOpenMap_unit {k : Type} [Field k] [IsAlgClosed k] (N : Over (Sp k))
    [GrpObj N] [LocallyOfFiniteType N.hom] [NoetherianSpace N.left]
    (h : IsOpenMap η[N].left) : Finite (𝟙_ (Over (Sp k)) ⟶ N) := by
  let pt : Sp k := IsLocalRing.closedPoint k
  let F : (𝟙_ (Over (Sp k)) ⟶ N) → N.left := fun x => x.left pt
  have hF : Function.Injective F := fun x y hxy =>
    Over.OverMorphism.ext (ext_of_apply_closedPoint_eq N.hom x.w y.w hxy)
  have ho : ∀ x, IsOpen {F x} := fun x => by
    have hx : η[N] ≫ (GrpObj.mulRight x).hom = x := by
      simpa [comp_lift_assoc] using lift_comp_one_left (𝟙 _) x
    have : IsIso (GrpObj.mulRight x).hom.left :=
      inferInstanceAs (IsIso ((Over.forget _).map (GrpObj.mulRight x).hom))
    have h₁ : IsOpenMap x.left := by
      rw [← hx, Over.comp_left]
      exact (GrpObj.mulRight x).hom.left.isOpenMap.comp h
    have h₂ := h₁ {pt} (by
      have : Subsingleton (Sp k) := inferInstance
      convert isOpen_univ
      exact Set.eq_univ_of_forall fun a => this.elim _ _)
    rwa [Set.image_singleton] at h₂
  obtain ⟨t, -, ht⟩ := (NoetherianSpace.isCompact (Set.range F)).elim_nhds_subcover
    (fun y => {y}) (by rintro _ ⟨x, rfl⟩; exact (ho x).mem_nhds rfl)
  have : (Set.range F).Finite := t.finite_toSet.subset fun y hy => by simpa using ht hy
  exact (Set.finite_range_iff hF).1 this

theorem exists_neutralComponent : ∀ (k : Type) [Field k] [IsAlgClosed k] (N : Over (Sp k)) [GrpObj N], Smooth N.hom → QuasiCompact N.hom → ∃ (N₀ : Over (Sp k)) (_ : GrpObj N₀) (ν : N₀ ⟶ N) (g : ℕ), IsMonHom ν ∧ IsOpenImmersion ν.left ∧ IsClosedImmersion ν.left ∧ GeometricallyConnected N₀.hom ∧ SmoothOfRelativeDimension g N₀.hom ∧ (g = 0 → Finite (𝟙_ (Over (Sp k)) ⟶ N)) := by
  intro k _ _ N _ hs hq
  have : IsLocallyNoetherian N.left := LocallyOfFiniteType.isLocallyNoetherian N.hom
  have : CompactSpace N.left := QuasiCompact.compactSpace_of_compactSpace N.hom
  have : IsNoetherian N.left := {}
  let pt : (𝟙_ (Over (Sp k))).left := IsLocalRing.closedPoint k
  let e₀ : N.left := η[N].left pt
  let U : N.left.Opens := ⟨connectedComponent e₀, isOpen_connectedComponent_of_noetherianSpace e₀⟩
  let N₀ : Over (Sp k) := Over.mk (U.ι ≫ N.hom)
  let ν : N₀ ⟶ N := Over.homMk U.ι rfl
  have hνo : IsOpenImmersion ν.left := inferInstanceAs (IsOpenImmersion U.ι)
  have hr : Set.range ν.left = connectedComponent e₀ := U.range_ι
  have hνc : IsClosedImmersion ν.left := .of_isPreimmersion _ (hr ▸ isClosed_connectedComponent)
  have : Mono ν := Over.mono_of_mono_left ν
  have hsm : Smooth N₀.hom := inferInstanceAs (Smooth (U.ι ≫ N.hom))
  have hc : ConnectedSpace N₀.left :=
    isConnected_iff_connectedSpace.1 (isConnected_connectedComponent (x := e₀))
  have hg : GeometricallyConnected N₀.hom := geometricallyConnected_of_isAlgClosed N₀.hom

  have fac : ∀ (T : Over (Sp k)) [ConnectedSpace T.left] (φ : T ⟶ N) (t : 𝟙_ _ ⟶ T),
      t ≫ φ = η[N] → ∃ ψ : T ⟶ N₀, ψ ≫ ν = φ := by
    intro T _ φ t ht
    have hsub : Set.range φ.left ⊆ Set.range ν.left := by
      rw [hr]
      refine (isConnected_range φ.left.continuous).subset_connectedComponent ⟨t.left pt, ?_⟩
      simp only [e₀, ← ht, Over.comp_left, Scheme.Hom.comp_apply]
    refine ⟨Over.homMk (IsOpenImmersion.lift ν.left φ.left hsub) ?_, ?_⟩
    · rw [← ν.w, IsOpenImmersion.lift_fac_assoc, φ.w]
    · exact Over.OverMorphism.ext (IsOpenImmersion.lift_fac ν.left φ.left hsub)
  have : ConnectedSpace (𝟙_ (Over (Sp k))).left := inferInstanceAs (ConnectedSpace (Sp k))
  obtain ⟨e, he⟩ := fac (𝟙_ _) η[N] (𝟙 _) (Category.id_comp _)
  have : ConnectedSpace (N₀ ⊗ N₀).left :=
    inferInstanceAs (ConnectedSpace ↥(pullback N₀.hom N₀.hom))
  obtain ⟨m, hm⟩ := fac (N₀ ⊗ N₀) ((ν ⊗ₘ ν) ≫ μ[N]) (lift e e)
    (by simpa [he] using lift_comp_one_left (𝟙 _) η[N])
  obtain ⟨i, hi⟩ := fac N₀ (ν ≫ ι[N]) e (by simp [reassoc_of% he])
  obtain ⟨G, hG⟩ := exists_grpObj_of_mono_of_fac ν e m i he hm hi
  obtain ⟨g, hgd⟩ := exists_dim_of_preconnected N₀.hom (e.left pt)
  refine ⟨N₀, G, ν, g, hG, hνo, hνc, hg, hgd, ?_⟩
  rintro rfl
  have : Etale N₀.hom := (Etale.iff_smoothOfRelativeDimension_zero _).2 hgd
  have : Etale (e.left ≫ N₀.hom) := by
    rw [e.w]; exact inferInstanceAs (Etale (𝟙 (Sp k)))
  have : Etale e.left := Etale.of_comp e.left N₀.hom
  refine finite_points_of_isOpenMap_unit N ?_
  rw [← he, Over.comp_left]
  exact (e.left ≫ ν.left).isOpenMap

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemNonzeroLocusOfPull
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SectionBaseChange

open TopologicalSpace ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.H1

section Pointwise

variable {X X' Z : Scheme.{0}}

theorem mem_nonzeroLocus {M : LB X} (s : M.Sec) (x : X) :
    x ∈ nonzeroLocus s ↔ ∃ k, x ∈ M.U k ∧ IsUnit (gs (𝟙 X) x _ (s.f k)) := by
  refine Opens.mem_iSup.trans (exists_congr fun k => ⟨fun h => ?_, fun ⟨h, hu⟩ => ?_⟩)
  · have hk : x ∈ M.U k := X.basicOpen_le _ h
    refine ⟨hk, ?_⟩
    rw [gs_eq (𝟙 X) x _ hk]
    exact (X.mem_basicOpen _ _ hk).1 h
  · rw [gs_eq (𝟙 X) x _ h] at hu
    exact (X.mem_basicOpen _ _ h).2 hu

theorem mem_nonzeroLocus_of_pull {L : LB X} {L' : LB X'} {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)} (hL' : L'.IsLB)
    {s : L.Sec} {s' : L'.Sec}
    (h : ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) j k, F (r z) ∈ L.U j → r z ∈ L'.U k →
      gs (r ≫ F) z _ (s.f j) = (gw w r z j k).val * gs r z _ (s'.f k))
    {x : X'} (hx : F x ∈ nonzeroLocus s) : x ∈ nonzeroLocus s' := by
  obtain ⟨j, hj, hu⟩ := (mem_nonzeroLocus s _).1 hx
  obtain ⟨k, hk⟩ := exists_chart hL' x
  refine (mem_nonzeroLocus s' _).2 ⟨k, hk, ?_⟩
  have e := h _ (𝟙 _) x j k hj hk
  rw [Category.id_comp, gs_stalkMap F x _ hj] at e
  exact isUnit_of_mul_isUnit_right (e ▸ hu.map (F.stalkMap x).hom)

theorem fibre_nonzero_of_pull {L : LB X} {L' : LB X'} {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)} (hL' : L'.IsLB)
    {s : L.Sec} {s' : L'.Sec}
    (h : ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) j k, F (r z) ∈ L.U j → r z ∈ L'.U k →
      gs (r ≫ F) z _ (s.f j) = (gw w r z j k).val * gs r z _ (s'.f k))
    {S S' : Scheme.{0}} {p : X ⟶ S} {p' : X' ⟶ S'} {t : S' ⟶ S} (hF : IsPullback F p' p t)
    (hs : ∀ y : S, ∃ x : X, p x = y ∧ x ∈ nonzeroLocus s) (y : S') : ∃ x : X', p' x = y ∧ x ∈ nonzeroLocus s' := by
  obtain ⟨x, hx, hn⟩ := hs (t y)
  obtain ⟨x', h₁, h₂⟩ := Scheme.exists_preimage_of_isPullback hF x y hx
  exact ⟨x', h₂, mem_nonzeroLocus_of_pull hL' h (by rwa [show F x' = x from h₁])⟩

theorem gs_comp_stalkMap {Y : Scheme.{0}} (r : Z ⟶ Y) (p : Y ⟶ X) (z : Z) (U : X.Opens) (h : p (r z) ∈ U) (a : Γ(X, U)) :
    (r.stalkMap z).hom (gs p (r z) U a) = gs (r ≫ p) z U a := by
  have e := gs_pull (𝟙 Y) p (r z) U h a
  rw [Category.id_comp] at e
  exact (congrArg (r.stalkMap z).hom e.symm).trans ((gs_stalkMap r z (p ⁻¹ᵁ U) h _).symm.trans (gs_pull r p z U h _))

theorem existsUnique_of_local {S : Scheme.{0}} (Rel : ∀ U : S.Opens, Γ(S, U) → Prop) (small : S.Opens → Prop)
    (cov : ∀ (x : S) (W : S.Opens), x ∈ W → ∃ U, U ≤ W ∧ x ∈ U ∧ small U)
    (hres : ∀ (U W : S.Opens) (h : U ≤ W) (a : Γ(S, W)), Rel W a → Rel U (resG S h a))
    (hloc : ∀ a : Γ(S, ⊤), (∀ x : S, ∃ U, x ∈ U ∧ Rel U (resG S le_top a)) → Rel ⊤ a)
    (hu : ∀ U, small U → ∃! a, Rel U a) : ∃! a, Rel ⊤ a := by
  have eq : ∀ (W W' : S.Opens) (a : Γ(S, W)) (a' : Γ(S, W')), Rel W a → Rel W' a' → ∀ x ∈ W ⊓ W',
      gs (𝟙 S) x W a = gs (𝟙 S) x W' a' := fun W W' a a' h h' x hx => by
    obtain ⟨U, le, hxU, hU⟩ := cov x _ hx
    have e := (hu U hU).unique (hres U W (le.trans inf_le_left) a h) (hres U W' (le.trans inf_le_right) a' h')
    exact (gs_res (𝟙 S) x _ hxU a).symm.trans ((congrArg (gs (𝟙 S) x U) e).trans (gs_res (𝟙 S) x _ hxU a'))
  choose U _ hxU hU using fun x : S => cov x ⊤ trivial
  choose a ha _ using fun x => hu (U x) (hU x)
  obtain ⟨g, hg, -⟩ := S.sheaf.existsUnique_gluing' U ⊤ (fun i => homOfLE le_top)
    (fun x _ => Opens.mem_iSup.2 ⟨x, hxU x⟩) a (fun i j => fn_ext (V := U i ⊓ U j) fun y hy =>
      (gs_res (𝟙 S) y inf_le_left hy _).trans ((eq _ _ _ _ (ha i) (ha j) y hy).trans
        (gs_res (𝟙 S) y inf_le_right hy _).symm))
  have hg' : Rel ⊤ g := hloc g fun x => ⟨U x, hxU x, (congrArg (Rel (U x)) (hg x)).mpr (ha x)⟩
  exact ⟨g, hg', fun g' h' => fn_ext fun x _ => eq _ _ _ _ h' hg' x ⟨trivial, trivial⟩⟩

end Pointwise

theorem generates_local (hS : SecBaseChangeSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) (p : S) :
    ∃ V : S.Opens, p ∈ V ∧ ∀ (C : Type) [CommRing C] (t : Sp C ⟶ S), (∀ z, t z ∈ V) →
      ∀ θ : (LPow P.A P.L (1 : ℕ) (Over.mk t)).Sec,
        (∀ z : Sp C, ∃ y, (fst (Over.mk t) P.A).left y = z ∧ y ∈ nonzeroLocus θ) →
        ∀ s : (LPow P.A P.L (1 : ℕ) (Over.mk t)).Sec, ∃! a : C, ∀ j, ∀ y ∈ (LPow P.A P.L (1 : ℕ) (Over.mk t)).U j,
          gs (𝟙 _) y _ (s.f j) = cst (fst (Over.mk t) P.A).left y a * gs (𝟙 _) y _ (θ.f j) := by
  obtain ⟨V, hV, b, hb⟩ := hS S P 1 le_rfl p
  refine ⟨V, hV, fun C _ t ht => ?_⟩
  obtain ⟨t₀, rfl⟩ : ∃ t₀ : Spec (CommRingCat.of C) ⟶ (overRes (T := baseOver S) V).left,
      t₀ ≫ (overRes (T := baseOver S) V).hom = t :=
    ⟨IsOpenImmersion.lift V.ι t (by rintro _ ⟨z, rfl⟩; rw [Scheme.Opens.range_ι]; exact ht z), by
      show _ ≫ (V.ι ≫ 𝟙 S) = t
      rw [Category.comp_id]; exact IsOpenImmersion.lift_fac _ _ _⟩
  intro θ hθ s
  have pull : ∀ i, ∃ b' : LB.Sec (LPow P.A P.L (1 : ℕ) (baseAt t₀)),
      IsPullSec P.A P.L (1 : ℕ) (homAt t₀ ▷ P.A) (whiskerRight_snd (homAt t₀) P.A) (b i) b' := fun i => by
    have gen : ∀ (φ' : Fin 1 → ((baseAt t₀ ⊗ P.A).left ⟶ P.A.left))
        (_ : (fun _ : Fin 1 => (homAt t₀ ▷ P.A).left ≫ (snd (overRes (T := baseOver S) V) P.A).left) = φ'),
        ∃ s' : LB.Sec (LB.LinComb P.L φ' (fun _ => ((1 : ℕ) : ℤ))), ∀ j (le : LB.wchart P.L φ' j ≤
          (homAt t₀ ▷ P.A).left ⁻¹ᵁ LB.wchart P.L (fun _ : Fin 1 => (snd (overRes (T := baseOver S) V) P.A).left) j),
          s'.f j = ((baseAt t₀ ⊗ P.A).left.presheaf.map (homOfLE le).op).hom
            (((homAt t₀ ▷ P.A).left.app _).hom ((b i).f j)) := by
      rintro _ rfl
      exact ⟨DVR.pullSec P.L _ _ (b i) _, fun _ _ => rfl⟩
    obtain ⟨s', hs'⟩ := gen (fun _ => (snd (baseAt t₀) P.A).left)
      (funext fun _ => congrArg CommaMorphism.left (whiskerRight_snd (homAt t₀) P.A))
    exact ⟨s', fun j => hs' j _⟩
  choose b' hb' using pull
  obtain ⟨hli, hsp⟩ := hb C t₀ b' hb'
  have hq : Unique (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
  rw [Set.range_unique] at hsp
  have li : ∀ r : Γ((baseAt t₀).left, ⊤),
      r • (SecM.ofSec P.A (b' hq.default) : SecM P.A P.L (1 : ℕ) (baseAt t₀)) = 0 → r = 0 := fun r hr =>
    Fintype.linearIndependent_iff.1 hli (fun _ => r) (by rw [Fintype.sum_unique]; exact hr) hq.default
  have sp : ∀ σ : SecM P.A P.L (1 : ℕ) (baseAt t₀), ∃ r : Γ((baseAt t₀).left, ⊤), r • SecM.ofSec P.A (b' hq.default) = σ :=
    fun σ => Submodule.mem_span_singleton.1 (hsp.ge Submodule.mem_top)
  have key : ∀ (r : Γ((baseAt t₀).left, ⊤)) (σ τ : LB.Sec (LPow P.A P.L (1 : ℕ) (baseAt t₀))),
      r • (SecM.ofSec P.A τ : SecM P.A P.L (1 : ℕ) (baseAt t₀)) = SecM.ofSec P.A σ ↔
      ∀ j, ∀ y ∈ (LPow P.A P.L (1 : ℕ) (baseAt t₀)).U j,
        gs (𝟙 _) y _ (σ.f j) = gs (fst (baseAt t₀) P.A).left y ⊤ r * gs (𝟙 _) y _ (τ.f j) := fun r σ τ => by
    have e : ∀ j, ∀ y ∈ (LPow P.A P.L (1 : ℕ) (baseAt t₀)).U j, gs (𝟙 _) y _ (liftHom P.A _ r * τ.f j) =
        gs (fst (baseAt t₀) P.A).left y ⊤ r * gs (𝟙 _) y _ (τ.f j) := fun j y hy =>
      (gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_res _ y le_top hy _).trans
        ((gs_pull (𝟙 _) (fst (baseAt t₀) P.A).left y ⊤ trivial _).trans (by rw [Category.id_comp]))) rfl)
    exact ⟨fun h j y hy => (congrArg (gs (𝟙 _) y _) (congrFun (congrArg Subtype.val h) j)).symm.trans (e j y hy),
      fun h => Subtype.ext (funext fun j => fn_ext fun y hy => (e j y hy).trans (h j y hy).symm)⟩
  obtain ⟨u, hu⟩ := sp (SecM.ofSec P.A θ)
  have un : IsUnit u := (baseAt t₀).left.toRingedSpace.isUnit_of_isUnit_germ ⊤ u fun z _ => by
    obtain ⟨y, rfl, hy⟩ := hθ z
    obtain ⟨j, hj, h⟩ := (mem_nonzeroLocus θ y).1 hy
    have h' := isUnit_of_mul_isUnit_left (((key u θ _).1 hu j y hj) ▸ h)
    rw [gs_stalkMap _ y ⊤ trivial, isUnit_map_iff, gs_eq _ _ ⊤ trivial] at h'
    exact h'
  obtain ⟨u, rfl⟩ := un
  obtain ⟨r, hr⟩ := sp (SecM.ofSec P.A s)
  have bij := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of C)).inv
  obtain ⟨a, ha⟩ := bij.2 (r * (u⁻¹).val)
  refine ⟨a, (key _ s θ).1 ?_, fun a' ha' => bij.1 ?_⟩
  · refine (congrArg (fun c : Γ((baseAt t₀).left, ⊤) =>
      c • (SecM.ofSec P.A θ : SecM P.A P.L (1 : ℕ) (baseAt t₀))) ha).trans ?_
    rw [← hu, smul_smul, Units.inv_mul_cancel_right, hr]
  · have e := (key _ s θ).2 ha'
    rw [← hu, smul_smul, ← hr, ← sub_eq_zero, ← sub_smul] at e
    exact ((Units.eq_mul_inv_iff_mul_eq u).2 (sub_eq_zero.1 (li _ e))).trans ha.symm

theorem generates (hS : SecBaseChangeSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) {R' : Type} [CommRing R']
    {t : Sp R' ⟶ S} {X' : Scheme.{0}} {q : X' ⟶ Sp R'} {φ : X' ⟶ P.A.left} (hφ : IsPullback φ q P.A.hom t) {L' : LB X'}
    (hL' : L'.IsLB) (hw : LBIso L' (P.L.pull φ)) (θ : L'.Sec) (hθ : ∀ y : Sp R', ∃ x : X', q x = y ∧ x ∈ nonzeroLocus θ)
    (s : L'.Sec) : ∃! a : R', ∀ i, s.f i = constFn q _ a * θ.f i := by
  choose V hV H using generates_local hS P
  let Rel : ∀ U : (Sp R').Opens, Γ(Sp R', U) → Prop := fun U a => ∀ k, ∀ x ∈ L'.U k, q x ∈ U →
    gs (𝟙 X') x _ (s.f k) = gs q x U a * gs (𝟙 X') x _ (θ.f k)
  have main : ∃! a, Rel ⊤ a := by
    refine existsUnique_of_local Rel (fun U => IsAffineOpen U ∧ ∃ p, U ≤ t ⁻¹ᵁ V p) (fun x W hx => ?_)
      (fun U W h a ha k x hk hx => (ha k x hk (h hx)).trans (congrArg₂ (· * ·) (gs_res q x h hx a).symm rfl))
      (fun a h k x hk _ => ?_) ?_
    · obtain ⟨U, hU, hxU, le⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ W ⊓ t ⁻¹ᵁ V (t x) from ⟨hx, hV _⟩)
      exact ⟨U, fun y hy => (le hy).1, hxU, hU, t x, fun y hy => (le hy).2⟩
    · obtain ⟨U, hU, h'⟩ := h (q x)
      exact (h' k x hk hU).trans (congrArg₂ (· * ·) (gs_res q x le_top hU a) rfl)
    rintro U ⟨hU, p, hp⟩
    let u : Sp Γ(Sp R', U) ⟶ Sp R' := hU.fromSpec
    have hι : IsOpenImmersion u := hU.isOpenImmersion_fromSpec
    have mι : ∀ z, u z ∈ U := fun z => hU.range_fromSpec.le ⟨z, rfl⟩
    let T : Over S := Over.mk (u ≫ t)
    have big : IsPullback (snd T P.A).left (fst T P.A).left P.A.hom (u ≫ t) := (IsPullback.of_hasPullback _ _).flip
    let ρ : (T ⊗ P.A).left ⟶ X' := hφ.lift (snd T P.A).left ((fst T P.A).left ≫ u) (by rw [Category.assoc]; exact big.w)
    have ρ₁ : ρ ≫ φ = (snd T P.A).left := hφ.lift_fst _ _ _
    have ρ₂ : ρ ≫ q = (fst T P.A).left ≫ u := hφ.lift_snd _ _ _
    have sq : IsPullback ρ (fst T P.A).left q u := IsPullback.of_right (by rw [ρ₁]; exact big) ρ₂ hφ
    have hρ : IsOpenImmersion ρ := MorphismProperty.of_isPullback (P := @IsOpenImmersion) sq.flip hι
    have hM : (LPow P.A P.L (1 : ℕ) T).IsLB := DVR.linComb_isLB P.L P.isLB _ _
    have m : ∀ (j : Fin 1 → P.L.ι) (y : (T ⊗ P.A).left), y ∈ (LPow P.A P.L (1 : ℕ) T).U j →
        ρ y ∈ (P.L.pull φ).U (fun _ => j 0) := fun j y h =>
      mem_pull.2 ((congrArg (fun e => e y ∈ P.L.U (j 0)) ρ₁).mpr (Set.mem_iInter.1 h 0))
    let cp : ChartPull (LPow P.A P.L (1 : ℕ) T) (P.L.pull φ) ρ :=
      { idx := fun j _ => j 0
        le := m
        g := fun y i j hi hj => (gm_linComb P.L _ _ (𝟙 _) y i j hi hj).trans
          (Eq.trans (by rw [ρ₁, Fin.prod_univ_one, Nat.cast_one, zpow_one, Category.id_comp])
            (gm_pull_g P.L φ ρ y _ _ (m i y hi) (m j y hj)).symm) }
    obtain ⟨w, hw'⟩ := LBIso.chartPull cp (chartPullPull L' ρ ρ rfl) hw.symm
    have down := sec_pull_down ((isGen_iff w).1 hw') hL' hM
    obtain ⟨θU, hθU⟩ := down θ
    obtain ⟨sU, hsU⟩ := down s
    have G := H p _ (u ≫ t) (fun z => hp (mι z)) θU (fibre_nonzero_of_pull hM hθU sq hθ) sU
    have key : ∀ (a : Γ(Sp R', U)) (y : (T ⊗ P.A).left) k j, ρ y ∈ L'.U k → y ∈ (LPow P.A P.L (1 : ℕ) T).U j →
        (gs (𝟙 _) y _ (sU.f j) = cst (fst T P.A).left y a * gs (𝟙 _) y _ (θU.f j) ↔
        gs (𝟙 X') (ρ y) _ (s.f k) = gs q (ρ y) U a * gs (𝟙 X') (ρ y) _ (θ.f k)) := fun a y k j hk hj => by
      have hq : q (ρ y) ∈ U := (congrArg (fun e => e y ∈ U) ρ₂).mpr (mι _)
      have inj : Function.Injective (ρ.stalkMap y).hom := (ConcreteCategory.bijective_of_isIso (ρ.stalkMap y)).1
      have c : (ρ.stalkMap y).hom (gs q (ρ y) U a) = cst (fst T P.A).left y a := by
        rw [gs_comp_stalkMap ρ q y U hq, ρ₂]
        refine (gs_fromSpec hU le_rfl _ y a).trans (congrArg _ ?_)
        simp
      have e₁ := hsU _ (𝟙 _) y k j hk hj
      have e₂ := hθU _ (𝟙 _) y k j hk hj
      rw [Category.id_comp] at e₁ e₂
      rw [← inj.eq_iff, map_mul, c, ← gs_stalkMap ρ y _ hk, ← gs_stalkMap ρ y _ hk, e₁, e₂, mul_left_comm,
        Units.mul_right_inj]
    refine (existsUnique_congr fun a => ⟨fun h k x hk hx => ?_, fun h j y hj => ?_⟩).1 G
    · obtain ⟨z, hz⟩ : ∃ z, u z = q x := hU.range_fromSpec.ge hx
      obtain ⟨y, h₁, -⟩ := Scheme.exists_preimage_of_isPullback sq x z hz.symm
      obtain rfl : ρ y = x := h₁
      obtain ⟨j, hj⟩ := exists_chart hM y
      exact (key a y k j hk hj).1 (h j y hj)
    · obtain ⟨k, hk⟩ := exists_chart hL' (ρ y)
      exact (key a y k j hk hj).2 (h k _ hk ((congrArg (fun e => e y ∈ U) ρ₂).mpr (mι _)))
  have bij := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R')).inv
  obtain ⟨r, hr, hu⟩ := main
  obtain ⟨a, rfl⟩ := bij.2 r
  exact ⟨a, (sec_eq_iff _ _ _ _).2 fun k x hk => hr k x hk trivial,
    fun a' ha' => bij.1 (hu _ fun k x hk _ => (sec_eq_iff _ _ _ _).1 ha' k x hk)⟩

theorem generates_and_baseChange : Out.SecBaseChangeSt → ∀ (R R' : Type) [CommRing R] [IsNoetherianRing R] [CommRing R'] (f : R →+* R') (P : Out.PolAV (Sp R)) (A' : Over (Sp R')) (φ : A'.left ⟶ P.A.left) (L' : LB A'.left) (w : LB.Iso L' (P.L.pull φ)) (th : P.L.Sec), IsPullback φ A'.hom P.A.hom (spMap f) → L'.IsLB → w.IsGen → (∀ y : Sp R, ∃ x : P.A.left, P.A.hom x = y ∧ x ∈ Out.nonzeroLocus th) → (∀ s : P.L.Sec, ∃! a : R, ∀ i, s.f i = constFn P.A.hom _ a * th.f i) ∧ ∃ th' : L'.Sec, (∀ (j : (P.L.pull φ).ι) (i : L'.ι) (h : (P.L.pull φ).U j ⊓ L'.U i ≤ φ ⁻¹ᵁ P.L.U (j PUnit.unit)), (φ.appLE _ _ h).hom (th.f (j PUnit.unit)) = (show Γ(A'.left, (P.L.pull φ).U j ⊓ L'.U i) from (w.s (j, i)).val) * resG _ inf_le_right (th'.f i)) ∧ (∀ y : Sp R', ∃ x : A'.left, A'.hom x = y ∧ x ∈ Out.nonzeroLocus th') ∧ (∀ s : L'.Sec, ∃! a : R', ∀ i, s.f i = constFn A'.hom _ a * th'.f i) := by
  intro hS R R' _ _ _ f P A' φ L' w th hφ hL' hw hth
  have refl : LBIso P.L (P.L.pull (𝟙 _)) :=
    LBIso.chartPull (chartPullUnpull P.L _ rfl) (chartPullId _)
      (exists_iso_linComb (F := 𝟙 P.A.left) P.isLB (fun _ : PUnit => 𝟙 _) (fun _ => 1) fun _ _ _ => rfl)
  refine ⟨generates hS P (t := 𝟙 _) (φ := 𝟙 _) (IsPullback.of_horiz_isIso ⟨by simp⟩) P.isLB refl th hth, ?_⟩
  obtain ⟨th', h⟩ := sec_pull_down ((isGen_iff w).1 hw) P.isLB hL' th
  have nz := fibre_nonzero_of_pull hL' h hφ hth
  refine ⟨th', fun j i le => fn_ext fun y hy => ?_, nz, generates hS P hφ hL' ⟨w, hw⟩ th' nz⟩
  refine (gs_appLE φ _ _ le (𝟙 _) y hy _).trans ((h _ (𝟙 _) y _ i (le hy) hy.2).trans (Eq.symm ?_))
  exact (gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) (gs_unit (𝟙 _) y _ hy _) (gs_res _ y _ hy _))

end GlobalTheory.SectionBaseChange
end
end

