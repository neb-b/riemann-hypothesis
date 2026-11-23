module

public import Development.EtaleCohomology.EtaleSheaves.LeafSSCut
public import Development.EtaleCohomology.EtaleSheaves.Bundle0013
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Development.EtaleCohomology.EtaleSheaves.Bundle0015
public import Development.EtaleCohomology.EtaleSheaves.Bundle0014

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafFiltPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.E.LeafFiltPf

abbrev Sg {R : Type} [CommRing R] (X : Shv R) : Cx R := (HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) 0).obj X

variable {R : Type} [CommRing R] (K : Cx R) (F : Shv R) (n : ℤ)

theorem coe_sub' {K L : Cx R} {m : ℤ} (a b : Cocycle K L m) :
    ((a - b : Cocycle K L m) : Cochain K L m) = (a : Cochain K L m) - (b : Cochain K L m) := rfl

theorem coe_zero' {K L : Cx R} {m : ℤ} : ((0 : Cocycle K L m) : Cochain K L m) = 0 := rfl

theorem res_zero (q : ℤ) (hq : q < 0) : IsZero ((res R F).X q) := by
  have : (res R F).IsStrictlyGE 0 := by unfold res; infer_instance
  exact CochainComplex.isZero_of_isStrictlyGE _ 0 q (by omega)

def V (s : ℤ) (z : Cocycle K (res R F) n) : Prop := ∀ p q (h : p + n = q), s < p → z.1.v p q h = 0

def S (s : ℤ) : Set (HK R K F n) := {x | ∃ z : Cocycle K (res R F) n, CohomologyClass.mk z = x ∧ V K F n s z}

theorem memS {s : ℤ} {x : HK R K F n} (h : x ∈ S K F n s) :
    ∃ z : Cocycle K (res R F) n, CohomologyClass.mk z = x ∧ V K F n s z := h

theorem cocyc (s d : ℤ) (hd : s + n = d) (z : Cocycle K (res R F) n) (hz : V K F n s z) :
    z.1.v s d hd ≫ (res R F).d d (d + 1) = 0 := by
  have h0 := Cochain.congr_v (Cocycle.δ_eq_zero z (n + 1)) s (d + 1) (by omega)
  rw [δ_v n (n + 1) rfl _ s (d + 1) _ d (s + 1) (by omega) rfl, hz (s + 1) (d + 1) (by omega) (by omega)] at h0
  simpa using h0

def clsC (s d : ℤ) (hd : s + n = d) (z : Cocycle K (res R F) n) (hz : V K F n s z) :
    Cocycle (Sg (K.X s)) (res R F) d :=
  Cocycle.fromSingleMk (z.1.v s d hd) (zero_add d) (d + 1) rfl (cocyc K F n s d hd z hz)

theorem clsC_v (s d : ℤ) (hd : s + n = d) (z : Cocycle K (res R F) n) (hz : V K F n s z) :
    (clsC K F n s d hd z hz).1.v 0 d (zero_add d) =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (K.X s)).hom ≫ z.1.v s d hd :=
  Cochain.fromSingleMk_v _ _

theorem CB (X : Shv R) (d : ℤ) (c : Cocycle (Sg X) (res R F) d) (hc : CohomologyClass.mk c = 0) (e : ℤ)
    (he : e + 1 = d) : ∃ β : Cochain (Sg X) (res R F) e,
      β.v 0 e (zero_add e) ≫ (res R F).d e d = c.1.v 0 d (zero_add d) := by
  obtain ⟨m, hm, β, hβ⟩ := (CohomologyClass.mk_eq_zero_iff c).1 hc
  obtain rfl : e = m := by omega
  refine ⟨β, ?_⟩
  have := Cochain.congr_v hβ 0 d (zero_add d)
  rw [δ_v e d hm β 0 d _ e 1 (by omega) rfl] at this
  have hz1 : IsZero ((Sg X).X 1) := HomologicalComplex.isZero_single_obj_X _ _ _ _ (by simp)
  rw [hz1.eq_of_tgt ((Sg X).d 0 1) 0] at this
  simpa using this

theorem KL (s d : ℤ) (hd : s + n = d) (z : Cocycle K (res R F) n) (hz : V K F n s z) (e : ℤ) (he : e + 1 = d)
    (β : Cochain (Sg (K.X s)) (res R F) e)
    (hβ : β.v 0 e (zero_add e) ≫ (res R F).d e d =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (K.X s)).hom ≫ z.1.v s d hd) :
    ∃ w : Cocycle K (res R F) n, CohomologyClass.mk w = CohomologyClass.mk z ∧ V K F n (s - 1) w := by
  let g : K.X s ⟶ (res R F).X e :=
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (K.X s)).inv ≫ β.v 0 e (zero_add e)
  let hh : Cochain K (res R F) (n - 1) := Cochain.single g (n - 1)
  let D : Cocycle K (res R F) n := Cocycle.mk (δ (n - 1) n hh) (n + 1) (by omega) (δ_δ _ _ _ _)
  refine ⟨z - D, ?_, ?_⟩
  · have hD : CohomologyClass.mk D = 0 := (CohomologyClass.mk_eq_zero_iff D).2 ⟨n - 1, by omega, hh, rfl⟩
    rw [CohomologyClass.mk_sub, hD, sub_zero]
  · intro p q hpq hp
    have hDv : D.1.v p q hpq = (δ (n - 1) n hh).v p q hpq := rfl
    simp only [coe_sub', Cochain.sub_v, hDv]
    rw [δ_v (n - 1) n (by omega) hh p q hpq (q - 1) (p + 1) rfl rfl]
    rcases lt_or_eq_of_le (show s ≤ p by omega) with h | h
    · rw [hz p q hpq h, Cochain.single_v_eq_zero _ _ _ _ _ (by omega),
        Cochain.single_v_eq_zero _ _ _ _ _ (by omega)]
      simp
    · subst h
      obtain rfl : q = d := by omega
      obtain rfl : e = q - 1 := by omega
      rw [Cochain.single_v, Cochain.single_v_eq_zero _ _ _ _ _ (by omega)]
      simp only [g, Category.assoc, hβ, Iso.inv_hom_id_assoc, comp_zero, smul_zero, add_zero, sub_self]

theorem step (s d : ℤ) (hd : s + n = d) [Finite (HK R (Sg (K.X s)) F d)] (hS : (S K F n (s - 1)).Finite) :
    (S K F n s).Finite := by
  classical
  let φ : HK R K F n → HK R (Sg (K.X s)) F d := fun x =>
    if h : x ∈ S K F n s then CohomologyClass.mk (clsC K F n s d hd (memS K F n h).choose (memS K F n h).choose_spec.2) else 0
  have key : ∀ x ∈ S K F n s, ∀ x' ∈ S K F n s, φ x = φ x' → x - x' ∈ S K F n (s - 1) := by
    intro x hx x' hx' he
    simp only [φ, dif_pos hx, dif_pos hx'] at he
    have hz := (memS K F n hx).choose_spec
    have hz' := (memS K F n hx').choose_spec
    have h0 : CohomologyClass.mk (clsC K F n s d hd (memS K F n hx).choose hz.2 -
        clsC K F n s d hd (memS K F n hx').choose hz'.2) = 0 := by
      rw [CohomologyClass.mk_sub, he, sub_self]
    obtain ⟨β, hβ⟩ := CB F (K.X s) d _ h0 (d - 1) (by omega)
    have hV : V K F n s ((memS K F n hx).choose - (memS K F n hx').choose) := by
      intro p q h hp
      simp [Cochain.sub_v, hz.2 p q h hp, hz'.2 p q h hp]
    obtain ⟨w, hw, hwV⟩ := KL K F n s d hd _ hV (d - 1) (by omega) β (by
      rw [hβ]
      simp only [coe_sub', Cochain.sub_v, clsC_v, Preadditive.comp_sub])
    exact ⟨w, by rw [hw, CohomologyClass.mk_sub, hz.1, hz'.1], hwV⟩
  let g : HK R (Sg (K.X s)) F d → HK R K F n := fun t =>
    if h : ∃ x ∈ S K F n s, φ x = t then h.choose else 0
  refine ((Set.finite_univ.prod hS).image (fun p => g p.1 + p.2)).subset ?_
  intro x hx
  have h : ∃ y ∈ S K F n s, φ y = φ x := ⟨x, hx, rfl⟩
  refine ⟨(φ x, x - g (φ x)), ⟨trivial, ?_⟩, ?_⟩
  · have hg : g (φ x) = h.choose := by simp only [g, dif_pos h]
    rw [hg]
    exact key x hx _ h.choose_spec.1 h.choose_spec.2.symm
  · simp

theorem base (s : ℤ) (hs : s + n < 0) : S K F n s ⊆ {0} := by
  rintro x ⟨z, rfl, hz⟩
  have : z = 0 := by
    refine Cocycle.ext (Cochain.ext _ _ (fun p q hpq => ?_))
    rw [coe_zero', Cochain.zero_v]
    rcases lt_or_ge s p with h | h
    · exact hz p q hpq h
    · exact (res_zero F q (by omega)).eq_of_tgt (z.1.v p q hpq) 0
  simp [this]

theorem LeafFilt_of : LateralTheory.E.LeafSSCut.LeafFilt := by
  intro _ R _ K _ F n hfin
  have ind : ∀ k : ℕ, ∀ r : ℕ, 1 ≤ r → n < r + k → (S K F n (-(r : ℤ))).Finite := by
    intro k
    induction k with
    | zero => intro r _ hr; exact (Set.finite_singleton 0).subset (base K F n _ (by push_cast at hr; omega))
    | succ k ih =>
      intro r hr1 hr
      by_cases hk : n < r + k
      · exact ih r hr1 hk
      · have : Finite (HK R (Sg (K.X (-(r : ℤ)))) F (n - r)) := hfin r (by omega) (by push_cast at hr; omega)
        have h2 := ih (r + 1) (by omega) (by push_cast at hr ⊢; omega)
        have e : (-((r + 1 : ℕ) : ℤ)) = -(r : ℤ) - 1 := by push_cast; ring
        rw [e] at h2
        exact step K F n (-(r : ℤ)) (n - r) (by omega) h2
  have hS := ind n.toNat 1 le_rfl (by omega)
  have e : (-((1 : ℕ) : ℤ)) = (0 : ℤ) - 1 := by norm_num
  rw [e] at hS
  have hsub : ((HK.pull R (LateralTheory.E.LeafSSCut.incl0 K) F n).ker : Set (HK R K F n)) ⊆ S K F n (0 - 1) := by
    intro x hx
    obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
    have hz : V K F n 0 z := fun p q hpq hp =>
      (CochainComplex.isZero_of_isStrictlyLE K 0 p hp).eq_of_src _ _
    have hc : CohomologyClass.mk (zcomp (Cocycle.ofHom (LateralTheory.E.LeafSSCut.incl0 K)) z (zero_add n)) = 0 := hx
    obtain ⟨β, hβ⟩ := CB F (K.X 0) n _ hc (n - 1) (by omega)
    obtain ⟨w, hw, hwV⟩ := KL K F n 0 n (zero_add n) z hz (n - 1) (by omega) β (by
      rw [hβ]
      change ((Cochain.ofHom (LateralTheory.E.LeafSSCut.incl0 K)).comp z.1 (zero_add n)).v 0 n (zero_add n) = _
      rw [Cochain.comp_v _ _ (zero_add n) 0 0 n (by omega) (by omega), Cochain.ofHom_v]
      simp [LateralTheory.E.LeafSSCut.incl0, HomologicalComplex.mkHomFromSingle_f])
    exact ⟨w, hw, hwV⟩
  exact (hS.subset hsub).to_subtype

end LateralTheory.E.LeafFiltPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafGeoVCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4

namespace LateralTheory.E.LeafGeoVCut

def FamilyVe {k Ω : Type} [Field k] [Field Ω] (X : Scheme.{0}) {C0 C1 C2 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (e : C0 ⟶ X)
    (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1) : Prop :=
  ∃ (B Y0 Y1 Y2 : Scheme.{0}) (b : B ⟶ Sp k) (V : B.Opens) (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1)
    (h : Y0 ⟶ X) (s : Sp Ω ⟶ B) (u0 : C0 ⟶ Y0) (u1 : C1 ⟶ Y1) (u2 : C2 ⟶ Y2),
    IsIntegral B ∧ IsProper b ∧ Set.range s ⊆ V ∧
    SmP p V ∧ SmP (g1 ≫ p) V ∧ SmP (g2 ≫ g1 ≫ p) V ∧ IsProper (g2 ≫ g1 ≫ h) ∧
    topologicalKrullDim B < topologicalKrullDim X ∧
    IrreducibleSpace Y0 ∧ topologicalKrullDim Y0 ≤ topologicalKrullDim X ∧ topologicalKrullDim Y0 < ⊤ ∧
    (p ⁻¹' (V : Set B)).Nonempty ∧
    IsPullback u0 c0 p s ∧ IsPullback u1 (γ1 ≫ c0) (g1 ≫ p) s ∧ IsPullback u2 (γ2 ≫ γ1 ≫ c0) (g2 ≫ g1 ≫ p) s ∧
    γ1 ≫ u0 = u1 ≫ g1 ∧ γ2 ≫ u1 = u2 ≫ g2 ∧ u0 ≫ h = e

def LeafCurveV : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k) [IsProper p],
  0 < topologicalKrullDim X → ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (_ : Algebra k Ω) (C0 : Scheme.{0})
    (c0 : C0 ⟶ Sp Ω) (e : C0 ⟶ X), IsCurve c0 ∧ e ≫ p = c0 ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)) ∧
    genericPoint X ∈ Set.range e ∧ ∀ R : Subalgebra k Ω, R.FG → ringKrullDim R < topologicalKrullDim X

theorem surj_of_generic {Y X : Scheme.{0}} [IrreducibleSpace X] (f : Y ⟶ X) [IsProper f]
    (hη : genericPoint X ∈ Set.range f) : Surjective f := by
  have hc : IsClosed (Set.range f) := f.isClosedMap.isClosed_range
  have h1 : closure ({genericPoint X} : Set X) ⊆ Set.range f :=
    closure_minimal (Set.singleton_subset_iff.mpr hη) hc
  rw [(genericPoint_spec X).def] at h1
  exact ⟨fun x => h1 (Set.mem_univ x)⟩

end LateralTheory.E.LeafGeoVCut

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafGeomPfLoc
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.D2 LateralTheory.E.LeafGeomPf

namespace LateralTheory.E.LeafGeomPfLoc

theorem projective_bundle_direct_sum_zero_vertex_coordinates_restrict {E : Spc} {a b : ℕ} (V : E ⟶ ofCat (glCat a)) (W : E ⟶ ofCat (glCat b)) {n : ℕ} {X Y : Scheme.{0}}
    (k : Y ⟶ X) (x : Sx (PB (bsumOf V W)) n X) (j : Fin (a + b)) :
    vec0 V W (((PB (bsumOf V W)).obj (op (SimplexCategory.mk n))).map k.op x) j = Scheme.Γ.map k.op (vec0 V W x j) := by
  set_option synthInstance.maxHeartbeats 200000 in
  have h := ConcreteCategory.congr_hom (((pullback.snd (bsumOf V W) (PGL.pr (a + b))).app (op (SimplexCategory.mk n))).naturality k.op) x
  unfold vec0
  erw [h]
  rfl

theorem unit_le {X : Scheme.{0}} (f : Γ(X, ⊤)) {V : X.Opens} (h : V ≤ X.basicOpen f) :
    IsUnit ((X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom f) := by
  have hu := X.toRingedSpace.isUnit_res_basicOpen (U := ⊤) f
  have := hu.map (X.presheaf.map (homOfLE h).op).hom
  erw [← CommRingCat.comp_apply, ← Functor.map_comp] at this
  exact this

theorem unit_basicOpen {X : Scheme.{0}} (f : Scheme.Γ.obj (op X)) :
    IsUnit (Scheme.Γ.map (X.basicOpen f).ι.op f) := by
  rw [Scheme.Γ_map_op, Scheme.Opens.ι_appTop]
  exact unit_le f (X.basicOpen f).ι_image_top.le

theorem leafLocal : LeafLocal := by
  intro E a b V W n X x
  have hspan : Ideal.span (Set.range (vec0 V W x)) = ⊤ :=
    ((show Fin (n + 1) ⥤ Um (a + b) (Scheme.Γ.obj (op X)) from
      ((pullback.snd (bsumOf V W) (PGL.pr (a + b))).app (op (SimplexCategory.mk n))).app (op X) x).obj 0).2
  have hcov : TopologicalSpace.IsOpenCover (fun j => X.basicOpen (vec0 V W x j)) := by
    have := AlgebraicGeometry.iSup_basicOpen_of_span_eq_top (X := X) ⊤ (Set.range (vec0 V W x)) hspan
    refine le_antisymm le_top ?_
    rw [← this]
    exact iSup₂_le fun _ ⟨j, hj⟩ => hj ▸ le_iSup (fun j => X.basicOpen (vec0 V W x j)) j
  let 𝒰 := X.openCoverOfIsOpenCover _ hcov
  refine ⟨Sieve.ofArrows 𝒰.X 𝒰.f, Scheme.zariskiTopology_le_etaleTopology _ 𝒰.mem_grothendieckTopology, ?_⟩
  intro Y k hk
  rw [Sieve.mem_ofArrows_iff] at hk
  obtain ⟨j, g, rfl⟩ := hk
  have hu : IsUnit (Scheme.Γ.map (g ≫ 𝒰.f j).op (vec0 V W x j)) := by
    rw [op_comp, Functor.map_comp]
    exact (unit_basicOpen (vec0 V W x j)).map (Scheme.Γ.map g.op).hom
  obtain ⟨i, rfl⟩ | ⟨i, rfl⟩ : (∃ i, j = Fin.castAdd b i) ∨ ∃ i, j = Fin.natAdd a i :=
    Fin.addCases (fun i => Or.inl ⟨i, rfl⟩) (fun i => Or.inr ⟨i, rfl⟩) j
  · left
    simp only [First, projective_bundle_direct_sum_zero_vertex_coordinates_restrict]
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩) hu
  · right
    simp only [Second, projective_bundle_direct_sum_zero_vertex_coordinates_restrict]
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩) hu

theorem LeafGeom_of (h1 : LeafHalf1) (h2 : LeafHalf2) : LateralTheory.E.D2.LeafGeom :=
  LateralTheory.E.LeafGeomPf.LeafGeom_of h1 h2 leafLocal

end LateralTheory.E.LeafGeomPfLoc
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafGhostRelCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex

namespace LateralTheory.E.LeafGhostRelCut
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut

def LeafTrunc : Prop := ∀ (A : Type 2) [Category.{1} A] [Abelian A] [HasDerivedCategory.{2} A]
  (K0 K1 K2 L : DerivedCategory A) (f : K0 ⟶ K1) (g : K1 ⟶ K2) (ℓ : L ⟶ K2),
  (∀ m : ℤ, 2 < m → IsZero ((DerivedCategory.homologyFunctor A m).obj K0)) →
  (DerivedCategory.homologyFunctor A 2).map f = 0 → (DerivedCategory.homologyFunctor A 1).map g = 0 →
  (∀ m : ℤ, m < 0 → IsZero ((DerivedCategory.homologyFunctor A m).obj K2)) →
  (∀ m : ℤ, m ≠ 0 → IsZero ((DerivedCategory.homologyFunctor A m).obj L)) →
  IsIso ((DerivedCategory.homologyFunctor A 0).map ℓ) →
  ∃ h : K0 ⟶ L, h ≫ ℓ = f ≫ g

def LeafRep : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  (∀ (A : Type) [CommRing A] (t : Sp A ⟶ B), SH A → Set.range t ⊆ V →
    (∀ m, 3 ≤ m → Subsingleton (Ht q (sch.obj (pullback p t)) m i)) ∧ pl q i (fibMap g1 p t) 2 = 0 ∧
    pl q i (fibMap g2 (g1 ≫ p) t) 1 = 0 ∧ Function.Bijective (pl q i (pullback.snd (g2 ≫ g1 ≫ p) t) 0)) →
  ∃ (A : Type 2) (_ : Category.{1} A) (_ : Abelian A) (_ : HasDerivedCategory.{2} A) (O K0 K1 K2 L : DerivedCategory A)
    (f : K0 ⟶ K1) (g : K1 ⟶ K2) (ℓ : L ⟶ K2)
    (e0 : ∀ n : ℤ, Hrel (ZMod q) (sch.map (pullback.fst p ι)) (tw q i) n → (O ⟶ (CategoryTheory.shiftFunctor (DerivedCategory A) n).obj K0))
    (e2 : ∀ n : ℤ, Hrel (ZMod q) (sch.map (pullback.fst (g2 ≫ g1 ≫ p) ι)) (tw q i) n → (O ⟶ (CategoryTheory.shiftFunctor (DerivedCategory A) n).obj K2))
    (eL : ∀ n : ℤ, Hrel (ZMod q) (sch.map ι) (tw q i) n → (O ⟶ (CategoryTheory.shiftFunctor (DerivedCategory A) n).obj L)),
    (∀ m : ℤ, 2 < m → IsZero ((DerivedCategory.homologyFunctor A m).obj K0)) ∧
    (DerivedCategory.homologyFunctor A 2).map f = 0 ∧ (DerivedCategory.homologyFunctor A 1).map g = 0 ∧
    (∀ m : ℤ, m < 0 → IsZero ((DerivedCategory.homologyFunctor A m).obj K2)) ∧
    (∀ m : ℤ, m ≠ 0 → IsZero ((DerivedCategory.homologyFunctor A m).obj L)) ∧
    IsIso ((DerivedCategory.homologyFunctor A 0).map ℓ) ∧
    (∀ n, Function.Injective (e2 n)) ∧ (∀ n, Function.Surjective (eL n)) ∧
    (∀ n y, e2 n (rpl q i (pullback.fst p ι) (pullback.fst (g2 ≫ g1 ≫ p) ι)
          (pullback.map (g2 ≫ g1 ≫ p) ι p ι (g2 ≫ g1) (𝟙 W) (𝟙 B) (by simp) (by simp)) (g2 ≫ g1)
          (pullback.lift_fst _ _ _).symm n y) = e0 n y ≫ (CategoryTheory.shiftFunctor (DerivedCategory A) n).map (f ≫ g)) ∧
    (∀ n c, e2 n (rpl q i ι (pullback.fst (g2 ≫ g1 ≫ p) ι) (pullback.snd (g2 ≫ g1 ≫ p) ι) (g2 ≫ g1 ≫ p)
          pullback.condition n c) = eL n c ≫ (CategoryTheory.shiftFunctor (DerivedCategory A) n).map ℓ)

theorem goal_of (hT : LeafTrunc) (hR : LeafRep) : LeafGhostRel := by
  intro hy q _ k _ hq i B W Y0 Y1 Y2 b ι _ V hV p g1 g2 h0 h1 h2 hA n y
  obtain ⟨A, _, _, _, O, K0, K1, K2, L, f, g, ℓ, e0, e2, eL, hK0, hf, hg, hK2, hL, hℓ, hinj, hsurj, n0, nL⟩ :=
    hR hy q k hq i b ι V hV p g1 g2 h0 h1 h2 hA
  obtain ⟨h, hh⟩ := hT A K0 K1 K2 L f g ℓ hK0 hf hg hK2 hL hℓ
  obtain ⟨c, hc⟩ := hsurj n (e0 n y ≫ (CategoryTheory.shiftFunctor (DerivedCategory A) n).map h)
  refine ⟨c, hinj n ?_⟩
  rw [n0, nL, hc, Category.assoc, ← Functor.map_comp, hh]

end LateralTheory.E.LeafGhostRelCut

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafKumSpecPfEv
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafKumSpecPf

theorem freeGen_res (R : Type) [CommRing R] (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    Sec.res g (freeGen R P U x) = freeGen R P V (P.map g.op x) := by
  unfold freeGen Sec.res
  have := ConcreteCategory.congr_hom ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).naturality g.op)
    (ModuleCat.freeMk (ULift.up x))
  have hm : (((freeP R).obj P).map g.op).hom (ModuleCat.freeMk (ULift.up x)) =
      ModuleCat.freeMk (ULift.up ((P.map g.op) x)) := by
    simp [freeP, ModuleCat.freeMk]
    first | (rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]; rfl) | (erw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]; rfl) | (simp [Finsupp.mapDomain_single]; rfl)
  erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hm] at this
  exact this.symm

end LateralTheory.E.LeafKumSpecPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafRepVanishPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafRepVanishPf

variable (R : Type) [CommRing R]

theorem free_mono {P Q : PSh} (φ : P ⟶ Q) [Mono φ] : Mono ((free R).map φ) := by
  have : Mono ((freeP R).map φ) := by
    rw [NatTrans.mono_iff_mono_app]
    intro Y
    rw [ModuleCat.mono_iff_injective]
    have hi : Function.Injective (φ.app Y) := (mono_iff_injective _).1 inferInstance
    have hu : Function.Injective (uliftFunctor.{1}.map (φ.app Y)) := by
      intro a b h; exact ULift.ext (hi (congrArg ULift.down h))
    exact Finsupp.mapDomain_injective hu
  unfold free
  simp only [Functor.comp_map]
  infer_instance

theorem chains_f (E E' : Spc) (f : E ⟶ E') (N : ℕ) :
    ((chains R).map f).f (-(N : ℤ)) = (chainsXIso R E N).hom ≫ (free R).map (f.app (op (SimplexCategory.mk N))) ≫ (chainsXIso R E' N).inv := by
  exact (HomologicalComplex.extendMap_f ((chainsN R).map f) ComplexShape.embeddingDownNat (i := N) rfl).trans rfl

theorem freeGen_nat {P Q : PSh} (φ : P ⟶ Q) (Y : Scheme.{0}) (x : P.obj (op Y)) :
    (((free R).map φ).hom.app (op Y)).hom (freeGen R P Y x) = freeGen R Q Y (φ.app _ x) := by
  have e := congrArg (fun t => (t.app (op Y)).hom (ModuleCat.freeMk (ULift.up.{1} x)))
    (toSheafify_naturality Scheme.etaleTopology ((freeP R).map φ))
  have e2 : (((freeP R).map φ).app (op Y)).hom (ModuleCat.freeMk (ULift.up.{1} x)) =
      ModuleCat.freeMk (ULift.up.{1} (φ.app _ x)) := ModuleCat.free_map_apply _ _
  simp only [NatTrans.comp_app, ModuleCat.hom_comp] at e
  refine e.symm.trans ?_
  exact congrArg (ModuleCat.Hom.hom ((toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op Y))) e2

theorem ev_pull {U E : Spc} (f : U ⟶ E) {K : Cx R} {n : ℤ} (γ : Cochain ((chains R).obj E) K n) (N : ℕ) (w : ℤ)
    (h : -(N : ℤ) + n = w) (Y : Scheme.{0}) (y : Sx U N Y) :
    ev ((Cochain.ofHom ((chains R).map f)).comp γ (zero_add n)) N w h Y y = ev γ N w h Y ((f.app _).app _ y) := by
  unfold ev
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, chains_f]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← freeGen_nat]
  rfl

theorem chains_mono {U E : Spc} (f : U ⟶ E) [Mono f] (p : ℤ) : Mono (((chains R).map f).f p) := by
  by_cases hp : p ≤ 0
  · obtain ⟨N, rfl⟩ : ∃ N : ℕ, p = -(N : ℤ) := ⟨p.natAbs, by omega⟩
    rw [chains_f]
    have := free_mono R (f.app (op (SimplexCategory.mk N)))
    infer_instance
  · have hz : IsZero (((chains R).obj U).X p) :=
      HomologicalComplex.isZero_extend_X _ _ _ (fun i hi => by
        change -(i : ℤ) = p at hi; omega)
    exact ⟨fun a b _ => hz.eq_of_tgt a b⟩

theorem LeafRepVanish_of : LateralTheory.E.LeafA6suppPf.LeafRepVanish := by
  intro R _ U E f hf F n a ha
  obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective a
  have hg := chains_mono R f
  have hinj : ∀ q, Injective ((res R F).X q) := fun q =>
    (inferInstance : Injective ((injectiveResolution F).cochainComplex.X q))
  have h1 : CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map f)) α (zero_add n)) = 0 := ha
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at h1
  obtain ⟨β', hβ'⟩ := h1
  let β : Cochain ((chains R).obj E) (res R F) (n - 1) :=
    Cochain.mk fun p q hpq => Injective.factorThru (β'.v p q hpq) (((chains R).map f).f p)
  have hβ : (Cochain.ofHom ((chains R).map f)).comp β (zero_add _) = β' := by
    refine Cochain.ext _ _ (fun p q hpq => ?_)
    rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
    simp only [β, Cochain.mk_v]
    exact Injective.comp_factorThru _ _
  let b : Cocycle ((chains R).obj E) (res R F) n := Cocycle.mk (δ (n - 1) n β) (n + 1) rfl (δ_δ _ _ _ _)
  refine ⟨α - b, ?_, ?_⟩
  · rw [CohomologyClass.mk_sub, (CohomologyClass.mk_eq_zero_iff b).2
      ((mem_coboundaries_iff b (n - 1) (by omega)).2 ⟨β, rfl⟩), sub_zero]
  · intro N w h Y y
    rw [← ev_pull]
    have e : (Cochain.ofHom ((chains R).map f)).comp (α - b).1 (zero_add n) = 0 := by
      rw [Cocycle.coe_sub, Cochain.comp_sub]
      have : (Cochain.ofHom ((chains R).map f)).comp (b : Cochain _ _ n) (zero_add n) = δ (n - 1) n β' := by
        rw [← hβ]; simp [b]
      rw [this, hβ']
      simp [zcomp]
    rw [e]
    simp [ev]

end LateralTheory.E.LeafRepVanishPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafTwistPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace LateralTheory.E.LeafTwistPf

def LeafLoc : Prop := Hyps → ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (F G : Shv R)
  (e : ∀ U : Scheme.{0}, (U ⟶ X) → (Sec F U ≃ₗ[ULift.{1} R] Sec G U)),
  (∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : U ⟶ X) (s : Sec F U), e V (g ≫ x) (Sec.res g s) = Sec.res g (e U x s)) →
  ∀ n : ℤ, Nonempty (H R (sch.obj X) F n ≃+ H R (sch.obj X) G n)

def LeafTwSec : Prop := ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B], Prim q B → ∀ i j : ℤ,
  ∃ e : ∀ U : Scheme.{0}, (U ⟶ Spec (CommRingCat.of B)) → (Sec (tw q i) U ≃ₗ[ULift.{1} (ZMod q)] Sec (tw q j) U),
    ∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : U ⟶ Spec (CommRingCat.of B)) (s : Sec (tw q i) U),
      e V (g ≫ x) (Sec.res g s) = Sec.res g (e U x s)

theorem LeafTwist_of (hL : LeafLoc) (hT : LeafTwSec) : LateralTheory.E.LeafKumCut.LeafTwist := by
  intro hy q _ B _ hP n i j
  obtain ⟨ζ⟩ := hP
  obtain ⟨e, he⟩ := hT q B ζ i j
  exact hL hy (ZMod q) (Spec (CommRingCat.of B)) (tw q i) (tw q j) e he n

end LateralTheory.E.LeafTwistPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.PointDetect0Of
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace LateralTheory.E.PointDetect0Pf

def EtSep : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0}) (s : Sec F X),
  (∀ x : X, ∃ (U : Scheme.{0}) (g : U ⟶ X), Etale g ∧ x ∈ Set.range g.base ∧ Sec.res g s = 0) → s = 0

theorem etSep : EtSep := by
  intro R _ F X s h
  choose U g hE hx h0 using h
  have hR : Presieve.ofArrows U g ∈ Scheme.precoverage @Etale X := by
    exact (Scheme.ofArrows_mem_precoverage_iff @Etale).2 ⟨fun x => ⟨x, hx x⟩, hE⟩
  have hT : Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) := by
    have := (Presheaf.isSheaf_iff_isSheaf_forget Scheme.etaleTopology F.obj (forget _)).1 F.property
    exact (isSheaf_iff_isSheaf_of_type _ _).1 this
  apply (hT.isSheafFor_of_mem_precoverage hR).isSeparatedFor.ext
  rintro Y f ⟨x⟩
  change Sec.res (g x) s = (F.obj.map (g x).op).hom 0
  rw [h0 x, map_zero]

end LateralTheory.E.PointDetect0Pf
end
end

