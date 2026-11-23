module

public import Development.EtaleCohomology.CohomologicalPurity.Bundle0004
public import Development.EtaleCohomology.CohomologicalPurity.Bundle0003
public import Development.EtaleCohomology.CohomologicalPurity.LeafClCut

@[expose] public section

-- bundled from Development.EtaleCohomology.CohomologicalPurity.FinLeafSemi
section
namespace LateralTheory.Fin.LeafSemi
theorem etale_purity_semilocal_of_reduction : LateralTheory.CohomologicalPurity.LeafSemi := by
  apply LateralTheory.CohomologicalPurity.LeafSemi_of
theorem intersectionNumber_baseChange : LateralTheory.CohomologicalPurity.LeafSemi := etale_purity_semilocal_of_reduction
end LateralTheory.Fin.LeafSemi
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.FreePMapMk
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Bd

namespace GenPf

variable (R : Type) [CommRing R]

abbrev mk {P : PSh} {U : Scheme.{0}} (x : P.obj (op U)) : ((freeP R).obj P).obj (op U) :=
  ModuleCat.freeMk (X := uliftFunctor.{1}.obj (P.obj (op U))) (ULift.up x)

theorem freePresheaf_obj_map_mk (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    (((freeP R).obj P).map g.op).hom (mk R x) = mk R (P.map g.op x) := by
  simp only [freeP]
  exact Finsupp.mapDomain_single

theorem freePresheaf_map_app_mk {P P' : PSh} (f : P ⟶ P') (U : Scheme.{0}) (x : P.obj (op U)) :
    (((freeP R).map f).app (op U)).hom (mk R x) = mk R (f.app (op U) x) := by
  simp only [freeP]
  exact Finsupp.mapDomain_single

theorem part1 (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    Sec.res g (freeGen R P U x) = freeGen R P V (P.map g.op x) := by
  have h := congrArg (fun k => ModuleCat.Hom.hom k (mk R x))
    ((toSheafify Scheme.etaleTopology.{0} ((freeP R).obj P)).naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [freePresheaf_obj_map_mk] at h
  exact h.symm

theorem part2 (P P' : PSh) (f : P ⟶ P') (U : Scheme.{0}) (x : P.obj (op U)) :
    Sec.map ((free R).map f) (freeGen R P U x) = freeGen R P' U (f.app (op U) x) := by
  have h := congrArg (fun k => ModuleCat.Hom.hom (NatTrans.app k (op U)) (mk R x))
    (toSheafify_naturality Scheme.etaleTopology.{0} ((freeP R).map f))
  simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [freePresheaf_map_app_mk] at h
  exact h.symm

def adjE (P : PSh) (G : Shv R) : ((free R).obj P ⟶ G) ≃ ((freeP R).obj P ⟶ G.obj) :=
  (sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))).homEquiv ((freeP R).obj P) G

theorem adjE_apply (P : PSh) (G : Shv R) (φ : (free R).obj P ⟶ G) :
    adjE R P G φ = toSheafify Scheme.etaleTopology.{0} ((freeP R).obj P) ≫ φ.hom :=
  Adjunction.homEquiv_unit _ _ _ _

theorem adjE_gen (P : PSh) (G : Shv R) (φ : (free R).obj P ⟶ G) (U : Scheme.{0}) (x : P.obj (op U)) :
    ((adjE R P G φ).app (op U)).hom (mk R x) = Sec.map φ (freeGen R P U x) := by
  rw [adjE_apply]; rfl

theorem part3 (P : PSh) (G : Shv R) (φ ψ : (free R).obj P ⟶ G)
    (h : ∀ (U : Scheme.{0}) (x : P.obj (op U)), Sec.map φ (freeGen R P U x) = Sec.map ψ (freeGen R P U x)) :
    φ = ψ := by
  apply (adjE R P G).injective
  refine NatTrans.ext (funext fun U => ?_)
  obtain ⟨U⟩ := U
  apply ModuleCat.free_hom_ext
  rintro ⟨y⟩
  exact (adjE_gen R P G φ U y).trans ((h U y).trans (adjE_gen R P G ψ U y).symm)

def descP (P : PSh) (G : Shv R) (t : ∀ U : Scheme.{0}, P.obj (op U) → Sec G U)
    (ht : ∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)), Sec.res g (t U x) = t V (P.map g.op x)) :
    (freeP R).obj P ⟶ G.obj where
  app U := ModuleCat.freeDesc (TypeCat.ofHom fun y => t U.unop (ULift.down y))
  naturality U V g := by
    apply ModuleCat.free_hom_ext
    obtain ⟨U⟩ := U
    obtain ⟨V⟩ := V
    rintro ⟨y⟩
    erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
    erw [freePresheaf_obj_map_mk R P g.unop y, ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
    exact (ht g.unop y).symm

theorem freePresheafDesc_app_mk (P : PSh) (G : Shv R) (t : ∀ U : Scheme.{0}, P.obj (op U) → Sec G U)
    (ht : ∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)), Sec.res g (t U x) = t V (P.map g.op x))
    (U : Scheme.{0}) (x : P.obj (op U)) : ((descP R P G t ht).app (op U)).hom (mk R x) = t U x := by
  simp only [descP]
  exact ModuleCat.freeDesc_apply _ _

theorem part4 (P : PSh) (G : Shv R) (t : ∀ U : Scheme.{0}, P.obj (op U) → Sec G U)
    (ht : ∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)), Sec.res g (t U x) = t V (P.map g.op x)) :
    ∃ φ : (free R).obj P ⟶ G, ∀ (U : Scheme.{0}) (x : P.obj (op U)), Sec.map φ (freeGen R P U x) = t U x := by
  refine ⟨(adjE R P G).symm (descP R P G t ht), fun U x => ?_⟩
  rw [← adjE_gen, Equiv.apply_symm_apply, freePresheafDesc_app_mk]

end GenPf

theorem LeafGen_of : LeafGen := by
  intro R _ P
  exact ⟨fun g x => GenPf.part1 R P g x, fun P' f U x => GenPf.part2 R P P' f U x,
    fun G φ ψ h => GenPf.part3 R P G φ ψ h, fun G t ht => GenPf.part4 R P G t ht⟩

end LateralTheory.CohomologicalPurity.Bd
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafCmpPf
section
noncomputable section
open CategoryTheory AlgebraicGeometry

namespace LateralTheory.CohomologicalPurity.Cl

def LeafCmpNb : Prop := ∀ (X : Scheme.{0}) (B B₀ : Type) [CommRing B] [CommRing B₀] (w : Spec (CommRingCat.of B) ⟶ X)
  (w₀ : Spec (CommRingCat.of B₀) ⟶ X), IsOpenImmersion w₀ → ∀ y, w y ∈ Set.range w₀ →
  ∃ (C : Type) (_ : CommRing C) (φ : B →+* C) (ψ : B₀ →+* C),
    IsOpenImmersion (Spec.map (CommRingCat.ofHom φ)) ∧ y ∈ Set.range (Spec.map (CommRingCat.ofHom φ)) ∧
    Spec.map (CommRingCat.ofHom φ) ≫ w = Spec.map (CommRingCat.ofHom ψ) ≫ w₀

def LeafCmpId : Prop := ∀ (d : ℕ) (P : SP d) (F F₀ : Frame P) (C : Type) [CommRing C] (φ : F.B →+* C) (ψ : F₀.B →+* C),
  Spec.map (CommRingCat.ofHom φ) ≫ F.w = Spec.map (CommRingCat.ofHom ψ) ≫ F₀.w → F.I.map φ = F₀.I.map ψ

theorem spec_comp_ofHom {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    Spec.map (CommRingCat.ofHom (g.comp f)) = Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) := by
  rw [← Spec.map_comp]; rfl

theorem LeafCmp_of (hMat : LeafMat) (hNb : LeafCmpNb) (hId : LeafCmpId) : LeafCmp := by
  intro d P F F₀ h₀ y hy
  obtain ⟨C, _, φ, ψ, ho, ⟨z, rfl⟩, e⟩ := hNb P.X F.B F₀.B F.w F₀.w h₀ y hy
  have hI := hId d P F F₀ C φ ψ e
  obtain ⟨M, hdet, hM⟩ := hMat d C (ψ ∘ F₀.x) (φ ∘ F.x)
    (by rw [span_comp, span_comp, F.hx, F₀.hx, hI]) z
  let g : C := M.det
  let l : C →+* Localization.Away g := algebraMap C (Localization.Away g)
  have hl : IsOpenImmersion (Spec.map (CommRingCat.ofHom l)) :=
    Scheme.isOpenImmersion_SpecMap_localizationAway (R := CommRingCat.of C) g
  refine ⟨Localization.Away g, inferInstance, l.comp φ, l.comp ψ, M.map l, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [spec_comp_ofHom φ l]; infer_instance
  · have hr : z ∈ Set.range (PrimeSpectrum.comap l) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]; exact hdet
    obtain ⟨z', hz'⟩ := hr
    refine ⟨show Spec (CommRingCat.of (Localization.Away g)) from z', ?_⟩
    rw [spec_comp_ofHom φ l]
    show (Spec.map (CommRingCat.ofHom φ)) ((Spec.map (CommRingCat.ofHom l)) z') = _
    exact congrArg (Spec.map (CommRingCat.ofHom φ)) hz'
  · rw [spec_comp_ofHom φ l, spec_comp_ofHom ψ l, Category.assoc, Category.assoc, e]
  · rw [← Ideal.map_map, ← Ideal.map_map, hI]
  · change IsUnit (l.mapMatrix M).det
    rw [← RingHom.map_det]; exact IsLocalization.Away.algebraMap_isUnit g
  · funext j
    change l (φ (F.x j)) = _
    rw [show φ (F.x j) = (φ ∘ F.x) j from rfl, hM, RingHom.map_mulVec]
    rfl

end LateralTheory.CohomologicalPurity.Cl
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafCoordPf
section
noncomputable section
open TensorProduct

namespace LateralTheory.CohomologicalPurity.ChartCut

lemma kd_span {R A A' : Type} [CommRing R] [CommRing A] [CommRing A'] [Algebra R A] [Algebra A A']
    [Algebra R A'] [IsScalarTower R A A'] (f : A) [IsLocalization.Away f A'] (N : Submodule A' Ω[A'⁄R])
    (hN : ∀ a : A, KaehlerDifferential.D R A' (algebraMap A A' a) ∈ N) : N = ⊤ := by
  rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation, Submodule.span_le]
  rintro _ ⟨a', rfl⟩
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers f) a'
  simp only at hs
  have hu : IsUnit (algebraMap A A' (s : A)) := IsLocalization.map_units A' s
  have h1 : algebraMap A A' (s : A) • KaehlerDifferential.D R A' a' ∈ N := by
    have h := congrArg (KaehlerDifferential.D R A') hs
    rw [Derivation.leibniz] at h
    have e : algebraMap A A' (s : A) • KaehlerDifferential.D R A' a' =
        KaehlerDifferential.D R A' (algebraMap A A' a) - a' • KaehlerDifferential.D R A' (algebraMap A A' s) := by
      rw [← h]; abel
    rw [e]; exact N.sub_mem (hN a) (N.smul_mem _ (hN s))
  obtain ⟨u, hu'⟩ := hu
  have h2 := N.smul_mem (↑u⁻¹ : A') h1
  rwa [← hu', smul_smul, Units.inv_mul, one_smul] at h2

theorem LeafCoord_of (hR : LeafRank) (hP : LeafPick) (hS : LeafSpan) (hE : LeafEt) : LeafCoord := by
  intro e d R A _ _ φ I p hp hIp hstd
  letI : Algebra R A := φ.toAlgebra
  haveI h1 : Algebra.IsStandardSmoothOfRelativeDimension (e + d) R A := hstd.1
  haveI h2 : Algebra.IsStandardSmoothOfRelativeDimension e R (A ⧸ I) := hstd.2
  haveI : Algebra.IsStandardSmooth R A := h1.isStandardSmooth
  haveI : Algebra.IsStandardSmooth R (A ⧸ I) := h2.isStandardSmooth
  have hfg : I.FG := by
    have := Algebra.FinitePresentation.ker_fG_of_surjective (Ideal.Quotient.mkₐ R I)
      (Ideal.Quotient.mkₐ_surjective R I)
    simpa [Ideal.Quotient.mkₐ_ker] using this
  haveI : Module.Finite A I := Module.Finite.iff_fg.mpr hfg
  haveI := hp
  have hrank := hR e d R A I p hIp h1 h2
  obtain ⟨x, f, hf, hx⟩ := hP d A I p hrank
  set x' : Fin d → A := fun j => (x j : A) with hx'
  have hxI : ∀ j, x' j ∈ I := fun j => (x j).2
  have hfx : ∀ a ∈ I, f * a ∈ Ideal.span (Set.range x') := by
    intro a ha
    have h := Submodule.mem_map_of_mem (f := I.subtype) (hx ⟨a, ha⟩)
    rw [Submodule.map_span, ← Set.range_comp] at h
    exact h
  obtain ⟨y, g, hg, hy⟩ := hS e d R A I p hp hIp h2 x' f hxI hf hfx
  refine ⟨f * g, fun h => (hp.mem_or_mem h).elim hf hg, ?_⟩
  intro A' _ _ _
  letI : Algebra R A' := ((algebraMap A A').comp φ).toAlgebra
  haveI : IsScalarTower R A A' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hfgu : IsUnit (algebraMap A A' (f * g)) := IsLocalization.Away.algebraMap_isUnit (f * g)
  rw [map_mul] at hfgu
  have hfu : IsUnit (algebraMap A A' f) := isUnit_of_mul_isUnit_left hfgu
  have hgu : IsUnit (algebraMap A A' g) := isUnit_of_mul_isUnit_right hfgu
  refine ⟨fun j => algebraMap A A' (x' j), fun k => algebraMap A A' (y k), ?_, ?_⟩
  · haveI : Algebra.IsStandardSmoothOfRelativeDimension 0 A A' :=
      Algebra.IsStandardSmoothOfRelativeDimension.localization_away (f * g)
    have h3 : Algebra.IsStandardSmoothOfRelativeDimension (0 + (e + d)) R A' :=
      Algebra.IsStandardSmoothOfRelativeDimension.trans (R := R) (S := A) (T := A') (n := e + d) (m := 0)
    rw [zero_add] at h3
    refine hE (e + d) R A' (Fin d ⊕ Fin e) _ (by simp [add_comm]) h3 ?_
    apply kd_span (R := R) (A := A) (f * g)
    intro a
    have hm := Submodule.mem_map_of_mem (f := KaehlerDifferential.map R R A A')
      (hy (KaehlerDifferential.D R A a))
    rw [Submodule.map_span, LinearMap.map_smul, KaehlerDifferential.map_D] at hm
    have hle : Submodule.span A (KaehlerDifferential.map R R A A' ''
        Set.range fun k => KaehlerDifferential.D R A (Sum.elim x' y k)) ≤
        (Submodule.span A' (Set.range fun k => KaehlerDifferential.D R A'
          (Sum.elim (fun j => algebraMap A A' (x' j)) (fun k => algebraMap A A' (y k)) k))).restrictScalars A := by
      rw [Submodule.span_le]
      rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      rw [KaehlerDifferential.map_D]
      apply Submodule.subset_span
      exact ⟨k, by cases k <;> rfl⟩
    have h5 := hle hm
    rw [Submodule.restrictScalars_mem, ← algebraMap_smul A'] at h5
    obtain ⟨u, hu⟩ := hgu
    have h6 := Submodule.smul_mem _ (↑u⁻¹ : A') h5
    rwa [← hu, smul_smul, Units.inv_mul, one_smul] at h6
  · apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap]
      have h := Ideal.mem_map_of_mem (algebraMap A A') (hfx a ha)
      rw [Ideal.map_span, map_mul, ← Set.range_comp] at h
      obtain ⟨u, hu⟩ := hfu
      have h6 := Ideal.mul_mem_left _ (↑u⁻¹ : A') h
      rw [← mul_assoc, ← hu, Units.inv_mul, one_mul] at h6
      exact h6
    · rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact Ideal.mem_map_of_mem _ (hxI j)

end LateralTheory.CohomologicalPurity.ChartCut
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafDeltaPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Bd

section Pf
variable {R : Type} [CommRing R] {A B D : Cx R} {i : A ⟶ B} {l r : B ⟶ D} {I : Cx R}

theorem pb_δ (f : A ⟶ B) {n m : ℤ} (c : Cochain B I n) : pb f (δ n m c) = δ n m (pb f c) := by
  simp [pb]

theorem pb_sub (f : A ⟶ B) {n : ℤ} (c c' : Cochain B I n) : pb f (c - c') = pb f c - pb f c' := by
  simp [pb]

theorem pb_zero (f : A ⟶ B) {n : ℤ} : pb f (0 : Cochain B I n) = 0 := by
  simp [pb]

theorem pb_add (f : A ⟶ B) {n : ℤ} (c c' : Cochain B I n) : pb f (c + c') = pb f c + pb f c' := by
  simp [pb]

theorem Tri.sub {n : ℤ} {a a' : Cocycle A I n} {c c' : Cochain B I n} {b b' : Cocycle D I (n + 1)}
    (h : Tri i l r a c b) (h' : Tri i l r a' c' b') : Tri i l r (a - a') (c - c') (b - b') := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  refine ⟨?_, ?_, ?_⟩
  · rw [pb_sub, h1, h1', Cocycle.coe_sub]
  · rw [Cocycle.coe_sub, pb_sub, h2, h2', δ_sub]
  · rw [Cocycle.coe_sub, pb_sub, h3, h3', sub_zero]

theorem Tri.add {n : ℤ} {a a' : Cocycle A I n} {c c' : Cochain B I n} {b b' : Cocycle D I (n + 1)}
    (h : Tri i l r a c b) (h' : Tri i l r a' c' b') : Tri i l r (a + a') (c + c') (b + b') := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  refine ⟨?_, ?_, ?_⟩
  · rw [pb_add, h1, h1', Cocycle.coe_add]
  · rw [Cocycle.coe_add, pb_add, h2, h2', δ_add]
  · rw [Cocycle.coe_add, pb_add, h3, h3', add_zero]

theorem Good.mk_zero (hG : Good i l r I) {n : ℤ} {a : Cocycle A I n} {c : Cochain B I n} {b : Cocycle D I (n + 1)}
    (h : Tri i l r a c b) (ha : a ∈ coboundaries A I n) : CohomologyClass.mk b = 0 := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨f, hf⟩ := (mem_coboundaries_iff a (n - 1) (by omega)).1 ha
  obtain ⟨g, hg⟩ := hG.surj (n - 1) f
  obtain ⟨e, he1, he2⟩ := hG.glue n (c - δ (n - 1) n g) 0 (by
    rw [pb_sub, pb_δ, hg, hf, h1, sub_self, pb_zero])
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff b n rfl]
  refine ⟨e, hG.ext (n + 1) _ _ ?_ ?_⟩
  · rw [pb_δ, he1, h2, δ_sub, δ_δ, sub_zero]
  · rw [pb_δ, he2, h3, δ_zero]

theorem Good.mk_eq (hG : Good i l r I) {n : ℤ} {a a' : Cocycle A I n} {c c' : Cochain B I n}
    {b b' : Cocycle D I (n + 1)} (h : Tri i l r a c b) (h' : Tri i l r a' c' b')
    (ha : a - a' ∈ coboundaries A I n) : CohomologyClass.mk b = CohomologyClass.mk b' := by
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub]
  exact hG.mk_zero (h.sub h') ha

theorem tri_zero {n : ℤ} : Tri i l r (0 : Cocycle A I n) 0 (0 : Cocycle D I (n + 1)) :=
  ⟨by rw [pb_zero, Cocycle.coe_zero], by rw [Cocycle.coe_zero, pb_zero, δ_zero], by rw [Cocycle.coe_zero, pb_zero]⟩

theorem Tri.ker {n : ℤ} {a : Cocycle A I n} {c : Cochain B I n} {b : Cocycle D I (n + 1)} (h : Tri i l r a c b) :
    CohomologyClass.mk b ∈ (hpb r I (n + 1)).ker := by
  rw [AddMonoidHom.mem_ker, hpb, cpre_mk, CohomologyClass.mk_eq_zero_iff]
  have : zcomp (Cocycle.ofHom r) b (zero_add (n + 1)) = 0 := Cocycle.ext (by
    change pb r b.1 = _
    rw [h.2.2, Cocycle.coe_zero])
  rw [this]
  exact zero_mem _

theorem LeafDelta_of : LeafDelta := by
  intro R _ A B D i l r I hG n
  choose c b hcb using fun a : Cocycle A I n => hG.tri a
  let F : Cocycle A I n →+ (hpb r I (n + 1)).ker :=
    AddMonoidHom.mk' (fun a => ⟨CohomologyClass.mk (b a), (hcb a).ker⟩) (fun a a' => by
      apply Subtype.ext
      change CohomologyClass.mk (b (a + a')) = CohomologyClass.mk (b a) + CohomologyClass.mk (b a')
      rw [← CohomologyClass.mk_add]
      exact hG.mk_eq (hcb _) ((hcb a).add (hcb a')) (by rw [sub_self]; exact zero_mem _))
  refine ⟨CohomologyClass.descAddMonoidHom F ?_, ?_⟩
  · intro a ha
    rw [AddMonoidHom.mem_ker]
    apply Subtype.ext
    change CohomologyClass.mk (b a) = 0
    rw [← CohomologyClass.mk_zero D I (n + 1)]
    exact hG.mk_eq (hcb a) tri_zero (by rw [sub_zero]; exact ha)
  · intro a c' b' h
    change CohomologyClass.mk (b a) = _
    exact hG.mk_eq (hcb a) h (by rw [sub_self]; exact zero_mem _)

end Pf
end LateralTheory.CohomologicalPurity.Bd
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafEtPf
section
noncomputable section
open TensorProduct KaehlerDifferential

namespace LateralTheory.CohomologicalPurity.LeafEtPf

theorem etale_main (n : ℕ) (R A ι : Type) [CommRing R] [CommRing A] [Algebra R A] [Fintype ι] (z : ι → A)
    (hn : Fintype.card ι = n) (hA : Algebra.IsStandardSmoothOfRelativeDimension n R A)
    (hspan : Submodule.span A (Set.range fun k => KaehlerDifferential.D R A (z k)) = ⊤) :
    (MvPolynomial.eval₂Hom (algebraMap R A) z).Etale := by
  rcases subsingleton_or_nontrivial A with hA0 | hA0
  · exact ChartCut.etale_of_subsingleton _
  letI : Algebra (MvPolynomial ι R) A := (MvPolynomial.aeval z).toRingHom.toAlgebra
  have : IsScalarTower R (MvPolynomial ι R) A :=
    IsScalarTower.of_algebraMap_eq fun r => (MvPolynomial.aeval_C z r).symm
  have := hA
  have : Algebra.IsStandardSmooth R A := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  have hD : ∀ k, mapBaseChange R (MvPolynomial ι R) A
      ((1 : A) ⊗ₜ D R (MvPolynomial ι R) (MvPolynomial.X k)) = D R A (z k) := by
    intro k
    rw [mapBaseChange_tmul, one_smul, map_D]
    congr 1
    exact MvPolynomial.aeval_X z k
  have hsurj : Function.Surjective (mapBaseChange R (MvPolynomial ι R) A) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact ⟨_, hD k⟩
  haveI hΩ : Subsingleton Ω[A⁄MvPolynomial ι R] := by
    refine subsingleton_of_forall_eq 0 fun ω => ?_
    obtain ⟨w, rfl⟩ := map_surjective R (MvPolynomial ι R) A ω
    obtain ⟨u, rfl⟩ := hsurj w
    exact (exact_mapBaseChange_map R (MvPolynomial ι R) A).apply_apply_eq_zero u
  have hfin : Module.finrank A Ω[A⁄R] = n :=
    Module.finrank_eq_of_rank_eq (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n)
  let b := Algebra.TensorProduct.basis A (mvPolynomialBasis R ι)
  have hli : LinearIndependent A (mapBaseChange R (MvPolynomial ι R) A ∘ b) := by
    have : (mapBaseChange R (MvPolynomial ι R) A ∘ b) = fun k => D R A (z k) := by
      funext k
      simp only [Function.comp_apply, b, Algebra.TensorProduct.basis_apply, mvPolynomialBasis_apply, hD]
    rw [this]
    exact linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge (hn.trans hfin.symm)
  have hinj : Function.Injective (mapBaseChange R (MvPolynomial ι R) A) :=
    LinearMap.injective_of_linearIndependent b.span_eq hli
  haveI hH1 : Subsingleton (Algebra.H1Cotangent (MvPolynomial ι R) A) := by
    refine subsingleton_of_forall_eq 0 fun h => ?_
    have h1 : Algebra.H1Cotangent.δ R (MvPolynomial ι R) A h = 0 := by
      apply hinj
      rw [map_zero]
      exact (Algebra.H1Cotangent.exact_δ_mapBaseChange R (MvPolynomial ι R) A).apply_apply_eq_zero h
    obtain ⟨g, rfl⟩ := ((Algebra.H1Cotangent.exact_map_δ R (MvPolynomial ι R) A) h).mp h1
    rw [Subsingleton.elim g 0, map_zero]
  have : Algebra.FinitePresentation (MvPolynomial ι R) A :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R (MvPolynomial ι R) A
  have : Algebra.IsStandardSmooth (MvPolynomial ι R) A :=
    Algebra.IsStandardSmooth.of_basis_kaehlerDifferential (I := Empty) (Module.Basis.empty _) (by rintro _ ⟨i, _⟩; exact i.elim)
  have : Algebra.FormallyUnramified (MvPolynomial ι R) A := ⟨hΩ⟩
  have : Algebra.Etale (MvPolynomial ι R) A :=
    Algebra.Etale.iff_formallyUnramified_and_smooth.mpr ⟨inferInstance, inferInstance⟩
  exact RingHom.etale_algebraMap.mpr this

theorem LeafEt_of : ChartCut.LeafEt := by
  intro n R A ι _ _ _ _ z hn hA hspan
  exact etale_main n R A ι z hn hA hspan

end LateralTheory.CohomologicalPurity.LeafEtPf
end
end

-- bundled from Development.EtaleCohomology.CohomologicalPurity.LeafExcSheafCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity

def LeafFreeCok : Prop := ∀ (R : Type) [CommRing R] {A' B' A B : PSh} (i' : A' ⟶ B') (i : A ⟶ B) (a : A' ⟶ A)
  (b : B' ⟶ B) (w : i' ≫ b = a ≫ i),
  (∀ (T : Scheme.{0}) (y : B'.obj (op T)) (x : A.obj (op T)), i.app (op T) x = b.app (op T) y →
    ∃ x' : A'.obj (op T), i'.app (op T) x' = y) →
  (∀ (T : Scheme.{0}) (y : B.obj (op T)), ∃ S ∈ Scheme.etaleTopology T, ∀ ⦃V : Scheme.{0}⦄ (g : V ⟶ T), S g →
    (∃ x : A.obj (op V), i.app (op V) x = B.map g.op y) ∨ ∃ y' : B'.obj (op V), b.app (op V) y' = B.map g.op y) →
  (∀ (T : Scheme.{0}) (y₁ y₂ : B'.obj (op T)), b.app (op T) y₁ = b.app (op T) y₂ →
    ∃ S ∈ Scheme.etaleTopology T, ∀ ⦃V : Scheme.{0}⦄ (g : V ⟶ T), S g →
      B'.map g.op y₁ = B'.map g.op y₂ ∨ ∃ x : A.obj (op V), i.app (op V) x = b.app (op V) (B'.map g.op y₁)) →
  IsIso (cokernel.map ((free R).map i') ((free R).map i) ((free R).map a) ((free R).map b)
    (by rw [← Functor.map_comp, ← Functor.map_comp, w]))

def LeafSurjGeo : Prop := ∀ {X' X Z : Scheme.{0}} (f : X' ⟶ X) [Etale f] (ι' : Z ⟶ X') (ι : Z ⟶ X)
  [IsClosedImmersion ι], IsPullback ι' (𝟙 Z) f ι → ∀ (U : X.Opens), (U : Set X) = (Set.range ι)ᶜ →
  ∀ {T : Scheme.{0}} (t : T ⟶ X), ∃ S ∈ Scheme.etaleTopology T, ∀ ⦃V : Scheme.{0}⦄ (g : V ⟶ T), S g →
    (∃ x : V ⟶ U.toScheme, x ≫ U.ι = g ≫ t) ∨ ∃ y : V ⟶ X', y ≫ f = g ≫ t

def LeafInjGeo : Prop := ∀ {X' X Z : Scheme.{0}} (f : X' ⟶ X) [Etale f] (ι' : Z ⟶ X') (ι : Z ⟶ X)
  [IsClosedImmersion ι], IsPullback ι' (𝟙 Z) f ι → ∀ (U : X.Opens), (U : Set X) = (Set.range ι)ᶜ →
  ∀ {T : Scheme.{0}} (y₁ y₂ : T ⟶ X'), y₁ ≫ f = y₂ ≫ f →
    ∃ S ∈ Scheme.etaleTopology T, ∀ ⦃V : Scheme.{0}⦄ (g : V ⟶ T), S g →
      g ≫ y₁ = g ≫ y₂ ∨ ∃ x : V ⟶ U.toScheme, x ≫ U.ι = (g ≫ y₁) ≫ f

theorem excSheaf_cart_preimage {X' X T : Scheme.{0}} (f : X' ⟶ X) (U : X.Opens) (y : T ⟶ X') (x : T ⟶ U.toScheme)
    (hx : x ≫ U.ι = y ≫ f) : ∃ x' : T ⟶ (f ⁻¹ᵁ U).toScheme, x' ≫ (f ⁻¹ᵁ U).ι = y :=
  ⟨(isPullback_morphismRestrict f U).lift x y hx, (isPullback_morphismRestrict f U).lift_snd _ _ _⟩

theorem LeafExcSheaf_of (hF : LeafFreeCok) (hS : LeafSurjGeo) (hI : LeafInjGeo) : LeafExcSheaf := by
  intro R _ X' X Z f _ ι' ι _ hp U' U hU h
  subst h
  exact hF R (yoneda.map (f ⁻¹ᵁ U).ι) (yoneda.map U.ι) (yoneda.map (f.resLE U (f ⁻¹ᵁ U) le_rfl)) (yoneda.map f)
    (by rw [← Functor.map_comp, ← Functor.map_comp, Scheme.Hom.resLE_comp_ι])
    (fun T y x hx => excSheaf_cart_preimage f U y x hx) (fun T y => hS f ι' ι hp U hU y)
    (fun T y₁ y₂ h => hI f ι' ι hp U hU y₁ y₂ h)

end LateralTheory.CohomologicalPurity
end
end

