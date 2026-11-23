module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne
public import Development.EtaleCohomology.EtaleTrace.Bundle0004
public import Development.EtaleCohomology.EtaleTrace.Bundle0001
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.CategoryTheory.CofilteredSystem
public import Development.EtaleCohomology.EtaleTrace.LRingPf

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PComps
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace

namespace UpperTheory.Gal.KunnethLefschetz

theorem comps_holds : Comps := by
  classical
  unfold Comps
  intro k _ _ d X p hp hX
  obtain ⟨hfin, hopen⟩ := comp_fin d p hp
  let m := Nat.card (_root_.ConnectedComponents X)
  let e : Fin m ≃ _root_.ConnectedComponents X := (Finite.equivFin _).symm
  let rep : Fin m → X := fun j => (ConnectedComponents.surjective_coe (e j)).choose
  have hrep : ∀ j, (rep j : _root_.ConnectedComponents X) = e j := fun j =>
    (ConnectedComponents.surjective_coe (e j)).choose_spec
  let U : Fin m → X.Opens := fun j => ⟨connectedComponent (rep j), hopen _⟩
  have hUc : ∀ j, IsClosed (U j : Set X) := fun j => isClosed_connectedComponent
  have hmem : ∀ j (x : X), x ∈ (U j : Set X) ↔ e j = (x : _root_.ConnectedComponents X) := by
    intro j x
    rw [← hrep]
    exact ⟨fun h => ConnectedComponents.coe_eq_coe.mpr (connectedComponent_eq h),
      fun h => by
        have := ConnectedComponents.coe_eq_coe.mp h
        show x ∈ connectedComponent (rep j)
        rw [this]; exact mem_connectedComponent⟩
  refine ⟨m, U, fun j => ?_, fun x => ?_, fun j j' hj => ?_⟩
  · have h2 := clopen_smoothProper_projective d p hp hX (U j) (hUc j)
    have hc : ConnectedSpace (U j) := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
    exact ⟨h2.1, h2.2, LCompInt_of k d ((U j).ι ≫ p) h2.1 hc⟩
  · refine ⟨e.symm (x : _root_.ConnectedComponents X), ?_⟩
    show x ∈ (U _ : Set X)
    rw [hmem]
    exact e.apply_symm_apply _
  · rw [disjoint_iff_inf_le]
    intro x hx
    exact (hj (e.injective (((hmem j x).mp hx.1).trans ((hmem j' x).mp hx.2).symm))).elim

end UpperTheory.Gal.KunnethLefschetz
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PFinFib
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

theorem UpperTheory.Gal.KunnethLefschetz.finFib_holds :
    UpperTheory.Gal.KunnethLefschetz.FinFib := by
  intro k _ _ X Y p r π hπ hfin t U hU
  classical
  obtain ⟨t0, ht0⟩ := t
  change ↑U = (Set.range t0)ᶜ at hU
  have hA : IsLocallyArtinian (pullback π t0) :=
    IsLocallyArtinian.of_locallyQuasiFinite (pullback.snd π t0)
  have hD : DiscreteTopology ↥(pullback π t0) := inferInstance
  have hF : Finite ↥(pullback π t0) := by
    have h := (pullback.snd π t0).finite_preimage_singleton (IsLocalRing.closedPoint k)
    rw [← Set.finite_univ_iff]
    refine h.subset fun z _ => ?_
    exact Subsingleton.elim _ _
  haveI : Fintype ↥(pullback π t0) := Fintype.ofFinite _
  let c : ↥(S k) := IsLocalRing.closedPoint k
  let e : ↥(pullback π t0) → (S k ⟶ pullback π t0) := fun z =>
    pointOfClosedPoint (pullback.snd π t0) z (isClosed_discrete _)
  have he : ∀ z, e z ≫ pullback.snd π t0 = 𝟙 _ := fun z => pointOfClosedPoint_comp _ _ _
  have he' : ∀ z, e z c = z := fun z => pointOfClosedPoint_apply _ _ _ _
  let g : ↥(pullback π t0) → Pt p := fun z =>
    ⟨e z ≫ pullback.fst π t0, by
      rw [Category.assoc, ← hπ, ← Category.assoc (pullback.fst π t0), pullback.condition,
        Category.assoc, ht0, Category.comp_id, he]⟩
  refine ⟨Finset.univ.image g, ?_⟩
  unfold OffPts
  rw [Scheme.Hom.coe_preimage, hU, Set.preimage_compl]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_range, Finset.mem_image, Finset.mem_univ, true_and,
    Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback x a ha.symm
    refine ⟨g z, ⟨z, rfl⟩, c, ?_⟩
    change (e z ≫ pullback.fst π t0) c = x
    rw [Scheme.Hom.comp_apply, he', hz1]
  · rintro ⟨y, ⟨z, rfl⟩, b, rfl⟩
    refine ⟨(e z ≫ pullback.snd π t0) b, ?_⟩
    change (e z ≫ pullback.snd π t0 ≫ t0) b = (e z ≫ pullback.fst π t0 ≫ π) b
    rw [pullback.condition]
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PFinSupp
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

namespace UpperTheory.Gal.KunnethLefschetz

private theorem pbc (l : ℕ) [Fact l.Prime] {A B C : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ C) (n : ℤ) (z : V l C n) :
    pb l (f ≫ g) n z = pb l f n (pb l g n z) := by
  rw [LateralTheory.EtaleTrace.pb_comp]; rfl

private theorem pbi (l : ℕ) [Fact l.Prime] (X : Scheme.{0}) (n : ℤ) (z : V l X n) : pb l (𝟙 X) n z = z := by
  show pullHQ l (sch.map (𝟙 X)) n 0 z = z
  rw [CategoryTheory.Functor.map_id]
  unfold pullHQ
  rw [pullHl_id, LinearMap.baseChange_id]; rfl

private theorem step {l : ℕ} [Fact l.Prime] {k : Type} [Field k] (hP : Pairs) (hL : Low l k) (G : GysQ k l) (d : ℕ)
    {X : Scheme.{0}} (p : X ⟶ S k) (hs : IsSeparated p) (hsm : SmoothOfRelativeDimension d p) (y : Pt p)
    (U' U : X.Opens) (hU : (U : Set X) = (U' : Set X) \ Set.range y.1) (hy : Set.range y.1 ⊆ (U' : Set X))
    (z : V l X (2 * d)) (hz : pb l U.ι _ z = 0) :
    ∃ r : ℚ_[l], pb l U'.ι _ (z - r • G.pt d y) = 0 := by
  have hsep : IsSeparated (U'.ι ≫ p) := inferInstance
  have hsm' : SmoothOfRelativeDimension d (U'.ι ≫ p) := by
    have h := smoothOfRelativeDimension_comp (n := 0) (m := d) U'.ι p
    rwa [Nat.zero_add] at h
  have hr : Set.range y.1 ⊆ Set.range U'.ι := by simpa using hy
  let y' : S k ⟶ U'.toScheme := IsOpenImmersion.lift U'.ι y.1 hr
  have hy' : y' ≫ U'.ι = y.1 := IsOpenImmersion.lift_fac _ _ _
  let t : Pt (U'.ι ≫ p) := ⟨y', by rw [← Category.assoc, hy', y.2]⟩
  have hpt : IsPair d 0 (U'.ι ≫ p) y' := ((hP k d _ hsep hsm').2 t).1
  have hpy : IsPair d 0 p y.1 := ((hP k d p hs hsm).2 y).1
  have hoff : Off y' (U'.ι ⁻¹ᵁ U) := by
    unfold Off
    ext x
    have hx : U'.ι x ∈ (U' : Set X) := by
      have : U'.ι x ∈ Set.range U'.ι := ⟨x, rfl⟩
      simpa using this
    show U'.ι x ∈ (U : Set X) ↔ x ∉ Set.range y'
    rw [hU]
    constructor
    · rintro ⟨-, h2⟩ ⟨w, rfl⟩
      exact h2 ⟨w, by rw [← hy']; rfl⟩
    · intro h
      refine ⟨hx, ?_⟩
      rintro ⟨w, hw⟩
      apply h
      refine ⟨w, ?_⟩
      apply U'.ι.isOpenEmbedding.injective
      rw [← hw, ← hy']; rfl
  have hdead : pb l (U'.ι ⁻¹ᵁ U).ι _ (pb l U'.ι _ z) = 0 := by
    rw [← pbc, ← morphismRestrict_ι, pbc, hz, map_zero]
  have hprop : IsProper (y' ≫ U'.ι ≫ p) := by
    have : y' ≫ U'.ι ≫ p = 𝟙 _ := t.2
    rw [this]; infer_instance
  obtain ⟨a, ha⟩ := G.onto hpt (zero_add _) _ hoff hprop _ hdead
  obtain ⟨r, hra, -⟩ := hL.line a
  refine ⟨r, ?_⟩
  have hpb : IsPullback y' (𝟙 _) U'.ι y.1 := IsPullback.of_vert_isIso_mono ⟨by simp [hy']⟩
  have hnat := G.nat hpt hpy U'.ι (𝟙 _) rfl hpb (zero_add _) (oneV l (S k))
  rw [pbi] at hnat
  have hpt' : G.pt d y = G.g hpy (zero_add _) (oneV l (S k)) := by
    simp only [GysQ.cls, dif_pos hpy]
  rw [map_sub, map_smul, hpt', hnat, ← map_smul, ← hra, ha, sub_self]

end UpperTheory.Gal.KunnethLefschetz

theorem UpperTheory.Gal.KunnethLefschetz.finSupp_holds :
    UpperTheory.Gal.KunnethLefschetz.FinSupp := by
  unfold FinSupp
  intro _ hP l _ k _ _ _ _ hL G d X p hsep hsm s
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro U hU z hz
    have hT : U = ⊤ := by
      apply SetLike.coe_injective
      simpa [OffPts] using hU
    subst hT
    have h0 : z = 0 := by
      have e : X.topIso.inv ≫ (⊤ : X.Opens).ι = 𝟙 X := by simp
      have h1 : pb l X.topIso.inv _ (pb l (⊤ : X.Opens).ι _ z) = z := by
        rw [← pbc, e, pbi]
      rw [← h1, hz, map_zero]
    rw [h0]; exact zero_mem _
  | insert y s hy ih =>
    intro U hU z hz
    have hcl : ∀ t : Pt p, IsClosed (Set.range t.1) := fun t => by
      haveI := ((hP k d p hsep hsm).2 t).1.cl
      exact t.1.isClosedEmbedding.isClosed_range
    have hopen : IsOpen ((⋃ t ∈ s, Set.range t.1)ᶜ) :=
      (s.finite_toSet.isClosed_biUnion fun t _ => hcl t).isOpen_compl
    let U' : X.Opens := ⟨_, hopen⟩
    have hU' : OffPts s U' := rfl
    have hU2 : (U : Set X) = (U' : Set X) \ Set.range y.1 := by
      rw [hU, Finset.set_biUnion_insert, Set.compl_union, Set.diff_eq, Set.inter_comm]; rfl
    by_cases hin : Set.range y.1 ⊆ (U' : Set X)
    · obtain ⟨r, hr⟩ := step hP hL G d p hsep hsm y U' U hU2 hin z hz
      have h1 := ih U' hU' _ hr
      have hz' : z = (z - r • G.pt d y) + r • G.pt d y := (sub_add_cancel _ _).symm
      rw [hz']
      exact add_mem h1 (Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, rfl⟩))
    · have hsub : Subsingleton (S k) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
      have hUU : U = U' := by
        apply SetLike.coe_injective
        rw [hU2]
        ext x
        constructor
        · exact fun h => h.1
        · intro hx
          refine ⟨hx, ?_⟩
          rintro ⟨w, rfl⟩
          apply hin
          rintro _ ⟨w', rfl⟩
          rwa [Subsingleton.elim w' w]
      subst hUU
      exact ih _ hU' z hz
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PLimOnto
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

theorem UpperTheory.Gal.KunnethLefschetz.limOnto_holds :
    UpperTheory.Gal.KunnethLefschetz.LimOnto := by
  intro A B _ ra rb f hf z hz hsurj
  let F : ℕ → Type 1 := fun j => {a : A j // f j a = z j}
  let g : ∀ n, F (n + 1) → F n := fun n a =>
    ⟨ra n a.1, by rw [← hf, a.2, hz]⟩
  let G : ℕᵒᵖ ⥤ Type 1 := Functor.ofOpSequence (X := F) (fun n => TypeCat.ofHom (g n))
  haveI : ∀ j : ℕᵒᵖ, Finite (G.obj j) := fun j => (inferInstance : Finite (F j.unop))
  haveI : ∀ j : ℕᵒᵖ, Nonempty (G.obj j) := fun j => by
    obtain ⟨a, ha⟩ := hsurj j.unop
    exact ⟨(⟨a, ha⟩ : F j.unop)⟩
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_inverse_system G
  refine ⟨fun j => (s (Opposite.op j) : F j).1, fun j => ?_, fun j => (s (Opposite.op j) : F j).2⟩
  have h1 := hs (homOfLE (Nat.le_succ j)).op
  rw [Functor.ofOpSequence_map_homOfLE_succ] at h1
  have h2 := congrArg Subtype.val h1
  exact h2
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.POffEx
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

theorem UpperTheory.Gal.KunnethLefschetz.offEx_holds :
    UpperTheory.Gal.KunnethLefschetz.OffEx := by
  refine ⟨fun {Z X} ι hι => ⟨⟨(Set.range ι)ᶜ, ι.isClosedEmbedding.isClosed_range.isOpen_compl⟩, rfl⟩, ?_⟩
  intro Z' X' Z X ι' ι f u h U hU
  change f ⁻¹' (U : Set X) = _
  rw [hU, Set.preimage_compl, ← Scheme.Pullback.range_fst]
  congr 1
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨h.isoPullback.inv y, by rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst]⟩
  · rintro ⟨y, rfl⟩
    exact ⟨h.isoPullback.hom y, by rw [← Scheme.Hom.comp_apply, h.isoPullback_hom_fst]⟩
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PPairs
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

theorem UpperTheory.Gal.KunnethLefschetz.pairs_holds :
    UpperTheory.Gal.KunnethLefschetz.Pairs := by
  unfold Pairs
  intro k _ d X p hsep hsm
  have hfst : SmoothOfRelativeDimension d (pullback.fst p p) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := d)).of_isPullback
      (IsPullback.of_hasPullback p p).flip hsm
  have hcomp : SmoothOfRelativeDimension (d + d) (pullback.fst p p ≫ p) :=
    smoothOfRelativeDimension_comp (n := d) (m := d) (pullback.fst p p) p
  have hid : SmoothOfRelativeDimension 0 (𝟙 (S k)) := inferInstance
  refine ⟨⟨inferInstance, hcomp, ?_⟩, fun y => ⟨⟨?_, ?_, ?_⟩, ?_⟩⟩
  · rw [pullback.diagonal_fst_assoc]
    exact hsm
  · have h1 : IsClosedImmersion (y.1 ≫ p) := by rw [y.2]; infer_instance
    exact IsClosedImmersion.of_comp y.1 p
  · rw [Nat.zero_add]; exact hsm
  · rw [y.2]; exact hid
  · have key : ∀ s : PullbackCone (slice y) (pullback.diagonal p),
        s.fst = s.snd ∧ s.fst ≫ p ≫ y.1 = s.snd := by
      intro s
      have c := s.condition
      have c1 := congrArg (· ≫ pullback.fst p p) c
      have c2 := congrArg (· ≫ pullback.snd p p) c
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.diagonal_fst,
        pullback.diagonal_snd, Category.comp_id] at c1 c2
      exact ⟨c1, c2⟩
    refine IsPullback.of_isLimit' ⟨?_⟩ (PullbackCone.IsLimit.mk _ (fun s => s.fst ≫ p) ?_ ?_ ?_)
    · have e1 : slice y ≫ pullback.fst p p = 𝟙 X := pullback.lift_fst _ _ _
      have e2 : slice y ≫ pullback.snd p p = p ≫ y.1 := pullback.lift_snd _ _ _
      have hy : y.1 ≫ p ≫ y.1 = y.1 := by rw [← Category.assoc, y.2, Category.id_comp]
      apply pullback.hom_ext
      · rw [Category.assoc, e1, Category.assoc, pullback.diagonal_fst, Category.comp_id]
      · rw [Category.assoc, e2, hy, Category.assoc, pullback.diagonal_snd, Category.comp_id]
    · intro s
      rw [Category.assoc, (key s).2, (key s).1]
    · intro s
      rw [Category.assoc, (key s).2]
    · intro s m h1 _
      rw [← h1, Category.assoc, y.2, Category.comp_id]
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PQEasy
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace
open scoped TensorProduct DirectSum

namespace UpperTheory.Gal.KunnethLefschetz

theorem qEasy_holds : QEasy := by
  unfold QEasy
  intro l _ k _ G
  haveI : Module.Flat ℤ_[l] ℚ_[l] := IsLocalization.flat ℚ_[l] (nonZeroDivisors ℤ_[l])
  refine ⟨?_, ?_, ?_⟩
  · intro d e Z X p ι h n m hn U hU a
    have h0 : (pullHl l (sch.map U.ι) m 0).comp (G.hl h hn) = 0 :=
      LinearMap.ext fun x => Subtype.ext (funext fun j =>
        (G.exact j h hn U hU _).mpr ⟨x.1 j, rfl⟩)
    have h1 : (pb l U.ι m).comp (G.q h hn) = 0 := by
      unfold Gys0.q pb pullHQ
      rw [← LinearMap.baseChange_comp, h0, LinearMap.baseChange_zero]
    exact LinearMap.congr_fun h1 a
  · intro d e Z X p ι h n m hn U hU hs
    have hinj : Function.Injective (G.hl h hn) := fun x y hxy =>
      Subtype.ext (funext fun j => G.inj j h hn U hU (hs j) (congrArg (fun z => z.1 j) hxy))
    unfold Gys0.q
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ hinj
  · intro d e' e Z' X' Z X p' ι' p ι h' h f u hf hp n m hn a
    have h0 : (pullHl l (sch.map f) m 0).comp (G.hl h hn) =
        (G.hl h' hn).comp (pullHl l (sch.map u) n 0) :=
      LinearMap.ext fun x => Subtype.ext (funext fun j => G.nat j h' h f u hf hp hn (x.1 j))
    have h1 : (pb l f m).comp (G.q h hn) = (G.q h' hn).comp (pb l u n) := by
      unfold Gys0.q pb pullHQ
      rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, h0]
    exact LinearMap.congr_fun h1 a

end UpperTheory.Gal.KunnethLefschetz
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PQOnto
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

private theorem tors_of {l : ℕ} [Fact l.Prime] {M : Type*} [AddCommGroup M] [Module ℤ_[l] M] (b : ℤ_[l]) (hb : b ≠ 0)
    (w : M) (h : ((b : ℚ_[l]))⁻¹ ⊗ₜ[ℤ_[l]] w = 0) : ∃ c : ℤ_[l], c ≠ 0 ∧ c • w = 0 := by
  have hb' : (b : ℚ_[l]) ≠ 0 := by rwa [Ne, PadicInt.coe_eq_zero]
  have h1 : (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] w = 0 := by
    have h2 := congrArg (fun t => (b : ℚ_[l]) • t) h
    simpa [TensorProduct.smul_tmul', hb'] using h2
  have hloc : IsLocalizedModule (nonZeroDivisors ℤ_[l]) (TensorProduct.mk ℤ_[l] ℚ_[l] M 1) := inferInstance
  obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ_[l]) (TensorProduct.mk ℤ_[l] ℚ_[l] M 1)).1 h1
  exact ⟨c, nonZeroDivisors.ne_zero c.2, hc⟩

theorem UpperTheory.Gal.KunnethLefschetz.qOnto_holds :
    UpperTheory.Gal.KunnethLefschetz.QOnto := by
  unfold QOnto
  intro hI hLim l _ k _ _ hl G d e Z X p ι h n m hn U hU hprop z hz
  obtain ⟨b, x, hb, rfl⟩ := H0LimitCoherence.tensor_form l z
  have hz' : ((b : ℚ_[l]))⁻¹ ⊗ₜ[ℤ_[l]] (pullHl l (sch.map U.ι) m 0 x) = 0 := by
    simpa [pb, pullHQ, LinearMap.baseChange_tmul] using hz
  obtain ⟨c, hc, hcx⟩ := tors_of b hb _ hz'
  have hunit : ∀ j : ℕ, IsUnit (((l ^ j : ℕ)) : k) := fun j => by
    push_cast
    exact (IsUnit.mk0 _ hl).pow j
  have hne : ∀ j : ℕ, NeZero (l ^ j) := fun j => ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hfin : ∀ j : ℕ, Finite (Ht (l ^ j) (sch.obj Z) n 0) := fun j => by
    haveI := hne j
    haveI := hprop
    exact hI.e4 (l ^ j) k (hunit j) (ι ≫ p) n 0
  set x' : Hl l (sch.obj X) m 0 := c • x with hx'
  have hpull : pullHl l (sch.map U.ι) m 0 x' = 0 := by
    rw [hx', map_smul]; exact hcx
  have hlev : ∀ j, ∃ a, G.g j h hn a = x'.1 j := fun j => by
    have h0 : pull _ (sch.map U.ι) (tw (l ^ j) 0) m (x'.1 j) = 0 := by
      have := congrArg (fun t : Hl l (sch.obj U) m 0 => t.1 j) hpull
      exact this
    exact (G.exact j h hn U hU _).1 h0
  obtain ⟨a, ha, hfa⟩ := hLim (fun j => Ht (l ^ j) (sch.obj Z) n 0) (fun j => Ht (l ^ j) (sch.obj X) m 0)
    (fun j => red (l ^ (j + 1)) (l ^ j) _ n 0) (fun j => red (l ^ (j + 1)) (l ^ j) _ m 0)
    (fun j => G.g j h hn) (fun j a => G.red j h hn a) (fun j => x'.1 j) (fun j => x'.2 j) hlev
  let a' : Hl l (sch.obj Z) n 0 := ⟨a, ha⟩
  have hga : G.hl h hn a' = x' := Subtype.ext (funext hfa)
  refine ⟨(((b * c : ℤ_[l]) : ℚ_[l]))⁻¹ ⊗ₜ a', ?_⟩
  have hc' : (c : ℚ_[l]) ≠ 0 := by rwa [Ne, PadicInt.coe_eq_zero]
  have hb' : (b : ℚ_[l]) ≠ 0 := by rwa [Ne, PadicInt.coe_eq_zero]
  change (G.hl h hn).baseChange ℚ_[l] _ = _
  rw [LinearMap.baseChange_tmul, hga, hx', ← TensorProduct.smul_tmul, Algebra.smul_def]
  congr 1
  have hal : algebraMap ℤ_[l] ℚ_[l] c = (c : ℚ_[l]) := rfl
  rw [hal, PadicInt.coe_mul]
  field_simp
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PQProj
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace
open scoped TensorProduct

namespace UpperTheory.Gal.KunnethLefschetz

theorem qProj_holds : QProj := by
  unfold QProj
  intro hI l _ k _ G d e Z X p ι h n m r s t h1 h2 h3 h4 a b
  have key : ∀ (x : Hl l (sch.obj X) n 0) (y : Hl l (sch.obj Z) m 0),
      G.q h h2 (cupV l Z h1 (pb l ι n ((1 : ℚ_[l]) ⊗ₜ x)) ((1 : ℚ_[l]) ⊗ₜ y)) =
        cupV l X h4 ((1 : ℚ_[l]) ⊗ₜ x) (G.q h h3 ((1 : ℚ_[l]) ⊗ₜ y)) := by
    intro x y
    rw [LRingPf.pb_tmul, LRingPf.cupV_eq l hI.a11 Z, LRingPf.cupV_eq l hI.a11 X, LRingPf.cupQ_tmul]
    simp only [Gys0.q, LinearMap.baseChange_tmul]
    rw [LRingPf.cupQ_tmul]
    congr 1
    refine Subtype.ext (funext fun j => ?_)
    exact G.proj j h h1 h2 h3 h4 (x.1 j) (y.1 j)
  have hfg : ((cupV l Z h1 ∘ₗ pb l ι n).compr₂ (G.q h h2)) = (cupV l X h4).compl₂ (G.q h h3) :=
    LRingPf.ext2 fun x y => key x y
  exact DFunLike.congr_fun (DFunLike.congr_fun hfg a) b

end UpperTheory.Gal.KunnethLefschetz
end
end

