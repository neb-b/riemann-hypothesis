module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.ProjectiveBaseChange.AdicTopOf
public import Development.EtaleCohomology.EtaleTrace.LRingPf
public import Development.EtaleCohomology.EtaleTrace.Bundle0001
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.Bundle0003
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ChowProduct

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.ProjectiveBaseChange.PCupEx
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace CrystallineSemistableComparison ReciprocityTheory.ChartRestriction.G.Geo.Tor UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

theorem UpperTheory.Gal.KunnethLefschetz.cupEx_holds :
    UpperTheory.Gal.KunnethLefschetz.CupEx := by
  intro hB l _ K M i j x y
  exact ⟨LateralTheory.EtaleTrace.LRingPf.cupL l M.spc (Nat.cast_add i j).symm hB x y,
    fun k => LateralTheory.EtaleTrace.LRingPf.cupL_apply l M.spc (Nat.cast_add i j).symm hB x y k⟩
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.ProjectiveBaseChange.PDualSum
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace

namespace UpperTheory.Gal.KunnethLefschetz

private theorem dualSum_abs {F : Type*} [Field F] {r : ℕ} {A B C : Type*}
    [AddCommGroup A] [Module F A] [AddCommGroup B] [Module F B] [AddCommGroup C] [Module F C]
    {A' B' C' : Fin r → Type*} [∀ s, AddCommGroup (A' s)] [∀ s, Module F (A' s)]
    [∀ s, AddCommGroup (B' s)] [∀ s, Module F (B' s)] [∀ s, AddCommGroup (C' s)] [∀ s, Module F (C' s)]
    (pa : ∀ s, A →ₗ[F] A' s) (pe : ∀ s, B →ₗ[F] B' s) (pc : ∀ s, C →ₗ[F] C' s)
    (ha : Function.Bijective fun (x : A) s => pa s x) (hb : Function.Bijective fun (x : B) s => pe s x)
    (hc : Function.Bijective fun (x : C) s => pc s x)
    (cup : A →ₗ[F] B →ₗ[F] C) (cup' : ∀ s, A' s →ₗ[F] B' s →ₗ[F] C' s)
    (nat : ∀ s x y, pc s (cup x y) = cup' s (pa s x) (pe s y))
    (tr : ∀ s, C' s ≃ₗ[F] F)
    (hd : ∀ s, Function.Bijective ((cup' s).compr₂ (tr s).toLinearMap).flip) :
    ∃ g : Fin r → C, (∀ s, pc s (g s) ≠ 0) ∧ (∀ s (v : C' s), ∃ z : F, v = z • pc s (g s)) ∧
      (∀ s t, s ≠ t → pc t (g s) = 0) ∧ Submodule.span F (Set.range g) = ⊤ ∧
      Submodule.span F {f : Module.Dual F A | ∃ (s : Fin r) (y : B), ∀ x, cup x y = f x • g s} = ⊤ := by
  classical
  let eA := LinearEquiv.ofBijective (LinearMap.pi pa) ha
  let eB := LinearEquiv.ofBijective (LinearMap.pi pe) hb
  let eC := LinearEquiv.ofBijective (LinearMap.pi pc) hc
  have kB : ∀ (x : ∀ s, B' s) t, pe t (eB.symm x) = x t := fun x t =>
    congrFun (eB.apply_symm_apply x) t
  have kC : ∀ (x : ∀ s, C' s) t, pc t (eC.symm x) = x t := fun x t =>
    congrFun (eC.apply_symm_apply x) t
  let g : Fin r → C := fun s => eC.symm (Pi.single (M := C') s ((tr s).symm 1))
  have hg : ∀ s t, pc t (g s) = Pi.single (M := C') s ((tr s).symm 1) t := fun s t => kC _ t
  refine ⟨g, ?_, ?_, ?_, ?_, ?_⟩
  · intro s h0
    rw [hg, Pi.single_eq_same] at h0
    have := congrArg (tr s) h0
    simp at this
  · intro s v
    refine ⟨tr s v, ?_⟩
    rw [hg, Pi.single_eq_same]
    apply (tr s).injective
    simp
  · intro s t hst
    rw [hg, Pi.single_eq_of_ne (Ne.symm hst)]
  · rw [eq_top_iff]
    intro c _
    have hc' : c = ∑ s, tr s (pc s c) • g s := by
      apply hc.1
      funext t
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, hg]
      rw [Finset.sum_eq_single t]
      · rw [Pi.single_eq_same]
        apply (tr t).injective
        simp
      · intro b _ hb
        rw [Pi.single_eq_of_ne (Ne.symm hb), smul_zero]
      · intro ht
        exact absurd (Finset.mem_univ t) ht
    rw [hc']
    exact Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)
  · rw [eq_top_iff]
    intro f _
    have hy : ∀ s, ∃ y' : B' s, ∀ a', tr s (cup' s a' y') = f (eA.symm (Pi.single s a')) := by
      intro s
      obtain ⟨y', hy'⟩ := (hd s).2 (f ∘ₗ eA.symm.toLinearMap ∘ₗ LinearMap.single F A' s)
      refine ⟨y', fun a' => ?_⟩
      have := LinearMap.congr_fun hy' a'
      simpa using this
    choose y' hy' using hy
    let φ : Fin r → Module.Dual F A := fun s =>
      f ∘ₗ eA.symm.toLinearMap ∘ₗ LinearMap.single F A' s ∘ₗ pa s
    have memS : ∀ s, φ s ∈ {f : Module.Dual F A | ∃ (s : Fin r) (y : B), ∀ x, cup x y = f x • g s} := by
      intro s
      refine ⟨s, eB.symm (Pi.single s (y' s)), fun x => ?_⟩
      apply hc.1
      funext t
      simp only [map_smul, nat, kB, hg]
      by_cases hts : t = s
      · subst hts
        simp only [Pi.single_eq_same]
        apply (tr t).injective
        rw [hy']
        simp [φ]
      · rw [Pi.single_eq_of_ne hts, Pi.single_eq_of_ne hts]
        simp
    have hf : f = ∑ s, φ s := by
      ext x
      have e1 : (∑ s, Pi.single s (pa s x) : ∀ s, A' s) = eA x := Finset.univ_sum_single _
      rw [LinearMap.sum_apply]
      calc f x = f (eA.symm (eA x)) := by rw [eA.symm_apply_apply]
        _ = f (eA.symm (∑ s, Pi.single s (pa s x))) := by rw [e1]
        _ = ∑ s, φ s x := by simp only [map_sum]; rfl
    rw [hf]
    exact Submodule.sum_mem _ fun s _ => Submodule.subset_span (memS s)

theorem dualSum_holds : DualSum := by
  unfold DualSum
  intro l _ hR X r Y j d hb hD a b w h hw
  subst hw
  have hD' : ∀ s, ∃ tr : V l (Y s) (2 * (d : ℤ)) ≃ₗ[ℚ_[l]] ℚ_[l], ∀ (n m : ℤ) (h : n + m = 2 * d),
      Function.Bijective ((cupV l (Y s) h).compr₂ tr.toLinearMap).flip := fun s => (hD s).2.2
  choose tr htr using hD'
  obtain ⟨g, h1, h2, h3, h4, h5⟩ := dualSum_abs (fun s => pb l (j s) a) (fun s => pb l (j s) b)
    (fun s => pb l (j s) (2 * (d : ℤ))) (hb a) (hb b) (hb _) (cupV l X h) (fun s => cupV l (Y s) h)
    (fun s x y => hR.nat (j s) a b _ h x y) tr (fun s => htr s a b h)
  exact ⟨g, ⟨h1, h2, h3⟩, h4, h5⟩

end UpperTheory.Gal.KunnethLefschetz
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.ProjectiveBaseChange.PGeomPb
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace CrystallineSemistableComparison ReciprocityTheory.ChartRestriction.G.Geo.Tor UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

private theorem isPullback_lift_fst {X Y S T : Scheme.{0}} (p : X ⟶ S) (q : Y ⟶ S) (t : T ⟶ S) (u : X ⟶ Y)
    (hu : u ≫ q = p) (w : (pullback.fst p t ≫ u) ≫ q = pullback.snd p t ≫ t) :
    IsPullback (pullback.lift (pullback.fst p t ≫ u) (pullback.snd p t) w) (pullback.fst p t)
      (pullback.fst q t) u := by
  refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback q t).flip
  rw [pullback.lift_snd, hu]
  exact (IsPullback.of_hasPullback p t).flip

theorem UpperTheory.Gal.KunnethLefschetz.geomPb_holds :
    UpperTheory.Gal.KunnethLefschetz.GeomPb := by
  unfold UpperTheory.Gal.KunnethLefschetz.GeomPb
  intro l _ K M N u hu
  exact IsPullback.paste_vert
    (isPullback_lift_fst M.q N.q _ (Model.genMap u hu) (Model.genMap_q u hu) _)
    (isPullback_lift_fst M.p N.p _ u hu _)
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.ProjectiveBaseChange.PIntFun
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace CrystallineSemistableComparison ReciprocityTheory.ChartRestriction.G.Geo.Tor UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

theorem UpperTheory.Gal.KunnethLefschetz.intFun_holds :
    UpperTheory.Gal.KunnethLefschetz.IntFun := by
  intro hB l _ K M hR i j r g h hspan
  refine eq_top_iff.mpr (le_trans (le_of_eq hspan.symm) ?_)
  apply Submodule.span_le.mpr
  rintro f ⟨s, y, hy⟩
  obtain ⟨b, y0, hb, rfl⟩ := LateralTheory.EtaleTrace.H0LimitCoherence.tensor_form l y
  have hb' : ((b : ℚ_[l])) ≠ 0 := fun e => hb (PadicInt.coe_eq_zero.mp e)
  have hone : (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] y0 = (b : ℚ_[l]) • (((b : ℚ_[l]))⁻¹ ⊗ₜ[ℤ_[l]] y0) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_inv_cancel₀ hb']
  have hmem : ((b : ℚ_[l]) • f) ∈
      {f | ∃ s y, ∀ (x : M.T i), ∃ z, M.CupT x y z ∧ M.toV (i + j) z = f (M.toV i x) • g s} := by
    refine ⟨s, y0, fun x => ⟨LateralTheory.EtaleTrace.LRingPf.cupL l M.spc h hB x y0, ?_, ?_⟩⟩
    · intro k
      exact LateralTheory.EtaleTrace.LRingPf.cupL_apply l M.spc h hB x y0 k
    · have hc := hR.isCup (GlobalTheory.Et.geom (PadicAlgCl l) M.q) (i : ℤ) (j : ℤ) ((i + j : ℕ) : ℤ) h x y0
        (LateralTheory.EtaleTrace.LRingPf.cupL l M.spc h hB x y0)
        (fun k => LateralTheory.EtaleTrace.LRingPf.cupL_apply l M.spc h hB x y0 k)
      have hx := hy (1 ⊗ₜ[ℤ_[l]] x)
      change (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] (LateralTheory.EtaleTrace.LRingPf.cupL l M.spc h hB x y0) = _
      rw [← hc, hone, LinearMap.map_smul, hx, smul_smul]
      rfl
  have hsub := Submodule.subset_span (R := ℚ_[l]) hmem
  have hsm := Submodule.smul_mem _ ((b : ℚ_[l]))⁻¹ hsub
  rw [smul_smul, inv_mul_cancel₀ hb', one_smul] at hsm
  exact hsm
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.ProjectiveBaseChange.PProjBC
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace CrystallineSemistableComparison ReciprocityTheory.ChartRestriction.G.Geo.Tor UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

theorem UpperTheory.Gal.KunnethLefschetz.projBC_holds :
    UpperTheory.Gal.KunnethLefschetz.ProjBC := by
  unfold UpperTheory.Gal.KunnethLefschetz.ProjBC
  refine ⟨?_, ?_⟩
  · intro R R' _ _ φ X p hp
    obtain ⟨N, i, hi, rfl⟩ := hp
    letI : Algebra R R' := φ.toAlgebra
    let s : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R) :=
      Spec.map (CommRingCat.ofHom (algebraMap R R'))
    let b := GroundTheory.Arith.SchemeCoh.ProjSpace.toSpecBase R N
    have H := GroundTheory.Arith.SchemeCoh.ProjSpace.isPullback_baseChange R R' N
    let ι : pullback (i ≫ b) s ⟶ GroundTheory.Arith.SchemeCoh.projectiveSpace R' N :=
      H.lift (pullback.fst (i ≫ b) s ≫ i) (pullback.snd (i ≫ b) s) (by rw [Category.assoc]; exact pullback.condition)
    have hι₁ : ι ≫ _ = pullback.fst (i ≫ b) s ≫ i := H.lift_fst _ _ _
    have hι₂ : ι ≫ _ = pullback.snd (i ≫ b) s := H.lift_snd _ _ _
    have hsq : IsPullback ι (pullback.fst (i ≫ b) s) (GroundTheory.Arith.SchemeCoh.ProjSpace.baseChangeMap R R' N) i := by
      refine IsPullback.of_right (h₂₂ := b) (v₁₃ := s) ?_ hι₁ H.flip
      rw [hι₂]
      exact (IsPullback.of_hasPullback (i ≫ b) s).flip
    exact ⟨N, ι, MorphismProperty.of_isPullback (P := @IsClosedImmersion) hsq.flip hi, hι₂⟩
  · intro R _ X p hp
    obtain ⟨N, i, hi, rfl⟩ := hp
    have : IsProper (GroundTheory.Arith.SchemeCoh.ProjSpace.toSpecBase R N) := inferInstance
    change IsProper (i ≫ GroundTheory.Arith.SchemeCoh.ProjSpace.toSpecBase R N)
    infer_instance
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.ProjectiveBaseChange.PSumBC
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace CrystallineSemistableComparison ReciprocityTheory.ChartRestriction.G.Geo.Tor UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

private theorem range_eq_preimage {P X Y Z : Scheme.{0}} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback a b f g) : Set.range a = f ⁻¹' Set.range g := by
  have e := h.isoPullback_hom_fst
  rw [← e, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr (fun y => ⟨h.isoPullback.inv y, by simp⟩), Set.image_univ,
    Scheme.Pullback.range_fst]

theorem UpperTheory.Gal.KunnethLefschetz.sumBC_holds :
    UpperTheory.Gal.KunnethLefschetz.SumBC := by
  unfold UpperTheory.Gal.KunnethLefschetz.SumBC
  intro X' X r Y' Y j' j f u h hj
  obtain ⟨ho, hc, hd⟩ := hj
  refine ⟨fun s => ?_, fun x => ?_, fun s s' hs => ?_⟩
  · have := ho s
    exact MorphismProperty.of_isPullback (P := @IsOpenImmersion) (h s).flip (ho s)
  · obtain ⟨s, hs⟩ := hc (f x)
    refine ⟨s, ?_⟩
    rw [range_eq_preimage (h s)]
    exact hs
  · rw [range_eq_preimage (h s), range_eq_preimage (h s')]
    exact (hd s s' hs).preimage f
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.ProjectiveBaseChange.PSumCl
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace CrystallineSemistableComparison ReciprocityTheory.ChartRestriction.G.Geo.Tor UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

theorem UpperTheory.Gal.KunnethLefschetz.sumCl_holds :
    UpperTheory.Gal.KunnethLefschetz.SumCl := by
  intro X r Y j hj s
  obtain ⟨hop, hcov, hdis⟩ := hj
  haveI := hop s
  apply AlgebraicGeometry.IsClosedImmersion.of_isPreimmersion
  have hc : (Set.range (j s).base)ᶜ = ⋃ t ∈ {t : Fin r | t ≠ s}, Set.range (j t).base := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    constructor
    · intro hx
      obtain ⟨t, ht⟩ := hcov x
      refine ⟨t, ?_, ht⟩
      rintro rfl
      exact hx ht
    · rintro ⟨t, hts, ht⟩ hx
      exact Set.disjoint_left.mp (hdis t s hts) ht hx
  rw [← isOpen_compl_iff, hc]
  refine isOpen_biUnion fun t _ => ?_
  haveI := hop t
  exact (j t).isOpenEmbedding.isOpen_range
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.ProjectiveBaseChange.PSumHl
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace CrystallineSemistableComparison ReciprocityTheory.ChartRestriction.G.Geo.Tor UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

theorem UpperTheory.Gal.KunnethLefschetz.sumHl_holds :
    UpperTheory.Gal.KunnethLefschetz.SumHl := by
  unfold UpperTheory.Gal.KunnethLefschetz.SumHl
  intro hS l _ X r Y j hj n
  have hb : ∀ k : ℕ, Function.Bijective fun (x : Ht (l ^ k) (sch.obj X) n 0) (s : Fin r) =>
      pull (ZMod (l ^ k)) (sch.map (j s)) (tw (l ^ k) 0) n x :=
    fun k => hS (ZMod (l ^ k)) (tw (l ^ k) 0) j hj n
  constructor
  · intro x y h
    refine Subtype.ext (funext fun k => (hb k).1 (funext fun s => ?_))
    exact congrArg (fun z : Hl l (sch.obj (Y s)) n 0 => z.1 k) (congrFun h s)
  · intro y
    choose x hx using fun k : ℕ => (hb k).2 (fun s => (y s).1 k)
    refine ⟨⟨x, fun k => (hb k).1 (funext fun s => ?_)⟩,
      funext fun s => Subtype.ext (funext fun k => congrFun (hx k) s)⟩
    exact (pull_red _ _ (sch.map (j s)) n 0 (x (k + 1))).trans
      ((congrArg (red (l ^ (k + 1)) (l ^ k) (sch.obj (Y s)) n 0) (congrFun (hx (k + 1)) s)).trans
        (((y s).2 k).trans (congrFun (hx k) s).symm))
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.ProjectiveBaseChange.PiBCHolds
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace CrystallineSemistableComparison ReciprocityTheory.ChartRestriction.G.Geo.Tor UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

theorem UpperTheory.Gal.KunnethLefschetz.piBC_holds :
    UpperTheory.Gal.KunnethLefschetz.PiBC := by
  intro l _ r A B _ _ _ _ f hf
  classical
  let e := LinearEquiv.ofBijective (LinearMap.pi f) hf
  let g := (LinearEquiv.baseChange ℤ_[l] ℚ_[l] A (∀ s, B s) e).trans
    (TensorProduct.piRight ℤ_[l] ℚ_[l] ℚ_[l] B)
  have key : (fun x s => (LinearMap.baseChange ℚ_[l] (f s)) x) = g := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => funext s; simp
    | tmul a b =>
      funext s
      simp [g, e]
      rfl
    | add x y hx hy =>
      rw [map_add (f := _), ← hx, ← hy]
      funext s
      simp
  rw [key]
  exact g.bijective
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.ProjectiveBaseChange.PullbackComp
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace CrystallineSemistableComparison ReciprocityTheory.ChartRestriction.G.Geo.Tor UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

private theorem pb_id_projective_base_change (l : ℕ) [Fact l.Prime] (X : Scheme.{0}) (n : ℤ) (z : V l X n) :
    pb l (𝟙 X) n z = z := by
  show LinearMap.baseChange ℚ_[l] (pullHl l (sch.map (𝟙 X)) n 0) z = z
  rw [CategoryTheory.Functor.map_id, pullHl_id, LinearMap.baseChange_id, LinearMap.id_apply]

private theorem pb_comp_projective_base_change (l : ℕ) [Fact l.Prime] {A B C : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ C) (n : ℤ)
    (v : V l C n) : pb l (f ≫ g) n v = pb l f n (pb l g n v) := by
  rw [pb_comp]; rfl

private theorem pb_iso_inj (l : ℕ) [Fact l.Prime] {A B : Scheme.{0}} (e : A ≅ B) (n : ℤ) :
    Function.Injective (pb l e.hom n) := by
  intro x y h
  have h2 := congrArg (pb l e.inv n) h
  rw [← pb_comp_projective_base_change, ← pb_comp_projective_base_change, e.inv_hom_id, pb_id_projective_base_change, pb_id_projective_base_change] at h2
  exact h2

theorem UpperTheory.Gal.KunnethLefschetz.perm_holds :
    UpperTheory.Gal.KunnethLefschetz.Perm := by
  intro l _ X r Y j w hinj g hg φ π θ hc s
  have hval : ∀ t, pb l (j t) w (pb l φ w (g (π s))) =
      pb l (θ t).hom w (pb l (j (π t)) w (g (π s))) := by
    intro t
    rw [← pb_comp_projective_base_change, hc, pb_comp_projective_base_change]
  obtain ⟨z, hz⟩ := hg.line s (pb l (θ s).hom w (pb l (j (π s)) w (g (π s))))
  refine ⟨z, ?_, ?_⟩
  · rintro rfl
    rw [zero_smul] at hz
    exact hg.ne (π s) (pb_iso_inj l (θ s) w (by rw [hz, map_zero]))
  · apply hinj
    funext t
    show pb l (j t) w (pb l φ w (g (π s))) = pb l (j t) w (z • g s)
    rw [hval, map_smul]
    by_cases hts : t = s
    · subst hts
      exact hz
    · rw [hg.off (π s) (π t) (fun h => hts (π.injective h).symm), map_zero,
        hg.off s t (fun h => hts h.symm), smul_zero]
end
end

