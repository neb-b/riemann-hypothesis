module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.LocTower
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0008
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0010
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0009
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.SimultaneousEigenspaces.EtaleCohomologyCorrOpCommPullback
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV UpperTheory.Gal.Int.Geo TensorProduct

private theorem l_unit_of_charZero (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [CharZero Ω] :
    IsUnit (l : Γ(UpperTheory.Gal.G3.sp Ω, ⊤)) := by
  have h1 : (l : Ω) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  have h2 : IsUnit (l : Ω) := isUnit_iff_ne_zero.mpr h1
  have h3 := h2.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).commRingCatIsoToRingEquiv.symm
  simpa using h3

private theorem pullTot_comp_apply (l : ℕ) [Fact l.Prime] {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (x) :
    pullTot l (sch.map (f ≫ g)) x = pullTot l (sch.map f) (pullTot l (sch.map g) x) := by
  rw [Functor.map_comp, pullTot_comp]; rfl

open UpperTheory.Gal.G3 in
theorem UpperTheory.etaleCohomology_corrOp_comm_pullback :
    ∀ (l : ℕ) [Fact l.Prime] (Ω' : Type) [Field Ω'] [CharZero Ω'] {Z Y Z₁ Y₁ : Scheme.{0}} (s t : Y ⟶ Z) [IsFinite s] [Etale s] (s₁ t₁ : Y₁ ⟶ Z₁) (q₁ : Z₁ ⟶ Spec (CommRingCat.of Ω')) (u : Z₁ ⟶ Z) (v : Y₁ ⟶ Y), IsPullback v s₁ s u → v ≫ t = t₁ ≫ u → t₁ ≫ q₁ = s₁ ≫ q₁ → ∀ (A : Htot l (sch.obj Z) →ₗ[ℚ_[l]] Htot l (sch.obj Z)) (A₁ : Htot l (sch.obj Z₁) →ₗ[ℚ_[l]] Htot l (sch.obj Z₁)), IsCorrOp l s t A → IsCorrOp l s₁ t₁ A₁ → pullTot l (sch.map u) ∘ₗ A = A₁ ∘ₗ pullTot l (sch.map u) := by
  intro l _ Ω' _ _ Z Y Z₁ Y₁ s t _ _ s₁ t₁ q₁ u v hv hvt hq A A₁ hA hA₁
  obtain ⟨W, c, G, _, _, a, J, _, σ, hG, hS, hc⟩ := hA
  have SB : SplitsBasic := pSplitsBasic (pSplitsPts pIsoPts) pPtsOfSplits
  have FB : FEtBasic := pFEtBasic pPtsOfSplits
  have hT : (et l (sp Ω')).Good := pEtGood (pEtnGood FB pEtTr) l _ (l_unit_of_charZero l Ω')
  have OE : OpEx.{1} := pOpEx pOpTr
  have FI : FEtInj.{1} := pFEtInj (pGalClosD (pSplitsPts pIsoPts) (pOrdEx pOrdStep))
  haveI : IsFinite s₁ := MorphismProperty.of_isPullback (P := @IsFinite) hv ‹_›
  haveI : Etale s₁ := MorphismProperty.of_isPullback (P := @Etale) hv ‹_›
  obtain ⟨hσ, -⟩ := id hS
  have e : ∀ j, (pullback.fst c u ≫ σ j) ≫ s = pullback.snd c u ≫ u := by
    intro j
    rw [Category.assoc, hσ j, pullback.condition]
  let σ₁ : J → (pullback c u ⟶ Y₁) := fun j => hv.lift (pullback.fst c u ≫ σ j) (pullback.snd c u) (e j)
  have σ₁v : ∀ j, σ₁ j ≫ v = pullback.fst c u ≫ σ j := fun j => hv.lift_fst _ _ _
  have σ₁s : ∀ j, σ₁ j ≫ s₁ = pullback.snd c u := fun j => hv.lift_snd _ _ _
  have hS0 : Splits s (pullback.snd c u ≫ u) fun j => σ₁ j ≫ v := by
    have h := SB.1 s c J σ (pullback.fst c u) hS
    simp only [σ₁v]
    rw [← pullback.condition]
    exact h
  have hS₁ : Splits s₁ (pullback.snd c u) σ₁ := (SB.2 v s₁ s u hv (pullback.snd c u) J σ₁ σ₁s).2 hS0
  have hOp : (et l (sp Ω')).IsOp q₁ q₁ s₁ t₁ A₁ := (pOpEt l q₁ q₁ s₁ t₁ hq A₁).2 hA₁
  have key := (OE _ hT q₁ q₁ s₁ t₁ hq).2 A₁ hOp _ (pullback.snd c u ≫ q₁) (pullback.snd c u) rfl J σ₁
    (fun j => by rw [Category.assoc, hq, ← Category.assoc, σ₁s]) hS₁
  have key' : ∀ y, pullTot l (sch.map (pullback.snd c u)) (A₁ y) =
      ∑ j, pullTot l (sch.map (σ₁ j ≫ t₁)) y := fun y => key y
  have hfet : FEt c (Nat.card G) := FB.2.2 c G a hG
  have hfet₁ : FEt (pullback.snd c u) (Nat.card G) :=
    FB.1 (pullback.fst c u) (pullback.snd c u) c u _ (IsPullback.of_hasPullback c u) hfet
  have hinj : Function.Injective (pullTot l (sch.map (pullback.snd c u))) :=
    FI _ hT q₁ (pullback.snd c u ≫ q₁) (pullback.snd c u) rfl _ Nat.card_pos hfet₁
  refine LinearMap.ext fun x => hinj ?_
  show pullTot l (sch.map (pullback.snd c u)) (pullTot l (sch.map u) (A x)) =
    pullTot l (sch.map (pullback.snd c u)) (A₁ (pullTot l (sch.map u) x))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [key', ← pullTot_comp_apply, ← pullback.condition, pullTot_comp_apply, hc, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← pullTot_comp_apply, ← pullTot_comp_apply]
  have hm : pullback.fst c u ≫ σ j ≫ t = (σ₁ j ≫ t₁) ≫ u := by
    rw [Category.assoc, ← hvt, ← Category.assoc (σ₁ j), σ₁v, Category.assoc]
  rw [hm]
end

-- bundled from Development.AutomorphicArithmetic.SimultaneousEigenspaces.ExistsAlgEquivRestrictHomOfAlgebraMapCompat
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV UpperTheory.Gal.Int.Geo TensorProduct

theorem UpperTheory.exists_algEquiv_restrict_hom_of_algebraMap_compat :
    ∀ (k K Ω Ω' : Type) [Field k] [Field K] [Field Ω] [Field Ω'] [Algebra k Ω] [IsAlgClosure k Ω] [Algebra K Ω'] (τ : k →+* K) (j : Ω →+* Ω'), (∀ x, j (algebraMap k Ω x) = algebraMap K Ω' (τ x)) → ∃ r : (Ω' ≃ₐ[K] Ω') →* (Ω ≃ₐ[k] Ω), ∀ σ' x, σ' (j x) = j (r σ' x) := by
  intro k K Ω Ω' _ _ _ _ _ _ _ τ j hj
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  have key : ∀ (s : Ω' ≃ₐ[K] Ω') (x : Ω), ∃ y, s (j x) = j y := by
    intro s x
    have hint : IsIntegral k x := Algebra.IsIntegral.isIntegral x
    have hP : ((minpoly k x).map (algebraMap k Ω)).Splits := IsAlgClosed.splits _
    have hPm : ((minpoly k x).map (algebraMap k Ω)).map j = ((minpoly k x).map τ).map (algebraMap K Ω') := by
      rw [Polynomial.map_map, Polynomial.map_map]
      congr 1
      ext c
      exact hj c
    have hne : ((minpoly k x).map (algebraMap k Ω)).map j ≠ 0 :=
      Polynomial.map_ne_zero (Polynomial.map_ne_zero (minpoly.ne_zero hint))
    have h0 : (((minpoly k x).map (algebraMap k Ω)).map j).eval (j x) = 0 := by
      rw [Polynomial.eval_map, Polynomial.eval₂_hom, Polynomial.eval_map_algebraMap, minpoly.aeval, map_zero]
    have hroot : s (j x) ∈ (((minpoly k x).map (algebraMap k Ω)).map j).roots := by
      rw [Polynomial.mem_roots hne]
      show Polynomial.eval _ _ = 0
      rw [hPm, Polynomial.eval_map_algebraMap,
        show s (j x) = (s : Ω' →ₐ[K] Ω') (j x) from rfl, Polynomial.aeval_algHom_apply,
        ← Polynomial.eval_map_algebraMap, ← hPm, h0, map_zero]
    rw [hP.roots_map_of_ne_zero hne, Multiset.mem_map] at hroot
    obtain ⟨y, -, hy⟩ := hroot
    exact ⟨y, hy.symm⟩
  choose g hg using key
  have hji : Function.Injective j := j.injective
  let gA : (Ω' ≃ₐ[K] Ω') → (Ω →ₐ[k] Ω) := fun s =>
    { toFun := g s
      map_one' := hji (by rw [← hg]; simp only [map_one])
      map_mul' := fun a b => hji (by rw [← hg]; simp only [map_mul, hg])
      map_zero' := hji (by rw [← hg]; simp only [map_zero])
      map_add' := fun a b => hji (by rw [← hg]; simp only [map_add (f := _), hg])
      commutes' := fun c => hji (by rw [← hg, hj, AlgEquiv.commutes]) }
  let r : (Ω' ≃ₐ[K] Ω') → (Ω ≃ₐ[k] Ω) := fun s => (Algebra.IsAlgebraic.algEquivEquivAlgHom k Ω).symm (gA s)
  have hr : ∀ s x, r s x = g s x := fun s x => rfl
  refine ⟨{ toFun := r, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · ext x
    apply hji
    rw [hr, ← hg]
    simp
  · intro s t
    ext x
    apply hji
    rw [hr, ← hg, AlgEquiv.mul_apply, AlgEquiv.mul_apply, hr, hr]
    simp only [hg]
  · intro s x
    show s (j x) = j (r s x)
    rw [hr, hg]
end

-- bundled from Development.AutomorphicArithmetic.SimultaneousEigenspaces.ExistsBasisSimultaneousEigenspaceOfEquivariantBi
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV UpperTheory.Gal.Int.Geo TensorProduct

theorem UpperTheory.exists_basis_simultaneousEigenspace_of_equivariant_bijective :
    ∀ (l : ℕ) [Fact l.Prime] (V V' : Type 1) [AddCommGroup V] [Module ℚ_[l] V] [AddCommGroup V'] [Module ℚ_[l] V'] (Φ : V →ₗ[ℚ_[l]] V'), Function.Bijective Φ → ∀ (I : Type) (T : I → V →ₗ[ℚ_[l]] V) (T' : I → V' →ₗ[ℚ_[l]] V'), (∀ g, Φ ∘ₗ T g = T' g ∘ₗ Φ) → ∀ (L : Type) [Field L] [Algebra ℚ_[l] L] (θ : I → L) (d : ℕ) (b : Module.Basis (Fin d) L ↥(⨅ g, Module.End.eigenspace ((T g).baseChange L) (θ g))), ∃ b' : Module.Basis (Fin d) L ↥(⨅ g, Module.End.eigenspace ((T' g).baseChange L) (θ g)), ∀ i, (b' i).1 = Φ.baseChange L (b i).1 := by
  intro l _ V V' _ _ _ _ Φ hΦ I T T' hT L _ _ θ d b
  let e : V ≃ₗ[ℚ_[l]] V' := LinearEquiv.ofBijective Φ hΦ
  let eL : L ⊗[ℚ_[l]] V ≃ₗ[L] L ⊗[ℚ_[l]] V' := LinearEquiv.baseChange ℚ_[l] L V V' e
  have hcoe : ∀ x, eL x = Φ.baseChange L x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v => rfl
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hcomm : ∀ g x, (T' g).baseChange L (Φ.baseChange L x) = Φ.baseChange L ((T g).baseChange L x) := by
    intro g x
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, hT g]
  have hmap : (⨅ g, Module.End.eigenspace ((T g).baseChange L) (θ g)).map (eL : L ⊗[ℚ_[l]] V →ₗ[L] L ⊗[ℚ_[l]] V') = ⨅ g, Module.End.eigenspace ((T' g).baseChange L) (θ g) := by
    apply le_antisymm
    · intro z hz
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hz
      rw [Submodule.mem_iInf] at hx ⊢
      intro g
      have hxg := Module.End.mem_eigenspace_iff.1 (hx g)
      rw [Module.End.mem_eigenspace_iff, LinearEquiv.coe_coe, hcoe, hcomm, hxg, map_smul]
    · intro y hy
      refine Submodule.mem_map.2 ⟨eL.symm y, ?_, by simp⟩
      rw [Submodule.mem_iInf] at hy ⊢
      intro g
      have hyg := Module.End.mem_eigenspace_iff.1 (hy g)
      rw [Module.End.mem_eigenspace_iff]
      apply eL.injective
      have h1 := hcomm g (eL.symm y)
      rw [← hcoe, LinearEquiv.apply_symm_apply, hyg] at h1
      rw [map_smul, LinearEquiv.apply_symm_apply, hcoe, ← h1]
  refine ⟨b.map (eL.ofSubmodules _ _ hmap), fun i => ?_⟩
  rw [Module.Basis.map_apply, LinearEquiv.ofSubmodules_apply, hcoe]
end

-- bundled from Development.AutomorphicArithmetic.SimultaneousEigenspaces.ExistsIsPullbackGeomFiberBaseChangeTower
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV UpperTheory.Gal.Int.Geo TensorProduct

noncomputable section

section Gen

variable {C : Type*} [Category C] [HasPullbacks C] {S A B D X : C}

private theorem uu_cond (p : X ⟶ S) (a : A ⟶ S) (b : B ⟶ S) (c : D ⟶ A) (d : D ⟶ B) (w : c ≫ a = d ≫ b)
    (p' : pullback p b ⟶ B) (hp : p' = pullback.snd p b) :
    (pullback.fst p' d ≫ pullback.fst p b) ≫ p = (pullback.snd p' d ≫ c) ≫ a := by
  subst hp
  rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc, w]

private def uu (p : X ⟶ S) (a : A ⟶ S) (b : B ⟶ S) (c : D ⟶ A) (d : D ⟶ B) (w : c ≫ a = d ≫ b)
    (p' : pullback p b ⟶ B) (hp : p' = pullback.snd p b) : pullback p' d ⟶ pullback p a :=
  pullback.lift (pullback.fst p' d ≫ pullback.fst p b) (pullback.snd p' d ≫ c) (uu_cond p a b c d w p' hp)

@[reassoc] private theorem uu_fst (p : X ⟶ S) (a : A ⟶ S) (b : B ⟶ S) (c : D ⟶ A) (d : D ⟶ B) (w : c ≫ a = d ≫ b)
    (p' : pullback p b ⟶ B) (hp : p' = pullback.snd p b) :
    uu p a b c d w p' hp ≫ pullback.fst p a = pullback.fst p' d ≫ pullback.fst p b := pullback.lift_fst _ _ _

private theorem uu_sq (p : X ⟶ S) (a : A ⟶ S) (b : B ⟶ S) (c : D ⟶ A) (d : D ⟶ B) (w : c ≫ a = d ≫ b)
    (p' : pullback p b ⟶ B) (hp : p' = pullback.snd p b) :
    IsPullback (uu p a b c d w p' hp) (pullback.snd p' d) (pullback.snd p a) c := by
  subst hp
  refine IsPullback.of_right (h₁₂ := pullback.fst p a) (v₁₃ := p) (h₂₂ := a) ?_ (pullback.lift_snd _ _ _)
    (IsPullback.of_hasPullback p a)
  rw [uu_fst, w]
  exact (IsPullback.of_hasPullback (pullback.snd p b) d).paste_horiz (IsPullback.of_hasPullback p b)

private theorem uu_nat {Y : C} (p : Y ⟶ S) (q : X ⟶ S) (a : A ⟶ S) (b : B ⟶ S) (c : D ⟶ A) (d : D ⟶ B)
    (w : c ≫ a = d ≫ b) (p' : pullback p b ⟶ B) (hp : p' = pullback.snd p b)
    (q' : pullback q b ⟶ B) (hq : q' = pullback.snd q b) (f : Y ⟶ X)
    (fB : pullback p b ⟶ pullback q b) (fA : pullback p a ⟶ pullback q a) (fD : pullback p' d ⟶ pullback q' d)
    (h1 : fB ≫ pullback.fst q b = pullback.fst p b ≫ f) (h2 : fA ≫ pullback.fst q a = pullback.fst p a ≫ f)
    (h3 : fA ≫ pullback.snd q a = pullback.snd p a) (h4 : fD ≫ pullback.fst q' d = pullback.fst p' d ≫ fB)
    (h5 : fD ≫ pullback.snd q' d = pullback.snd p' d) :
    uu p a b c d w p' hp ≫ fA = fD ≫ uu q a b c d w q' hq := by
  apply pullback.hom_ext
  · simp only [Category.assoc, h2, uu_fst, uu_fst_assoc, reassoc_of% h4, h1]
  · simp only [Category.assoc, h3, uu, pullback.lift_snd, reassoc_of% h5]

end Gen

end

theorem UpperTheory.exists_isPullback_geomFiber_baseChange_tower :
    ∀ (k K Ω Ω' : Type) [Field k] [Field K] [Field Ω] [Field Ω'] [Algebra k Ω] [Algebra K Ω'] (τ : k →+* K) (j : Ω →+* Ω'), (∀ x, j (algebraMap k Ω x) = algebraMap K Ω' (τ x)) → ∀ (H : HTower k), ∃ (u : (bcAlong H τ).geomZ Ω' ⟶ H.geomZ Ω) (v : ∀ g : H.Γ, GlobalTheory.Et.geom Ω' ((bcAlong H τ).s g ≫ (bcAlong H τ).q) ⟶ GlobalTheory.Et.geom Ω (H.s g ≫ H.q)), IsPullback u (pullback.snd _ _) (pullback.snd _ _) (Spec.map (CommRingCat.ofHom j)) ∧ (∀ g, IsPullback (v g) ((bcAlong H τ).sΩ Ω' g) (H.sΩ Ω g) u ∧ v g ≫ H.tΩ Ω g = (bcAlong H τ).tΩ Ω' g ≫ u) ∧ ∀ (σ : Ω ≃ₐ[k] Ω) (σ' : Ω' ≃ₐ[K] Ω'), (∀ x, σ' (j x) = j (σ x)) → GlobalTheory.Et.galMap Ω' (bcAlong H τ).q σ' ≫ u = u ≫ GlobalTheory.Et.galMap Ω H.q σ := by
  intro k K Ω Ω' _ _ _ _ _ _ τ j hj H
  have w : Spec.map (CommRingCat.ofHom j) ≫ Spec.map (CommRingCat.ofHom (algebraMap k Ω)) =
      Spec.map (CommRingCat.ofHom (algebraMap K Ω')) ≫ Spec.map (CommRingCat.ofHom τ) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    exact hj x
  have hZ : (bcAlong H τ).q = pullback.snd H.q (Spec.map (CommRingCat.ofHom τ)) := rfl
  have hY : ∀ g, (bcAlong H τ).s g ≫ (bcAlong H τ).q =
      pullback.snd (H.s g ≫ H.q) (Spec.map (CommRingCat.ofHom τ)) := fun g => pullback.lift_snd _ _ _
  let u : (bcAlong H τ).geomZ Ω' ⟶ H.geomZ Ω := uu H.q _ _ _ _ w _ hZ
  let v : ∀ g : H.Γ, GlobalTheory.Et.geom Ω' ((bcAlong H τ).s g ≫ (bcAlong H τ).q) ⟶ GlobalTheory.Et.geom Ω (H.s g ≫ H.q) :=
    fun g => uu (H.s g ≫ H.q) _ _ _ _ w _ (hY g)
  have hu : IsPullback u (pullback.snd _ _) (pullback.snd _ _) (Spec.map (CommRingCat.ofHom j)) :=
    uu_sq H.q _ _ _ _ w _ hZ
  have hu1 : u ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _ := uu_fst H.q _ _ _ _ w _ hZ
  have hu2 : u ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom j) :=
    pullback.lift_snd _ _ _
  have vs : ∀ g, v g ≫ H.sΩ Ω g = (bcAlong H τ).sΩ Ω' g ≫ u := fun g =>
    uu_nat (H.s g ≫ H.q) H.q _ _ _ _ w _ (hY g) _ hZ (H.s g) ((bcAlong H τ).s g) (H.sΩ Ω g) ((bcAlong H τ).sΩ Ω' g)
      (pullback.lift_fst _ _ _) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  have vt : ∀ g, v g ≫ H.tΩ Ω g = (bcAlong H τ).tΩ Ω' g ≫ u := fun g =>
    uu_nat (H.s g ≫ H.q) H.q _ _ _ _ w _ (hY g) _ hZ (H.t g) ((bcAlong H τ).t g) (H.tΩ Ω g) ((bcAlong H τ).tΩ Ω' g)
      (pullback.lift_fst _ _ _) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  refine ⟨u, v, hu, fun g => ⟨?_, vt g⟩, ?_⟩
  · refine IsPullback.of_bot (v₂₁ := pullback.snd _ _) (v₂₂ := pullback.snd _ _) ?_ (vs g) hu
    have e1 : (bcAlong H τ).sΩ Ω' g ≫ pullback.snd (bcAlong H τ).q (Spec.map (CommRingCat.ofHom (algebraMap K Ω'))) =
        pullback.snd _ _ := pullback.lift_snd _ _ _
    have e2 : H.sΩ Ω g ≫ pullback.snd H.q (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) =
        pullback.snd _ _ := pullback.lift_snd _ _ _
    rw [e1, e2]
    exact uu_sq (H.s g ≫ H.q) _ _ _ _ w _ (hY g)
  · intro σ σ' hσ
    have hg : Spec.map (CommRingCat.ofHom (σ' : Ω' →+* Ω')) ≫ Spec.map (CommRingCat.ofHom j) =
        Spec.map (CommRingCat.ofHom j) ≫ Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) := by
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext x
      exact hσ x
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, GlobalTheory.Et.galMap_fst, hu1]
      exact GlobalTheory.Et.galMap_fst_assoc Ω' (bcAlong H τ).q σ' _
    · rw [Category.assoc, Category.assoc, GlobalTheory.Et.galMap_snd, hu2, GlobalTheory.Et.galMap_snd_assoc, reassoc_of% hu2, hg]
end

