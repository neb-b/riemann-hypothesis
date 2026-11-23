module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealEqBotOfFlatQuotientOfMapMaximalIdeal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSmoothAtOfSmoothQuotientPow
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SmoothLimit

section Ring
open TensorProduct IsLocalRing

variable {V A S C : Type} [CommRing V] [CommRing A] [CommRing S] [CommRing C] [Algebra V A]
  [Algebra A S] [Algebra V S] [IsScalarTower V A S] [Algebra V C]

theorem flat_and_formallySmooth_tensor (M : Submonoid A) [IsLocalization M S]
    [Algebra.Smooth C (C ⊗[V] A)] :
    Module.Flat C (C ⊗[V] S) ∧ Algebra.FormallySmooth C (C ⊗[V] S) := by
  let φ : C ⊗[V] A →ₐ[C] C ⊗[V] S :=
    Algebra.TensorProduct.map (AlgHom.id C C) (IsScalarTower.toAlgHom V A S)
  letI := φ.toRingHom.toAlgebra
  haveI : IsScalarTower C (C ⊗[V] A) (C ⊗[V] S) :=
    IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  haveI := IsLocalization.tensorProduct_tensorProduct_right V C M S (by
    ext a; simp [RingHom.algebraMap_toAlgebra, φ])
  haveI : Module.Flat (C ⊗[V] A) (C ⊗[V] S) :=
    IsLocalization.flat _ (M.map (Algebra.TensorProduct.includeRight (R := V) (A := C)))
  haveI : Algebra.FormallySmooth (C ⊗[V] A) (C ⊗[V] S) :=
    .of_isLocalization (M.map (Algebra.TensorProduct.includeRight (R := V) (A := C)))
  exact ⟨.trans C (C ⊗[V] A) _, .comp C (C ⊗[V] A) _⟩

theorem isSmoothAt_of_smooth_quotient_pow [IsLocalRing V] [IsNoetherianRing V]
    [Algebra.FiniteType V A]
    (h : ∀ e : ℕ, Algebra.Smooth (V ⧸ maximalIdeal V ^ (e + 1))
      ((V ⧸ maximalIdeal V ^ (e + 1)) ⊗[V] A))
    (q : Ideal A) [q.IsPrime] (hq : q.comap (algebraMap V A) = maximalIdeal V) :
    Algebra.IsSmoothAt V q := by
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing V A
  haveI : Algebra.FinitePresentation V A := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  let S := Localization.AtPrime q
  have hle : (maximalIdeal V).map (algebraMap V S) ≤ maximalIdeal S := by
    rw [Ideal.map_le_iff_le_comap, IsScalarTower.algebraMap_eq V A S, ← Ideal.comap_comap,
      show (maximalIdeal S).comap (algebraMap A S) = q from
        Localization.AtPrime.under_maximalIdeal, hq]
  haveI : IsLocalHom (algebraMap V S) :=
    ((IsLocalRing.local_hom_tfae (algebraMap V S)).out 3 1).mp hle
  haveI : Module.Flat V S := by
    refine LocalFlat.flat_of_relationsLift S (I := maximalIdeal V)
      (hle.trans (IsLocalRing.maximalIdeal_le_jacobson _)) fun n => ?_
    rcases n with _ | e
    · intro F _ _ f x _
      exact LocalFlat.range_lTensor_le LinearMap.id _ (by simp) ⟨x, by simp⟩
    · haveI := h e
      haveI := (flat_and_formallySmooth_tensor (V := V) (S := S)
        (C := V ⧸ maximalIdeal V ^ (e + 1)) q.primeCompl).1
      refine LocalFlat.relationsLift_of_flat (C := V ⧸ maximalIdeal V ^ (e + 1))
        Ideal.Quotient.mk_surjective Ideal.mk_ker
        (TensorProduct.mk V (V ⧸ maximalIdeal V ^ (e + 1)) S 1)
        (TensorProduct.mk_surjective _ _ _ Ideal.Quotient.mk_surjective) ?_
      exact LinearMap.ker_tensorProductMk _
  haveI : Algebra.Smooth (ResidueField V) (ResidueField V ⊗[V] A) := by
    haveI := h 0
    let C := V ⧸ maximalIdeal V ^ (0 + 1)
    letI : Algebra C (ResidueField V) :=
      (Ideal.Quotient.factor (S := maximalIdeal V ^ (0 + 1)) (T := maximalIdeal V)
        (by simp)).toAlgebra
    haveI : IsScalarTower V C (ResidueField V) := IsScalarTower.of_algebraMap_eq fun _ => rfl
    exact .of_equiv (Algebra.TensorProduct.cancelBaseChange V C (ResidueField V) (ResidueField V) A)
  haveI := (flat_and_formallySmooth_tensor (V := V) (S := S)
        (C := ResidueField V) q.primeCompl).2
  exact Algebra.FormallySmooth.of_formallySmooth_residueField_tensor (R := V) (S := S) (P := A)
    q.primeCompl

end Ring

theorem mem_smoothLocus {V : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of V)) [LocallyOfFinitePresentation f]
    (h : ∀ e, Smooth (pullback.snd f (thick V (IsLocalRing.maximalIdeal V) e)))
    (x : X) (hx : f x = IsLocalRing.closedPoint V) : x ∈ f.smoothLocus := by
  wlog hX : ∃ S, X = Spec S generalizing f X
  · obtain ⟨i, y, rfl⟩ := X.affineCover.exists_eq x
    have H := this (X.affineCover.f i ≫ f) (fun e => by
      haveI := h e
      rw [← pullbackRightPullbackFstIso_inv_snd_snd]
      infer_instance) y (by simpa using hx) ⟨_, rfl⟩
    rwa [← Scheme.Hom.preimage_smoothLocus_eq] at H
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  letI := φ.hom.toAlgebra
  haveI : Algebra.FinitePresentation V S :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation) (φ := φ)).mp ‹_›
  have hs (e : ℕ) : Algebra.Smooth (V ⧸ IsLocalRing.maximalIdeal V ^ (e + 1))
      (TensorProduct V (V ⧸ IsLocalRing.maximalIdeal V ^ (e + 1)) S) := by
    have H := isPullback_SpecMap_of_isPushout _ _ _ _
      (CommRingCat.isPushout_tensorProduct V (V ⧸ IsLocalRing.maximalIdeal V ^ (e + 1)) S)
    have e1 := H.flip.isoPullback_hom_snd
    have h1 : Smooth (H.flip.isoPullback.hom ≫ pullback.snd _ _) := by
      haveI : Smooth (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap V S)))
        (Spec.map (CommRingCat.ofHom
          (algebraMap V (V ⧸ IsLocalRing.maximalIdeal V ^ (e + 1)))))) := h e
      infer_instance
    rw [e1, HasRingHomProperty.Spec_iff (P := @Smooth)] at h1
    exact RingHom.smooth_algebraMap.mp h1
  haveI : x.asIdeal.IsPrime := PrimeSpectrum.isPrime x
  haveI := isSmoothAt_of_smooth_quotient_pow hs x.asIdeal (congrArg PrimeSpectrum.asIdeal hx)
  obtain ⟨g, hg, hsm⟩ := Algebra.IsSmoothAt.exists_notMem_smooth V x.asIdeal
  let j : Spec (CommRingCat.of (Localization.Away g)) ⟶ Spec S :=
    Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))
  haveI : IsOpenImmersion j := IsOpenImmersion.of_isLocalization g
  haveI : Smooth (j ≫ Spec.map φ) := by
    rw [← Spec.map_comp, HasRingHomProperty.Spec_iff (P := @Smooth)]
    exact RingHom.smooth_algebraMap.mpr hsm
  obtain ⟨y, rfl⟩ : x ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away g))) := by
    rw [PrimeSpectrum.localization_away_comap_range _ g]
    exact hg
  have := (j ≫ Spec.map φ).smoothLocus_eq_top.ge (Set.mem_univ y)
  rwa [← Scheme.Hom.preimage_smoothLocus_eq] at this

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V] (B : Over (Spec (CommRingCat.of V))) [IsProper B.hom], (∀ e, Smooth (thickObj V (IsLocalRing.maximalIdeal V) e B).hom) → Smooth B.hom := by
  intro V _ _ _ _ B _ h
  haveI : LocallyOfFinitePresentation B.hom := inferInstance
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← top_le_iff]
  intro x _
  by_contra hx
  have hc : IsClosed (B.hom '' (B.hom.smoothLocus : Set B.left)ᶜ) :=
    B.hom.isClosedMap _ B.hom.smoothLocus.2.isClosed_compl
  obtain ⟨y, hy, hy'⟩ := (IsLocalRing.specializes_closedPoint (R := V) (B.hom x)).mem_closed hc ⟨x, hx, rfl⟩
  exact hy (mem_smoothLocus B.hom h y hy')

end GlobalTheory.SmoothLimit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KTrivExternalTensorPowerLineBundle
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BoxKernel

open GlobalTheory.KerPow

variable {X X' Y B : Scheme.{0}} {L : LB X} {K J : Type} [Fintype K] [Fintype J]

theorem hasGen_flat (F : J → (X' ⟶ X)) {ψ : K → (Y ⟶ X')} {ε : K → ℤ}
    (H : HasGen (LB.LinComb L F (fun _ => 1)) ψ ε) :
    HasGen L (K := K × J) (fun q => ψ q.1 ≫ F q.2) (fun q => ε q.1) := by
  have le : ∀ (j : K × J → L.ι) (y : Y), y ∈ LB.wchart L (K := K × J) (fun q => ψ q.1 ≫ F q.2) j →
      y ∈ LB.wchart (LB.LinComb L F (fun _ => 1)) ψ (fun k i => j (k, i)) := fun j y hy =>
    Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun i => Set.mem_iInter.1 hy (k, i)
  refine gen_transfer (M := LB.LinComb (LB.LinComb L F (fun _ => 1)) ψ ε)
    (M' := LB.LinComb L (K := K × J) (fun q => ψ q.1 ≫ F q.2) (fun q => ε q.1))
    (fun j k i => j (k, i)) (fun j y hy => le j y hy) (fun j j' y hj hj' => ?_) H
  refine (gm_linComb L (K := K × J) (fun q => ψ q.1 ≫ F q.2) (fun q => ε q.1) (𝟙 Y) y j j' hj hj').trans
    (Eq.trans ?_ (gm_linComb (LB.LinComb L F (fun _ => 1)) ψ ε (𝟙 Y) y _ _ (le j y hj) (le j' y hj')).symm)
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun k _ => ?_
  refine Eq.trans ?_ (congrArg (· ^ ε k) (gm_linComb L F (fun _ => 1) (𝟙 Y ≫ ψ k) y (fun i => j (k, i))
    (fun i => j' (k, i)) (Set.mem_iInter.1 (le j y hj) k) (Set.mem_iInter.1 (le j' y hj') k)).symm)
  simp only [zpow_one, Category.assoc, Finset.prod_zpow]

theorem gen_of_chart {M : LB Y} (hM : M.IsLB) (i₀ : M.ι) (h : ∀ y, y ∈ M.U i₀) : ∃ t : LB.Gen M, t.IsGen := by
  refine ⟨⟨fun i => res (le_inf le_rfl (fun y _ => h y) : M.U i ≤ M.U i ⊓ M.U i₀) (M.g i i₀)⟩, fun i j => ?_⟩
  have := LB.res_cocycle hM i j i₀ (W := M.U i ⊓ M.U j) le_rfl (le_inf inf_le_right fun y _ => h y)
    (le_inf inf_le_left fun y _ => h y)
  refine (LB.res_res _ _ _).trans (this.symm.trans (congrArg₂ (· * ·) ?_ (LB.res_res _ _ _).symm))
  exact unit_ext fun y hy => gm_res _ y _ hy _

theorem locGen_base (hL : L.IsLB) (π : Y ⟶ B) (b : K → (B ⟶ X)) (ε : K → ℤ) :
    LocGen L π (fun k => π ≫ b k) ε := by
  intro p
  choose j hj using fun k => exists_chart hL (b k p)
  refine ⟨LB.wchart L b j, Set.mem_iInter.2 hj, gen_of_chart (LB.isLB_linComb hL _ _) j fun y => ?_⟩
  exact Set.mem_iInter.2 fun k => Set.mem_iInter.1 y.2 k

theorem locGen_flat (F : J → (X' ⟶ X)) {π : Y ⟶ B} {ψ : K → (Y ⟶ X')} {ε : K → ℤ}
    (H : LocGen (LB.LinComb L F (fun _ => 1)) π ψ ε) :
    LocGen L (K := K × J) π (fun q => ψ q.1 ≫ F q.2) (fun q => ε q.1) := by
  intro p
  obtain ⟨V, hV, t⟩ := H p
  exact ⟨V, hV, (hasGen_flat F t).pull (𝟙 _) fun q => by rw [Category.id_comp, Category.assoc]⟩

end GlobalTheory.BoxKernel

namespace GlobalTheory


open KerPow BoxKernel in
theorem kTriv_boxLB : ∀ (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G]
    (j : ℕ) (p : IsPowGrp G' G j) (L : LB G.left), L.IsLB → KTriv G L → KTriv G' (boxLB L p.pr) := by
  intro S G' G _ _ _ _ j p L hL hK R _ t x hx
  classical
  have H : LocGen (boxLB L p.pr) (K := Fin 2) (fst (Over.mk t) G').left
      ![(translPt G' x).left, (snd (Over.mk t) G').left] ![1, -1] := (locGen_iff _ _ _).1 hx
  clear hx
  generalize Over.mk t = T at x H
  refine p.lim.hom_ext fun ⟨i⟩ => ?_
  have := p.hom
  show x ≫ p.pr i = (1 : T ⟶ G') ≫ p.pr i
  rw [MonObj.one_comp]
  let u : G ⟶ G' := p.lim.lift (Fan.mk G fun i' => if i' = i then 𝟙 G else 1)
  have hu : ∀ i', u ≫ p.pr i' = if i' = i then 𝟙 G else 1 := fun i' => p.lim.fac _ ⟨i'⟩
  let a : Fin 2 → (T ⊗ G ⟶ G') := ![(fst T G ≫ x) * (snd T G ≫ u), snd T G ≫ u]
  have H₁ := H.baseChange (π' := (fst T G).left) (T ◁ u).left (𝟙 _)
    ((congrArg (fun q => q.left) (whiskerLeft_fst T u)).trans (Category.comp_id _).symm)
    (φ' := fun k => (a k).left) (fun k => by
      fin_cases k
      · refine congrArg (fun q => q.left) (show T ◁ u ≫ ((fst T G' ≫ x) * snd T G') = (fst T G ≫ x) * (snd T G ≫ u) from ?_)
        rw [MonObj.comp_mul, whiskerLeft_fst_assoc, whiskerLeft_snd]
      · exact congrArg (fun q => q.left) (whiskerLeft_snd T u))
  let b : Fin 2 × Fin j → (T ⟶ G) := fun q => ![x ≫ p.pr q.2, 1] q.1
  have H₂ := locGen_base hL (fst T G).left (fun q => (b q).left)
    (fun q => if q.2 = i then 0 else (![1, -1] : Fin 2 → ℤ) q.1)
  refine eq_one_of_locGen hK _ ((locGen_flat _ H₁).comb hL H₂ fun U _ h => ?_)
  have e₀ : ∀ k i', i' ≠ i → (a k).left ≫ (p.pr i').left = (fst T G).left ≫ (b (k, i')).left := fun k i' hi => by
    refine congrArg (fun q => q.left) (show a k ≫ p.pr i' = fst T G ≫ b (k, i') from ?_)
    fin_cases k
    · show ((fst T G ≫ x) * (snd T G ≫ u)) ≫ p.pr i' = fst T G ≫ x ≫ p.pr i'
      rw [MonObj.mul_comp, Category.assoc, Category.assoc, hu, if_neg hi, MonObj.comp_one, _root_.mul_one]
    · show (snd T G ≫ u) ≫ p.pr i' = fst T G ≫ 1
      rw [Category.assoc, hu, if_neg hi, MonObj.comp_one, MonObj.comp_one]
  have e₁ : ∀ k, (a k).left ≫ (p.pr i).left =
      (![(translPt G (x ≫ p.pr i)).left, (snd T G).left] : Fin 2 → _) k := fun k => by
    fin_cases k
    · refine congrArg (fun q => q.left)
        (show ((fst T G ≫ x) * (snd T G ≫ u)) ≫ p.pr i = (fst T G ≫ x ≫ p.pr i) * snd T G from ?_)
      rw [MonObj.mul_comp, Category.assoc, Category.assoc, hu, if_pos rfl, Category.comp_id]
    · refine congrArg (fun q => q.left) (show (snd T G ≫ u) ≫ p.pr i = snd T G from ?_)
      rw [Category.assoc, hu, if_pos rfl, Category.comp_id]
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finset.prod_eq_single i (fun i' _ hi => ?_) (fun hi => (hi (Finset.mem_univ _)).elim)]
  · simp only [if_true, zpow_zero, inv_one, _root_.mul_one, e₁]
  · simp only [if_neg hi, e₀ k i' hi, mul_inv_cancel]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PerfectPairingOrthogonalOfCard
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PerfectPairingCount

variable {F : Type} [Field F]

theorem linearIndependent_unitsChar (G : Type) [Group G] :
    LinearIndependent F (fun (f : G →* Fˣ) => (fun g => ((f g : Fˣ) : F) : G → F)) := by
  have h := linearIndependent_monoidHom G F
  have hinj : Function.Injective (fun f : G →* Fˣ => (Units.coeHom F).comp f) := by
    intro f g hfg
    ext x
    exact DFunLike.congr_fun hfg x
  exact h.comp _ hinj

theorem finite_unitsChar (G : Type) [Group G] [Finite G] : Finite (G →* Fˣ) :=
  (linearIndependent_unitsChar (F := F) G).finite

theorem card_unitsChar_le (G : Type) [Group G] [Finite G] :
    Nat.card (G →* Fˣ) ≤ Nat.card G := by
  classical
  haveI := finite_unitsChar (F := F) G
  haveI := Fintype.ofFinite (G →* Fˣ)
  haveI := Fintype.ofFinite G
  have h := (linearIndependent_unitsChar (F := F) G).fintype_card_le_finrank
  rw [Module.finrank_fintype_fun_eq_card] at h
  simpa [Nat.card_eq_fintype_card] using h

variable {A : Type} [CommGroup A] [Finite A]

theorem card_ker_mul_le (E : A →* (A →* Fˣ)) (hE : ∀ a, (∀ b, E a b = 1) → a = 1)
    (H K : Subgroup A) (hK : ∀ k ∈ K, ∀ h ∈ H, E k h = 1) :
    Nat.card K * Nat.card H ≤ Nat.card A := by
  haveI := finite_unitsChar (F := F) (A ⧸ H)
  let φ : K → (A ⧸ H →* Fˣ) := fun k =>
    QuotientGroup.lift H (E k) (fun h hh => hK k k.2 h hh)
  have hφ : Function.Injective φ := by
    intro k k' hkk
    have h1 : E k = E k' := by
      apply MonoidHom.ext
      intro b
      have := DFunLike.congr_fun hkk (QuotientGroup.mk b)
      exact this
    have h2 : (k : A) * (k' : A)⁻¹ = 1 := by
      apply hE
      intro b
      rw [map_mul, map_inv, h1, mul_inv_cancel]
      rfl
    exact Subtype.ext (mul_inv_eq_one.mp h2)
  have h3 : Nat.card K ≤ Nat.card (A ⧸ H) :=
    (Nat.card_le_card_of_injective φ hφ).trans (card_unitsChar_le _)
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup H]
  exact Nat.mul_le_mul_right _ h3

theorem right_nondegenerate (E : A →* (A →* Fˣ)) (hE : ∀ a, (∀ b, E a b = 1) → a = 1)
    (b : A) (hb : ∀ a, E a b = 1) : b = 1 := by
  have h := card_ker_mul_le E hE E.flip.ker ⊤ (fun k _ h hh => by
    have := DFunLike.congr_fun (MonoidHom.mem_ker.mp hh) k
    simpa using this)
  rw [Subgroup.card_top] at h
  have hpos : 0 < Nat.card A := Nat.card_pos
  have h1 : Nat.card E.flip.ker ≤ 1 := by
    have : Nat.card A * Nat.card E.flip.ker ≤ Nat.card A * 1 := by simpa using h
    exact Nat.le_of_mul_le_mul_left this hpos
  have h2 : E.flip.ker = ⊥ := Subgroup.card_le_one_iff_eq_bot _ |>.mp h1
  have h3 : b ∈ E.flip.ker := by
    rw [MonoidHom.mem_ker]
    apply MonoidHom.ext
    intro a
    simpa using hb a
  rw [h2] at h3
  exact Subgroup.mem_bot.mp h3

theorem one_side (E : A →* (A →* Fˣ)) (hE : ∀ a, (∀ b, E a b = 1) → a = 1)
    (T H : Subgroup A) (hTH : ∀ t ∈ T, ∀ h ∈ H, E t h = 1)
    (hc : Nat.card T * Nat.card H = Nat.card A) :
    (∀ x, (∀ h ∈ H, E x h = 1) ↔ x ∈ T) ∧ (∀ χ : H →* Fˣ, ∃ x, ∀ h : H, E x h = χ h) := by
  let R : A →* (H →* Fˣ) :=
    { toFun := fun a => (E a).comp H.subtype
      map_one' := by apply MonoidHom.ext; intro h; simp
      map_mul' := by intro a a'; apply MonoidHom.ext; intro h; simp }
  have hR : ∀ x, x ∈ R.ker ↔ ∀ h ∈ H, E x h = 1 := by
    intro x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx h hh
      exact DFunLike.congr_fun hx ⟨h, hh⟩
    · intro hx
      apply MonoidHom.ext
      intro h
      exact hx h h.2
  have hle : T ≤ R.ker := fun t ht => (hR t).mpr (hTH t ht)
  have hHpos : 0 < Nat.card H := Nat.card_pos
  have hTpos : 0 < Nat.card T := Nat.card_pos
  have hcard : Nat.card R.ker ≤ Nat.card T := by
    have := card_ker_mul_le E hE H R.ker (fun k hk => (hR k).mp hk)
    rw [← hc] at this
    exact Nat.le_of_mul_le_mul_right this hHpos
  have heq : T = R.ker := Subgroup.eq_of_le_of_card_ge hle hcard
  refine ⟨fun x => by rw [← hR, heq], ?_⟩
  haveI := finite_unitsChar (F := F) H
  have hrange : Nat.card R.range = Nat.card H := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup R.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange R).toEquiv, ← heq, ← hc,
      mul_comm] at h1
    exact (Nat.eq_of_mul_eq_mul_right hTpos h1).symm
  have htop : R.range = ⊤ := by
    apply Subgroup.eq_of_le_of_card_ge le_top
    rw [Subgroup.card_top, hrange]
    exact card_unitsChar_le _
  intro χ
  have : χ ∈ R.range := by rw [htop]; trivial
  obtain ⟨x, hx⟩ := this
  exact ⟨x, fun h => DFunLike.congr_fun hx h⟩

end GlobalTheory.PerfectPairingCount

namespace GlobalTheory

theorem perfectPairing_orthogonal_of_card :
    ∀ (F : Type) [Field F] (A : Type) [CommGroup A] [Finite A] (e : A → A → Fˣ), (∀ a a' b, e (a * a') b = e a b * e a' b) → (∀ a b b', e a (b * b') = e a b * e a b') → (∀ a, (∀ b, e a b = 1) → a = 1) → ∀ T H : Subgroup A, (∀ t ∈ T, ∀ h ∈ H, e t h = 1) → Nat.card T * Nat.card H = Nat.card A → (∀ x, (∀ h ∈ H, e x h = 1) ↔ x ∈ T) ∧ (∀ x, (∀ t ∈ T, e t x = 1) ↔ x ∈ H) ∧ (∀ χ : H →* Fˣ, ∃ x, ∀ h : H, e x h = χ h) ∧ (∀ χ : T →* Fˣ, ∃ x, ∀ t : T, e t x = χ t) := by
  intro F _ A _ _ e h1 h2 h3 T H hTH hc
  let E : A →* (A →* Fˣ) :=
    MonoidHom.mk' (fun a => MonoidHom.mk' (e a) (h2 a)) (fun a a' => by
      apply MonoidHom.ext
      intro b
      exact h1 a a' b)
  have hE : ∀ a, (∀ b, E a b = 1) → a = 1 := h3
  have hE' : ∀ b, (∀ a, E.flip b a = 1) → b = 1 :=
    fun b hb => PerfectPairingCount.right_nondegenerate E hE b hb
  obtain ⟨a1, a2⟩ := PerfectPairingCount.one_side E hE T H hTH hc
  obtain ⟨b1, b2⟩ := PerfectPairingCount.one_side E.flip hE' H T
    (fun h hh t ht => hTH t ht h hh) (by rw [mul_comm, hc])
  exact ⟨a1, b1, a2, b2⟩

end GlobalTheory
end

