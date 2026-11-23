module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.AbsGood
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.PxIsCont
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FinLamOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SeedOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.ComponentsGoodRankTwo
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.PropagationTheoremGL3
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0066

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.AbsGood
section
theorem UpperTheory.V.J.absGood :
    UpperTheory.V.J.AbsGood := by
  intro l _ O _ _ _ _ _ F T₂ T₃ J₂ J₃ h₂ h₃
  obtain ⟨φ₂, hφ₂, hs₂⟩ := UpperTheory.V.Pr.phiEx l O F 2 T₂
  obtain ⟨φ₃, hφ₃, hs₃⟩ := UpperTheory.V.Pr.phiEx l O F 3 T₃
  obtain ⟨Λ₂, hΛ₂⟩ := h₂.fin
  obtain ⟨Λ₃, hΛ₃⟩ := h₃.fin
  have good₂ : UpperTheory.V.Pr.AllGood T₂.S (Ideal.map φ₂ J₂) :=
    UpperTheory.V.Pr.components_good_rank_two l O F T₂.C₀ T₂.ok T₂.big T₂.S (Ideal.map φ₂ J₂)
      (UpperTheory.V.Pr.finLamOf l O F 2 T₂ φ₂ hφ₂ hs₂ Λ₂ J₂ hΛ₂)
      (UpperTheory.V.Pr.p1Of l O F 2 T₂ φ₂ hφ₂ h₂.n4 J₂ h₂.p1)
      (UpperTheory.V.Pr.seedOf l O F 2 T₂ φ₂ hφ₂ J₂ h₂.unr h₂.dim h₂.seed)
  refine ⟨φ₃, hφ₃, hs₃, ?_⟩
  exact (UpperTheory.V.Pr.components_good_rank_three l O F T₃.C₀ T₃.ok T₃.big T₂.S (Ideal.map φ₂ J₂)
      (UpperTheory.V.Pr.finLamOf l O F 2 T₂ φ₂ hφ₂ hs₂ Λ₂ J₂ hΛ₂) good₂
      T₃.S (Ideal.map φ₃ J₃)
      (UpperTheory.V.Pr.finLamOf l O F 3 T₃ φ₃ hφ₃ hs₃ Λ₃ J₃ hΛ₃)
      (UpperTheory.V.Pr.p1Of l O F 3 T₃ φ₃ hφ₃ h₃.n4 J₃ h₃.p1)
      (UpperTheory.V.Pr.rankThree_deformationSetup_splitting_condition l O F T₃ φ₃ hφ₃ h₃.n4 J₃ h₃.p3)
      (UpperTheory.V.Pr.seedOf l O F 3 T₃ φ₃ hφ₃ J₃ h₃.unr h₃.dim h₃.seed)).1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.IrrOpen
section
noncomputable section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg
open UpperTheory.V.W UpperTheory.V.Pr UpperTheory.V.CA Formalism.MainNotions.N

namespace UpperTheory.V.J

section Abstract

private theorem tr_comap' {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : GDet n A G) (φ : H →* G) (g : H) :
    (D.comap φ).tr (MonoidAlgebra.single g 1) = D.tr (MonoidAlgebra.single (φ g) 1) := by
  have hc : (D.comap φ).chi (MonoidAlgebra.single g 1) = D.chi (MonoidAlgebra.single (φ g) 1) := by
    show D.D (Polynomial A) (MonoidAlgebra.mapDomainRingHom (Polynomial A) φ
        (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.mapRingHom H Polynomial.C (MonoidAlgebra.single g 1))) = _
    congr 1
    rw [map_sub]
    simp [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapRingHom_apply, MonoidAlgebra.mapDomain_single]
  simp only [GDet.tr, GDet.lam, hc]

private theorem tr_at {n : ℕ} {A G H K : Type} [CommRing A] [Group G] [Group H] [CommRing K] (hn : 1 ≤ n)
    (D : GDet n A G) (f : A →+* K) (φ : H →* G) (ρ : H →* Matrix (Fin n) (Fin n) K)
    (h : (D.map f).comap φ = GDet.ofRep ρ) (g : H) :
    f (D.tr (MonoidAlgebra.single (φ g) 1)) = (ρ g).trace := by
  have h1 : f (D.tr (MonoidAlgebra.single (φ g) 1)) = (D.map f).tr (MonoidAlgebra.single (φ g) 1) := by
    have := ((UpperTheory.V.CA.d_gmap D).2.2.1 f (MonoidAlgebra.single (φ g) 1)).2 1
    simpa [GDet.tr, MonoidAlgebra.mapRingHom_apply] using this.symm
  rw [h1, ← tr_comap', h, ← (UpperTheory.V.CA.d_toDet _ _).2.2.1, (UpperTheory.V.CA.d_toDet_ofRep).1 ρ,
    (UpperTheory.V.CA.d_ofRep _ _ _).2.2.1 hn, GDet.repAlg, MonoidAlgebra.lift_single, one_smul]
  congr 1

private theorem gram_at {n : ℕ} {A G H K : Type} [CommRing A] [Group G] [Group H] [CommRing K] (hn : 1 ≤ n)
    (D : GDet n A G) (f : A →+* K) (φ : H →* G) (ρ : H →* Matrix (Fin n) (Fin n) K)
    (h : (D.map f).comap φ = GDet.ofRep ρ) (g : Fin n × Fin n → H) :
    f (Matrix.det (Matrix.of fun a b => D.tr (MonoidAlgebra.single (φ (g a * g b)) 1))) =
      Matrix.det (Matrix.of fun a b => (ρ (g a) * ρ (g b)).trace) := by
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  rw [tr_at hn D f φ ρ h, map_mul]

private theorem isIrr_iff_span {Γ k : Type} [Group Γ] [Field k] [IsAlgClosed k] {n : ℕ} (hn : 1 ≤ n)
    (r : Γ →* GL (Fin n) k) : IsIrr r ↔ Submodule.span k (Set.range (mat r)) = ⊤ := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [← UpperTheory.V.AlgebraTools.Det.irrIffSpan]
  constructor
  · intro h N hN
    obtain ⟨-, -, h3⟩ := h
    exact h3 N le_top fun g v hv => hN g v hv
  · intro h
    refine ⟨top_ne_bot, fun g v _ => Submodule.mem_top, fun W _ hW => h W fun g v hv => hW g v hv⟩

end Abstract

end UpperTheory.V.J

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.IsLiftMap
section
noncomputable section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.Fr

namespace UpperTheory.V.J

section Lift

variable {O R C : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R]
  [CommRing C] [Algebra O C] [IsCO O C]

private theorem map_max_le (f : R →ₐ[O] C) :
    (maximalIdeal R).map (f : R →+* C) ≤ maximalIdeal C := by
  refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
  show f a ∈ maximalIdeal C
  rw [← res_eq_zero_iff O C, res_map, res_eq_zero_iff]
  exact ha

private theorem adic_map {Γ : Type} [TopologicalSpace Γ] (f : R →ₐ[O] C) {u : Γ → R}
    (hu : AdicCont (maximalIdeal R) u) : AdicCont (maximalIdeal C) fun g => f (u g) := by
  intro N
  have hle : maximalIdeal R ^ N ≤ (maximalIdeal C ^ N).comap (f : R →+* C) := by
    refine Ideal.map_le_iff_le_comap.1 ?_
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono (map_max_le f) N
  exact (hu N).comp (Ideal.quotientMap (maximalIdeal C ^ N) (f : R →+* C) hle)

variable {l : ℕ} [Fact l.Prime] {F : Frame l (ResidueField O)} {n : ℕ}

private theorem isLift_map (f : R →ₐ[O] C) {ρ : NRep F n R} (h : UpperTheory.V.Fr.IsLift O ρ) :
    UpperTheory.V.Fr.IsLift O (ρ.map (f : R →+* C)) := by
  obtain ⟨hc, hb, hd⟩ := h
  have hres : ((res O C : C →ₐ[O] ResidueField O) : C →+* ResidueField O).comp (f : R →+* C) =
      ((res O R : R →ₐ[O] ResidueField O) : R →+* ResidueField O) := by
    ext x
    exact res_map f x
  refine ⟨⟨fun i j => ?_, fun v i => ?_⟩, ?_, ?_⟩
  · exact adic_map f (hc.1 i j)
  · exact adic_map f (hc.2 v i)
  · rw [NRep.map_map, hres]
    exact hb
  · rw [NRep.map_map, hres]
    exact hd

end Lift

theorem det : Det := by
  intro l _ O _ _ _ _ F n S ξ D hD hr hψ
  haveI hc : IsAdicComplete (maximalIdeal O) O := UpperTheory.V.Fr.IsCoef.complete (l := l)
  haveI hn : IsNoetherianRing O := PrincipalIdealRing.isNoetherianRing
  haveI : IsCO O O := IsCO.self O
  haveI : IsCO O (TrivSqZeroExt O O) := co_sqz O O O (fun c => rfl)
  obtain ⟨y, hy⟩ := (der_hom O S.R O O ξ D).1 ⟨D, hD, rfl⟩
  let z : S.R →ₐ[O] TrivSqZeroExt O O := (TrivSqZeroExt.inlAlgHom O O O).comp ξ
  have key : ∀ a : S.R, D a = 0 → y a = z a := fun a ha =>
    TrivSqZeroExt.ext (hy a).1 (by rw [(hy a).2, ha]; rfl)
  have hmap : NRep.map (y : S.R →+* TrivSqZeroExt O O) S.ρ =
      NRep.map (z : S.R →+* TrivSqZeroExt O O) S.ρ := by
    apply NRep.ext
    · refine MonoidHom.ext fun g => Matrix.ext fun i j => ?_
      exact key _ (hr g i j)
    · funext v i
      refine MonoidHom.ext fun g => Units.ext ?_
      exact key _ (hψ v i g)
  obtain ⟨f, _, huniq⟩ := S.univ (TrivSqZeroExt O O) _ (isLift_map z S.lift)
  have e : y = z := (huniq y hmap).trans (huniq z rfl).symm
  ext a
  have h2 := (hy a).2
  rw [e] at h2
  rw [← h2]
  rfl

end UpperTheory.V.J

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.LamDer
section
set_option linter.overlappingInstances false

open Polynomial IsLocalRing UpperTheory.V.Alg

namespace UpperTheory.V.J

private theorem finite_of_alg {O R : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    [CommRing R] [IsDomain R] [Algebra O R] [IsCO O R] (hinj : Function.Injective (algebraMap O R))
    (hal : ∀ a : R, ∃ P : O[X], P ≠ 0 ∧ aeval a P = 0) : Module.Finite O R :=
  _root_.UpperTheory.Reformulated.B.Ra2.finite_of_alg hinj hal

private theorem exists_sqz {O Λ A N : Type} [CommRing O] [IsLocalRing O] [CommRing Λ] [Algebra O Λ] [CommRing A] [Algebra O A]
    [IsCO O A] [AddCommGroup N] [Module A N] [Module O N] [IsScalarTower O A N] [Module.Finite A N] (p : Λ →ₐ[O] A)
    (d : Λ →ₗ[O] N) (hd : ∀ f g, d (f * g) = p f • d g + p g • d f) :
    ∃ (T : Type) (_ : CommRing T) (_ : Algebra O T) (_ : IsCO O T) (f₀ f₁ : Λ →ₐ[O] T), ∀ a, f₀ a = f₁ a ↔ d a = 0 := by
  letI : Module Aᵐᵒᵖ N := Module.compHom N ((RingHom.id A).fromOpposite fun x y => Commute.all x y)
  haveI : IsCentralScalar A N := ⟨fun _ _ => rfl⟩
  haveI : SMulCommClass A Aᵐᵒᵖ N := ⟨fun a b n => smul_comm a (MulOpposite.unop b) n⟩
  haveI : IsScalarTower O Aᵐᵒᵖ N := ⟨fun c b n => by
    change (c • MulOpposite.unop b) • n = c • (MulOpposite.unop b • n)
    exact smul_assoc c _ n⟩
  letI : Algebra O (TrivSqZeroExt A N) := TrivSqZeroExt.algebra' O A N
  have h1 : d 1 = 0 := by
    have := hd 1 1
    simp only [mul_one, map_one, one_smul] at this
    exact left_eq_add.1 this
  let f₁ : Λ →ₐ[O] TrivSqZeroExt A N :=
    { toFun := fun a => TrivSqZeroExt.inl (p a) + TrivSqZeroExt.inr (d a)
      map_one' := TrivSqZeroExt.ext (by simp) (by simp [h1])
      map_zero' := TrivSqZeroExt.ext (by simp) (by simp)
      map_add' := fun a b => TrivSqZeroExt.ext (by simp) (by simp)
      map_mul' := fun a b => by
        refine TrivSqZeroExt.ext (by simp) ?_
        rw [TrivSqZeroExt.snd_mul]
        simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero, TrivSqZeroExt.snd_add,
          TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
        rw [hd, op_smul_eq_smul]
      commutes' := fun c => by
        refine TrivSqZeroExt.ext ?_ ?_
        · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
          exact p.commutes c
        · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
          rw [Algebra.algebraMap_eq_smul_one, map_smul, h1, smul_zero]
          rfl }
  refine ⟨TrivSqZeroExt A N, inferInstance, inferInstance, co_sqz O A N fun _ => rfl,
    (TrivSqZeroExt.inlAlgHom O A N).comp p, f₁, fun a => ⟨fun h => ?_, fun h => ?_⟩⟩
  · simpa [f₁] using (congrArg TrivSqZeroExt.snd h).symm
  · exact TrivSqZeroExt.ext (by simp [f₁]) (by simp [f₁, h])

private theorem exists_pair_of_der {O Λ K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CommRing Λ] [Algebra O Λ] [IsCO O Λ] [Field K] [Algebra O K]
    (hinj : Function.Injective (algebraMap O K)) (hal : ∀ a : K, ∃ P : O[X], P ≠ 0 ∧ aeval a P = 0) (p : Λ →ₐ[O] K)
    (d : Λ →ₗ[O] K) (hd : ∀ f g, d (f * g) = p f * d g + p g * d f) :
    ∃ (T : Type) (_ : CommRing T) (_ : Algebra O T) (_ : IsCO O T) (f₀ f₁ : Λ →ₐ[O] T), ∀ a, f₀ a = f₁ a ↔ d a = 0 := by
  classical
  have hsurj : Function.Surjective p.rangeRestrict := p.rangeRestrict_surjective
  haveI : IsCO O p.range := co_quot O Λ p.range p.rangeRestrict hsurj
  have hfin : Module.Finite O p.range := finite_of_alg
    (fun a b h => hinj (congrArg Subtype.val h))
    fun a => by
      obtain ⟨P, hP, h0⟩ := hal a
      exact ⟨P, hP, Subtype.ext (by rw [← Subalgebra.aeval_coe]; simpa using h0)⟩
  obtain ⟨G, hG⟩ := hfin.fg_top
  choose ℓ hℓ using hsurj
  obtain ⟨Q, hQ⟩ : (RingHom.ker p).FG := IsNoetherian.noetherian _
  let N : Submodule p.range K := Submodule.span p.range (d '' ((G.image ℓ : Finset Λ) ∪ Q : Finset Λ))
  have hsub : ∀ f ∈ (G.image ℓ : Finset Λ) ∪ Q, d f ∈ N := fun f hf =>
    Submodule.subset_span ⟨f, by exact_mod_cast hf, rfl⟩
  have hq : ∀ z ∈ Submodule.span Λ (Q : Set Λ), p z = 0 ∧ d z ∈ N := fun z hz => by
    induction hz using Submodule.span_induction with
    | mem g hg =>
      refine ⟨?_, hsub g (Finset.mem_union_right _ hg)⟩
      have : g ∈ RingHom.ker p := hQ ▸ Submodule.subset_span hg
      exact this
    | zero => exact ⟨map_zero p, by rw [map_zero]; exact zero_mem _⟩
    | add x y _ _ hx hy =>
      exact ⟨by rw [map_add, hx.1, hy.1, add_zero], by rw [map_add]; exact add_mem hx.2 hy.2⟩
    | smul b y _ hy =>
      refine ⟨by rw [smul_eq_mul, map_mul, hy.1, mul_zero], ?_⟩
      rw [smul_eq_mul, hd, hy.1, zero_mul, add_zero]
      exact N.smul_mem (p.rangeRestrict b) hy.2
  have hl : ∀ y ∈ Submodule.span O (G : Set p.range), ∃ g, p.rangeRestrict g = y ∧ d g ∈ N := fun y hy => by
    induction hy using Submodule.span_induction with
    | mem y hy =>
      exact ⟨ℓ y, hℓ y, hsub _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hy))⟩
    | zero => exact ⟨0, map_zero _, by rw [map_zero]; exact zero_mem _⟩
    | add x y _ _ hx hy =>
      obtain ⟨g, rfl, hg⟩ := hx
      obtain ⟨g', rfl, hg'⟩ := hy
      exact ⟨g + g', map_add _ _ _, by rw [map_add]; exact add_mem hg hg'⟩
    | smul c y _ hy =>
      obtain ⟨g, rfl, hg⟩ := hy
      refine ⟨c • g, map_smul _ _ _, ?_⟩
      rw [map_smul, ← algebraMap_smul p.range c (d g)]
      exact N.smul_mem _ hg
  have key : ∀ f, d f ∈ N := fun f => by
    obtain ⟨g, hg, hgN⟩ := hl (p.rangeRestrict f) (by rw [hG]; trivial)
    have h1 : f - g ∈ Submodule.span Λ (Q : Set Λ) := by
      have h2 : p (f - g) = 0 := by
        rw [map_sub]
        exact sub_eq_zero.2 (congrArg Subtype.val hg).symm
      have : f - g ∈ RingHom.ker p := RingHom.mem_ker.2 h2
      rw [← hQ] at this
      exact this
    have := add_mem hgN (hq _ h1).2
    rwa [← map_add, add_sub_cancel] at this
  let d' : Λ →ₗ[O] N :=
    { toFun := fun f => ⟨d f, key f⟩
      map_add' := fun a b => Subtype.ext (map_add d a b)
      map_smul' := fun c a => Subtype.ext (map_smul d c a) }
  haveI : Module.Finite p.range N := Module.Finite.iff_fg.2 (Submodule.fg_span (Set.Finite.image _ (Finset.finite_toSet _)))
  obtain ⟨T, i1, i2, i3, f₀, f₁, hf⟩ := exists_sqz p.rangeRestrict d' fun f g => Subtype.ext (hd f g)
  exact ⟨T, i1, i2, i3, f₀, f₁, fun a => (hf a).trans ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩⟩

private theorem map_mem_max {O Λ T : Type} [CommRing O] [IsLocalRing O] [CommRing Λ] [Algebra O Λ] [IsCO O Λ] [CommRing T]
    [Algebra O T] [IsCO O T] (f : Λ →ₐ[O] T) {x : Λ} (hx : x ∈ maximalIdeal Λ) : f x ∈ maximalIdeal T := by
  by_contra hn
  obtain ⟨b, hb⟩ := IsCO.res_surj (O := O) (f x)
  have hbu : IsUnit (algebraMap O T b) := by
    by_contra h
    have h2 := add_mem hb ((mem_maximalIdeal _).2 h)
    rw [sub_add_cancel] at h2
    exact hn h2
  have hb' : IsUnit (algebraMap O Λ b) := (isUnit_of_map_unit (algebraMap O T) b hbu).map _
  have hu : IsUnit (x - algebraMap O Λ b) := by
    by_contra h
    have h2 := (mem_maximalIdeal _).2 h
    have h3 := sub_mem hx h2
    rw [sub_sub_cancel] at h3
    exact (mem_maximalIdeal _).1 h3 hb'
  have h3 := hu.map f
  rw [map_sub, f.commutes] at h3
  exact (mem_maximalIdeal _).1 hb h3

private theorem adic_push {O Λ T Γ : Type} [CommRing O] [IsLocalRing O] [CommRing Λ] [Algebra O Λ] [IsCO O Λ] [CommRing T]
    [Algebra O T] [IsCO O T] [TopologicalSpace Γ] (f : Λ →ₐ[O] T) {u : Γ → Λ} (h : AdicCont (maximalIdeal Λ) u) :
    AdicCont (maximalIdeal T) fun g => f (u g) := fun N => by
  have hm : Ideal.map (f : Λ →+* T) (maximalIdeal Λ ^ N) ≤ maximalIdeal T ^ N := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 fun x hx => Ideal.mem_comap.2 (map_mem_max f hx)) N
  let φ : Λ ⧸ maximalIdeal Λ ^ N →+* T ⧸ maximalIdeal T ^ N :=
    Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (f : Λ →+* T)) fun a ha =>
      Ideal.Quotient.eq_zero_iff_mem.2 (hm (Ideal.mem_map_of_mem _ ha))
  exact (h N).comp φ

private theorem inert_push {l : ℕ} [Fact l.Prime] {F : W.GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    {n : ℕ} (r : W.Resid F O n) (Λ : W.LamObj r) {T : Type} [CommRing T] [Algebra O T] [IsCO O T] (f : Λ.Λ →ₐ[O] T) :
    W.IsInert r fun v i => W.pushCh (f : Λ.Λ →+* T) (Λ.κ v i) := fun v i => by
  obtain ⟨ψ, h, hk⟩ := Λ.inert v i
  refine ⟨W.pushCh (f : Λ.Λ →+* T) ψ, ⟨adic_push f h.cont, fun g => ?_, fun g => ?_⟩, ?_⟩
  · exact (res_map f _).trans (h.red g)
  · exact (congrArg f (h.mu g)).trans (f.commutes _)
  · change W.pushCh _ (Λ.κ v i) = _
    rw [hk]
    rfl

end UpperTheory.V.J

open UpperTheory.V.J UpperTheory.V.W UpperTheory.V.HV Formalism.ConjugateSelfDual ReciprocityTheory.Gal in
theorem UpperTheory.V.J.lamDer :
    UpperTheory.V.J.LamDer := by
  intro l _ L Ω _ _ _ _ _ _ s V c n r B Λ x m _ δ hδ hk a
  haveI : IsAdicComplete (maximalIdeal c.O) c.O := (UpperTheory.V.abelian₂.dvr_finite l c.O).1
  have hinj : Function.Injective (algebraMap c.O (Qbar l)) := Subtype.val_injective
  have hal : ∀ a : Qbar l, ∃ P : c.O[X], P ≠ 0 ∧ aeval a P = 0 := fun a => by
    have h1 : IsAlgebraic ℚ_[l] a := Algebra.IsAlgebraic.isAlgebraic a
    have h2 : IsAlgebraic ℤ_[l] a := (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] (Qbar l)).2 h1
    have h3 : IsAlgebraic c.O a := h2.extendScalars (UpperTheory.V.abelian₂.dvr_finite l c.O).2.2.2.1
    exact h3
  let t := Λ.toPair B.u
  let d : Λ.Λ →ₗ[c.O] Qbar l := δ.comp t.toLinearMap
  obtain ⟨T, _, _, _, f₀, f₁, hf⟩ := exists_pair_of_der hinj hal (x.comp t) d fun f g => by
    have := hδ (t f) (t g)
    simpa [d, map_mul] using this
  have hκ : ∀ v i (g : V.frame.Iv v), d ((Λ.κ v i g : Λ.Λˣ) : Λ.Λ) = 0 := fun v i g => by
    have h1 := congrArg Units.val (DFunLike.congr_fun (W.LamObj.toPair_spec r Λ B.u v i) g)
    have h2 : t ((Λ.κ v i g : Λ.Λˣ) : Λ.Λ) = (B.u.ψ v i g : B.Bˣ) := h1
    change δ (t _) = 0
    rw [h2]
    exact hk v i g g.2
  obtain ⟨u, -, hu⟩ := Λ.univ T _ (inert_push r Λ f₀)
  have e0 := hu f₀ fun _ _ => rfl
  have e1 := hu f₁ fun v i => MonoidHom.ext fun g => Units.ext ((hf _).2 (hκ v i g)).symm
  exact (hf a).1 (by rw [e0, ← e1])
end

