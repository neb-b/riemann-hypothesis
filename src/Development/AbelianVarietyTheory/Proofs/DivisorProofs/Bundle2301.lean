module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFrobGBaseChange
public import Formalism.SharpRestriction.Divisibility.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0806
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0837
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0832
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0685
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0702
public import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2201
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1979
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0275
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2213
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2111
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyPullbackStructureModuleIso
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory.FieldProj

theorem chi_eq_length_sections {X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X] (k : Type)
    [Field k] [Algebra k Γ(X, ⊤)] (F : X.Modules) [IsFiniteQC F] (h : suppDim F ≤ 0) :
    chi k F = (Module.length k (sectionsOn F ⊤)).toNat := by
  rw [chi_eq_hdim_zero k fun n hn => subsingleton_coh_of_suppDim_le_zero h hn, hdim_zero,
    Module.length_eq_rank, Cardinal.toNat_toENat]
  rfl

theorem dim_le_zero_of_finite_closed {T : Type} [TopologicalSpace T] {s : Set T} (hs : s.Finite)
    (hc : ∀ x ∈ s, IsClosed ({x} : Set T)) : topologicalKrullDim s ≤ 0 := by
  have : Finite s := hs.to_subtype
  have : T1Space s := ⟨fun x => by
    simpa [← Set.image_singleton, Set.preimage_image_eq _ Subtype.val_injective] using
      (hc x.1 x.2).preimage (continuous_subtype_val (p := (· ∈ s)))⟩
  exact topologicalKrullDim_zero_of_discreteTopology s

theorem eq_empty_of_dim_add_one_le_zero {T : Type} [TopologicalSpace T] {S : Set T}
    (h : topologicalKrullDim S + 1 ≤ ((0 : ℕ) : WithBot ℕ∞)) : S = ∅ := by
  by_contra hS
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 hS
  have hne : topologicalKrullDim S ≠ ⊥ :=
    mt topologicalKrullDim_eq_bot_iff.1 (not_isEmpty_iff.2 ⟨⟨x, hx⟩⟩)
  obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.1 hne
  rw [← ha] at h
  have h' : ((a + 1 : ℕ∞) : WithBot ℕ∞) ≤ ((0 : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast h
  rw [WithBot.coe_le_coe] at h'
  simp at h'

theorem closure_nonzeroLocus_eq_top {X : Scheme.{0}} [IsLocallyNoetherian X] {A : LB X}
    (hA : IsAmpleLB A) {S : Set X} (hS : S.Finite) :
    AddSubgroup.closure {c : Pic X | ∃ (N : LB X) (hN : N.IsLB) (t : N.Sec),
      S ⊆ nonzeroLocus t ∧ c = cls N hN} = ⊤ := by
  refine eq_top_iff.2 fun c _ => ?_
  obtain ⟨M, hM, rfl⟩ := cls_surj c
  obtain ⟨n, h₁, h₂⟩ := ((hA.eventually_exists_finite_subset_nonzeroLocus hM hS).and
    (hA.eventually_exists_finite_subset_nonzeroLocus (LB.isLB_triv X) hS)).exists
  obtain ⟨P, hP, eP⟩ := cls_surj (cls M hM + n • cls A hA.isLB)
  obtain ⟨Q, hQ, eQ⟩ := cls_surj (cls _ (LB.isLB_triv X) + n • cls A hA.isLB)
  obtain ⟨s, hs⟩ := h₁ P hP eP
  obtain ⟨t, ht⟩ := h₂ Q hQ eQ
  have e : cls M hM = cls P hP - cls Q hQ := by
    rw [eP, eQ, cls_triv, zero_add, add_sub_cancel_right]
  rw [e]
  exact sub_mem (AddSubgroup.subset_closure ⟨P, hP, s, hs, rfl⟩)
    (AddSubgroup.subset_closure ⟨Q, hQ, t, ht, rfl⟩)

theorem nonempty_pullback_structureModule_iso {X Y : Scheme.{0}} (f : X ⟶ Y) :
    Nonempty ((Scheme.Modules.pullback f).obj (QCoh.structureModule Y) ≅ QCoh.structureModule X) :=
  haveI : (TopologicalSpace.Opens.map f.base).Final :=
    final_of_representablyFlat _
  haveI : IsIso (SheafOfModules.pullbackObjUnitToUnit.{0} f.toRingCatSheafHom) := inferInstance
  ⟨asIso (SheafOfModules.pullbackObjUnitToUnit.{0} f.toRingCatSheafHom)⟩

section Main

variable {k : Type} [Field k] {X Y : Scheme.{0}} [Algebra k Γ(X, ⊤)] [Algebra k Γ(Y, ⊤)]
  (f : X ⟶ Y) (hf : ∀ r : k, f.appTop (algebraMap k Γ(Y, ⊤) r) = algebraMap k Γ(X, ⊤) r)
  (V : Y.Opens) (n : ℕ) (hV : IsAffineOpen V) (hV' : IsAffineOpen (f ⁻¹ᵁ V))
  (hfree : letI := (f.app V).hom.toAlgebra
    Module.Free Γ(Y, V) Γ(X, f ⁻¹ᵁ V) ∧ Module.Finite Γ(Y, V) Γ(X, f ⁻¹ᵁ V) ∧
      Module.finrank Γ(Y, V) Γ(X, f ⁻¹ᵁ V) = n)

include hf hV hV' hfree

theorem chi_pullback_eq_mul [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    (G : Y.Modules) [IsFiniteQC G] (hdim : suppDim G ≤ 0) (hsub : support G ⊆ (V : Set Y)) :
    chi k ((Scheme.Modules.pullback f).obj G) = n * chi k G := by
  have hfin : (support G).Finite := finite_support_of_suppDim_le_zero hdim
  have hcl : ∀ x ∈ support G, IsClosed ({x} : Set Y) := fun x hx =>
    isClosed_singleton_of_suppDim_le_zero hdim hx
  have hsupp' : support ((Scheme.Modules.pullback f).obj G) = f.base ⁻¹' support G :=
    QCoh.support_pullback f G
  have hpts : ∀ y ∈ support ((Scheme.Modules.pullback f).obj G), IsClosed ({y} : Set X) := by
    intro y hy
    rw [hsupp'] at hy
    exact (fibre_finite_isClosed_of_affine_finite f V hV hV' hfree.2.1 _ (hsub hy) (hcl _ hy)).2 y rfl
  have hfin' : (support ((Scheme.Modules.pullback f).obj G)).Finite := by
    rw [hsupp']
    refine (Set.Finite.biUnion (t := fun x => f.base ⁻¹' {x}) hfin fun x hx =>
      (fibre_finite_isClosed_of_affine_finite f V hV hV' hfree.2.1 _ (hsub hx) (hcl _ hx)).1).subset
      fun y hy => ?_
    exact Set.mem_biUnion hy rfl
  have hdim' : suppDim ((Scheme.Modules.pullback f).obj G) ≤ 0 :=
    dim_le_zero_of_finite_closed hfin' hpts
  rw [chi_eq_length_sections k _ hdim, chi_eq_length_sections k _ hdim',
    length_sectionsOn_top_eq_sum_of_separating G k (fun _ : Unit => V)
      (fun x hx => Set.mem_iUnion.2 ⟨(), hsub hx⟩) (fun i j hij => absurd rfl hij),
    length_sectionsOn_top_eq_sum_of_separating _ k (fun _ : Unit => f ⁻¹ᵁ V) ?_
      (fun i j hij => absurd rfl hij)]
  · simp_rw [length_sectionsOn_pullback_of_free k f hf _ n hV hV' hfree G]
    rw [← Finset.mul_sum, ENat.toNat_mul]
    simp
  · intro y hy
    rw [hsupp'] at hy
    exact Set.mem_iUnion.2 ⟨(), hsub hy⟩

theorem diffVanish_chiPic_pullback_sub [AlgebraicGeometry.IsNoetherian X]
    [AlgebraicGeometry.IsNoetherian Y] {A : LB Y} (hA : IsAmpleLB A)
    (hX : ∀ (F : X.Modules) [IsFiniteQC F], FiniteCohTwists k F)
    (hY : ∀ (F : Y.Modules) [IsFiniteQC F], FiniteCohTwists k F) :
    ∀ (m : ℕ) (G : Y.Modules) [IsFiniteQC G], suppDim G ≤ m →
      topologicalKrullDim (support G ∩ (V : Set Y)ᶜ : Set Y) + 1 ≤ (m : WithBot ℕ∞) →
      DiffVanish m ((chiPic k ((Scheme.Modules.pullback f).obj G) ∘ pull f) -
        (AddMonoidHom.mulLeft (n : ℤ)) ∘ chiPic k G) := by
  intro m
  induction m with
  | zero =>
    intro G _ h0 hk
    have hGU : support G ⊆ (V : Set Y) := fun x hx => by
      by_contra h
      have := eq_empty_of_dim_add_one_le_zero hk
      exact (Set.eq_empty_iff_forall_notMem.1 this) x ⟨hx, h⟩
    refine diffVanish_zero_iff.2 (funext fun c => ?_)
    obtain ⟨M, hM, rfl⟩ := cls_surj c
    have hM' := Semi.LB.isLB_pull hM f
    have := isFiniteQC_twist (F := G) hM
    have e := Twist.pullbackIso G f hM
    have hb := chi_pullback_eq_mul f hf V n hV hV' hfree (twist G M) (by rwa [suppDim_twist hM])
      (by rwa [support_twist hM])
    simp only [Pi.sub_apply, Function.comp_apply, Pi.zero_apply, AddMonoidHom.coe_mulLeft]
    rw [← cls_pull hM f hM', chiPic_cls, chiPic_cls, ← chi_congr k e, hb, sub_self]
  | succ m ih =>
    intro G _ hk hUk
    set G' := (Scheme.Modules.pullback f).obj G
    have hZ : IsClosed (support G ∩ (V : Set Y)ᶜ) :=
      (isClosed_support (F := G)).inter V.isOpen.isClosed_compl
    obtain ⟨S₃, hS₃, hS₃'⟩ := exists_finite_topologicalKrullDim_inter_add_one_le _ hZ
    let S : Set Y := assPoints G ∪ f.base '' assPoints G' ∪ S₃
    have hS : S.Finite := ((finite_assPoints G).union ((finite_assPoints G').image _)).union hS₃
    refine diffVanish_of_generators (closure_nonzeroLocus_eq_top hA hS) fun g hg => ?_
    obtain ⟨N, hN, t, hSt, e⟩ := hg 0
    have hN' := Semi.LB.isLB_pull hN f
    haveI hmono : Mono (cutHom G hN t) :=
      (mono_cutHom_iff G hN t).2 fun x hx => hSt (Or.inl (Or.inl hx))
    haveI hmono' : Mono (cutHom G' hN' (secPull t f)) :=
      (mono_cutHom_iff G' hN' _).2 fun x hx => by
        rw [nonzeroLocus_secPull]
        exact hSt (Or.inl (Or.inr ⟨x, hx, rfl⟩))
    have h₁ := bwdDiff_chiPic_eq_chiPic_cut hN t (hY G)
    have h₂ := bwdDiff_chiPic_eq_chiPic_cut hN' (secPull t f) (hX G')
    obtain ⟨ec⟩ := cut_pullback_iso f G hN t hN'
    have key : bwdDiff (cls N hN) ((chiPic k G' ∘ pull f) -
        (AddMonoidHom.mulLeft (n : ℤ)) ∘ chiPic k G) =
        (chiPic k ((Scheme.Modules.pullback f).obj (cut G hN t)) ∘ pull f) -
          (AddMonoidHom.mulLeft (n : ℤ)) ∘ chiPic k (cut G hN t) := by
      funext c
      have a₁ := congrFun h₁ c
      have a₂ := congrFun h₂ (pull f c)
      rw [chiPic_congr k ec.symm] at a₂
      simp only [bwdDiff_apply] at a₁ a₂
      simp only [bwdDiff_apply, Pi.sub_apply, Function.comp_apply,
        AddMonoidHom.coe_mulLeft, map_sub, cls_pull hN f hN'] at a₂ ⊢
      rw [← a₁, ← a₂]
      ring
    rw [← Fin.cons_self_tail g, multiDiff_cons', e, key]
    refine ih (cut G hN t) (suppDim_cut_le G hN t hk) ?_ _
    have hdim := hS₃' (nonzeroLocus t : Set Y)ᶜ (nonzeroLocus t).isOpen.isClosed_compl
      (Set.disjoint_compl_right_iff_subset.2 fun x hx => hSt (Or.inr hx))
    have hZk : topologicalKrullDim (support G ∩ (V : Set Y)ᶜ : Set Y) ≤ m :=
      ENat.WithBot.add_le_add_one_right_iff.1 (hUk.trans_eq (Nat.cast_succ m))
    refine le_trans ?_ (hdim.trans hZk)
    refine add_le_add_left (topologicalKrullDim_mono ?_) 1
    rw [support_cut]
    rintro x ⟨⟨hx, hx'⟩, hxU⟩
    exact ⟨⟨hx, hxU⟩, hx'⟩

end Main

theorem interNum_pull_eq_mul (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral Y]
    (sY : Y ⟶ Sp k) (f : X ⟶ Y) (hX : IsProjOver (f ≫ sY)) (hY : IsProjOver sY)
    (V : Y.Opens) (n : ℕ) (hgen : genericPoint Y ∈ V) (hV : IsAffineOpen V)
    (hV' : IsAffineOpen (f ⁻¹ᵁ V))
    (hfree : letI := (f.app V).hom.toAlgebra
      Module.Free Γ(Y, V) Γ(X, f ⁻¹ᵁ V) ∧ Module.Finite Γ(Y, V) Γ(X, f ⁻¹ᵁ V) ∧
        Module.finrank Γ(Y, V) Γ(X, f ⁻¹ᵁ V) = n)
    (d : ℕ) (hd : topologicalKrullDim Y ≤ d) (L : Fin d → LB Y) (hL : ∀ i, (L i).IsLB) :
    letI := GlobalTheory.algebraΓOfHom (f ≫ sY); letI := GlobalTheory.algebraΓOfHom sY
    GlobalTheory.interNum k (GlobalTheory.QCoh.structureModule X) (fun i => (L i).pull f) =
      (n : ℤ) * GlobalTheory.interNum k (GlobalTheory.QCoh.structureModule Y) L := by
  letI := GlobalTheory.algebraΓOfHom (f ≫ sY)
  letI := GlobalTheory.algebraΓOfHom sY
  have := isNoetherian_of_isProjOver hX
  have := isNoetherian_of_isProjOver hY
  obtain ⟨-, A, hA⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hY
  have hf : ∀ r : k, f.appTop (algebraMap k Γ(Y, ⊤) r) = algebraMap k Γ(X, ⊤) r := fun _ => rfl
  have hVd : topologicalKrullDim ((V : Set Y)ᶜ : Set Y) + 1 ≤ (d : WithBot ℕ∞) := by
    refine (topologicalKrullDim_add_one_le V.isOpen.isClosed_compl isClosed_univ
      fun x _ => ⟨genericPoint Y, trivial, fun h => h hgen, genericPoint_specializes x⟩).trans ?_
    exact (topologicalKrullDim_subspace_le _ _).trans hd
  have hD := diffVanish_chiPic_pullback_sub f hf V n hV hV' hfree hA
    (fun F _ => finiteCohTwists_of_isProjOver (fun _ => rfl) F hX)
    (fun F _ => finiteCohTwists_of_isProjOver (fun _ => rfl) F hY) d (QCoh.structureModule Y)
    (suppDim_structureModule.trans_le hd)
    ((add_le_add_left (topologicalKrullDim_mono Set.inter_subset_right) 1).trans hVd)
  obtain ⟨e⟩ := nonempty_pullback_structureModule_iso f
  have h0 := congrFun (hD fun i => cls (L i) (hL i)) 0
  simp only [multiDiff_sub, multiDiff_map, multiDiff_comap, Pi.sub_apply, Pi.zero_apply,
    Function.comp_apply, chiPic_congr k e, map_zero] at h0
  rw [AddMonoidHom.coe_mulLeft, sub_eq_zero] at h0
  rw [interNum_eq_multiDiff k _ hL,
    interNum_eq_multiDiff k _ fun i => Semi.LB.isLB_pull (hL i) f]
  exact h0

end GlobalTheory.FieldProj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptySmoothLiftAffineThickenings
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.SmoothLift.LiftEx

theorem isPDNilpotent_map {R A : Type} [CommRing R] [CommRing A] {I : Ideal R} {κ : DividedPowers I} (f : R →+* A)
    {δ : DividedPowers (I.map f)} (h : IsDPMorphism κ δ f) (hκ : IsNilDP κ) : IsNilDP δ := by
  obtain ⟨N, hN⟩ := (isDPNilpotent_iff_exists_isLevel κ).1 hκ
  refine (isDPNilpotent_iff_exists_isLevel δ).2 ⟨N, ?_⟩
  have := fil_le_map_fil R I κ A _ δ f h rfl N
  rw [show fil κ N = ⊥ from hN, Ideal.map_bot] at this
  exact le_bot_iff.1 this

theorem isDPMorphism_algHom {R A A' : Type} [CommRing R] [CommRing A] [CommRing A'] [Algebra R A] [Algebra R A']
    {I : Ideal R} {κ : DividedPowers I} {δ : DividedPowers (I.map (algebraMap R A))}
    {δ' : DividedPowers (I.map (algebraMap R A'))} (h : IsDPMorphism κ δ (algebraMap R A))
    (h' : IsDPMorphism κ δ' (algebraMap R A')) (φ : A →ₐ[R] A') : IsDPMorphism δ δ' (φ : A →+* A') := by
  refine IsDPMorphism.on_span δ δ' (S := algebraMap R A '' I) rfl ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    rw [RingHom.coe_coe, φ.commutes]
    exact Ideal.mem_map_of_mem _ ha
  · rintro n _ ⟨a, ha, rfl⟩
    rw [h.2 a ha, RingHom.coe_coe, φ.commutes, φ.commutes, h'.2 a ha]

abbrev ext (D : Data) (U : D.X.affineOpens) : Ideal (Sec D.s U.1) := D.I.map (algebraMap D.R (Sec D.s U.1))

theorem exists_pt (D : Data) (U : D.X.affineOpens) : ∃ x : Sp (Sec D.s U.1 ⧸ ext D U) ⟶ D.X₀,
    x ≫ D.i = spMap (Ideal.Quotient.mk (ext D U)) ≫ affPt D.s U ∧
    x ≫ D.t = spMap ((Ideal.Quotient.mk (ext D U)).comp (algebraMap D.R (Sec D.s U.1))) := by
  obtain ⟨s₀, hpb, ht⟩ := D.red
  let q : D.R ⧸ D.I →+* Sec D.s U.1 ⧸ ext D U :=
    Ideal.quotientMap (ext D U) (algebraMap D.R (Sec D.s U.1)) Ideal.le_comap_map
  have hq : spMap q ≫ spMap (Ideal.Quotient.mk D.I) =
      spMap ((Ideal.Quotient.mk (ext D U)).comp (algebraMap D.R (Sec D.s U.1))) := by
    rw [← Cris.spMap_comp]; rfl
  refine ⟨hpb.lift (spMap (Ideal.Quotient.mk (ext D U)) ≫ affPt D.s U) (spMap q) ?_, hpb.lift_fst _ _ _, ?_⟩
  · rw [hq, Category.assoc, affPt_w, Cris.spMap_comp]
  · rw [ht, ← Category.assoc, hpb.lift_snd, hq]

theorem exists_dp (D : Data) (U : D.X.affineOpens) :
    ∃ δ : DividedPowers (ext D U), IsDPMorphism D.κ δ (algebraMap D.R (Sec D.s U.1)) := by
  haveI := D.sec_smooth U
  exact _root_.GlobalTheory.DPFlat.exists_isDPMorphism_of_flat D.R (Sec D.s U.1) D.I D.κ

theorem thick_hom_ext {R : Type} [CommRing R] {I : Ideal R}
    {X : Scheme} {γ : DividedPowers I} {s : X ⟶ Sp R}
    {T T' : Thick γ s} {f g : T ⟶ T'}
    (h : ∀ b, f.φ b = g.φ b) : f = g := by
  rcases f with ⟨φ, φ₀, comm, dp, pt⟩
  rcases g with ⟨ψ, ψ₀, comm', dp', pt'⟩
  obtain rfl : φ = ψ := AlgHom.ext h
  obtain rfl : φ₀ = ψ₀ := RingHom.ext fun c ↦ by
    obtain ⟨b, rfl⟩ := T.surj c
    rw [comm, comm']
  rfl

theorem nonempty_lift : ∀ D : Data, Nonempty (Lift D) := by
  intro D
  choose δ hδ using exists_dp D
  choose x hx hw using exists_pt D
  haveI := D.mono_i
  let T : D.X.affineOpens → Thick D.κ D.t := fun U ↦
    { B := Sec D.s U.1
      J := ext D U
      δ := δ U
      nil := isPDNilpotent_map _ (hδ U) D.nil
      dp := hδ U
      B₀ := Sec D.s U.1 ⧸ ext D U
      π := Ideal.Quotient.mk _
      surj := Ideal.Quotient.mk_surjective
      ker := fun _ ↦ Ideal.Quotient.eq_zero_iff_mem
      x := x U
      w := hw U }
  let m : ∀ {U V : D.X.affineOpens}, V.1 ≤ U.1 → (T U ⟶ T V) := fun {U V} h ↦
    { φ := Sec.res D.s h
      φ₀ := Ideal.quotientMap (ext D V) (Sec.res D.s h : Sec D.s U.1 →+* Sec D.s V.1)
        (Ideal.map_le_iff_le_comap.1 (isDPMorphism_algHom (hδ U) (hδ V) (Sec.res D.s h)).1)
      comm := fun _ ↦ rfl
      dp := isDPMorphism_algHom (hδ U) (hδ V) (Sec.res D.s h)
      pt := by
        rw [← cancel_mono D.i, Category.assoc]
        change spMap _ ≫ x U ≫ D.i = x V ≫ D.i
        rw [hx, hx, ← affPt_res D.s h, ← Category.assoc, ← Category.assoc, ← Cris.spMap_comp, ← Cris.spMap_comp]
        rfl }
  refine ⟨{ L := { obj := fun U ↦ T U.unop
                   map := fun a ↦ m (leOfHom a.unop)
                   map_id := fun U ↦ thick_hom_ext fun b ↦ mp_id (OAff D.s) U b
                   map_comp := fun a b ↦ thick_hom_ext fun c ↦ mp_comp (OAff D.s) a b c }
            e := fun _ ↦ AlgEquiv.refl
            nat := fun _ _ ↦ rfl
            gen := fun _ ↦ rfl
            pt := fun U ↦ (hx U.unop).symm
            mem := fun U ↦ ?_ }⟩
  change ⊤ ≤ (x U.unop ≫ D.i) ⁻¹ᵁ U.unop.1
  rw [hx, Scheme.Hom.comp_preimage]
  have : affPt D.s U.unop ⁻¹ᵁ U.unop.1 = ⊤ := U.unop.2.fromSpec_preimage_self
  rw [this]
  exact le_rfl

end GlobalTheory.SmoothLift.LiftEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormNotMemIff
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem algebraMap_norm_mem_span_singleton (A B : Type) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] [Module.Free A B] (f : B) :
    algebraMap A B (Algebra.norm A f) ∈ Ideal.span {f} := by
  set g : B →ₗ[A] B := Algebra.lmul A B f with hg
  set p := g.charpoly
  obtain ⟨q, hq⟩ := Polynomial.X_dvd_sub_C (p := p)
  have h0 : Polynomial.aeval f p = 0 := by
    have h1 : Polynomial.aeval g p = 0 := LinearMap.aeval_self_charpoly g
    rw [hg, Polynomial.aeval_algHom_apply] at h1
    have h2 := congrArg (fun u : B →ₗ[A] B => u 1) h1
    simpa using h2
  have h3 := congrArg (Polynomial.aeval f) hq
  simp only [map_sub, Polynomial.aeval_C, map_mul, Polynomial.aeval_X, h0, zero_sub] at h3
  rw [Algebra.norm_apply, LinearMap.det_eq_sign_charpoly_coeff, map_mul,
    show algebraMap A B (g.charpoly.coeff 0) = -(f * Polynomial.aeval f q) by
      rw [← h3, neg_neg]]
  exact Ideal.mul_mem_left _ _ (neg_mem (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self f)))

theorem norm_not_mem_iff (A B : Type) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] [Module.Free A B] (f : B) (P : PrimeSpectrum A) :
    Algebra.norm A f ∉ P.asIdeal ↔
      ∀ Q : PrimeSpectrum B, Q.asIdeal.comap (algebraMap A B) = P.asIdeal → f ∉ Q.asIdeal := by
  constructor
  · intro hN Q hQ hf
    apply hN
    rw [← hQ, Ideal.mem_comap]
    exact (Ideal.span_singleton_le_iff_mem _).mpr hf (algebraMap_norm_mem_span_singleton A B f)
  · intro h hN
    let Rₘ := Localization.AtPrime P.asIdeal
    let Sₘ := Localization (Algebra.algebraMapSubmonoid B P.asIdeal.primeCompl)
    have hnu : ¬ IsUnit (algebraMap B Sₘ f) := by
      intro hu
      have h1 := hu.map (Algebra.norm Rₘ (S := Sₘ))
      rw [Algebra.norm_localization A P.asIdeal.primeCompl] at h1
      exact (IsLocalization.AtPrime.isUnit_to_map_iff Rₘ P.asIdeal _).mp h1 hN
    obtain ⟨M, hM, hfM⟩ := exists_max_ideal_of_mem_nonunits hnu
    haveI : Module.Finite Rₘ Sₘ := Module.Finite.of_basis
      ((Module.Free.chooseBasis A B).localizationLocalization Rₘ P.asIdeal.primeCompl Sₘ)
    have hMc : M.comap (algebraMap Rₘ Sₘ) = IsLocalRing.maximalIdeal Rₘ :=
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := Rₘ) M)
    refine h ⟨M.comap (algebraMap B Sₘ), hM.isPrime.comap _⟩ ?_ hfM
    show (M.comap (algebraMap B Sₘ)).comap (algebraMap A B) = P.asIdeal
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq A Rₘ Sₘ,
      ← Ideal.comap_comap, hMc]
    exact Localization.AtPrime.under_maximalIdeal

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalFiniteDominantRefinement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
open CategoryTheory.Limits TopologicalSpace

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mean4O.CommonGen

theorem exists_common (F : Type) [Field F] [NumberField F] (Y : Var F) (V₁ V₂ : Mean4O.Cover Y) :
    ∃ (G : Scheme.{0}) (_ : IsIntegral G) (_ : GlobalTheory.IsNormalScheme G) (g : G ⟶ V₁.G) (k : G ⟶ V₂.G),
      IsFinite g ∧ IsDominant g ∧ k ≫ V₂.π = g ≫ V₁.π := by
  have : IsProper V₁.p := CommonModel.isProper_of_isProjOver V₁.ar.isProjOver
  have : IsProper (V₁.π ≫ Y.str) := MorphismProperty.of_isPullback V₁.pb ‹IsProper V₁.p›
  let Q : Scheme.{0} := pullback V₁.π V₂.π
  let a : Q ⟶ V₁.G := pullback.fst V₁.π V₂.π
  let b : Q ⟶ V₂.G := pullback.snd V₁.π V₂.π
  have : IsFinite a := inferInstanceAs (IsFinite (pullback.fst V₁.π V₂.π))
  have hs : Surjective a := inferInstanceAs (Surjective (pullback.fst V₁.π V₂.π))
  obtain ⟨η, hη⟩ := hs.surj (genericPoint V₁.G)
  let s : Q ⟶ Spec (.of F) := a ≫ V₁.π ≫ Y.str
  have : IsProper s := inferInstanceAs (IsProper (a ≫ V₁.π ≫ Y.str))
  have : CharZero (Q.residueField η) := charZero_of_injective_ringHom
    ((Scheme.ΓSpecIso (.of F)).inv ≫ s.appTop ≫ Q.Γevaluation η).hom.injective
  let u : Spec (.of (Q.residueField η)) ⟶ Q := Spec.map (Q.residue η) ≫ Q.fromSpecStalk η
  have hfin : IsFinite u.fromNormalization :=
    GlobalTheory.isFinite_fromNormalization_SpecMap_fromSpecStalk s η (L := Q.residueField η) (Q.residue η)
      (RingHom.FiniteType.of_surjective _ (Q.residue_surjective η)).essFiniteType
  have hu : u (IsLocalRing.closedPoint (Q.residueField η)) = η :=
    Scheme.fromSpecResidueField_apply η _
  have : IsDominant (u ≫ a) := ⟨(dense_iff_closure_eq.2 (genericPoint_spec V₁.G)).mono
    (Set.singleton_subset_iff.2 ⟨IsLocalRing.closedPoint (Q.residueField η), by
      change a (u _) = _
      rw [hu, hη]⟩)⟩
  have hd : IsDominant (u.fromNormalization ≫ a) := by
    have : IsDominant (u.toNormalization ≫ u.fromNormalization ≫ a) := by
      rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization]; infer_instance
    exact IsDominant.of_comp u.toNormalization _
  refine ⟨u.normalization, inferInstance, GlobalTheory.IsNormalScheme.normalization_of_isIntegral u,
    u.fromNormalization ≫ a, u.fromNormalization ≫ b, inferInstance, hd, ?_⟩
  rw [Category.assoc, Category.assoc, pullback.condition]

end GlobalTheory.Mean4O.CommonGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiConditionOfGrpPullbackSquareStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rosatiCondition_of_grpPullback_square : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (S H E : Scheme.{0}) (A₀ : Over S) [GrpObj A₀] (P : LB (G2 A₀).left), P.IsLB → ∀ (AH : Over H) [GrpObj AH] (AE : Over E) [GrpObj AE] (f : E ⟶ H) (φ : AE.left ⟶ AH.left) (φ₂ : (G2 AE).left ⟶ (G2 AH).left) (φ₂H : (G2 AH).left ⟶ (G2 A₀).left) (actH : OActN D.O AH) (actE : OActN D.O AE), IsGrpPullback AE AH f φ → IsSquare φ φ₂ → (∀ a : D.O, (actE.act a).left ≫ φ = φ ≫ (actH.act a).left) → RosatiFor D actH (P.pull φ₂H) → RosatiFor D actE (P.pull (φ₂ ≫ φ₂H)) := by
  first | (exact @GlobalTheory.RosatiPull.rosatiFor_pull) | (exact GlobalTheory.RosatiPull.rosatiFor_pull) | (intros; apply GlobalTheory.RosatiPull.rosatiFor_pull <;> assumption)
end

