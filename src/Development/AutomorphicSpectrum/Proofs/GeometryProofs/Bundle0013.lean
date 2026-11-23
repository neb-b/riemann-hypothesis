module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0001
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0008

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenPtSpecializes
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.CptInh

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem dom (ξ : Spec (CommRingCat.of Ω) ⟶ X) (h : IsCptGen ξ) (p : Cpt ξ) :
    IsDomain (X.presheaf.stalk p.1) := by
  exact Function.Injective.isDomain (genMap ξ p) (h.inj p)

theorem nogen (ξ : Spec (CommRingCat.of Ω) ⟶ X) (h : IsCptGen ξ) (y : X) (hy : y ⤳ genPt ξ) :
    y = genPt ξ := by
  have hy' : y ∈ Set.range (X.fromSpecStalk (genPt ξ)) := by
    rw [Scheme.range_fromSpecStalk]
    exact hy
  obtain ⟨q, hq⟩ := hy'
  obtain ⟨f, hf⟩ : ∃ f : X.presheaf.stalk (genPt ξ) →+* Ω, Function.Bijective f :=
    ⟨(Scheme.stalkClosedPointTo ξ).hom, h.bij⟩
  have hmax : ∀ x ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (genPt ξ)), x = 0 := by
    intro x hx
    by_contra hne
    have h1 : f x ≠ 0 := by
      intro h0
      apply hne
      apply hf.1
      rw [h0, map_zero]
    obtain ⟨v, hv⟩ := hf.2 (f x)⁻¹
    have hxv : x * v = 1 := hf.1 (by rw [map_mul, hv, mul_inv_cancel₀ h1, map_one])
    exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal x).mp hx) (IsUnit.of_mul_eq_one v hxv)
  have hq' : q = IsLocalRing.closedPoint (X.presheaf.stalk (genPt ξ)) := by
    apply PrimeSpectrum.ext
    apply le_antisymm
    · exact IsLocalRing.le_maximalIdeal (PrimeSpectrum.isPrime q).ne_top
    · intro x hx
      rw [hmax x hx]
      exact zero_mem _
  rw [← hq, hq']
  exact Scheme.fromSpecStalk_closedPoint

end GlobalTheory.CompanionTheory.Ar.CptInh
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericVanishingStalkVanishing
section
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.CompanionTheory.Ggeo

theorem germ_vanish_of_generic_dominated : ∀ (X : Scheme.{0}) [IsReduced X] (Ω O : Type) [Field Ω] [CommRing O] (ξ : Spec (CommRingCat.of Ω) ⟶ X), (∀ q : X, ξ (IsLocalRing.closedPoint Ω) ⤳ q) → ∀ (s₀ : X ⟶ Spec (CommRingCat.of O)) (gm : O →+* Ω), ξ ≫ s₀ = Spec.map (CommRingCat.ofHom gm) → ∀ (x : X) (a : O), gm a = 0 → (Spec.preimage (X.fromSpecStalk x ≫ s₀)).hom a = 0 :=
  PositivityTheory.UnitarySelfGeneration.germ_vanishes_of_generic_vanishing

end GlobalTheory.CompanionTheory.Ggeo
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermGenPtInjectiveRangeRegAt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.RegSec

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)

noncomputable def val (U : X.Opens) (h : genPt ξ ∈ U) : Γ(X, U) →+* Ω :=
  (X.presheaf.germ U (genPt ξ) h ≫ Scheme.stalkClosedPointTo ξ).hom

theorem genMap_germ (U : X.Opens) (h : genPt ξ ∈ U) {q : X} (hq : genPt ξ ⤳ q) (hqU : q ∈ U)
    (s : Γ(X, U)) :
    genMap ξ ⟨q, hq⟩ ((X.presheaf.germ U q hqU).hom s) = val ξ U h s := by
  have key : ∀ {A B C : CommRingCat} (f : A ⟶ B) (g : B ⟶ C) (x : A), (f ≫ g).hom x = g.hom (f.hom x) :=
    fun _ _ _ => rfl
  unfold genMap val
  rw [← X.presheaf.germ_stalkSpecializes hqU hq]
  exact (key (X.presheaf.stalkSpecializes hq) (Scheme.stalkClosedPointTo ξ) _).trans
    ((congrArg (fun y => (Scheme.stalkClosedPointTo ξ).hom y)
      (key (X.presheaf.germ U q hqU) (X.presheaf.stalkSpecializes hq) s).symm).trans
      (key (X.presheaf.germ U q hqU ≫ X.presheaf.stalkSpecializes hq)
        (Scheme.stalkClosedPointTo ξ) s).symm)

theorem val_res {V U : X.Opens} (i : V ⟶ U) (hV : genPt ξ ∈ V) (hU : genPt ξ ∈ U) (s : Γ(X, U)) :
    val ξ V hV ((X.presheaf.map i.op).hom s) = val ξ U hU s := by
  have key : ∀ {A B C : CommRingCat} (f : A ⟶ B) (g : B ⟶ C) (x : A), (f ≫ g).hom x = g.hom (f.hom x) :=
    fun _ _ _ => rfl
  unfold val
  rw [← X.presheaf.germ_res i (genPt ξ) hV]
  exact (key (X.presheaf.germ V (genPt ξ) hV) (Scheme.stalkClosedPointTo ξ) _).trans
    ((congrArg (fun y => (Scheme.stalkClosedPointTo ξ).hom y)
      (key (X.presheaf.map i.op) (X.presheaf.germ V (genPt ξ) hV) s).symm).trans
      (key (X.presheaf.map i.op ≫ X.presheaf.germ V (genPt ξ) hV)
        (Scheme.stalkClosedPointTo ξ) s).symm)

theorem val_injective (hξ : IsCptGen ξ) (U : X.Opens) (h : genPt ξ ∈ U)
    (hU : ∀ q : X, q ∈ U → genPt ξ ⤳ q) : Function.Injective (val ξ U h) := by
  intro s t hst
  refine TopCat.Presheaf.section_ext X.sheaf U s t (fun q hq => ?_)
  have hq' := hU q hq
  apply hξ.inj ⟨q, hq'⟩
  exact (genMap_germ ξ U h hq' hq s).trans (hst.trans (genMap_germ ξ U h hq' hq t).symm)

theorem mem_range_val_iff (hξ : IsCptGen ξ) (U : X.Opens) (h : genPt ξ ∈ U)
    (hU : ∀ q : X, q ∈ U → genPt ξ ⤳ q) (a : Ω) :
    a ∈ (val ξ U h).range ↔ ∀ q : Cpt ξ, q.1 ∈ U → a ∈ regAt ξ q := by
  constructor
  · intro ha q hqU
    obtain ⟨s, rfl⟩ := RingHom.mem_range.mp ha
    exact RingHom.mem_range.mpr ⟨(X.presheaf.germ U q.1 hqU).hom s, genMap_germ ξ U h q.2 hqU s⟩
  · intro H
    have loc : ∀ q : U, ∃ (W : X.Opens) (t : Γ(X, W)) (_ : (q : X) ∈ W) (hg : genPt ξ ∈ W),
        val ξ W hg t = a := by
      rintro ⟨q, hq⟩
      have hq' : genPt ξ ⤳ q := hU q hq
      obtain ⟨x, hx⟩ := RingHom.mem_range.mp (H ⟨q, hq'⟩ hq)
      obtain ⟨W, hqW, t, ht⟩ := TopCat.Presheaf.germ_exist X.presheaf x
      have hg : genPt ξ ∈ W := hq'.mem_open W.isOpen hqW
      refine ⟨W, t, hqW, hg, ?_⟩
      rw [← genMap_germ ξ W hg hq' hqW t]
      exact (congrArg (genMap ξ ⟨q, hq'⟩) ht).trans hx
    choose W t hqW hg hval using loc
    let V : U → X.Opens := fun q => W q ⊓ U
    have hgV : ∀ q, genPt ξ ∈ V q := fun q => ⟨hg q, h⟩
    let sf : ∀ q : U, Γ(X, V q) := fun q =>
      (X.presheaf.map (homOfLE inf_le_left : V q ⟶ W q).op).hom (t q)
    have hsf : ∀ q, val ξ (V q) (hgV q) (sf q) = a := fun q =>
      (val_res ξ (homOfLE inf_le_left : V q ⟶ W q) (hgV q) (hg q) (t q)).trans (hval q)
    have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 V sf := by
      intro i j
      apply val_injective ξ hξ (V i ⊓ V j) ⟨hgV i, hgV j⟩ (fun q hq => hU q hq.1.2)
      exact ((val_res ξ (TopologicalSpace.Opens.infLELeft (V i) (V j)) ⟨hgV i, hgV j⟩
        (hgV i) (sf i)).trans (hsf i)).trans
        ((val_res ξ (TopologicalSpace.Opens.infLERight (V i) (V j)) ⟨hgV i, hgV j⟩
        (hgV j) (sf j)).trans (hsf j)).symm
    have hcover : U ≤ iSup V := by
      intro q hq
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨q, hq⟩, hqW ⟨q, hq⟩, hq⟩
    obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' (F := X.sheaf) (U := V) U
      (fun q => homOfLE inf_le_right) hcover sf hcompat
    refine RingHom.mem_range.mpr ⟨s, ?_⟩
    have i0 : U := ⟨genPt ξ, h⟩
    exact (val_res ξ (homOfLE inf_le_right : V i0 ⟶ U) (hgV i0) h s).symm.trans
      ((congrArg (val ξ (V i0) (hgV i0)) (hs i0)).trans (hsf i0))

end GlobalTheory.CompanionTheory.Ar.RegSec

namespace GlobalTheory.CompanionTheory.Ar

theorem regAt_sections : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X),
    IsCptGen ξ → ∀ (U : X.Opens) (h : genPt ξ ∈ U), (∀ q : X, q ∈ U → genPt ξ ⤳ q) →
      Function.Injective (X.presheaf.germ U (genPt ξ) h ≫ Scheme.stalkClosedPointTo ξ).hom ∧
      ∀ a : Ω, a ∈ (X.presheaf.germ U (genPt ξ) h ≫ Scheme.stalkClosedPointTo ξ).hom.range ↔
        ∀ q : Cpt ξ, q.1 ∈ U → a ∈ regAt ξ q := by
  intro X Ω _ ξ hξ U h hU
  exact ⟨RegSec.val_injective ξ hξ U h hU, RegSec.mem_range_val_iff ξ hξ U h hU⟩

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ImplicitFunctionHolomorphic
section
open Filter Topology Metric

namespace GlobalTheory.CompanionTheory.HoloChart

theorem holomorphic_inverse_with_parameters :
    ∀ (n : ℕ) (I J : Type) [Fintype I] [Fintype J] (Ω : Set ((Fin n → ℂ) × (I → ℂ)))
      (Φ : (Fin n → ℂ) × (I → ℂ) → (J → ℂ)) (b₀ : Fin n → ℂ) (x₀ : I → ℂ)
      (L : (I → ℂ) ≃L[ℂ] (J → ℂ)), IsOpen Ω → (b₀, x₀) ∈ Ω → DifferentiableOn ℂ Φ Ω →
      HasFDerivAt (fun x => Φ (b₀, x)) (L : (I → ℂ) →L[ℂ] (J → ℂ)) x₀ →
  ∃ (ε δ : ℝ) (X : (Fin n → ℂ) × (J → ℂ) → (I → ℂ)), 0 < ε ∧ 0 < δ ∧ X (b₀, Φ (b₀, x₀)) = x₀ ∧
    DifferentiableOn ℂ X (ball b₀ ε ×ˢ ball (Φ (b₀, x₀)) ε) ∧
    (∀ p ∈ ball b₀ ε ×ˢ ball (Φ (b₀, x₀)) ε, (p.1, X p) ∈ Ω ∧ Φ (p.1, X p) = p.2 ∧
      ∀ v, fderiv ℂ (fun x => Φ (p.1, x)) (X p) v = 0 → v = 0) ∧
    ∀ b ∈ ball b₀ δ, ∀ x ∈ ball x₀ δ, (b, x) ∈ Ω ∧ Φ (b, x) ∈ ball (Φ (b₀, x₀)) ε ∧
      X (b, Φ (b, x)) = x := by
  intro n I J _ _ Ω Φ b₀ x₀ L hΩ ha hΦ hL
  have cS := ReciprocityTheory.ChartRestriction.DS.S7.cca_contDiffOn hΩ hΦ
  have cΦ : ContDiffAt ℂ 1 Φ (b₀, x₀) :=
    (cS.contDiffAt (hΩ.mem_nhds ha)).of_le (by exact_mod_cast le_top)
  have hinr : ∀ p : (Fin n → ℂ) × (I → ℂ), DifferentiableAt ℂ Φ p →
      HasFDerivAt (fun x => Φ (p.1, x))
        ((fderiv ℂ Φ p).comp (ContinuousLinearMap.inr ℂ (Fin n → ℂ) (I → ℂ))) p.2 := fun p hp =>
    HasFDerivAt.comp p.2 (f := fun x => (p.1, x)) hp.hasFDerivAt (hasFDerivAt_prodMk_right p.1 p.2)
  let D := fderiv ℂ Φ (b₀, x₀)
  have hD : HasFDerivAt Φ D (b₀, x₀) := (cΦ.differentiableAt one_ne_zero).hasFDerivAt
  have hDL : D.comp (ContinuousLinearMap.inr ℂ (Fin n → ℂ) (I → ℂ)) = (L : (I → ℂ) →L[ℂ] (J → ℂ)) :=
    (hinr (b₀, x₀) hD.differentiableAt).unique hL
  have hDuv : ∀ u v, D (u, v) = D (u, 0) + L v := fun u v => by
    have h1 : D (0, v) = L v := by
      have := congrArg (fun A : (I → ℂ) →L[ℂ] (J → ℂ) => A v) hDL
      simpa using this
    rw [← h1, ← map_add (f := _)]; simp
  let F₀ : ((Fin n → ℂ) × (I → ℂ)) →L[ℂ] ((Fin n → ℂ) × (J → ℂ)) :=
    (ContinuousLinearMap.fst ℂ (Fin n → ℂ) (I → ℂ)).prod D
  let G₀ : ((Fin n → ℂ) × (J → ℂ)) →L[ℂ] ((Fin n → ℂ) × (I → ℂ)) :=
    (ContinuousLinearMap.fst ℂ (Fin n → ℂ) (J → ℂ)).prod
      ((L.symm : (J → ℂ) →L[ℂ] (I → ℂ)).comp
        (ContinuousLinearMap.snd ℂ (Fin n → ℂ) (J → ℂ) -
          (D.comp (ContinuousLinearMap.inl ℂ (Fin n → ℂ) (I → ℂ))).comp
            (ContinuousLinearMap.fst ℂ (Fin n → ℂ) (J → ℂ))))
  have hGF : Function.LeftInverse G₀ F₀ := by
    rintro ⟨u, v⟩
    simp [F₀, G₀, hDuv u v]
  have hFG : Function.RightInverse G₀ F₀ := by
    rintro ⟨u, w⟩
    have h : G₀ (u, w) = (u, L.symm (w - D (u, 0))) := by simp [G₀]
    rw [h]
    refine Prod.ext rfl ?_
    show D (u, L.symm (w - D (u, 0))) = w
    rw [hDuv]
    simp
  let F' : ((Fin n → ℂ) × (I → ℂ)) ≃L[ℂ] ((Fin n → ℂ) × (J → ℂ)) :=
    ContinuousLinearEquiv.equivOfInverse F₀ G₀ hGF hFG
  let F : (Fin n → ℂ) × (I → ℂ) → (Fin n → ℂ) × (J → ℂ) := fun p => (p.1, Φ p)
  have hF : HasFDerivAt F (F' : ((Fin n → ℂ) × (I → ℂ)) →L[ℂ] ((Fin n → ℂ) × (J → ℂ))) (b₀, x₀) :=
    hasFDerivAt_fst.prodMk hD
  have cF : ContDiffAt ℂ 1 F (b₀, x₀) := contDiffAt_fst.prodMk cΦ
  let T := cF.toOpenPartialHomeomorph F (f' := F') hF one_ne_zero
  have hTF : ∀ p, T p = F p := fun _ => rfl
  have src : (b₀, x₀) ∈ T.source := cF.mem_toOpenPartialHomeomorph_source (f' := F') hF one_ne_zero
  have tgt : F (b₀, x₀) ∈ T.target :=
    cF.image_mem_toOpenPartialHomeomorph_target (f' := F') hF one_ne_zero
  have hinv : T.symm (F (b₀, x₀)) = (b₀, x₀) := T.left_inv src
  let O := (T.target ∩ interior {w | ContDiffAt ℂ 1 T.symm w}) ∩ (T.target ∩ T.symm ⁻¹' Ω)
  have oO : IsOpen O := (T.open_target.inter isOpen_interior).inter (T.isOpen_inter_preimage_symm hΩ)
  have mO : F (b₀, x₀) ∈ O := by
    refine ⟨⟨tgt, mem_interior_iff_mem_nhds.2 ?_⟩, tgt, ?_⟩
    · exact (cF.to_localInverse (f' := F') hF one_ne_zero).eventually (by simp)
    · simpa [hinv] using ha
  obtain ⟨ε, ε0, hε⟩ := Metric.isOpen_iff.1 oO _ mO
  have hball : ball b₀ ε ×ˢ ball (Φ (b₀, x₀)) ε ⊆ O := by
    rw [ball_prod_same]; exact hε
  obtain ⟨δ, δ0, hδ⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem (Filter.inter_mem
    (T.open_source.mem_nhds src) (hΩ.mem_nhds ha))
    (hF.continuousAt.preimage_mem_nhds (ball_mem_nhds (F (b₀, x₀)) ε0)))
  have hsec : ∀ p ∈ O, T.symm p = (p.1, (T.symm p).2) ∧ Φ (T.symm p) = p.2 := fun p hp => by
    have h : F (T.symm p) = p := T.right_inv hp.1.1
    have h1 : (T.symm p).1 = p.1 := congrArg Prod.fst h
    have h2 : Φ (T.symm p) = p.2 := congrArg Prod.snd h
    exact ⟨Prod.ext h1 rfl, h2⟩
  refine ⟨ε, min δ δ, fun p => (T.symm p).2, ε0, lt_min δ0 δ0, ?_, ?_, ?_, ?_⟩
  · exact congrArg Prod.snd hinv
  · intro p hp
    have c : ContDiffAt ℂ 1 T.symm p := interior_subset (hball hp).1.2
    exact ((differentiableAt_snd).comp p (c.differentiableAt one_ne_zero)).differentiableWithinAt
  · intro p hp
    have hpO := hball hp
    obtain ⟨e1, e2⟩ := hsec p hpO
    have hq : T.symm p ∈ Ω := hpO.2.2
    have hq' : (p.1, (T.symm p).2) ∈ Ω := e1 ▸ hq
    refine ⟨hq', by rw [← e1]; exact e2, fun v hv => ?_⟩
    have dΦ : DifferentiableAt ℂ Φ (T.symm p) := (hΦ _ hq).differentiableAt (hΩ.mem_nhds hq)
    have h1 := (hinr (T.symm p) dΦ).fderiv
    have h2 : (T.symm p).1 = p.1 := congrArg Prod.fst e1
    rw [h2] at h1
    rw [h1] at hv
    have dF : HasFDerivAt F ((ContinuousLinearMap.fst ℂ (Fin n → ℂ) (I → ℂ)).prod
        (fderiv ℂ Φ (T.symm p))) (T.symm p) := hasFDerivAt_fst.prodMk dΦ.hasFDerivAt
    have c : ContDiffAt ℂ 1 T.symm p := interior_subset hpO.1.2
    have dS : HasFDerivAt T.symm (fderiv ℂ T.symm p) (F (T.symm p)) := by
      rw [show F (T.symm p) = p from T.right_inv hpO.1.1]
      exact (c.differentiableAt one_ne_zero).hasFDerivAt
    have hcomp := dS.comp (T.symm p) dF
    have hid : HasFDerivAt (T.symm ∘ F) (ContinuousLinearMap.id ℂ _) (T.symm p) := by
      refine (hasFDerivAt_id (𝕜 := ℂ) (T.symm p)).congr_of_eventuallyEq ?_
      filter_upwards [T.open_source.mem_nhds (T.map_target hpO.1.1)] with q hq
      exact T.left_inv hq
    have hu := hcomp.unique hid
    have hv' : fderiv ℂ Φ (T.symm p) (0, v) = 0 := by simpa using hv
    have e0 : ((ContinuousLinearMap.fst ℂ (Fin n → ℂ) (I → ℂ)).prod
        (fderiv ℂ Φ (T.symm p))) (0, v) = 0 := Prod.ext (by simp) (by simpa using hv')
    have h3 := DFunLike.congr_fun hu (0, v)
    rw [ContinuousLinearMap.comp_apply, e0, map_zero] at h3
    exact (congrArg Prod.snd h3).symm
  · intro b hb x hx
    have hbx : (b, x) ∈ ball (b₀, x₀) δ := by
      rw [← ball_prod_same]; exact ⟨by simpa using hb, by simpa using hx⟩
    obtain ⟨⟨h1, h2⟩, h3⟩ := hδ hbx
    have h3' : F (b, x) ∈ ball b₀ ε ×ˢ ball (Φ (b₀, x₀)) ε := by
      rw [ball_prod_same]; exact h3
    exact ⟨h2, h3'.2, congrArg Prod.snd (T.left_inv h1)⟩

end GlobalTheory.CompanionTheory.HoloChart
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ImplicitRootAnalyticStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.implicit_root_analytic : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (n : ℕ) (c : ℕ → E → ℂ) (w₀ : E) (τ₀ : ℂ), (∀ j, AnalyticAt ℂ (c j) w₀) → ∑ j ∈ Finset.range (n + 1), c j w₀ * τ₀ ^ j = 0 → ∑ j ∈ Finset.range (n + 1), (j : ℂ) * c j w₀ * τ₀ ^ (j - 1) ≠ 0 → ∃ (V : Set E) (W : Set ℂ) (g : E → ℂ), IsOpen V ∧ w₀ ∈ V ∧ IsOpen W ∧ τ₀ ∈ W ∧ AnalyticOnNhd ℂ g V ∧ ∀ w ∈ V, ∀ τ ∈ W, ∑ j ∈ Finset.range (n + 1), c j w * τ ^ j = 0 → τ = g w := by
  first | exact @GlobalTheory.CompanionTheory.SimpleRoot.exists_analytic_simple_root | exact GlobalTheory.CompanionTheory.SimpleRoot.exists_analytic_simple_root | (intros; apply GlobalTheory.CompanionTheory.SimpleRoot.exists_analytic_simple_root <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IotaMultiNeZeroOfLinIndepStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iota_multi_ne_zero_of_lin_indep : ∀ (Ω V : Type) [Field Ω] [AddCommGroup V] [Module Ω V] (n : ℕ) (e : Fin n → V), LinearIndependent Ω e → exteriorPower.ιMulti Ω n e ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Exterior.ιMulti_ne_zero_of_linearIndependent | exact GlobalTheory.CompanionTheory.Exterior.ιMulti_ne_zero_of_linearIndependent | (intros; apply GlobalTheory.CompanionTheory.Exterior.ιMulti_ne_zero_of_linearIndependent <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsClopenSpecializationsGenPt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem exists_isOpen_common_generization {Y : Type*} [TopologicalSpace Y]
    [TopologicalSpace.NoetherianSpace Y] [QuasiSober Y] (p : Y) :
    ∃ V : Set Y, IsOpen V ∧ p ∈ V ∧ ∀ q ∈ V, ∃ z : Y, z ⤳ p ∧ z ⤳ q := by
  have hF : (irreducibleComponents Y).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  refine ⟨⋂ Z ∈ {Z ∈ irreducibleComponents Y | p ∉ Z}, Zᶜ, ?_, ?_, ?_⟩
  · refine (hF.subset (Set.sep_subset _ _)).isOpen_biInter fun Z hZ => ?_
    exact (isClosed_of_mem_irreducibleComponents Z hZ.1).isOpen_compl
  · simp only [Set.mem_iInter]
    exact fun Z hZ => hZ.2
  · intro q hq
    have hmem := irreducibleComponent_mem_irreducibleComponents q
    have hpZ : p ∈ irreducibleComponent q := by
      by_contra hp
      exact (Set.mem_iInter₂.1 hq _ ⟨hmem, hp⟩) mem_irreducibleComponent
    obtain ⟨z, hz⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x := q))
      isClosed_irreducibleComponent
    exact ⟨z, hz.specializes hpZ, hz.specializes mem_irreducibleComponent⟩

theorem genPt_specializes_of_specializes {X : Scheme.{0}} {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (h : IsCptGen ξ) {p z : X}
    (hp : genPt ξ ⤳ p) (hz : z ⤳ p) : genPt ξ ⤳ z := by
  obtain ⟨y, rfl⟩ : z ∈ Set.range (X.fromSpecStalk p) := by
    rw [Scheme.range_fromSpecStalk]; exact hz
  have hinj := h.inj ⟨p, hp⟩
  haveI : IsDomain (X.presheaf.stalk p) := hinj.isDomain (genMap ξ ⟨p, hp⟩)
  have hp' : ξ (IsLocalRing.closedPoint (CommRingCat.of Ω)) ⤳ p := hp
  let φ := X.presheaf.stalkSpecializes hp' ≫ Scheme.stalkClosedPointTo ξ
  have hφ : Spec.map φ ≫ X.fromSpecStalk p = ξ := by
    change Spec.map (X.presheaf.stalkSpecializes hp' ≫ Scheme.stalkClosedPointTo ξ) ≫ _ = ξ
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  have hbot : (Spec.map φ) (IsLocalRing.closedPoint Ω) =
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (X.presheaf.stalk p)) := by
    apply PrimeSpectrum.ext
    change Ideal.comap (genMap ξ ⟨p, hp⟩) (IsLocalRing.maximalIdeal Ω) = ⊥
    rw [IsLocalRing.maximalIdeal_eq_bot]
    exact Ideal.comap_bot_of_injective _ hinj
  have hη : genPt ξ = X.fromSpecStalk p ⟨⊥, Ideal.isPrime_bot⟩ := by
    rw [← hbot]
    conv_lhs => rw [genPt, ← hφ]
    rfl
  rw [hη]
  exact ((PrimeSpectrum.le_iff_specializes _ _).1 bot_le).map (X.fromSpecStalk p).continuous

theorem isClopen_setOf_genPt_specializes (X : Scheme.{0}) (Ω : Type) [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) [IsLocallyNoetherian X] (h : IsCptGen ξ) :
    IsClopen {q : X | genPt ξ ⤳ q} := by
  refine ⟨?_, ?_⟩
  · have : {q : X | genPt ξ ⤳ q} = closure {genPt ξ} := by
      ext q; exact specializes_iff_mem_closure
    rw [this]; exact isClosed_closure
  · rw [isOpen_iff_mem_nhds]
    intro p hp
    obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := p) trivial
    haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    obtain ⟨V, hV, hpV, hVq⟩ := @exists_isOpen_common_generization U _
      (noetherianSpace_of_isAffineOpen U hU) U.isOpen.isOpenEmbedding_subtypeVal.quasiSober
      ⟨p, hpU⟩
    have hopen : IsOpen (Subtype.val '' V : Set X) := U.isOpen.isOpenMap_subtype_val V hV
    refine Filter.mem_of_superset (hopen.mem_nhds ⟨_, hpV, rfl⟩) ?_
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨z, hzp, hzq⟩ := hVq q hq
    exact (genPt_specializes_of_specializes ξ h (p := p) hp
      (hzp.map continuous_subtype_val)).trans (hzq.map continuous_subtype_val)

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsCptGenResidueFieldGeneric
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem injective_of_maximal_point {X : Scheme.{0}} {Ω : Type} [Field Ω] (p : X)
    [IsDomain (X.presheaf.stalk p)] (φ : X.presheaf.stalk p ⟶ CommRingCat.of Ω)
    (h : ∀ y : X, y ⤳ (Spec.map φ ≫ X.fromSpecStalk p) (IsLocalRing.closedPoint Ω) →
      y = (Spec.map φ ≫ X.fromSpecStalk p) (IsLocalRing.closedPoint Ω)) :
    Function.Injective φ.hom := by
  let z : PrimeSpectrum (X.presheaf.stalk p) := ⟨⊥, Ideal.isPrime_bot⟩
  let q : PrimeSpectrum (X.presheaf.stalk p) := PrimeSpectrum.comap φ.hom (IsLocalRing.closedPoint Ω)
  have hs : z ⤳ q := (PrimeSpectrum.le_iff_specializes z q).1 bot_le
  have hq : (Spec.map φ ≫ X.fromSpecStalk p) (IsLocalRing.closedPoint Ω) = X.fromSpecStalk p q := rfl
  rw [hq] at h
  have h1 : X.fromSpecStalk p z = X.fromSpecStalk p q :=
    h _ (hs.map (X.fromSpecStalk p).continuous)
  have h2 : z = q := (X.fromSpecStalk p).isEmbedding.injective h1
  refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
  have h3 : a ∈ q.asIdeal := by
    change φ.hom a ∈ (IsLocalRing.closedPoint Ω).asIdeal
    rw [ha]
    exact Ideal.zero_mem _
  rw [← h2] at h3
  exact h3

theorem isCptGen_of_maximal_of_surjective {X : Scheme.{0}} {Ω : Type} [Field Ω]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x)) (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (h : ∀ y : X, y ⤳ genPt ξ → y = genPt ξ)
    (hs : Function.Surjective (Scheme.stalkClosedPointTo ξ).hom) : IsCptGen ξ := by
  refine ⟨⟨?_, hs⟩, fun p => ?_⟩
  · have := hX (ξ (IsLocalRing.closedPoint Ω))
    refine injective_of_maximal_point _ (Scheme.stalkClosedPointTo ξ) ?_
    rw [Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
    exact h
  · obtain ⟨p, hp⟩ := p
    have := hX p
    have hp' : ξ (IsLocalRing.closedPoint Ω) ⤳ p := hp
    refine injective_of_maximal_point p
      (X.presheaf.stalkSpecializes hp' ≫ Scheme.stalkClosedPointTo ξ) ?_
    have e : Spec.map (X.presheaf.stalkSpecializes hp' ≫ Scheme.stalkClosedPointTo ξ) ≫
        X.fromSpecStalk p = ξ := by
      rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
      exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
    rw [e]
    exact h

theorem isCptGen_of_maximal : ∀ (X : Scheme.{0}), (∀ x : X, IsDomain (X.presheaf.stalk x)) → ∀ x : X,
    (∀ y : X, y ⤳ x → y = x) → IsCptGen (Ω := X.residueField x) (X.fromSpecResidueField x) := by
  intro X hX x h
  have e : genPt (Ω := X.residueField x) (X.fromSpecResidueField x) = x :=
    X.fromSpecResidueField_apply x _
  refine isCptGen_of_maximal_of_surjective hX _ (by rw [e]; exact h) ?_
  unfold Scheme.stalkClosedPointTo
  rw [CommRingCat.hom_comp, RingHom.coe_comp]
  exact (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso _).hom).2.comp
    ((X.fromSpecResidueField x).stalkMap_surjective _)

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.KaehlerFinrankFractionFieldStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kaehler_finrank_fraction_field : ∀ (S T K L : Type) [CommRing S] [CommRing T] [Field K] [Field L] [Algebra S T] [Algebra S K]
    [Algebra S L] [Algebra T L] [Algebra K L] [IsScalarTower S T L] [IsScalarTower S K L]
    [IsFractionRing S K] [IsFractionRing T L] (m : ℕ) (w : Fin m → T),
    LinearIndependent T (fun i => KaehlerDifferential.D S T (w i)) →
    Submodule.span T (Set.range fun i => KaehlerDifferential.D S T (w i)) = ⊤ →
    Module.finrank L (KaehlerDifferential K L) = m := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.finrank_kaehler_fractionRing_eq_of_basis | exact GlobalTheory.CompanionTheory.Ggeo.finrank_kaehler_fractionRing_eq_of_basis | (intros; apply GlobalTheory.CompanionTheory.Ggeo.finrank_kaehler_fractionRing_eq_of_basis <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LuFactorsGenerateSameFieldStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lu_factors_generate_same_field : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (n : ℕ) (A : Matrix (Fin n) (Fin n) K) (u v w : Matrix (Fin n) (Fin n) L), A.det ≠ 0 → (∀ k, u k k = 1) → (∀ l k, l < k → u l k = 0) → (∀ k, v k k = 1) → (∀ l k, l < k → v l k = 0) → (∀ l k, k < l → w l k = 0) → (∀ k, w k k ≠ 0) → A.map (algebraMap K L) * u = v * w → IntermediateField.adjoin K (Set.range fun p : Fin n × Fin n => u p.1 p.2) = IntermediateField.adjoin K (Set.range fun p : Fin n × Fin n => v p.1 p.2) := by
  first | exact @GlobalTheory.CompanionTheory.LuFields.adjoin_entries_eq | exact GlobalTheory.CompanionTheory.LuFields.adjoin_entries_eq | (intros; apply GlobalTheory.CompanionTheory.LuFields.adjoin_entries_eq <;> assumption)
end

