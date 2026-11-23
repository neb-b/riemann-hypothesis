module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsSide
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BaseChangeIsomorphicFields
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0697
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.SatLocFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.FormsFiniteGL

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

open GlobalTheory.CuspRep.LocEx GlobalTheory.LFun GlobalTheory.PRep

theorem UpperTheory.ConvolutionTheory.R2.H.unrSplit :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), ThetaLiftTrivialOrbitTermsVanish W M π → ∀ Q : CuspSub E 2, Q.V ≤ span W M π →
      ∀ (v : P F) (w : P E), SplitAt v w → ∀ B, π.HasSat v B → (CG.mk Q).HasSat w B := by
  intro F E _ _ _ _ _ _ _ D W M π hN Q hQ v w hs B hB
  obtain ⟨hq, i, hc, hx, hv⟩ := hs
  have hSmooth : IsSmooth (π.locRep v) := fun x =>
    (π.isSmooth_finPart x).preimage (GlobalTheory.CuspRep.CuspSub.continuous_locGL v)

  have cpt_fin (k : TR.Kinf F 2) (g : GL (Fin 2) (Af F)) (y : π.V) :
      π.op (.cpt k) (π.finPart g y) = π.finPart g (π.op (.cpt k) y) := by
    refine Subtype.ext ?_
    change (TR.rt F 2 (TR.infGL F 2 (Unitary.toUnits k)) * TR.rt F 2 (finGL F 2 g)) y.1 =
      (TR.rt F 2 (finGL F 2 g) * TR.rt F 2 (TR.infGL F 2 (Unitary.toUnits k))) y.1
    rw [← map_mul, ← map_mul, TR.infGL_comm]

  have fin_loc {k : GL (Fin 2) (Af F)}
      (hk : GeneralLinearGroup.map (pLoc F v) k = 1) (g : GL (Fin 2) (v.adicCompletion F)) (y : π.V) :
      π.finPart k (π.locRep v g y) = π.locRep v g (π.finPart k y) := by
    simp only [TR.CuspSub.locRep, MonoidHom.comp_apply]
    rw [← mul_apply_eq_comp, ← mul_apply_eq_comp, ← map_mul, ← map_mul,
      GlobalTheory.CuspRep.LocUniq.comm_locGL v hk]

  have bot_or_top (W : Submodule ℂ π.V)
      (h1 : ∀ g, ∀ x ∈ W, π.locRep v g x ∈ W)
      (h2 : ∀ T : Module.End ℂ π.V, (∀ g x, T (π.locRep v g x) = π.locRep v g (T x)) → ∀ x ∈ W, T x ∈ W) :
      W = ⊥ ∨ W = ⊤ := by
    have hi := Submodule.map_injective_of_injective π.V.injective_subtype
    have hop : ∀ o, ∀ x ∈ W, π.op o x ∈ W := fun o x hx => by
      cases o with
      | fin k =>
        have h3 := h1 (GeneralLinearGroup.map (pLoc F v) k) _ (h2
          (π.finPart ((locGL F 2 v (GeneralLinearGroup.map (pLoc F v) k))⁻¹ * k))
          (fin_loc (map_pLoc_inv_mul v k)) x hx)
        rwa [TR.CuspSub.locRep, MonoidHom.comp_apply, ← mul_apply_eq_comp, ← map_mul, mul_inv_cancel_left] at h3
      | cpt k => exact h2 _ (fun g y => cpt_fin k _ y) x hx
      | lie X => exact h2 _ (fun g y => Subtype.ext (LinearMap.congr_fun (TR.lie_rt_fin X (locGL F 2 v g)) y.1)) x hx
    rcases π.irred (W.map π.V.subtype) (Submodule.map_subtype_le _ _) (by
      rintro o _ ⟨x, hx, rfl⟩
      exact ⟨_, hop o x hx, rfl⟩) with h | h
    · exact Or.inl (hi (h.trans (Submodule.map_bot _).symm))
    · exact Or.inr (hi (h.trans (Submodule.map_subtype_top _).symm))

  let K := KGL v (n := 2)
  have hSat : HasSatGL v (π.locRep v) B := hB
  obtain ⟨φ, hφ⟩ := hSat.exists_vec
  obtain ⟨hKo, hKc⟩ := SatCompare.isOpen_isCompact_KGL v 2
  -- Every nonzero local invariant subspace has a spherical vector.
  have detects_fixed (S : Submodule ℂ π.V) (hS : ∀ g, ∀ x ∈ S, π.locRep v g x ∈ S)
      (h : S ⊓ fixed (π.locRep v) K = ⊥) : S = ⊥ := by
    rcases bot_or_top (nullPart (π.locRep v) K) (fun g x hx => nullPart_act _ K g hx)
      (fun T hT x hx => nullPart_comm _ K T hT hx) with hnull | hnull
    · exact le_bot_iff.1 (hnull ▸ le_nullPart hSmooth hKc S hS h)
    · exact (hφ.1 (eq_zero_of_mem_nullPart hSmooth hKc hφ.2.1 (hnull ▸ Submodule.mem_top))).elim

  have exists_comp : ∃ σ, π.IsLocComp v σ := by
    let orb {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V]
        (κ : Representation ℂ K V) (x : V) : (K →₀ ℂ) →ₗ[ℂ] V :=
      Finsupp.linearCombination ℂ fun k => κ k x

    have orb_comm {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V]
        (κ : Representation ℂ K V) (T : Module.End ℂ V) (hT : ∀ k x, T (κ k x) = κ k (T x)) (x : V)
        (c : K →₀ ℂ) : orb κ (T x) c = T (orb κ x c) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [orb, Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul, hT]

    have orb_act {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V]
        (κ : Representation ℂ K V) (x : V) (k : K) (c : K →₀ ℂ) :
        orb κ x (c.mapDomain (k * ·)) = κ k (orb κ x c) := by
      induction c using Finsupp.induction_linear with
      | zero => simp
      | add c c' h h' => rw [Finsupp.mapDomain_add, map_add (f := _), map_add (f := _), map_add (f := _), h, h']
      | single a b => simp [orb]

    let annPart {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V]
        (κ : Representation ℂ K V) (φ : V) : Submodule ℂ V := {
      carrier := {x | ∀ c, orb κ φ c = 0 → orb κ x c = 0}
      add_mem' := fun {x y} hx hy c hc => by
        have : orb κ (x + y) c = orb κ x c + orb κ y c := by
          simp only [orb, Finsupp.linearCombination_apply, Finsupp.sum, map_add (f := _), smul_add, Finset.sum_add_distrib]
        rw [this, hx c hc, hy c hc, add_zero]
      zero_mem' := fun c _ => by simp [orb, Finsupp.linearCombination_apply, Finsupp.sum]
      smul_mem' := fun a x hx c hc => by
        have := orb_comm κ (a • (1 : Module.End ℂ V)) (fun k x => by simp) x c
        simpa [hx c hc] using this }

    -- Vectors annihilated by the relations of φ are images of its compact type.
    have exists_type {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V]
        (κ : Representation ℂ K V) (φ : V)
        (hφ : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => κ k φ))) :
        ∃ (d : ℕ) (ξ : K →* Matrix (Fin d) (Fin d) ℂ), ∀ x ∈ annPart κ φ, ∃ f : (Fin d → ℂ) →ₗ[ℂ] V,
          (∀ k v, f (ξ k *ᵥ v) = κ k (f v)) ∧ x ∈ LinearMap.range f ∧ ∀ v, ∃ c, f v = orb κ x c := by
      have hO : ∀ k, ∀ y ∈ LinearMap.range (orb κ φ), κ k y ∈ LinearMap.range (orb κ φ) := by
        rintro k _ ⟨c, rfl⟩
        exact ⟨_, orb_act κ φ k c⟩
      have : FiniteDimensional ℂ (LinearMap.range (orb κ φ)) := by
        change FiniteDimensional ℂ (LinearMap.range (Finsupp.linearCombination ℂ fun k => κ k φ))
        rw [Finsupp.range_linearCombination]
        exact hφ
      let b := Module.finBasis ℂ (LinearMap.range (orb κ φ))
      obtain ⟨s, hs⟩ := (orb κ φ).rangeRestrict.exists_rightInverse_of_surjective (LinearMap.range_rangeRestrict _)
      refine ⟨_, (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp (sub κ _ hO), fun x hx => ?_⟩
      have key : ∀ c, orb κ x (s ((orb κ φ).rangeRestrict c)) = orb κ x c := fun c => by
        rw [← sub_eq_zero, ← map_sub]
        refine hx _ ?_
        rw [map_sub, sub_eq_zero]
        exact congrArg Subtype.val (LinearMap.congr_fun hs ((orb κ φ).rangeRestrict c))
      refine ⟨orb κ x ∘ₗ s ∘ₗ b.equivFun.symm.toLinearMap, fun k v => ?_,
        ⟨b.equivFun ((orb κ φ).rangeRestrict (Finsupp.single 1 1)), ?_⟩, fun v => ⟨_, rfl⟩⟩
      · obtain ⟨y, rfl⟩ := b.equivFun.surjective v
        obtain ⟨c, rfl⟩ := (orb κ φ).surjective_rangeRestrict y
        have h1 : (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp (sub κ _ hO) k *ᵥ b.equivFun ((orb κ φ).rangeRestrict c) =
            b.equivFun ((orb κ φ).rangeRestrict (c.mapDomain (k * ·))) := by
          have h2 : (orb κ φ).rangeRestrict (c.mapDomain (k * ·)) = sub κ _ hO k ((orb κ φ).rangeRestrict c) :=
            Subtype.ext (orb_act κ φ k c)
          rw [h2]
          exact LinearMap.toMatrix_mulVec_repr b b _ _
        rw [h1]
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, key, orb_act]
      · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, key]
        simp [orb]

    let cptPart : Representation ℂ (TR.Kinf F 2) π.V :=
      sub (TR.cptRep F 2) π.V fun k => π.stable (.cpt k)

    let L := stab π.finPart φ
    have hL : IsOpen (L : Set (GL (Fin 2) (Af F))) := π.isSmooth_finPart φ
    have hfd : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptPart k φ)) := by
      have := (π.cusp φ.1 φ.2).1.kfin
      refine FiniteDimensional.of_injective ((π.V.subtype ∘ₗ Submodule.subtype _).codRestrict
        (Submodule.span ℂ (Set.range fun k => TR.cptRep F 2 k φ.1)) fun x => ?_)
        fun x y e => Subtype.ext (Subtype.ext (by
          have e' := congrArg Subtype.val e
          exact e'))
      refine Submodule.mem_comap.1 ((Submodule.span_le (p := Submodule.comap π.V.subtype _)).2 ?_ x.2)
      rintro _ ⟨k, rfl⟩
      exact Submodule.subset_span ⟨k, rfl⟩
    obtain ⟨d, ξ, hξ⟩ := exists_type cptPart φ hfd
    have hcomm : ∀ g k x, π.finPart g (cptPart k x) = cptPart k (π.finPart g x) := fun g k x => (cpt_fin k g x).symm
    let U : Submodule ℂ π.V := annPart cptPart φ ⊓
      fixed π.finPart (L ⊓ (GeneralLinearGroup.map (n := Fin 2) (pLoc F v)).ker)
    obtain ⟨σ, hσ, -⟩ := exists_irred hSmooth hKo detects_fixed
      U (fun g x hx => ⟨fun c hc => by
          rw [TR.CuspSub.locRep, MonoidHom.comp_apply, orb_comm _ _ (hcomm _), hx.1 c hc, map_zero],
        mem_fix.2 fun k hk => by rw [fin_loc hk.2, mem_fix.1 hx.2 k hk]⟩)
      ((Submodule.ne_bot_iff _).2 ⟨φ, ⟨fun _ hc => hc, mem_fix.2 fun k hk => hk.1⟩, hφ.1⟩) (fun K' hK' => by
        obtain ⟨W, hW, hWf⟩ := UpperTheory.V.Af.admissibleReal F 2 π (L ⊓ (K' ⊓ L.comap (locGL F 2 v)).comap (GeneralLinearGroup.map (pLoc F v)))
          (hL.inter ((hK'.inter (hL.preimage (GlobalTheory.CuspRep.CuspSub.continuous_locGL v))).preimage
            (continuous_map_pLoc v))) d ξ
        refine Submodule.finiteDimensional_of_le (S₂ := W) fun x hx => ?_
        obtain ⟨f, hf, hx1, hf2⟩ := hξ x hx.1.1
        refine hWf f hf (fun k hk z => ?_) hx1
        have h1 := mem_fix.1 hx.1.2 _ ⟨L.mul_mem (L.inv_mem hk.2.2) hk.1, map_pLoc_inv_mul v k⟩
        have h2 := mem_fix.1 hx.2 _ hk.2.1
        have h3 : π.finPart k x = x := by
          rw [← mul_inv_cancel_left (locGL F 2 v (GeneralLinearGroup.map (pLoc F v) k)) k, map_mul,
            mul_apply_eq_comp, h1]
          exact h2
        obtain ⟨c, hc⟩ := hf2 z
        rw [hc, ← orb_comm _ _ (hcomm k), h3])
    exact ⟨σ, hσ⟩

  obtain ⟨σ, hσ⟩ := exists_comp
  have h1 : HasSatGL v σ.ρ B := by
    obtain ⟨f, hf0, hf⟩ := hσ
    have hi := GlobalTheory.BcSpehCompare.injective_of_irred σ.irred
      (τ := fun g => π.locRep v g) (fun _ => map_zero _) hf0 hf
    have hfix : ∀ x ∈ fixed σ.ρ K, f x ∈ fixed (π.locRep v) K := fun x hx =>
      mem_fix.2 fun k hk => by rw [← hf, mem_fix.1 hx k hk]
    constructor
    · have hRange : LinearMap.range f ⊓ fixed (π.locRep v) K ≠ ⊥ := fun h =>
        hf0 (LinearMap.range_eq_bot.1 (detects_fixed (LinearMap.range f)
          (by rintro g _ ⟨x, rfl⟩; exact ⟨_, hf g x⟩) h))
      obtain ⟨_, ⟨⟨x, rfl⟩, hx⟩, hx0⟩ := (Submodule.ne_bot_iff _).1 hRange
      exact (Submodule.ne_bot_iff _).2 ⟨x, mem_fix.2 fun k hk => hi (by
        rw [hf, mem_fix.1 hx k hk]), fun e => hx0 (by rw [e, map_zero])⟩
    · intro x hx hx0
      exact (hSat.2 _ (hfix x hx) ((map_ne_zero_iff f hi).2 hx0)).of_map f hf hi
  obtain ⟨σ', hσ', -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp UpperTheory.V.Af.formsFiniteGL E 2 Q w
  obtain ⟨e, he⟩ := UpperTheory.ConvolutionTheory.R2.split F E D W M π hN Q hQ v w i hc hx σ σ' hσ hσ'
  have hq' : Formalism.UG.qV E w = Formalism.UG.qV F v := by
    simpa [Formalism.UG.qV, Ideal.absNorm_apply, Submodule.cardQuot_apply, normV] using hq
  have h2 : GlobalTheory.LFun.HasSatGL w σ'.ρ B :=
    GlobalTheory.IsoPull.hasSatGL_of_ringEquiv i hv hq' e (fun g x => (he g x).symm) h1
  exact (GlobalTheory.BcSpehCompare.hasSat_iff hσ' B).2 h2
