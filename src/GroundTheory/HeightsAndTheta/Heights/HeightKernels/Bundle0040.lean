module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0037
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0024
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0027
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsVertPointNagata
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PVertPointResidue

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGenFibreModelTransport
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial GenericFibreModelTransport

theorem GenFibreModelTransport.proof : GenFibreModelTransport.Statement := by
  intro K _ ι _ K' _ ι' _ v P' G Ω _ z hz Φ₀ _ _ hΦ₀ τ w q
  let φ : MRing ι' →+* G.Φ' := (aeval G.x').toRingHom
  let ψ : MRing ι' →+* Ω := eval₂Hom (Int.castRingHom Ω) z
  have : P'.IsPrime := hz ▸ RingHom.ker_isPrime ψ
  have hφ : ∀ a ∈ P', φ a = 0 := fun a ha => RingHom.mem_ker.1 (G.genericFibre_ker_target.symm ▸ ha)
  have hψ : ∀ a ∈ P', ψ a = 0 := fun a ha => RingHom.mem_ker.1 (hz.symm ▸ ha)
  let α : FractionRing (MRing ι' ⧸ P') →+* G.Φ' :=
    IsFractionRing.lift (quotient_lift_injective φ P' G.genericFibre_ker_target hφ)
  let β : FractionRing (MRing ι' ⧸ P') →+* Ω := IsFractionRing.lift (quotient_lift_injective ψ P' hz hψ)
  let ξ : (Σ k', ι' k') → FractionRing (MRing ι' ⧸ P') := fun p =>
    algebraMap _ _ (Ideal.Quotient.mk P' (X p))
  have hα : α ∘ ξ = G.x' := funext fun p => by simp [α, ξ, φ]
  have hβ : β ∘ ξ = z := funext fun p => by simp [β, ξ, ψ]
  let k := Subfield.closure (Set.range (ξ ∘ v))
  have h₁ : (algebraMap G.Φ G.Φ').fieldRange = k.map α := by
    rw [RingHom.map_field_closure, ← Set.range_comp, ← Function.comp_assoc, hα]
    refine le_antisymm ?_ (Subfield.closure_le.2 ?_)
    · rintro _ ⟨c, rfl⟩
      obtain ⟨f, g, -, rfl⟩ := G.gen c
      have key : ∀ f : MRing ι, algebraMap G.Φ G.Φ' (aeval G.x f) ∈ Subfield.closure (Set.range (G.x' ∘ v)) := by
        intro f
        rw [aeval_def, eval₂_comp_left]
        convert eval₂_mem_closure _ (G.x' ∘ v) f using 2
        exact funext fun p => (G.compat p).symm
      rw [map_div₀]
      exact div_mem (key f) (key g)
    · rintro _ ⟨p, rfl⟩
      exact ⟨G.x p, (G.compat p).symm⟩
  have h₂ : (algebraMap Φ₀ Ω).fieldRange = k.map β := by
    rw [hΦ₀, RingHom.map_field_closure, ← Set.range_comp, ← Function.comp_assoc, hβ]
  obtain ⟨e₁, he₁⟩ := subfield_equiv k α (algebraMap G.Φ G.Φ') h₁
  obtain ⟨e₂, he₂⟩ := subfield_equiv k β (algebraMap Φ₀ Ω) h₂
  let s : Set (FractionRing (MRing ι' ⧸ P')) := Set.range fun t => ξ (w t) / ξ q
  have hs : ∀ (F : Type) [Field F] (γ : FractionRing (MRing ι' ⧸ P') →+* F) (y : (Σ k', ι' k') → F),
      γ ∘ ξ = y → γ '' s = Set.range fun t => y (w t) / y q := by
    rintro F _ γ y rfl
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun t => map_div₀ γ _ _)
  obtain ⟨f₁, t₁⟩ := adjoin_transport e₁ α (RingHom.ext he₁) s (ξ q)
  obtain ⟨f₂, t₂⟩ := adjoin_transport e₂ β (RingHom.ext he₂) s (ξ q)
  rw [hs _ α _ hα] at f₁ t₁
  rw [show α (ξ q) = G.x' q from congrFun hα q] at t₁
  rw [hs _ β _ hβ] at f₂ t₂
  rw [show β (ξ q) = z q from congrFun hβ q] at t₂
  refine ⟨?_, f₁.symm.trans f₂, t₁.symm.trans t₂⟩
  rw [← congrFun hα q, ← congrFun hβ q]
  exact (map_eq_zero α).trans (map_eq_zero β).symm

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PPointArInt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial

noncomputable section

namespace PointArithIntersection

open IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree

variable {T : Type} [Fintype T]

theorem logNorm_smul {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (fun _ : Unit => T)} {s : MRing (fun _ : Unit => T)}
    {P : Ideal (MRing (fun _ : Unit => T))} (hs : IsSectionOn P A s) (c : ℂ) (hc : c ≠ 0)
    (z : (Σ _ : Unit, T) → ℂ) : logNorm A s (fun p => c * z p) = logNorm A s z := by
  obtain ⟨a, ha, hhom, -⟩ := hs
  have hz : (fun p : Σ _ : Unit, T => c * z p) = scaleBlock () c z := by
    funext p
    simp [scaleBlock]
  have hh : A.h (fun p => c * z p) = ‖c‖ ^ A.a () * A.h z := by
    simpa using A.smul (fun _ => c) z (fun _ => hc)
  unfold logNorm
  rw [hh, hz, eval_scaleBlock () c z s a hhom, ha (), zpow_natCast, norm_mul, norm_pow]
  rw [mul_div_mul_left _ _ (pow_ne_zero _ (norm_ne_zero_iff.mpr hc))]

variable {K' : Type} [Field K'] [NumberField K']

theorem eq_of_ptOf_eq_smul {y : (Σ _ : Unit, T) → K'} {c : Unit → T} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    {φ ψ : blockFnField y →ₐ[ℚ] ℂ} (t : ℂ) (h : ptOf y c φ = fun p => t * ptOf y c ψ p) : φ = ψ := by
  have ht : t = 1 := by
    have := congrFun h ⟨(), c ()⟩
    simp only [ptOf_chart hc, mul_one] at this
    exact this.symm
  subst ht
  refine IntermediateField.algHom_ext_of_eq_adjoin ℚ (blockFnField_eq y c hc) ?_
  rintro _ ⟨p, rfl⟩
  have := congrFun h p
  simp only [one_mul] at this
  exact this

theorem sum_reps_eq {y : (Σ _ : Unit, T) → K'} (hP : IsArithVar (mCoordIdeal y) 1) {c : Unit → T}
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (R : Finset ((Σ _ : Unit, T) → ℂ))
    (hR : ∀ t ∈ R, t ∈ mcPts (mCoordIdeal y))
    (hU : ∀ z ∈ mcPts (mCoordIdeal y), ∃! t, t ∈ R ∧ SameOrbit z t)
    (F : ((Σ _ : Unit, T) → ℂ) → ℝ) (hF : ∀ t : ℂ, t ≠ 0 → ∀ z, F (fun p => t * z p) = F z)
    [Fintype (blockFnField y →ₐ[ℚ] ℂ)] :
    ∑ t ∈ R, F t = ∑ φ : blockFnField y →ₐ[ℚ] ℂ, F (ptOf y c φ) := by
  have hex : ∀ t ∈ R, ∃ φ : blockFnField y →ₐ[ℚ] ℂ,
      ptOf y c φ = (fun p => (t ⟨p.1, c p.1⟩)⁻¹ * t p) ∧ ∀ k, t ⟨k, c k⟩ ≠ 0 :=
    fun t ht => exists_ptOf hP hc (hR t ht)
  refine Finset.sum_bij (fun t ht => (hex t ht).choose) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro t ht t' ht' he
    have h1 := (hex t ht).choose_spec
    have h2 := (hex t' ht').choose_spec
    rw [he] at h1
    obtain ⟨u, -, hu⟩ := hU t (hR t ht)
    have e1 : t = u := hu t ⟨ht, ⟨fun _ => 1, fun _ => one_ne_zero, by simp⟩⟩
    have e2 : t' = u := by
      refine hu t' ⟨ht', fun k => t ⟨k, c k⟩ * (t' ⟨k, c k⟩)⁻¹,
        fun k => mul_ne_zero (h1.2 k) (inv_ne_zero (h2.2 k)), funext fun p => ?_⟩
      have := congrFun (h1.1.symm.trans h2.1) p
      have h0 := h1.2 p.1
      have h0' := h2.2 p.1
      simp only at this ⊢
      rw [show t p = t ⟨p.1, c p.1⟩ * ((t ⟨p.1, c p.1⟩)⁻¹ * t p) by field_simp, this]
      ring
    rw [e1, e2]
  · intro φ _
    obtain ⟨u, ⟨hu, ⟨d, hd, hdu⟩⟩, -⟩ := hU _ (ptOf_mem hc φ)
    refine ⟨u, hu, eq_of_ptOf_eq_smul hc ((u ⟨(), c ()⟩)⁻¹ * (d ())⁻¹) ?_⟩
    rw [(hex u hu).choose_spec.1, hdu]
    funext p
    have h0 := hd ()
    ring_nf
    field_simp
  · intro t ht
    rw [(hex t ht).choose_spec.1]
    exact (hF _ (inv_ne_zero ((hex t ht).choose_spec.2 ())) t).symm

theorem sum_ringHom_restrict (κ : IntermediateField ℚ K') (H : (κ →ₐ[ℚ] ℂ) → ℝ)
    [Fintype (κ →ₐ[ℚ] ℂ)] :
    ∑ σ : K' →+* ℂ, H ((σ.toRatAlgHom).comp (IsScalarTower.toAlgHom ℚ κ K')) =
      (Module.finrank κ K' : ℝ) * ∑ f, H f := by
  classical
  rw [Fintype.sum_equiv (RingHom.equivRatAlgHom K' ℂ)
    (fun σ : K' →+* ℂ => H ((σ.toRatAlgHom).comp (IsScalarTower.toAlgHom ℚ κ K')))
    (fun σ : K' →ₐ[ℚ] ℂ => H (σ.comp (IsScalarTower.toAlgHom ℚ κ K'))) (fun _ => rfl)]
  let res : (K' →ₐ[ℚ] ℂ) → (κ →ₐ[ℚ] ℂ) := fun σ => σ.comp (IsScalarTower.toAlgHom ℚ κ K')
  rw [← Fintype.sum_fiberwise res, Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  have hconst : ∀ i : {σ // res σ = f}, H (res i) = H f := fun i => by rw [i.2]
  rw [Finset.sum_congr rfl fun i _ => hconst i, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  congr 1
  have e : {σ // res σ = f} ≃ @AlgHom κ K' ℂ _ _ _ _ f.toRingHom.toAlgebra :=
    ((algHomEquivSigma (A := ℚ) (B := κ) (C := K') (D := ℂ)).subtypeEquiv
      (p := fun σ => res σ = f) (q := fun x => x.1 = f) fun σ => Iff.rfl).trans (Equiv.sigmaSubtype f)
  let _ := f.toRingHom.toAlgebra
  rw [Fintype.card_eq_nat_card, Nat.card_congr e,
    AlgHom.natCard_of_splits κ K' ℂ fun _ => IsAlgClosed.splits _]

end PointArithIntersection


open PointArithIntersection IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree in
theorem PointArInt.proof : PointArInt.Statement := by
  intro T _ K' _ _ y A s hP hs
  classical
  obtain ⟨c0, hc0⟩ := hP.2.1.2.2 ()
  let c : Unit → T := fun _ => c0
  have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h => hc0 (X_mem_of_eq_zero h)
  obtain ⟨R, hR, hU, hsum⟩ := Inter.regularityPointsSum_holds.proof Unit (fun _ => T) (mCoordIdeal y) hP
  have harInt : arInt (mCoordIdeal y) s A (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine (fun _ : Unit => T)) =
      ∑ t ∈ R, logNorm A s t := by
    unfold arInt
    have e0 : (fun (j : Fin 0) (z : (Σ _ : Unit, T) → ℂ) =>
        Real.log (((Fin.elim0 j : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (fun _ : Unit => T))).h z)) =
        (Fin.elim0 : Fin 0 → ((Σ _ : Unit, T) → ℂ) → ℝ) := funext fun j => j.elim0
    rw [e0]
    apply hsum
    rintro z z' - ⟨d, hd, rfl⟩
    exact logNorm_smul hs (d ()) (hd ()) z'
  set κ := blockFnField y
  have hσ : ∀ σ : K' →+* ℂ, logNorm A s (fun p => σ (y p)) =
      logNorm A s (ptOf y c ((σ.toRatAlgHom).comp (IsScalarTower.toAlgHom ℚ κ K'))) := by
    intro σ
    have hy0 : σ (y ⟨(), c0⟩) ≠ 0 := (map_ne_zero σ).mpr (hc ())
    have e : (fun p => σ (y p)) = fun p => σ (y ⟨(), c0⟩) *
        ptOf y c ((σ.toRatAlgHom).comp (IsScalarTower.toAlgHom ℚ κ K')) p := by
      funext p
      have : ptOf y c ((σ.toRatAlgHom).comp (IsScalarTower.toAlgHom ℚ κ K')) p =
          σ (y p / y ⟨(), c0⟩) := rfl
      rw [this, map_div₀]
      field_simp
    rw [e, logNorm_smul hs _ hy0]
  rw [harInt, sum_reps_eq hP hc R hR hU (logNorm A s) (fun t ht z => logNorm_smul hs t ht z),
    Finset.sum_congr rfl (fun σ _ => hσ σ),
    sum_ringHom_restrict κ (fun φ => logNorm A s (ptOf y c φ)), degC_eq hP,
    AlgHom.natCard_of_splits ℚ κ ℂ fun _ => IsAlgClosed.splits _, ← Module.finrank_mul_finrank ℚ κ K']
  push_cast
  ring

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PPointDegCPos
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 NumberField

noncomputable section

namespace PointDegreeComplexPositive

theorem card_algHom_pos {K' : Type} [Field K'] [NumberField K'] (E : IntermediateField ℚ K') :
    0 < Nat.card (E →ₐ[ℚ] ℂ) := by
  have : FiniteDimensional ℚ E := inferInstance
  have : Algebra.IsAlgebraic ℚ E := Algebra.IsAlgebraic.of_finite ℚ E
  have : Nonempty (E →ₐ[ℚ] ℂ) := ⟨IsAlgClosed.lift⟩
  exact Nat.card_pos

end PointDegreeComplexPositive

theorem PointDegCPos.proof : PointDegCPos.Statement := by
  intro T _ K' _ _ y hP
  rw [IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.full Unit (fun _ => T) K' y hP]
  exact PointDegreeComplexPositive.card_algHom_pos _

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PPointVertR
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section

namespace PointVertRAux

theorem degC_eq_finrank {T : Type} [Fintype T] {K' : Type} [Field K'] [NumberField K']
    {y : (Σ _ : Unit, T) → K'} (hP : IsArithVar (mCoordIdeal y) 1) :
    degC (mCoordIdeal y) = Module.finrank ℚ (blockFnField y) := by
  rw [IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.full Unit (fun _ => T) K' y hP, Nat.card_eq_fintype_card,
    AlgHom.card]

end PointVertRAux

theorem PointVertR.proof (hI : VertRIndex.Statement) (hN : SectionIndexNorm.Statement) :
    PointVertR.Statement := by
  intro T _ K' _ _ y s hP hs hsP
  rw [hI T K' y s hP hs hsP, PointVertRAux.degC_eq_finrank hP,
    ← (letI : Module.Free (blockFnField y) K' := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (blockFnField y) K'), Nat.cast_mul, mul_assoc,
    hN T K' y s hP hs hsP]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PVertPointMultChart
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

namespace VerticalPointMultiplicityChart

theorem length_localizedModule_quotient {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime] (I : Ideal R) :
    Module.length (Localization.AtPrime p) (LocalizedModule p.primeCompl (R ⧸ I)) =
      Module.length (Localization.AtPrime p)
        (Localization.AtPrime p ⧸ I.map (algebraMap R (Localization.AtPrime p))) := by
  have := IsLocalization.linearMap_compatibleSMul p.primeCompl
  let e := (IsLocalizedModule.linearEquiv p.primeCompl
    (I.toLocalizedQuotient' (Localization.AtPrime p) p.primeCompl
      (Algebra.linearMap R (Localization.AtPrime p)))
    (LocalizedModule.mkLinearMap p.primeCompl (R ⧸ I))).restrictScalars (Localization.AtPrime p)
  rw [← e.length_eq]
  exact (Submodule.quotEquivOfEq _ _ (Ideal.localized'_eq_map _ _ I)).length_eq

theorem length_quotient_of_surjective {A N : Type*} [CommRing A] [CommRing N] (Φ : A →+* N)
    (hΦ : Function.Surjective Φ) (J : Ideal A) (hJ : RingHom.ker Φ ≤ J) :
    Module.length A (A ⧸ J) = Module.length N (N ⧸ J.map Φ) := by
  let _ := Φ.toAlgebra
  have hs : Function.Surjective (algebraMap A (N ⧸ J.map Φ)) :=
    (Ideal.Quotient.mk_surjective).comp hΦ
  have hker : RingHom.ker (Algebra.ofId A (N ⧸ J.map Φ)) = J := by
    ext x
    rw [RingHom.mem_ker]
    change Ideal.Quotient.mk _ (Φ x) = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap, Ideal.comap_map_of_surjective _ hΦ,
      ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hJ]
  let e := (Ideal.quotientEquivAlgOfEq A hker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId A (N ⧸ J.map Φ)) hs)
  rw [e.toLinearEquiv.length_eq]
  exact Module.length_eq_of_surjective hΦ

theorem aeval_C_mul_X {T : Type} [Fintype T] {S : Type*} [CommRing S] (r : (Σ _ : Unit, T) → S)
    (f : MRing (fun _ : Unit => T)) (d : ℕ) (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f (fun _ => d)) :
    eval₂ (Int.castRingHom (Polynomial S)) (fun p => Polynomial.C (r p) * Polynomial.X) f =
      Polynomial.C (eval₂ (Int.castRingHom S) r f) * Polynomial.X ^ d := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [eval₂_eq, eval₂_eq, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmd : ∑ i, m ⟨(), i⟩ = d := hf m hm ()
  rw [Finset.prod_subset (Finset.subset_univ m.support) (fun p _ hp => by
      rw [Finsupp.notMem_support_iff.mp hp, pow_zero]),
    Finset.prod_subset (Finset.subset_univ m.support) (fun p _ hp => by
      rw [Finsupp.notMem_support_iff.mp hp, pow_zero])]
  simp_rw [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [Fintype.sum_sigma, Fintype.sum_unique, hmd, map_mul, map_prod]
  simp only [map_pow, eq_intCast, map_intCast]
  ring

end VerticalPointMultiplicityChart


open VerticalPointMultiplicityChart in
theorem VertPointMultChart.proof (hCh : VertPointChart.Statement) (hN : VertPointNagata.Statement) :
    VertPointMultChart.Statement := by
  intro T _ K' _ _ y s hP hs hsP W hW t ht a b hb hab
  obtain ⟨hmax, hrat, -⟩ := hCh T K' y s hP hs hsP W hW t ht
  have hWp : W.IsPrime := hW.1.1.1
  have hmp : (curvePtIdeal y W).IsPrime := hmax.isPrime
  choose a' b' hb' hab' using hrat
  obtain ⟨Φ, hsurj, hker, hΦ⟩ := hN T K' y s hP hs hsP W hW t ht a' b' hb' hab'
  have hPW : mCoordIdeal y ≤ W := le_sup_left.trans hW.1.1.2
  have hyt : y ⟨(), t⟩ ≠ 0 := by
    intro h0
    apply ht
    apply hPW
    change _ ∈ RingHom.ker _
    rw [RingHom.mem_ker, mConeMap, aeval_X, h0, map_zero, zero_mul]

  have hunit : ∀ x : (curvePtIdeal y W).primeCompl, IsUnit ((curveRing y).subtype x) := fun x =>
    isUnit_iff_ne_zero.mpr fun h => x.2 (by
      rw [show (x : curveRing y) = 0 from Subtype.ext h]; exact zero_mem _)
  let ι : Localization.AtPrime (curvePtIdeal y W) →+* K' := IsLocalization.lift hunit
  have hinj : Function.Injective ι := by
    rw [IsLocalization.lift_injective_iff]
    intro x z
    rw [(IsLocalization.injective (M := (curvePtIdeal y W).primeCompl) (Localization.AtPrime (curvePtIdeal y W))
      (le_nonZeroDivisors_of_noZeroDivisors fun h => h (zero_mem _))).eq_iff]
    exact Subtype.val_injective.eq_iff.symm
  have hbc : b ∈ (curvePtIdeal y W).primeCompl := hb
  have hbc' : ∀ u, b' u ∈ (curvePtIdeal y W).primeCompl := hb'
  let r : (Σ _ : Unit, T) → Localization.AtPrime (curvePtIdeal y W) := fun p =>
    IsLocalization.mk' _ (a' p.2) (⟨b' p.2, hbc' p.2⟩ : (curvePtIdeal y W).primeCompl)
  have hιr : ∀ p, ι (r p) = y p / y ⟨(), t⟩ := by
    rintro ⟨⟨⟩, u⟩
    exact (IsLocalization.lift_mk'_spec _ _ _ _).mpr (hab' u).symm
  have hιa : ∀ f : MRing (fun _ : Unit => T), ι (aeval r f) = aeval (fun p => ι (r p)) f := fun f => by
    induction f using MvPolynomial.induction_on with
    | C n => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p i hp => simp [hp]
  have hsr : aeval r s = IsLocalization.mk' _ a (⟨b, hbc⟩ : (curvePtIdeal y W).primeCompl) := by
    apply hinj
    rw [hιa, funext hιr, VerticalPointResidue.aeval_div y t s 1 hs]
    symm
    refine (IsLocalization.lift_mk'_spec _ _ _ _).mpr ?_
    change (a : K') = (b : K') * (aeval y s * (y ⟨(), t⟩ ^ 1)⁻¹)
    rw [pow_one, ← mul_assoc, hab, mul_assoc, mul_inv_cancel₀ hyt, mul_one]

  have hX : (Polynomial.X : Polynomial (Localization.AtPrime (curvePtIdeal y W))) ∈
      ((IsLocalRing.maximalIdeal (Localization.AtPrime (curvePtIdeal y W))).map
        (Polynomial.C : _ →+* Polynomial _)).primeCompl := by
    intro h
    have h1 := Ideal.mem_map_C_iff.mp h 1
    rw [Polynomial.coeff_X_one] at h1
    exact (IsLocalRing.maximalIdeal _).ne_top_iff_one.mp (IsLocalRing.maximalIdeal.isMaximal _).ne_top h1
  have hbu : IsUnit (IsLocalization.mk' (Localization.AtPrime (curvePtIdeal y W)) (1 : curveRing y)
      (⟨b, hbc⟩ : (curvePtIdeal y W).primeCompl)) := by
    exact isUnit_iff_exists_inv.mpr ⟨algebraMap _ _ b, (IsLocalization.mk'_spec _ _ _).trans (map_one _)⟩
  have hΦs : Φ (algebraMap _ _ s) =
      algebraMap (Localization.AtPrime (curvePtIdeal y W)) (nagataRing (Localization.AtPrime (curvePtIdeal y W)))
        (algebraMap (curveRing y) _ a) *
      (algebraMap (Polynomial (Localization.AtPrime (curvePtIdeal y W))) (nagataRing (Localization.AtPrime (curvePtIdeal y W)))
        (Polynomial.C (IsLocalization.mk' (Localization.AtPrime (curvePtIdeal y W)) (1 : curveRing y)
          (⟨b, hbc⟩ : (curvePtIdeal y W).primeCompl))) *
        algebraMap (Polynomial (Localization.AtPrime (curvePtIdeal y W))) (nagataRing (Localization.AtPrime (curvePtIdeal y W))) Polynomial.X) := by
    have hΦ' : Φ (algebraMap _ _ s) = algebraMap (Polynomial (Localization.AtPrime (curvePtIdeal y W)))
        (nagataRing (Localization.AtPrime (curvePtIdeal y W)))
        (aeval (fun p => Polynomial.C (r p) * Polynomial.X) s) := hΦ s
    rw [hΦ', aeval_def, RingHom.ext_int (algebraMap ℤ (Polynomial (Localization.AtPrime (curvePtIdeal y W))))
      (Int.castRingHom (Polynomial (Localization.AtPrime (curvePtIdeal y W)))), aeval_C_mul_X r s 1 hs,
      ← RingHom.ext_int (algebraMap ℤ (Localization.AtPrime (curvePtIdeal y W)))
        (Int.castRingHom (Localization.AtPrime (curvePtIdeal y W))), ← aeval_def, hsr, IsLocalization.mk'_eq_mul_mk'_one, pow_one, map_mul, map_mul,
      map_mul, IsScalarTower.algebraMap_apply (Localization.AtPrime (curvePtIdeal y W))
        (Polynomial (Localization.AtPrime (curvePtIdeal y W))) (nagataRing _), Polynomial.algebraMap_eq,
      mul_assoc]
  have hv : IsUnit (algebraMap (Polynomial (Localization.AtPrime (curvePtIdeal y W))) (nagataRing (Localization.AtPrime (curvePtIdeal y W)))
        (Polynomial.C (IsLocalization.mk' (Localization.AtPrime (curvePtIdeal y W)) (1 : curveRing y)
          (⟨b, hbc⟩ : (curvePtIdeal y W).primeCompl))) *
        algebraMap (Polynomial (Localization.AtPrime (curvePtIdeal y W))) (nagataRing (Localization.AtPrime (curvePtIdeal y W))) Polynomial.X) :=
    ((hbu.map Polynomial.C).map _).mul (IsLocalization.map_units _ ⟨_, hX⟩)

  have hJ : ((mCoordIdeal y ⊔ Ideal.span {s}).map (algebraMap _ (Localization.AtPrime W))).map Φ =
      (Ideal.span {algebraMap (curveRing y) (Localization.AtPrime (curvePtIdeal y W)) a}).map
        (algebraMap _ (nagataRing (Localization.AtPrime (curvePtIdeal y W)))) := by
    rw [Ideal.map_sup, Ideal.map_sup, (Ideal.map_eq_bot_iff_le_ker _).mpr hker.ge, bot_sup_eq,
      Ideal.map_span, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton,
      Set.image_singleton, hΦs, Ideal.span_singleton_mul_right_unit hv]

  have hmap : (IsLocalRing.maximalIdeal (Localization.AtPrime (curvePtIdeal y W))).map
      (algebraMap _ (nagataRing (Localization.AtPrime (curvePtIdeal y W)))) =
      IsLocalRing.maximalIdeal (nagataRing (Localization.AtPrime (curvePtIdeal y W))) := by
    rw [IsScalarTower.algebraMap_eq (Localization.AtPrime (curvePtIdeal y W))
      (Polynomial (Localization.AtPrime (curvePtIdeal y W))) (nagataRing _), ← Ideal.map_map,
      Polynomial.algebraMap_eq, IsLocalization.AtPrime.map_eq_maximalIdeal]
  have : IsLocalHom (algebraMap (Localization.AtPrime (curvePtIdeal y W))
      (nagataRing (Localization.AtPrime (curvePtIdeal y W)))) := by
    refine ⟨fun x hx => ?_⟩
    by_contra hx'
    have h1 : x ∈ IsLocalRing.maximalIdeal _ := hx'
    have h2 := Ideal.mem_map_of_mem (algebraMap _ (nagataRing (Localization.AtPrime (curvePtIdeal y W)))) h1
    rw [hmap] at h2
    exact h2 hx
  have hfib : Module.length (nagataRing (Localization.AtPrime (curvePtIdeal y W)))
      (nagataRing (Localization.AtPrime (curvePtIdeal y W)) ⧸
        (IsLocalRing.maximalIdeal (Localization.AtPrime (curvePtIdeal y W))).map
          (algebraMap _ (nagataRing (Localization.AtPrime (curvePtIdeal y W))))) = 1 := by
    rw [hmap]
    have : IsSimpleModule (nagataRing (Localization.AtPrime (curvePtIdeal y W)))
        (nagataRing (Localization.AtPrime (curvePtIdeal y W)) ⧸
          IsLocalRing.maximalIdeal (nagataRing (Localization.AtPrime (curvePtIdeal y W)))) :=
      isSimpleModule_iff_quot_maximal.mpr ⟨_, inferInstance, ⟨LinearEquiv.refl _ _⟩⟩
    exact Module.length_eq_one _ _

  rw [multAt, dite_eq_left hWp, locLen, dite_eq_left hmp]
  congr 1
  rw [length_localizedModule_quotient, length_localizedModule_quotient,
    length_quotient_of_surjective Φ hsurj _ (hker.le.trans (Ideal.map_mono le_sup_left)), hJ,
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (nagataRing (Localization.AtPrime (curvePtIdeal y W)))
      (Ideal.span {algebraMap (curveRing y) (Localization.AtPrime (curvePtIdeal y W)) a})).toLinearEquiv.length_eq,
    IsLocalRing.length_baseChange, hfib, mul_one, Ideal.map_span, Set.image_singleton]

end

end GroundTheory.Heights₂.Heights
end

