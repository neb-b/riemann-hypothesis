module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.IsOpenPart
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0087
public import Formalism.LocalToGlobal.LatticeGeometry.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QuadraticCharProductFormulaCMHost
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.Divisibility.Bundle0001
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0098

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIntegralOfDivisibleCharacters
section
open Formalism.MainNotions.DIV.Cons (intO)
open Polynomial

namespace GlobalTheory.IntegralOfPointValues

theorem mem_intO_of_isIntegral {C : Type} [NormedField C] [IsUltrametricDist C] {z : C}
    (hz : IsIntegral ↥(intO C) z) : z ∈ intO C := by
  let V : ValuationSubring C :=
    { intO C with
      mem_or_inv_mem' := fun x => by
        change ‖x‖ ≤ 1 ∨ ‖x⁻¹‖ ≤ 1
        rcases le_total ‖x‖ 1 with h | h
        · exact Or.inl h
        · exact Or.inr (by rw [norm_inv]; exact inv_le_one_of_one_le₀ h) }
  have hz' : IsIntegral V z := hz
  obtain ⟨v, rfl⟩ := (IsIntegrallyClosed.isIntegral_iff (R := V) (K := C)).1 hz'
  exact v.2


open Polynomial in
theorem _root_.GlobalTheory.IntegralOfPointValues.isIntegral_inv_smul_of_closed {O C B₀ B₁ : Type*} [CommRing O] [Field C] [IsAlgClosed C]
    [Algebra O C] (hinj : Function.Injective (algebraMap O C))
    (hcl : ∀ z : C, IsIntegral O z → z ∈ (algebraMap O C).range)
    [CommRing B₀] [Algebra O B₀] [Algebra.IsIntegral O B₀] [CommRing B₁] [Algebra C B₁]
    [Algebra O B₁] [IsScalarTower O C B₁] (j : B₀ →ₐ[O] B₁) (x : B₀) (q : O) (hq : q ≠ 0)
    (h : ∀ χ : B₀ →ₐ[O] O, q ∣ χ x) : IsIntegral O ((algebraMap O C q)⁻¹ • j x) := by
  classical
  set y := j x with hy
  set a := (algebraMap O C q)⁻¹ with ha
  have hjint : ∀ b, IsIntegral C (j b) := fun b =>
    ((Algebra.IsIntegral.isIntegral (R := O) b).map j).tower_top
  have hyint : IsIntegral C y := hjint x
  have hroot : ∀ α ∈ (minpoly C y).roots, ∃ k : O, algebraMap O C k = a * α := by
    intro α hα
    set D := Algebra.adjoin C (Set.range j) with hD
    haveI : Algebra.IsIntegral C D :=
      Algebra.IsIntegral.adjoin (by rintro _ ⟨b, rfl⟩; exact hjint b)
    have hmem : ∀ b, j b ∈ D := fun b => Algebra.subset_adjoin ⟨b, rfl⟩
    let yD : D := ⟨y, hmem x⟩
    have hnu : yD - algebraMap C D α ∈ nonunits D := by
      intro hu
      have hu' : IsUnit (y - algebraMap C B₁ α) := by
        simpa using hu.map D.val
      have hαr : IsRoot (minpoly C y) α := (mem_roots (minpoly.ne_zero hyint)).1 hα
      have hfac := mul_divByMonic_eq_iff_isRoot.2 hαr
      have hmon : ((minpoly C y) /ₘ (X - Polynomial.C α)).Monic :=
        (monic_X_sub_C α).of_mul_monic_left (by rw [hfac]; exact minpoly.monic hyint)
      apply minpoly.aeval_ne_zero_of_dvdNotUnit_minpoly (A := C) (x := y) hyint hmon
      · refine ⟨hmon.ne_zero, X - Polynomial.C α, ?_, by rw [mul_comm, hfac]⟩
        exact not_isUnit_X_sub_C α
      · have h0 := minpoly.aeval C y
        rw [← hfac, map_mul] at h0
        simpa using (hu'.mul_right_eq_zero).1 (by simpa using h0)
    obtain ⟨M, hMmax, hMmem⟩ := exists_max_ideal_of_mem_nonunits hnu
    letI : Field (D ⧸ M) := Ideal.Quotient.field M
    have hbij : Function.Bijective (algebraMap C (D ⧸ M)) :=
      IsAlgClosed.algebraMap_bijective_of_isIntegral
    let e : C ≃ₐ[C] D ⧸ M := AlgEquiv.ofBijective (Algebra.ofId C (D ⧸ M)) hbij
    let ψ : D →ₐ[C] C := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ C M)
    have hψy : ψ yD = α := by
      have h1 : Ideal.Quotient.mkₐ C M yD = e α := by
        rw [Ideal.Quotient.mkₐ_eq_mk]
        change _ = Ideal.Quotient.mk M (algebraMap C D α)
        rw [Ideal.Quotient.eq]
        exact hMmem
      simp only [ψ, AlgHom.comp_apply, h1]
      exact e.symm_apply_apply α
    have hcomm : ∀ o : O,
        (⟨j (algebraMap O B₀ o), hmem _⟩ : D) = algebraMap C D (algebraMap O C o) :=
      fun o => by ext; simp [IsScalarTower.algebraMap_apply O C B₁]
    let jres : B₀ →+* D := (j : B₀ →+* B₁).codRestrict D hmem
    let χ₀ : B₀ →ₐ[O] C :=
      { ψ.toRingHom.comp jres with
        commutes' := fun o => by
          show ψ ⟨j (algebraMap O B₀ o), hmem _⟩ = _
          rw [hcomm]; exact ψ.commutes _ }
    have hχ₀x : χ₀ x = α := hψy
    have hval : ∀ b, χ₀ b ∈ (⊥ : Subalgebra O C) := fun b => by
      rw [Algebra.mem_bot]
      obtain ⟨t, ht⟩ := hcl _ ((Algebra.IsIntegral.isIntegral (R := O) b).map χ₀)
      exact ⟨t, ht⟩
    let eb := Algebra.botEquivOfInjective hinj
    let χ : B₀ →ₐ[O] O := eb.toAlgHom.comp (χ₀.codRestrict ⊥ hval)
    have hback : ∀ s : (⊥ : Subalgebra O C), algebraMap O C (eb s) = s := fun s => by
      have h2 : eb.symm (eb s) = s := eb.symm_apply_apply s
      rw [← Algebra.algebraMap_self_apply (eb s), eb.symm.commutes] at h2
      exact congrArg Subtype.val h2
    have hχx : algebraMap O C (χ x) = α := by
      rw [← hχ₀x]; exact hback _
    obtain ⟨k, hk⟩ := h χ
    refine ⟨k, ?_⟩
    have hq' : algebraMap O C q ≠ 0 := (map_ne_zero_iff _ hinj).2 hq
    rw [← hχx, hk, map_mul, ha, ← mul_assoc, inv_mul_cancel₀ hq', one_mul]
  set s := (minpoly C y).roots with hs
  let f : C → O := fun α => if hh : ∃ k : O, algebraMap O C k = a * α then hh.choose else 0
  have hf : ∀ α ∈ s, algebraMap O C (f α) = a * α := fun α hα => by
    have hh := hroot α hα
    simp only [f, dif_pos hh]
    exact hh.choose_spec
  have hsplit : minpoly C y = (s.map fun α => X - Polynomial.C α).prod :=
    (IsAlgClosed.splits (minpoly C y)).eq_prod_roots_of_monic (minpoly.monic hyint)
  have hzero : (s.map fun α => y - algebraMap C B₁ α).prod = 0 := by
    have h0 := minpoly.aeval C y
    rw [hsplit, map_multiset_prod, Multiset.map_map] at h0
    simpa [Function.comp_def] using h0
  refine ⟨(s.map fun α => X - Polynomial.C (f α)).prod,
    monic_multiset_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _), ?_⟩
  rw [eval₂_multiset_prod, Multiset.map_map]
  have hfac : ∀ α ∈ s, (eval₂ (algebraMap O B₁) (a • y) ∘ fun α => X - Polynomial.C (f α)) α =
      algebraMap C B₁ a * (y - algebraMap C B₁ α) := fun α hα => by
    simp only [Function.comp_apply, eval₂_sub, eval₂_X, eval₂_C]
    rw [IsScalarTower.algebraMap_apply O C B₁, hf α hα, Algebra.smul_def, map_mul, mul_sub]
  rw [Multiset.map_congr rfl hfac, Multiset.prod_map_mul, hzero, mul_zero]

theorem isIntegral_inv_smul : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] (B₀ B₁ : Type) [CommRing B₀] [Algebra ↥(intO C) B₀] [Module.Finite ↥(intO C) B₀] [CommRing B₁] [Algebra C B₁] [Algebra ↥(intO C) B₁] [IsScalarTower ↥(intO C) C B₁] (j : B₀ →ₐ[↥(intO C)] B₁) (x : B₀) (q : ↥(intO C)), q ≠ 0 → (∀ χ : B₀ →ₐ[↥(intO C)] ↥(intO C), q ∣ χ x) → IsIntegral ↥(intO C) (((q : C)⁻¹) • j x) := by
  intro C _ _ _ B₀ B₁ _ _ _ _ _ _ _ j x q hq h
  exact isIntegral_inv_smul_of_closed (O := ↥(intO C)) (C := C) Subtype.val_injective
    (fun z hz => ⟨⟨z, mem_intO_of_isIntegral hz⟩, rfl⟩) j x q hq h

end GlobalTheory.IntegralOfPointValues
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

namespace GlobalTheory.HeckeGal

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime]

theorem lPow_diagUnits (ι : Qbar l ≃+* ℂ) (n : (E →+* ℂ) → ℤ) (k : Eˣ) :
    lPow ι n (diagUnits E k) = ∏ φ : E →+* ℂ, ι.symm (φ (k : E)) ^ n φ := by
  classical
  let J : HeightOneSpectrum (𝓞 E) → Type := fun v => {j : v.adicCompletion E →+* Qbar l // Continuous j}
  let res : (Σ v, J v) → (E →+* ℂ) := fun p =>
    (ι.toRingHom.comp p.2.1).comp (algebraMap E (p.1.adicCompletion E))
  have hinj : Function.Injective res := by
    rintro ⟨v, j⟩ ⟨v', j'⟩ h
    have h1 : j.1.comp (algebraMap E (v.adicCompletion E)) = j'.1.comp (algebraMap E (v'.adicCompletion E)) := by
      ext a
      exact ι.injective (DFunLike.congr_fun h a)
    obtain rfl := GlobalTheory.HeckeGal.place_eq_of_contEmb_comp_eq E l v v' j.1 j'.1 j.2 j'.2 h1
    congr 1
    apply Subtype.ext
    apply DFunLike.coe_injective
    refine (HeightOneSpectrum.denseRange_algebraMap E v).equalizer j.2 j'.2 ?_
    funext a
    exact DFunLike.congr_fun h1 a
  have hsurj : Function.Surjective res := by
    intro φ
    obtain ⟨v, hv⟩ := GlobalTheory.LadicPlace.exists_place_of_embedding E l (ι.symm.toRingHom.comp φ)
    obtain ⟨j, hj, e⟩ := GlobalTheory.exists_continuous_extension_adicCompletion E l _ v hv
    refine ⟨⟨v, j, hj⟩, ?_⟩
    ext a
    have := DFunLike.congr_fun e a
    show ι (j (algebraMap E _ a)) = φ a
    rw [show j (algebraMap E _ a) = ι.symm (φ a) from this, ι.apply_symm_apply]
  haveI : Fintype (Σ v, J v) := Fintype.ofInjective res hinj
  haveI : ∀ v, Fintype (J v) := fun v => @Fintype.ofFinite _ (finite_contEmb (l := l) v)
  let F : (Σ v, J v) → Qbar l := fun p => ι.symm (res p (k : E)) ^ n (res p)
  have h1 : ∏ φ : E →+* ℂ, ι.symm (φ (k : E)) ^ n φ = ∏ p, F p :=
    (Fintype.prod_bijective res ⟨hinj, hsurj⟩ F _ fun _ => rfl).symm
  have h2 : ∀ v, locPow ι n v (((diagUnits E k : Ideles E) : AdeleRing (𝓞 E) E).2 v) = ∏ j : J v, F ⟨v, j⟩ := by
    intro v
    unfold locPow
    rw [finprod_eq_prod_of_fintype]
    refine Finset.prod_congr rfl fun j _ => ?_
    congr 1
    exact (ι.symm_apply_apply _).symm
  rw [h1, ← Finset.prod_fiberwise_of_maps_to (t := Finset.univ.image Sigma.fst) (g := Sigma.fst)
    (fun p hp => Finset.mem_image_of_mem _ hp)]
  unfold lPow
  simp only [h2]
  rw [finprod_eq_prod_of_mulSupport_subset (s := Finset.univ.image (Sigma.fst : (Σ v, J v) → _))]
  · refine Finset.prod_congr rfl fun v _ => ?_
    refine Finset.prod_bij (fun j _ => (⟨v, j⟩ : Σ v, J v)) (fun j _ => by simp) (fun a _ b _ h => ?_) ?_
      (fun _ _ => rfl)
    · exact eq_of_heq (Sigma.mk.inj h).2
    · rintro ⟨w, j⟩ hp
      obtain rfl : w = v := (Finset.mem_filter.mp hp).2
      exact ⟨j, Finset.mem_univ _, rfl⟩
  · intro v hv
    obtain ⟨j, -, -⟩ := Finset.exists_ne_one_of_prod_ne_one hv
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨⟨v, j⟩, Finset.mem_univ _, rfl⟩)

abbrev inlInf (E : Type) [Field E] [NumberField E] : (InfiniteAdeleRing E)ˣ →* Ideles E :=
  Units.map (MonoidHom.inl (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E))

abbrev inrFin (E : Type) [Field E] [NumberField E] : (FiniteAdeleRing (𝓞 E) E)ˣ →* Ideles E :=
  Units.map (MonoidHom.inr (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E))

theorem continuous_inlInf : Continuous (inlInf E) :=
  Continuous.units_map _ (continuous_id.prodMk continuous_const)

theorem continuous_inrFin : Continuous (inrFin E) :=
  Continuous.units_map _ (continuous_const.prodMk continuous_id)

theorem infDiag_eq (k : Eˣ) :
    infDiag k = inlInf E (Units.map (algebraMap E (InfiniteAdeleRing E)).toMonoidHom k) := by
  classical
  have h : ∀ y : (InfiniteAdeleRing E)ˣ, inlInf E y = ∏ w : InfinitePlace E,
      infIdele E w (Units.map (Pi.evalMonoidHom (fun w : InfinitePlace E => w.Completion) w) y) := by
    intro y
    have : y = ∏ w : InfinitePlace E, (Units.map (MonoidHom.mulSingle (fun w : InfinitePlace E => w.Completion) w)
        (Units.map (Pi.evalMonoidHom (fun w : InfinitePlace E => w.Completion) w) y) : (InfiniteAdeleRing E)ˣ) := by
      apply Units.ext
      rw [Units.coe_prod]
      exact (Finset.univ_prod_mulSingle (y : InfiniteAdeleRing E)).symm
    exact (congrArg (inlInf E) this).trans (map_prod (inlInf E) _ _)
  rw [h, infDiag, MonoidHom.finsetProd_apply]
  rfl

theorem IsAlgPos.eq_infPow {χ : HChar E} {n : (E →+* ℂ) → ℤ} (h : IsAlgPos χ n) {x : Ideles E}
    (hx : x ∈ infConn E) : ((χ.1 x : ℂˣ) : ℂ) = infPow n x := by
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨f, hf, hfe⟩ := exists_infPow_hom E n
  have hcl : IsClosed {y : (InfiniteAdeleRing E)ˣ | χ.1 (inlInf E y) = f (inlInf E y)} :=
    isClosed_eq (χ.2.1.comp continuous_inlInf) (hf.comp continuous_inlInf)
  have hmem := (denseRange_units_inf E).open_subset_closure_inter (isOpen_connectedComponentOfOne_inf E) hy
  have : y ∈ {y : (InfiniteAdeleRing E)ˣ | χ.1 (inlInf E y) = f (inlInf E y)} := by
    refine closure_minimal ?_ hcl hmem
    rintro _ ⟨hk, k, rfl⟩
    apply Units.ext
    show ((χ.1 (inlInf E _) : ℂˣ) : ℂ) = ((f (inlInf E _) : ℂˣ) : ℂ)
    rw [hfe, ← infDiag_eq]
    have h1 := h k (pos_of_mem_connectedComponentOfOne E k hk)
    rw [← infPow_diagUnits E n k] at h1
    refine Eq.trans h1 ?_
    rw [infDiag_eq]
    rfl
  rw [← hfe]
  exact congrArg Units.val this

theorem isOpen_ker_of_infConn (θ : Ideles E →* ℂˣ) (hθ : Continuous θ) (h : ∀ x ∈ infConn E, θ x = 1) :
    IsOpen (θ.ker : Set (Ideles E)) := by
  let p : Ideles E →* (InfiniteAdeleRing E)ˣ :=
    Units.map (MonoidHom.fst (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E))
  let q : Ideles E →* (FiniteAdeleRing (𝓞 E) E)ˣ :=
    Units.map (MonoidHom.snd (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E))
  have hp : Continuous p := Continuous.units_map _ continuous_fst
  have hq : Continuous q := Continuous.units_map _ continuous_snd
  have ho := ((isOpen_connectedComponentOfOne_inf E).preimage hp).inter
    ((show IsOpen ((θ.comp (inrFin E)).ker : Set (FiniteAdeleRing (𝓞 E) E)ˣ) from
      GlobalTheory.CuspRep.isOpen_ker_finIdele E (θ.comp (inrFin E)) (hθ.comp continuous_inrFin)).preimage hq)
  refine θ.ker.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset (ho.mem_nhds ⟨?_, ?_⟩) ?_)
  · rw [Set.mem_preimage, map_one]
    exact Subgroup.one_mem _
  · rw [Set.mem_preimage, map_one]
    exact Subgroup.one_mem _
  · rintro x ⟨h1, h2⟩
    have e : x = inlInf E (p x) * inrFin E (q x) :=
      Units.ext (Prod.ext (mul_one _).symm (one_mul _).symm)
    have h3 : θ (inrFin E (q x)) = 1 := h2
    show θ x = 1
    rw [e, map_mul, h3, mul_one]
    exact h _ ⟨_, h1, rfl⟩

theorem lPow_of_mem_infConn (ι : Qbar l ≃+* ℂ) (n : (E →+* ℂ) → ℤ) {x : Ideles E} (hx : x ∈ infConn E) :
    lPow ι n x = 1 := by
  obtain ⟨y, -, rfl⟩ := hx
  exact finprod_eq_one_of_forall_eq_one fun v => locPow_one ι n v

theorem IsGlobalArtin.exists_isLAdicOf {art : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art) (ι : Qbar l ≃+* ℂ)
    {χ : HChar E} {n : (E →+* ℂ) → ℤ} (h : IsAlgPos χ n) :
    ∃ r : G E Ω →* (Qbar l)ˣ, Continuous r ∧ IsLAdicOf art ι χ n r := by
  obtain ⟨f, hf, hfe⟩ := exists_infPow_hom E n
  obtain ⟨g, hg, hge⟩ := exists_lPow_hom E l ι n
  let θ : Ideles E →* ℂˣ := χ.1 * f⁻¹
  have hθ : Continuous θ := χ.2.1.mul hf.inv
  have hθe : ∀ x, ((θ x : ℂˣ) : ℂ) = ((χ.1 x : ℂˣ) : ℂ) * (infPow n x)⁻¹ := fun x => by
    rw [← hfe, ← Units.val_inv_eq_inv_val]
    rfl
  have hθ1 : ∀ x ∈ infConn E, θ x = 1 := fun x hx => by
    have : χ.1 x = f x := Units.ext (by rw [hfe, h.eq_infPow hx])
    show χ.1 x * (f x)⁻¹ = 1
    rw [this, mul_inv_cancel]
  let θ' : Ideles E →* (Qbar l)ˣ := (Units.map ι.symm.toRingHom.toMonoidHom).comp θ
  have hθ' : Continuous θ' := continuous_of_isOpen_ker' θ' (Subgroup.isOpen_mono (fun x hx => by
      rw [MonoidHom.mem_ker] at hx ⊢
      rw [MonoidHom.comp_apply, hx, map_one]) (isOpen_ker_of_infConn θ hθ hθ1))
  let ψ : Ideles E →* (Qbar l)ˣ := θ' * g
  have hψ : Continuous ψ := hθ'.mul hg
  have hψe : ∀ x, ((ψ x : (Qbar l)ˣ) : Qbar l) =
      ι.symm (((χ.1 x : ℂˣ) : ℂ) * (infPow n x)⁻¹) * lPow ι n x := fun x => by
    rw [← hθe, ← hge]
    rfl
  have hker : art.ker ≤ ψ.ker := by
    rw [ha.ker]
    refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) (isClosed_singleton.preimage hψ)
    · rintro _ ⟨k, rfl⟩
      apply Units.ext
      rw [hψe, χ.2.2 k, infPow_diagUnits, lPow_diagUnits, Units.val_one, one_mul, map_inv₀, map_prod]
      simp only [map_zpow₀]
      refine inv_mul_cancel₀ (Finset.prod_ne_zero_iff.mpr fun φ _ => zpow_ne_zero _ ?_)
      simp
    · intro x hx
      apply Units.ext
      rw [hψe, ← hθe, hθ1 x hx, lPow_of_mem_infConn ι n hx]
      simp
  let ρ : Gab E Ω →* (Qbar l)ˣ := art.liftOfSurjective ha.quot.surjective ⟨ψ, hker⟩
  have hρ : ∀ x, ρ (art x) = ψ x := fun x => art.liftOfRightInverse_comp_apply _ _ ⟨ψ, hker⟩ x
  have hρc : Continuous ρ := ha.quot.isQuotientMap.continuous_iff.mpr (hψ.congr fun x => (hρ x).symm)
  refine ⟨ρ.comp (toAb E Ω), hρc.comp QuotientGroup.continuous_mk, fun x σ hx => ?_⟩
  rw [MonoidHom.comp_apply, ← hx, hρ, hψe]

end GlobalTheory.HeckeGal

namespace GlobalTheory.Published

open GlobalTheory.HeckeGal

theorem GlobalArtinReciprocity.heckeLAdicCharacter : GlobalArtinReciprocity → HeckeLAdicCharacter := by
  intro H E Ω _ _ _ _ _
  obtain ⟨art, ha⟩ := H E Ω
  refine ⟨art, ha, fun l _ ι χ n h => ?_⟩
  obtain ⟨r, hr, hf⟩ := ha.exists_isLAdicOf ι h
  exact ⟨r, ⟨hr, hf⟩, fun r' h' => h'.2.unique ha.quot.surjective hf⟩

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTotallyComplexOfI
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem

namespace GlobalTheory.Mem.BaseEx

section ext

variable {K K' : Type} [Field K] [Field K'] (f : K →+* K')

end ext

section host

variable {R : Ranks} (H : Host R)

theorem conjugate_emb (g : R.GG) :
    ComplexEmbedding.conjugate (H.emb g) = H.emb (g * R.cc) := by
  rw [Formalism.L2.Geo.emb_mul_cc_comp]
  refine RingHom.ext fun x => ?_
  have hcm := H.isCMField_hostE
  have h : IsCMField.complexConj H.E x = H.conj x := by
    apply H.φ₀.injective
    rw [IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]
  show starRingEnd ℂ (H.emb g x) = H.emb g (H.conj x)
  rw [← h, IsCMField.complexEmbedding_complexConj]

theorem ex_emb_iff (g : R.GG) :
    (∃ t : Tau R, H.emb t = H.emb g) ↔ g ∈ R.Psi :=
  ⟨fun ⟨t, ht⟩ => (factEmb R H).1.1 ht ▸ t.2, fun h => ⟨⟨g, h⟩, rfl⟩⟩

theorem emb_cm (σ : H.E →+* ℂ) :
    (∃ t : Tau R, H.emb t = σ) ↔ ¬ ∃ t : Tau R, H.emb t = ComplexEmbedding.conjugate σ := by
  obtain ⟨g, rfl⟩ := (factEmb R H).1.2 σ
  rw [conjugate_emb, ex_emb_iff, ex_emb_iff]
  exact Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem g

theorem sum_emb_bijective : Function.Bijective
    (Sum.elim (fun t : Tau R => H.emb t) fun t : Tau R => ComplexEmbedding.conjugate (H.emb t)) := by
  have hc : ∀ σ : H.E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ :=
    fun σ => star_star σ
  have hi : ∀ {a b : Tau R}, H.emb a = H.emb b → a = b := fun h => Subtype.ext ((factEmb R H).1.1 h)
  constructor
  · rintro (a | a) (b | b) h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
    · rw [hi h]
    · exact absurd ⟨a, h⟩ ((emb_cm H (H.emb b)).1 ⟨b, rfl⟩)
    · exact absurd ⟨b, h.symm⟩ ((emb_cm H (H.emb a)).1 ⟨a, rfl⟩)
    · have := congrArg ComplexEmbedding.conjugate h
      rw [hc, hc] at this
      rw [hi this]
  · intro σ
    by_cases h : ∃ t : Tau R, H.emb t = ComplexEmbedding.conjugate σ
    · obtain ⟨t, ht⟩ := h
      exact ⟨Sum.inr t, by simp only [Sum.elim_inr]; rw [ht, hc]⟩
    · obtain ⟨t, ht⟩ := (emb_cm H σ).2 h
      exact ⟨Sum.inl t, ht⟩


end host

end GlobalTheory.Mem.BaseEx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QuadraticCharProductFormulaCMHostStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadraticChar_product_formula_CM_host : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (a : (H.F)ˣ), (∏ᶠ v : HeightOneSpectrum (𝓞 H.F), etaFin (L := H.E) H.F v a) * ∏ w : InfinitePlace H.F, etaInf H.F w a = 1 := by
  first | exact @GlobalTheory.EtaProduct.eta_product_formula | exact GlobalTheory.EtaProduct.eta_product_formula | (intros; apply GlobalTheory.EtaProduct.eta_product_formula <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDeterminantKernelOpenAndFactor
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.KerDet

variable {L : Type} [Field L] [NumberField L]

theorem finPartI_localIdele (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    finPartI L (Neutral.B1.localIdele L v x) = Neutral.B1.localIdele L v x :=
  finPartI_eq_self fun _ => rfl

theorem map_finPartI_locF {F : Type} [Field F] [NumberField F] [Algebra F L] {χ : HChar L} (h : χ.TrivOn F)
    (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) : χ.1 (finPartI L (locF F v k)) = 1 := by
  have h1 := h.1 v k
  unfold HChar.resFin at h1
  rw [MonoidHom.finsetProd_apply] at h1
  unfold GlobalTheory.Mem.Chr.locF
  rw [map_prod, map_prod, ← h1]
  exact Finset.prod_congr rfl fun Q _ => congrArg χ.1 (finPartI_localIdele Q _)

theorem le_exp_neg_one {γ : WithZero (Multiplicative ℤ)} (h : γ < 1) : γ ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
  rcases eq_or_ne γ 0 with rfl | h0
  · exact zero_le
  · rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
    omega


local notation "Ideles" => _root_.Neutral.B1.Ideles
local notation "infIdele" => _root_.ReciprocityTheory.Neutral.Bridge.HCFR.infIdele
local notation "diagUnits" => _root_.Neutral.B1.diagUnits

open Classical in
theorem kernel_open_and_factor : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), IsOpen (KD H : Set (Ideles H.E)) ∧ (∀ w y, infIdele H.E w y ∈ KD H) ∧ (∀ k : (H.F)ˣ, diagUnits H.E (upF H.F k) ∈ KD H) ∧ ∀ χ : HChar H.E, χ.TrivOn H.F → (∀ v, χ.TameAt v) → (∀ v, (∀ k, ¬ OverP H (H.g k) v) → χ.UnrAt v) → KD H ≤ (χ.1.comp (finPartI H.E)).ker := by
  intro R H
  refine ⟨KDq_empty H ▸ isOpen_KDq H ∅, fun w y => KDq_le_KD H ∅ (infIdele_mem_KDq H ∅ w y),
    fun k => KDq_le_KD H ∅ (diag_upF_mem_KDq H ∅ k), fun χ hT hta hu => (Subgroup.closure_le _).2 ?_⟩
  rintro a (ha | ⟨v, k, rfl⟩)
  · refine GlobalTheory.T.idele_character_trivial_on_local_units H.E χ.1 χ.2.1 (finPartI H.E a) (finPartI_mem_unitIdl.2 ha.1) (fun _ => rfl) fun v x hx => ?_
    have hx' : (x : v.adicCompletion H.E) = (a : AdeleRing (𝓞 H.E) H.E).2 v := hx
    have hxu : IsUnitAt v x := by
      unfold IsUnitAt
      rw [hx']
      exact ha.1 v
    by_cases hv : ∃ k, OverP H (H.g k) v
    · obtain ⟨k, hk⟩ := hv
      refine hta v x hxu (le_exp_neg_one ?_)
      rw [hx']
      exact ha.2 k v hk
    · exact hu v (not_exists.1 hv) x hxu
  · exact map_finPartI_locF hT v k

end GlobalTheory.Mem.KerDet
end

