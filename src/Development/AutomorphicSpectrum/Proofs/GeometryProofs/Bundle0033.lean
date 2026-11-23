module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PlaceEqOneOfNotMem
public import ReciprocityTheory.SemistableReduction.Bundle0022
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0028
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GlobalIndexFrameLogNorm
section
open NumberField Matrix IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame

namespace GlobalTheory.CompanionTheory.Ar.Cusp.GlobDet

section Index

variable {W : Type} [AddCommGroup W]

theorem relIndex_pair (Λ : AddSubgroup W) (M a : W →+ W) (hM : Function.Injective M)
    (hc : ∀ x, a (M x) = M (a x)) (h2 : Λ.map a ≤ Λ) (i2 : (Λ.map a).relIndex Λ ≠ 0)
    (h3 : Λ.map (a.comp M) ≤ Λ) (i3 : (Λ.map (a.comp M)).relIndex Λ ≠ 0) :
    Λ.relIndex (Λ.map M) ≠ 0 ∧ (Λ.map M).relIndex Λ ≠ 0 := by
  have e3 : Λ.map (a.comp M) = (Λ.map a).map M := by
    rw [AddSubgroup.map_map]
    congr 1
    ext x
    exact hc x
  have l1 : Λ.map (a.comp M) ≤ Λ.map M := by rw [e3]; exact AddSubgroup.map_mono h2
  have n1 : (Λ.map (a.comp M)).relIndex (Λ.map M) ≠ 0 := by
    rw [e3, AddSubgroup.relIndex_map_map_of_injective _ _ hM]; exact i2
  have o1 : (Λ.map M).relIndex (Λ.map (a.comp M)) ≠ 0 := by
    rw [AddSubgroup.relIndex_eq_one.2 l1]; exact one_ne_zero
  have o3 : Λ.relIndex (Λ.map (a.comp M)) ≠ 0 := by
    rw [AddSubgroup.relIndex_eq_one.2 h3]; exact one_ne_zero
  exact ⟨AddSubgroup.relIndex_ne_zero_trans o3 n1, AddSubgroup.relIndex_ne_zero_trans o1 i3⟩

end Index

variable {L : Type} [Field L] [NumberField L] {n : ℕ}

noncomputable def mulVecHom (T : Matrix (Fin n) (Fin n) L) : (Fin n → L) →+ (Fin n → L) :=
  AddMonoidHom.mk' (fun x => T *ᵥ x) (Matrix.mulVec_add T)

theorem mulVecHom_apply (T : Matrix (Fin n) (Fin n) L) (x : Fin n → L) : mulVecHom T x = T *ᵥ x := rfl

theorem frame_eq_map (T : Matrix (Fin n) (Fin n) L) :
    (frame T).toAddSubgroup = (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup.map (mulVecHom T) := by
  ext x
  rw [Submodule.mem_toAddSubgroup, AddSubgroup.mem_map, mem_frame]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨_, (Submodule.mem_toAddSubgroup _).2 (mem_frame.2 ⟨z, by simp⟩), rfl⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, rfl⟩ := mem_frame.1 ((Submodule.mem_toAddSubgroup _).1 hy)
    exact ⟨z, by simp [mulVecHom_apply]⟩

theorem frame_map_le (D : Matrix (Fin n) (Fin n) (𝓞 L)) :
    frame (D.map (algebraMap (𝓞 L) L)) ≤ frame (1 : Matrix (Fin n) (Fin n) L) := by
  rw [frame, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  exact mem_frame_one.2 fun i => ⟨D i k, rfl⟩

theorem log_abs_norm (x : 𝓞 L) (hx : x ≠ 0) :
    Real.log ((|Algebra.norm ℤ x| : ℤ) : ℝ) = ∑ σ : L →+* ℂ, Real.log ‖σ (algebraMap (𝓞 L) L x)‖ := by
  have hx' : algebraMap (𝓞 L) L x ≠ 0 := by simpa using hx
  rw [← Real.log_prod (fun σ _ => norm_ne_zero_iff.2 ((map_ne_zero σ).2 hx'))]
  congr 1
  have h1 : ∏ σ : L →+* ℂ, σ (algebraMap (𝓞 L) L x) =
      algebraMap ℚ ℂ (Algebra.norm ℚ (algebraMap (𝓞 L) L x)) := by
    rw [Algebra.norm_eq_prod_embeddings ℚ ℂ (algebraMap (𝓞 L) L x)]
    exact Fintype.prod_equiv (RingHom.equivRatAlgHom L ℂ) _ _
      (fun σ => by simp [RingHom.equivRatAlgHom_apply])
  rw [← norm_prod, h1, ← Algebra.coe_norm_int x]
  simp

theorem relIndex_frame (D : Matrix (Fin n) (Fin n) (𝓞 L)) (hD : D.det ≠ 0) :
    (((frame (D.map (algebraMap (𝓞 L) L))).toAddSubgroup.relIndex
      (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup : ℕ) : ℤ) = |Algebra.norm ℤ D.det| := by
  have hb : LinearIndependent L (fun k j => (1 : Matrix (Fin n) (Fin n) L) j k) := by
    have e : (fun k j => (1 : Matrix (Fin n) (Fin n) L) j k) = ⇑(Pi.basisFun L (Fin n)) := by
      funext k j
      simp [Matrix.one_apply, Pi.single_apply]
    rw [e]
    exact (Pi.basisFun L (Fin n)).linearIndependent
  have h := ReciprocityTheory.MultiplicativeHeights.relIndex_span_comb _ hb D hD
  have e : frame (D.map (algebraMap (𝓞 L) L)) = Submodule.span (𝓞 L)
      (Set.range fun j => ∑ i, D i j • fun l => (1 : Matrix (Fin n) (Fin n) L) l i) := by
    rw [frame]
    congr 2
    funext k j
    simp [Finset.sum_apply, Matrix.one_apply, Algebra.smul_def]
  rw [e]
  exact h

theorem relIndex_frame_ne (D : Matrix (Fin n) (Fin n) (𝓞 L)) (hD : D.det ≠ 0) :
    (frame (D.map (algebraMap (𝓞 L) L))).toAddSubgroup.relIndex
      (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup ≠ 0 := by
  intro h
  have h1 := relIndex_frame D hD
  rw [h, Nat.cast_zero, eq_comm, abs_eq_zero, Algebra.norm_eq_zero_iff] at h1
  exact hD h1

theorem log_relIndex_frame (D : Matrix (Fin n) (Fin n) (𝓞 L)) (hD : D.det ≠ 0) :
    Real.log (((frame (D.map (algebraMap (𝓞 L) L))).toAddSubgroup.relIndex
      (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup : ℕ) : ℝ) =
      ∑ σ : L →+* ℂ, Real.log ‖σ (algebraMap (𝓞 L) L D.det)‖ := by
  rw [← log_abs_norm _ hD, ← relIndex_frame D hD]
  simp

theorem exists_int_matrix (C : Matrix (Fin n) (Fin n) L) :
    ∃ (d : 𝓞 L) (D : Matrix (Fin n) (Fin n) (𝓞 L)), d ≠ 0 ∧
      D.map (algebraMap (𝓞 L) L) = algebraMap (𝓞 L) L d • C := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 L))
    (fun p : Fin n × Fin n => C p.1 p.2)
  choose D hD using hb
  refine ⟨b, Matrix.of fun i j => D (i, j), nonZeroDivisors.ne_zero b.2, ?_⟩
  ext i j
  simpa [Algebra.smul_def] using hD (i, j)

theorem coe_det (D : Matrix (Fin n) (Fin n) (𝓞 L)) :
    algebraMap (𝓞 L) L D.det = (D.map (algebraMap (𝓞 L) L)).det := by
  rw [RingHom.map_det]
  rfl

theorem gIdx_frame : ∀ (L : Type) [Field L] [NumberField L] (n : ℕ) (C : Matrix (Fin n) (Fin n) L),
    C.det ≠ 0 →
    (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup.relIndex (frame C).toAddSubgroup ≠ 0 ∧
    (frame C).toAddSubgroup.relIndex (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup ≠ 0 ∧
    gIdx (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup (frame C).toAddSubgroup =
      ∑ σ : L →+* ℂ, Real.log ‖σ C.det‖ := by
  intro L _ _ n C hC
  obtain ⟨d, D, hd, hDC⟩ := exists_int_matrix C
  have hδ : algebraMap (𝓞 L) L d ≠ 0 := by simpa using hd
  obtain ⟨δ, hδe⟩ : ∃ δ, δ = algebraMap (𝓞 L) L d := ⟨_, rfl⟩
  rw [← hδe] at hDC hδ
  obtain ⟨S, hSe⟩ : ∃ S : Matrix (Fin n) (Fin n) (𝓞 L), S = d • 1 := ⟨_, rfl⟩
  have hS : S.map (algebraMap (𝓞 L) L) = δ • 1 := by
    ext i j
    by_cases h : i = j <;> simp [hSe, hδe, Matrix.smul_apply, Matrix.one_apply, h]
  have hSdet : S.det = d ^ n := by simp [hSe, Matrix.det_smul]
  have hDdet : algebraMap (𝓞 L) L D.det = δ ^ n * C.det := by
    rw [coe_det, hDC, Matrix.det_smul, Fintype.card_fin]
  have hS0 : S.det ≠ 0 := by rw [hSdet]; exact pow_ne_zero _ hd
  have hD0 : D.det ≠ 0 := by
    intro h
    rw [h, map_zero] at hDdet
    exact mul_ne_zero (pow_ne_zero _ hδ) hC hDdet.symm
  set Λ := (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup with hΛ
  have ea : Λ.map (mulVecHom (δ • 1)) = (frame (S.map (algebraMap (𝓞 L) L))).toAddSubgroup := by
    rw [hS, frame_eq_map]
  have eM : (mulVecHom (δ • 1)).comp (mulVecHom C) = mulVecHom (D.map (algebraMap (𝓞 L) L)) := by
    refine AddMonoidHom.ext fun x => ?_
    simp [mulVecHom_apply, hDC, Matrix.smul_mulVec]
  have eaM : Λ.map ((mulVecHom (δ • 1)).comp (mulVecHom C)) =
      (frame (D.map (algebraMap (𝓞 L) L))).toAddSubgroup := by
    rw [eM, frame_eq_map]
  have hc : ∀ x, mulVecHom (δ • 1) (mulVecHom C x) = mulVecHom C (mulVecHom (δ • 1) x) := by
    intro x
    simp [mulVecHom_apply, Matrix.smul_mulVec, Matrix.mulVec_smul]
  have hinj : Function.Injective (mulVecHom C) :=
    Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det C).2 (IsUnit.mk0 _ hC))
  have h2 : Λ.map (mulVecHom (δ • 1)) ≤ Λ := by
    rw [ea]; exact fun x hx => frame_map_le S hx
  have i2 : (Λ.map (mulVecHom (δ • 1))).relIndex Λ ≠ 0 := by
    rw [ea]; exact relIndex_frame_ne S hS0
  have h3 : Λ.map ((mulVecHom (δ • 1)).comp (mulVecHom C)) ≤ Λ := by
    rw [eaM]; exact fun x hx => frame_map_le D hx
  have i3 : (Λ.map ((mulVecHom (δ • 1)).comp (mulVecHom C))).relIndex Λ ≠ 0 := by
    rw [eaM]; exact relIndex_frame_ne D hD0
  obtain ⟨p1, p2⟩ := relIndex_pair Λ _ _ hinj hc h2 i2 h3 i3
  have hf := GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame.gIdx_frac Λ _ _ hinj hc h2 i2 h3 i3
  rw [ea, eaM, log_relIndex_frame S hS0, log_relIndex_frame D hD0] at hf
  have eC : (frame C).toAddSubgroup = Λ.map (mulVecHom C) := frame_eq_map C
  refine ⟨by rw [eC]; exact p1, by rw [eC]; exact p2, ?_⟩
  rw [eC, gIdx_swap, hf]
  have hsum : ∀ σ : L →+* ℂ, Real.log ‖σ (algebraMap (𝓞 L) L D.det)‖ =
      Real.log ‖σ (algebraMap (𝓞 L) L S.det)‖ + Real.log ‖σ C.det‖ := by
    intro σ
    have a1 : ‖σ (algebraMap (𝓞 L) L S.det)‖ ≠ 0 := by
      rw [norm_ne_zero_iff, map_ne_zero, hSdet, map_pow, ← hδe]
      exact pow_ne_zero _ hδ
    have a2 : ‖σ C.det‖ ≠ 0 := by
      rw [norm_ne_zero_iff, map_ne_zero]; exact hC
    rw [← Real.log_mul a1 a2, ← norm_mul, ← map_mul, hDdet, hSdet, map_pow, ← hδe]
  simp_rw [hsum]
  rw [Finset.sum_add_distrib]
  ring

end GlobalTheory.CompanionTheory.Ar.Cusp.GlobDet
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HeightOnePrimeDvrStalk
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieStalk

namespace GlobalTheory.CompanionTheory.Ar.LieStalk.HeightOne

theorem isDVR_of_ringKrullDim_eq_one (B : Type*) [CommRing B] [IsDomain B] [IsLocalRing B] [IsNoetherianRing B]
    [IsIntegrallyClosed B] (h : ringKrullDim B = 1) : IsDiscreteValuationRing B := by
  have hf : ¬ IsField B := fun hB => by
    rw [ringKrullDim_eq_zero_of_isField hB] at h
    exact zero_ne_one h
  have hle : Ring.KrullDimLE 1 B := Ring.krullDimLE_iff.2 (by rw [h]; rfl)
  have hmax := Ring.krullDimLE_one_iff_of_noZeroDivisors.1 hle
  have hT := (IsDiscreteValuationRing.TFAE B hf).out 1 4
  refine hT.2 ⟨inferInstance, ExistsUnique.intro (IsLocalRing.maximalIdeal B) ⟨?_, inferInstance⟩ ?_⟩
  · exact fun h0 => hf (IsLocalRing.isField_iff_maximalIdeal_eq.2 h0)
  · rintro Q ⟨h0, hQ⟩
    have := hmax Q h0 hQ
    exact IsLocalRing.eq_maximalIdeal this

theorem comap_maximalIdeal_stalkSpecializes {X : Scheme.{0}} {x y : X} (h : x ⤳ y)
    (P : PrimeSpectrum (X.presheaf.stalk y)) (hP : X.fromSpecStalk y P = x) :
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).comap (X.presheaf.stalkSpecializes h).hom = P.asIdeal := by
  have e := Scheme.SpecMap_stalkSpecializes_fromSpecStalk h
  have e3 : (Spec.map (X.presheaf.stalkSpecializes h) ≫ X.fromSpecStalk y)
      (IsLocalRing.closedPoint (X.presheaf.stalk x) : Spec (X.presheaf.stalk x)) = x := by
    rw [e]
    exact Scheme.fromSpecStalk_closedPoint
  have e2 : X.fromSpecStalk y (Spec.map (X.presheaf.stalkSpecializes h)
      (IsLocalRing.closedPoint (X.presheaf.stalk x) : Spec (X.presheaf.stalk x))) = X.fromSpecStalk y P :=
    (Scheme.Hom.comp_apply _ _ _).symm.trans (e3.trans hP.symm)
  have inj : Function.Injective (X.fromSpecStalk y) := (X.fromSpecStalk y).isEmbedding.injective
  exact congrArg PrimeSpectrum.asIdeal (inj e2)

theorem exists_mul_stalkSpecializes {X : Scheme.{0}} {x y : X} (h : x ⤳ y)
    (P : Ideal (X.presheaf.stalk y))
    (hP : (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).comap (X.presheaf.stalkSpecializes h).hom = P)
    (b : X.presheaf.stalk x) :
    ∃ a, a ∉ P ∧ ∃ c, (X.presheaf.stalkSpecializes h).hom a * b = (X.presheaf.stalkSpecializes h).hom c := by
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
  have hxU : x ∈ U := h.mem_open U.isOpen hyU
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxU⟩ : U)
  have loc := hU.isLocalization_stalk ⟨x, hxU⟩
  obtain ⟨⟨r, t⟩, ht⟩ := IsLocalization.surj (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl b
  have hg : ∀ r : Γ(X, U), (X.presheaf.stalkSpecializes h).hom ((X.presheaf.germ U y hyU).hom r) =
      algebraMap Γ(X, U) (X.presheaf.stalk x) r := fun r =>
    ConcreteCategory.congr_hom (TopCat.Presheaf.germ_stalkSpecializes X.presheaf hyU h) r
  have hu : IsUnit (algebraMap Γ(X, U) (X.presheaf.stalk x) (t : Γ(X, U))) := IsLocalization.map_units _ t
  refine ⟨(X.presheaf.germ U y hyU).hom t, fun hm => ?_, (X.presheaf.germ U y hyU).hom r, ?_⟩
  · rw [← hP, Ideal.mem_comap, hg] at hm
    exact (IsLocalRing.mem_maximalIdeal _).1 hm hu
  · rw [hg, hg, mul_comm]
    exact ht

end GlobalTheory.CompanionTheory.Ar.LieStalk.HeightOne

namespace GlobalTheory.CompanionTheory.Ar.LieStalk.HeightOne

theorem exists_generisation_of_height_eq_one : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X), IsCptGen ξ → IsLocallyNoetherian X → IsNormalScheme X → ∀ (p : Cpt ξ) (P : PrimeSpectrum (regAt ξ p)), P.asIdeal.height = 1 → ∃ (q : Cpt ξ) (hs : q.1 ⤳ p.1), (∃ _ : IsDomain (X.presheaf.stalk q.1), IsDiscreteValuationRing (X.presheaf.stalk q.1)) ∧ (∀ s : regAt ξ p, s ∉ P.asIdeal → (s : Ω)⁻¹ ∈ regAt ξ q) ∧ ∀ a ∈ regAt ξ q, ∃ s : regAt ξ p, s ∉ P.asIdeal ∧ (s : Ω) * a ∈ regAt ξ p := by
  intro X Ω _ ξ hgen hN hnorm p P hP
  let P' : PrimeSpectrum (X.presheaf.stalk p.1) := ⟨Ideal.comap (regIso hgen p) P.asIdeal, inferInstance⟩
  have hP' : P'.asIdeal.height = 1 := ((regIso hgen p).height_comap P.asIdeal).trans hP
  have hmem : ∀ a, a ∈ P'.asIdeal ↔ regIso hgen p a ∈ P.asIdeal := fun a => Iff.rfl
  have hs : X.fromSpecStalk p.1 P' ⤳ p.1 := by
    have h : X.fromSpecStalk p.1 P' ∈ Set.range (X.fromSpecStalk p.1) := ⟨P', rfl⟩
    rwa [Scheme.range_fromSpecStalk] at h
  have hgq : genPt ξ ⤳ X.fromSpecStalk p.1 P' := by
    have e1 : genPt ξ = X.fromSpecStalk p.1 (spMap (genMap ξ p)
        (IsLocalRing.closedPoint Ω : Sp Ω)) :=
      (congrArg (fun g : Sp Ω ⟶ X => g (IsLocalRing.closedPoint Ω : Sp Ω))
        (spMap_genMap_fromSpecStalk p)).symm.trans (Scheme.Hom.comp_apply _ _ _)
    refine (specializes_of_eq e1).trans (Specializes.map ?_ (X.fromSpecStalk p.1).continuous)
    refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
    intro a ha
    have h0 : genMap ξ p a ∈ IsLocalRing.maximalIdeal Ω := ha
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at h0
    have : a = 0 := hgen.inj p (h0.trans (map_zero _).symm)
    rw [this]
    exact Ideal.zero_mem _
  let q : Cpt ξ := ⟨X.fromSpecStalk p.1 P', hgq⟩
  have hs' : q.1 ⤳ p.1 := hs
  obtain ⟨hdom, hic⟩ := hnorm q.1
  haveI := hN
  let f : X.presheaf.stalk p.1 →+* X.presheaf.stalk q.1 := (X.presheaf.stalkSpecializes hs').hom
  have hcomap : (IsLocalRing.maximalIdeal (X.presheaf.stalk q.1)).comap f = P'.asIdeal :=
    comap_maximalIdeal_stalkSpecializes hs' P' rfl
  have hgf : ∀ a, genMap ξ q (f a) = genMap ξ p a := genMap_specializes hs'
  have hfinj : Function.Injective f := fun a b hab =>
    hgen.inj p (by rw [← hgf, ← hgf, hab])
  have hunit : ∀ a, a ∉ P'.asIdeal → IsUnit (f a) := fun a ha => by
    by_contra hu
    exact ha (hcomap ▸ (IsLocalRing.mem_maximalIdeal _).2 hu)
  have hfrac : ∀ b, ∃ a, a ∉ P'.asIdeal ∧ ∃ c, f a * b = f c :=
    exists_mul_stalkSpecializes hs' P'.asIdeal hcomap
  have hdim : ringKrullDim (X.presheaf.stalk q.1) = 1 := by
    letI : Algebra (X.presheaf.stalk p.1) (X.presheaf.stalk q.1) := f.toAlgebra
    haveI : IsLocalization.AtPrime (X.presheaf.stalk q.1) P'.asIdeal :=
      { map_units := fun s => hunit s.1 s.2
        surj := fun b => by
          obtain ⟨a, ha, c, hc⟩ := hfrac b
          exact ⟨⟨c, ⟨a, ha⟩⟩, by rw [mul_comm]; exact hc⟩
        exists_of_eq := fun {a b} h => ⟨1, by rw [hfinj h]⟩ }
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height P'.asIdeal (X.presheaf.stalk q.1), hP']
    rfl
  refine ⟨q, hs', ⟨hdom, isDVR_of_ringKrullDim_eq_one _ hdim⟩, fun s hsP => ?_, ?_⟩
  · have ha : (regIso hgen p).symm s ∉ P'.asIdeal := by
      rw [hmem, RingEquiv.apply_symm_apply]
      exact hsP
    obtain ⟨u, hu⟩ := (hunit _ ha).exists_right_inv
    refine ⟨u, ?_⟩
    refine eq_inv_of_mul_eq_one_right ?_
    have h1 := congrArg (genMap ξ q) hu
    rw [map_mul, map_one, hgf, genMap_regIso_symm] at h1
    exact h1
  · rintro _ ⟨b, rfl⟩
    obtain ⟨a, ha, c, hc⟩ := hfrac b
    refine ⟨regIso hgen p a, fun h => ha ((hmem a).2 h), ⟨c, ?_⟩⟩
    have h1 := congrArg (genMap ξ q) hc
    rw [map_mul, hgf, hgf] at h1
    exact h1.symm

end GlobalTheory.CompanionTheory.Ar.LieStalk.HeightOne
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralClosureChartSpan
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar.IntClGens

variable {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} (x : κ → Ω)

theorem twist_mem {c j : κ} (hc : x c ≠ 0) {b : Ω} (hb : b ∈ chRing o x c) :
    ∃ e : ℕ, ∀ m, e ≤ m → (x c / x j) ^ m * b ∈ chRing o x j := by
  have ht : x c / x j ∈ chRing o x j := Algebra.subset_adjoin ⟨c, rfl⟩
  induction hb using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨l, rfl⟩ := hy
    refine ⟨1, fun m hm => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    have key : x c / x j * (x l / x c) = x l / x j := by
      rw [div_mul_div_comm, mul_comm (x j), mul_div_mul_left _ _ hc]
    have : (x c / x j) ^ (1 + k) * (x l / x c) = (x c / x j) ^ k * (x l / x j) := by
      rw [← key]; ring
    rw [this]
    exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ ht _) (Algebra.subset_adjoin ⟨l, rfl⟩)
  | algebraMap r =>
    exact ⟨0, fun m _ => Subalgebra.mul_mem _ (Subalgebra.pow_mem _ ht _) (Subalgebra.algebraMap_mem _ r)⟩
  | add y z _ _ hy hz =>
    obtain ⟨e1, h1⟩ := hy
    obtain ⟨e2, h2⟩ := hz
    exact ⟨max e1 e2, fun m hm => by
      rw [mul_add]
      exact Subalgebra.add_mem _ (h1 m (le_of_max_le_left hm)) (h2 m (le_of_max_le_right hm))⟩
  | mul y z _ _ hy hz =>
    obtain ⟨e1, h1⟩ := hy
    obtain ⟨e2, h2⟩ := hz
    refine ⟨e1 + e2, fun m hm => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    have : (x c / x j) ^ (e1 + e2 + k) * (y * z) =
        ((x c / x j) ^ (e1 + k) * y) * ((x c / x j) ^ e2 * z) := by ring
    rw [this]
    exact Subalgebra.mul_mem _ (h1 _ (by omega)) (h2 _ le_rfl)

theorem twist_integral {c j : κ} (hc : x c ≠ 0) {a : Ω} (ha : IsIntegral (chRing o x c) a) :
    ∃ e : ℕ, ∀ m, e ≤ m → IsIntegral (chRing o x j) ((x c / x j) ^ m * a) := by
  have ht : x c / x j ∈ chRing o x j := Algebra.subset_adjoin ⟨c, rfl⟩
  obtain ⟨p, hmon, hp⟩ := ha
  have hE : ∀ i, ∃ e : ℕ, ∀ m, e ≤ m → (x c / x j) ^ m * (p.coeff i : Ω) ∈ chRing o x j :=
    fun i => twist_mem x hc (p.coeff i).2
  choose E hE using hE
  obtain ⟨E0, hE0⟩ : ∃ E0, ∀ i ≤ p.natDegree, E i ≤ E0 :=
    ⟨(Finset.range (p.natDegree + 1)).sup E, fun i hi => Finset.le_sup (Finset.mem_range.2 (by omega))⟩
  have hn' : (p.map (algebraMap (chRing o x c) Ω)).natDegree = p.natDegree := hmon.natDegree_map _
  have hqm : ((p.map (algebraMap (chRing o x c) Ω)).scaleRoots ((x c / x j) ^ E0)).Monic :=
    (Polynomial.monic_scaleRoots_iff _).2 (hmon.map _)
  have hq0 : ((p.map (algebraMap (chRing o x c) Ω)).scaleRoots ((x c / x j) ^ E0)).eval
      ((x c / x j) ^ E0 * a) = 0 := by
    have h1 : (p.map (algebraMap (chRing o x c) Ω)).eval₂ (RingHom.id Ω) a = 0 := by
      rw [Polynomial.eval₂_map, RingHom.id_comp]; exact hp
    have := Polynomial.scaleRoots_eval₂_eq_zero (RingHom.id Ω) (s := (x c / x j) ^ E0) h1
    simpa [Polynomial.eval₂_id] using this
  have hlift : (p.map (algebraMap (chRing o x c) Ω)).scaleRoots ((x c / x j) ^ E0) ∈
      Polynomial.lifts (algebraMap (chRing o x j) Ω) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    have hmem : ((p.map (algebraMap (chRing o x c) Ω)).scaleRoots ((x c / x j) ^ E0)).coeff i ∈
        chRing o x j := by
      rw [Polynomial.coeff_scaleRoots, hn', Polynomial.coeff_map]
      rcases lt_trichotomy i p.natDegree with hi | hi | hi
      · have h1 : E i ≤ E0 := hE0 i hi.le
        have h2 : 1 ≤ p.natDegree - i := by omega
        have hle : E i ≤ E0 * (p.natDegree - i) :=
          calc E i ≤ E0 := h1
            _ = E0 * 1 := (mul_one _).symm
            _ ≤ E0 * (p.natDegree - i) := Nat.mul_le_mul_left _ h2
        rw [← pow_mul, mul_comm]
        exact hE i _ hle
      · rw [hi, Nat.sub_self, pow_zero, mul_one, hmon.coeff_natDegree, map_one]
        exact Subalgebra.one_mem _
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hi, map_zero, zero_mul]
        exact Subalgebra.zero_mem _
    exact ⟨⟨_, hmem⟩, rfl⟩
  obtain ⟨q0, hq0map, -, hq0m⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hqm
  have hint : IsIntegral (chRing o x j) ((x c / x j) ^ E0 * a) :=
    ⟨q0, hq0m, by rw [← Polynomial.eval_map, hq0map]; exact hq0⟩
  refine ⟨E0, fun m hm => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  have : (x c / x j) ^ (E0 + k) * a = (x c / x j) ^ k * ((x c / x j) ^ E0 * a) := by ring
  rw [this]
  have htk : IsIntegral (chRing o x j) ((x c / x j) ^ k) :=
    isIntegral_algebraMap (x := (⟨_, Subalgebra.pow_mem _ ht k⟩ : chRing o x j))
  exact htk.mul hint

theorem exists_twisted_gens : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ]
    (x : κ → Ω), (∀ c, x c ≠ 0 → Module.Finite (chRing o x c) (integralClosure (chRing o x c) Ω)) →
    ∃ (d n : ℕ) (z : κ ⊕ Fin n → Ω), (∀ c, z (Sum.inl c) = x c ^ d) ∧ ∀ c, x c ≠ 0 → ∀ a : Ω,
      IsIntegral (chRing o x c) a ↔ a ∈ Submodule.span (chRing o x c) (Set.range fun k => z k / x c ^ d) := by
  intro o _ Ω _ _ κ _ x hfin
  have hgen : ∀ c, ∃ (N : ℕ) (g : Fin N → Ω), (∀ k, x c ≠ 0 ∧ IsIntegral (chRing o x c) (g k)) ∧
      (x c ≠ 0 → ∀ a, IsIntegral (chRing o x c) a → a ∈ Submodule.span (chRing o x c) (Set.range g)) := by
    intro c
    by_cases hc : x c = 0
    · exact ⟨0, Fin.elim0, fun k => k.elim0, fun h => absurd hc h⟩
    · haveI := hfin c hc
      obtain ⟨N, s, hs⟩ := Module.Finite.exists_fin (R := chRing o x c) (M := integralClosure (chRing o x c) Ω)
      refine ⟨N, fun k => ((s k : integralClosure (chRing o x c) Ω) : Ω),
        fun k => ⟨hc, (s k).2⟩, fun _ a ha => ?_⟩
      have hle : Submodule.map (integralClosure (chRing o x c) Ω).val.toLinearMap
          (Submodule.span (chRing o x c) (Set.range s)) ≤
          Submodule.span (chRing o x c) (Set.range fun k => ((s k : integralClosure (chRing o x c) Ω) : Ω)) := by
        rw [Submodule.map_span_le]
        rintro _ ⟨k, rfl⟩
        exact Submodule.subset_span ⟨k, rfl⟩
      rw [hs] at hle
      exact hle (Submodule.mem_map_of_mem (p := ⊤) (f := (integralClosure (chRing o x c) Ω).val.toLinearMap)
        (r := ⟨a, ha⟩) Submodule.mem_top)
  choose N g hg using hgen
  obtain ⟨M, ⟨eI⟩⟩ := Finite.exists_equiv_fin (Σ c, Fin (N c))
  have hD : ∀ (i : Σ c, Fin (N c)) (j : κ), ∃ e : ℕ, ∀ m, e ≤ m →
      IsIntegral (chRing o x j) ((x i.1 / x j) ^ m * g i.1 i.2) :=
    fun i j => twist_integral x ((hg i.1).1 i.2).1 ((hg i.1).1 i.2).2
  choose D hD using hD
  obtain ⟨d, hd⟩ := Finite.exists_le (fun q : (Σ c, Fin (N c)) × κ => D q.1 q.2)
  refine ⟨d, M, Sum.elim (fun c => x c ^ d) (fun k => x (eI.symm k).1 ^ d * g (eI.symm k).1 (eI.symm k).2),
    fun c => rfl, fun c hc a => ⟨fun ha => ?_, fun ha => ?_⟩⟩
  · refine Submodule.span_mono ?_ ((hg c).2 hc a ha)
    rintro _ ⟨k, rfl⟩
    refine ⟨Sum.inr (eI ⟨c, k⟩), ?_⟩
    have he : eI.symm (eI ⟨c, k⟩) = ⟨c, k⟩ := eI.symm_apply_apply _
    simp only [Sum.elim_inr]
    rw [he]
    exact mul_div_cancel_left₀ _ (pow_ne_zero _ hc)
  · have hsub : (Set.range fun k => (Sum.elim (fun c => x c ^ d)
        (fun k => x (eI.symm k).1 ^ d * g (eI.symm k).1 (eI.symm k).2) k : Ω) / x c ^ d) ⊆
        ((integralClosure (chRing o x c) Ω).toSubmodule : Set Ω) := by
      rintro _ ⟨k, rfl⟩
      rw [SetLike.mem_coe, Subalgebra.mem_toSubmodule, mem_integralClosure_iff]
      rcases k with j | k
      · simp only [Sum.elim_inl]
        rw [← div_pow]
        exact isIntegral_algebraMap (x := (⟨_, Subalgebra.pow_mem _
          (Algebra.subset_adjoin ⟨j, rfl⟩ : x j / x c ∈ chRing o x c) d⟩ : chRing o x c))
      · simp only [Sum.elim_inr]
        rw [mul_div_right_comm, ← div_pow]
        exact hD (eI.symm k) c d (hd (eI.symm k, c))
    have := Submodule.span_le.2 hsub ha
    rwa [Subalgebra.mem_toSubmodule, mem_integralClosure_iff] at this

end GlobalTheory.CompanionTheory.Ar.IntClGens
end

