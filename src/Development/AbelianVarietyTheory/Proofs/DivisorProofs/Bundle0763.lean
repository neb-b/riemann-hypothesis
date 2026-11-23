module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0737
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0493
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackSchBc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0435
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0752
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0740
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFrobAtRestrictFiniteAbelianSubextension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0747
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNumeratorIdealOfAntiInvariantDivisor
section
open NumberField IsDedekindDomain Formalism.L2.Pj
open scoped nonZeroDivisors

namespace GlobalTheory.NumeratorIdeal

section general
variable {R : Type} [CommRing R] [IsDedekindDomain R] (K : Type) [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem count_span_int (v : HeightOneSpectrum R) {a : R} (ha : a ≠ 0) :
    v.valuation K (algebraMap R K a) =
      WithZero.exp (-FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ (algebraMap R K a))) := by
  classical
  have hJ : (Ideal.span {a} : Ideal R) ≠ 0 := by simpa using ha
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K v hJ,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_if_neg v ha]

theorem valuation_eq_count (v : HeightOneSpectrum R) {x : K} (hx : x ≠ 0) :
    v.valuation K x =
      WithZero.exp (-FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ x)) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by rintro rfl; simp at hx
  have ha' : algebraMap R K a ≠ 0 := by simpa using ha0
  have hb' : algebraMap R K b ≠ 0 := by simpa using hb0
  rw [map_div₀, count_span_int K v ha0, count_span_int K v hb0, div_eq_mul_inv (algebraMap R K a),
    ← FractionalIdeal.spanSingleton_mul_spanSingleton, FractionalIdeal.count_mul K v
      (by simpa [FractionalIdeal.spanSingleton_eq_zero_iff] using ha0)
      (by simpa [FractionalIdeal.spanSingleton_eq_zero_iff] using hb0),
    ← FractionalIdeal.spanSingleton_inv, FractionalIdeal.count_inv, ← WithZero.exp_sub]
  congr 1
  ring

theorem le_one_of_count {I : FractionalIdeal R⁰ K} (hI : I ≠ 0)
    (h : ∀ v : HeightOneSpectrum R, 0 ≤ FractionalIdeal.count K v I) : I ≤ 1 := by
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI]
  refine finprod_induction (fun J : FractionalIdeal R⁰ K => J ≤ 1) le_rfl
    (fun a b ha hb => mul_le_one' ha hb) fun v => ?_
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (h v)
  show _ ≤ _
  rw [hn, zpow_natCast, ← FractionalIdeal.coeIdeal_pow]
  exact FractionalIdeal.coeIdeal_le_one

theorem le_of_count {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v : HeightOneSpectrum R, FractionalIdeal.count K v J ≤ FractionalIdeal.count K v I) :
    I ≤ J := by
  have h1 : I * J⁻¹ ≤ 1 := le_one_of_count K (mul_ne_zero hI (inv_ne_zero hJ)) fun v => by
    rw [FractionalIdeal.count_mul K v hI (inv_ne_zero hJ), FractionalIdeal.count_inv]
    linarith [h v]
  have h2 := mul_le_mul_left h1 J
  rwa [inv_mul_cancel_right₀ hJ, one_mul] at h2

theorem mem_iff_valuation {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) (x : K) :
    x ∈ I ↔ ∀ v : HeightOneSpectrum R,
      v.valuation K x ≤ WithZero.exp (-FractionalIdeal.count K v I) := by
  by_cases hx : x = 0
  · subst hx
    simp [FractionalIdeal.zero_mem]
  have hs : FractionalIdeal.spanSingleton R⁰ x ≠ 0 := by
    simpa [FractionalIdeal.spanSingleton_eq_zero_iff] using hx
  rw [← FractionalIdeal.spanSingleton_le_iff_mem]
  simp only [valuation_eq_count K _ hx, WithZero.exp_le_exp, neg_le_neg_iff]
  exact ⟨fun h v => FractionalIdeal.count_mono K v hs h, le_of_count K hs hI⟩

theorem one_le_count {I : Ideal R} (hI : I ≠ ⊥) (v : HeightOneSpectrum R) (h : I ≤ v.asIdeal) :
    1 ≤ FractionalIdeal.count K v (I : FractionalIdeal R⁰ K) := by
  rw [← FractionalIdeal.count_self K v]
  exact FractionalIdeal.count_mono K v (FractionalIdeal.coeIdeal_ne_zero.2 hI)
    ((FractionalIdeal.coeIdeal_le_coeIdeal K).2 h)

theorem sup_eq_top_of {I J : Ideal R} (hI : I ≠ ⊥)
    (h : ∀ v : HeightOneSpectrum R, I ≤ v.asIdeal → J ≤ v.asIdeal → False) : I ⊔ J = ⊤ := by
  by_contra H
  obtain ⟨p, hp, hle⟩ := Ideal.exists_le_maximal _ H
  have h1 : I ≤ p := le_sup_left.trans hle
  exact h ⟨p, hp.isPrime, fun e => hI (le_bot_iff.1 (e ▸ h1))⟩ h1 (le_sup_right.trans hle)

theorem count_prod_pow (s : Finset (HeightOneSpectrum R)) (n : HeightOneSpectrum R → ℕ)
    (f : HeightOneSpectrum R → HeightOneSpectrum R) (hf : ∀ Q, f (f Q) = Q)
    (hs : ∀ Q, Q ∉ s → n Q = 0) (P : HeightOneSpectrum R) :
    FractionalIdeal.count K P ((∏ Q ∈ s, (f Q).asIdeal ^ n Q : Ideal R) : FractionalIdeal R⁰ K)
      = n (f P) := by
  classical
  have e : ((∏ Q ∈ s, (f Q).asIdeal ^ n Q : Ideal R) : FractionalIdeal R⁰ K)
      = ∏ Q ∈ s, ((f Q).asIdeal : FractionalIdeal R⁰ K) ^ n Q := by
    have := map_prod (FractionalIdeal.coeIdealHom R⁰ K) (fun Q => (f Q).asIdeal ^ n Q) s
    simp only [map_pow] at this
    exact this
  rw [e, FractionalIdeal.count_prod K P _ _
    (fun Q _ => pow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.2 (f Q).ne_bot)),
    Finset.sum_eq_single (f P)]
  · rw [hf, FractionalIdeal.count_pow_self]
  · intro Q _ hQ
    rw [FractionalIdeal.count_pow, FractionalIdeal.count_maximal_coprime, mul_zero]
    rintro rfl
    exact hQ (hf Q).symm
  · intro h
    rw [hs _ h, pow_zero, FractionalIdeal.count_one]

end general

theorem exists_numerator : ∀ (E : Type) [Field E] [NumberField E] (σ : 𝓞 E ≃+* 𝓞 E) (cp : HeightOneSpectrum (𝓞 E) → HeightOneSpectrum (𝓞 E)), (∀ x, σ (σ x) = x) → (∀ Q x, x ∈ (cp Q).asIdeal ↔ σ x ∈ Q.asIdeal) → ∀ δ : HeightOneSpectrum (𝓞 E) → ℤ, (Function.support δ).Finite → (∀ Q, δ (cp Q) = -δ Q) → ∃ cc : Ideal (𝓞 E), cc ≠ ⊥ ∧ cc ⊔ cc.map (σ : 𝓞 E →+* 𝓞 E) = ⊤ ∧ (∀ Q, FractionalIdeal.count E Q (cc : FractionalIdeal (𝓞 E)⁰ E) = max (δ Q) 0) ∧ (∀ b : 𝓞 E, (∀ Q, δ Q ≠ 0 → b ∉ Q.asIdeal) → cc ⊔ Ideal.span {b} = ⊤) ∧ ∀ J : Submodule (𝓞 E) E, (∀ x, x ∈ J ↔ ∀ Q : HeightOneSpectrum (𝓞 E), Q.valuation E x ≤ WithZero.exp (-δ Q)) → J * idlE (cc.map (σ : 𝓞 E →+* 𝓞 E)) = idlE cc := by
  intro E _ _ σ cp hσ hcp δ hfin hanti
  have hinv : ∀ Q, cp (cp Q) = Q := fun Q => by
    ext x
    rw [hcp, hcp, hσ]
  have hmap : ∀ Q : HeightOneSpectrum (𝓞 E),
      Q.asIdeal.map (σ : 𝓞 E →+* 𝓞 E) = (cp Q).asIdeal := fun Q => by
    ext x
    rw [hcp, Ideal.mem_map_iff_of_surjective (σ : 𝓞 E →+* 𝓞 E) σ.surjective]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [hσ] using hy
    · intro h
      exact ⟨σ x, h, hσ x⟩
  set s := hfin.toFinset with hsdef
  have hs : ∀ Q, Q ∉ s → (δ Q).toNat = 0 := fun Q hQ => by
    have : δ Q = 0 := by simpa [hsdef] using hQ
    simp [this]
  set cc : Ideal (𝓞 E) := ∏ Q ∈ s, Q.asIdeal ^ (δ Q).toNat with hcc
  have hbar : cc.map (σ : 𝓞 E →+* 𝓞 E) = ∏ Q ∈ s, (cp Q).asIdeal ^ (δ Q).toNat := by
    have := map_prod (Ideal.mapHom (σ : 𝓞 E →+* 𝓞 E)) (fun Q => Q.asIdeal ^ (δ Q).toNat) s
    simp only [map_pow, Ideal.mapHom_apply, hmap] at this
    exact this
  have h0 : cc ≠ ⊥ := Finset.prod_ne_zero_iff.2 fun Q _ => pow_ne_zero _ Q.ne_bot
  have h0' : cc.map (σ : 𝓞 E →+* 𝓞 E) ≠ ⊥ := by
    rw [hbar]
    exact Finset.prod_ne_zero_iff.2 fun Q _ => pow_ne_zero _ (cp Q).ne_bot
  have hc : ∀ Q, FractionalIdeal.count E Q (cc : FractionalIdeal (𝓞 E)⁰ E) = max (δ Q) 0 :=
    fun Q => by
      rw [← Int.ofNat_toNat]
      exact count_prod_pow E s (fun Q => (δ Q).toNat) id (fun _ => rfl) hs Q
  have hc' : ∀ Q, FractionalIdeal.count E Q
      ((cc.map (σ : 𝓞 E →+* 𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) = max (-δ Q) 0 :=
    fun Q => by
      rw [← hanti, ← Int.ofNat_toNat, hbar]
      exact count_prod_pow E s (fun Q => (δ Q).toNat) cp hinv hs Q
  refine ⟨cc, h0, sup_eq_top_of h0 fun v h1 h2 => ?_, hc, fun b hb => sup_eq_top_of h0 fun v h1 h2 => ?_,
    fun J hJ => ?_⟩
  · have a1 := one_le_count E h0 v h1
    have a2 := one_le_count E h0' v h2
    rw [hc] at a1
    rw [hc'] at a2
    omega
  · have a1 := one_le_count E h0 v h1
    rw [hc] at a1
    exact hb v (by omega) ((Ideal.span_singleton_le_iff_mem _).1 h2)
  · have f0 : (cc : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 h0
    have f0' : ((cc.map (σ : 𝓞 E →+* 𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 :=
      FractionalIdeal.coeIdeal_ne_zero.2 h0'
    have hJD : J = (((cc : FractionalIdeal (𝓞 E)⁰ E) *
        ((cc.map (σ : 𝓞 E →+* 𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)⁻¹ :
          FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) := by
      ext x
      rw [hJ, FractionalIdeal.mem_coe, mem_iff_valuation E (mul_ne_zero f0 (inv_ne_zero f0'))]
      refine forall_congr' fun Q => ?_
      rw [FractionalIdeal.count_mul E Q f0 (inv_ne_zero f0'), FractionalIdeal.count_inv, hc, hc']
      have : max (δ Q) 0 + -max (-δ Q) 0 = δ Q := by omega
      rw [this]
    have hid : ∀ I : Ideal (𝓞 E),
        idlE I = ((I : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) := fun _ => rfl
    rw [hJD, hid, hid, ← FractionalIdeal.coe_mul, inv_mul_cancel_right₀ f0']

end GlobalTheory.NumeratorIdeal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitarySheafContinuousBaseChangeLevelwiseQcqs
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem contCone_bc_sch_qcqs (R : Type) [CommRing R] (F : Shv R) (hF : Finitary F) (S X : Scheme.{0})
    (r : X ⟶ S) (hqc : QuasiCompact r) (hqs : QuasiSeparated r) (I : Type) [SmallCategory I] [IsCofiltered I]
    (G : I ⥤ Over S) (c : Cone G) (hc : IsLimit c) (hG : ∀ i, IsAffine (G.obj i).left) :
    ContCone R F ((bc (sch.map r)).mapCone c) := by
  obtain ⟨e, -⟩ := GlobalTheory.EtC.bc_sch_iso S X r
  let H : Over S ⥤ Scheme.{0} := Over.pullback r ⋙ Over.forget X
  have hl : IsLimit (H.mapCone c) := isLimitOfPreserves H hc
  have hcomp : ∀ i, CompactSpace ((G ⋙ H).obj i) := by
    intro i
    haveI := hG i
    haveI : QuasiCompact (pullback.fst (G.obj i).hom r) := MorphismProperty.of_isPullback (P := @QuasiCompact) (IsPullback.of_hasPullback (G.obj i).hom r).flip hqc
    have hc' := QuasiCompact.compactSpace_of_compactSpace (pullback.fst (G.obj i).hom r)
    exact hc'
  have hqsp : ∀ i, QuasiSeparatedSpace ((G ⋙ H).obj i) := by
    intro i
    haveI := hG i
    haveI : QuasiSeparated (pullback.fst (G.obj i).hom r) := MorphismProperty.of_isPullback (P := @QuasiSeparated) (IsPullback.of_hasPullback (G.obj i).hom r).flip hqs
    have hs' := quasiSeparatedSpace_of_quasiSeparated (pullback.fst (G.obj i).hom r)
    exact hs'
  have haff : ∀ (i j : I) (f : i ⟶ j), IsAffineHom ((G ⋙ H).map f) := by
    intro i j f
    haveI := hG i
    haveI := hG j
    have hsq : IsPullback ((G ⋙ H).map f) (pullback.fst (G.obj i).hom r) (pullback.fst (G.obj j).hom r)
        (G.map f).left := by
      refine IsPullback.of_right (h₁₂ := pullback.snd (G.obj j).hom r) (h₂₂ := (G.obj j).hom) (v₁₃ := r) ?_ ?_ ?_
      · have e1 : (G ⋙ H).map f ≫ pullback.snd (G.obj j).hom r = pullback.snd (G.obj i).hom r := by
          exact pullback.lift_snd _ _ _
        have e2 : (G.map f).left ≫ (G.obj j).hom = (G.obj i).hom := Over.w (G.map f)
        have key : ∀ {P₁ P₂ P₃ P₄ : Scheme.{0}} {l : P₁ ⟶ P₃} {rr : P₂ ⟶ P₄} {a a' : P₁ ⟶ P₂} {b b' : P₃ ⟶ P₄},
            a = a' → b = b' → IsPullback a' l rr b' → IsPullback a l rr b := by
          rintro _ _ _ _ _ _ _ _ _ _ rfl rfl h; exact h
        exact key e1 e2 (IsPullback.of_hasPullback (G.obj i).hom r).flip
      · exact pullback.lift_fst _ _ _
      · exact (IsPullback.of_hasPullback (G.obj j).hom r).flip
    exact MorphismProperty.of_isPullback (P := @IsAffineHom) hsq.flip (isAffineHom_of_isAffine _)
  have h1 : ContCone R F (sch.mapCone (H.mapCone c)) :=
    GlobalTheory.T.contCone_of_isLimit_of_qcqs_affine_transitions R F hF I (G ⋙ H) (H.mapCone c) hl hcomp hqsp haff
  have hb := GlobalTheory.EtC.eqv_basic R F
  refine (GlobalTheory.EtC.ContCone.iff_of_eqv R F I (G ⋙ H ⋙ sch) (G ⋙ bc (sch.map r)) (sch.mapCone (H.mapCone c))
    ((bc (sch.map r)).mapCone c) (Functor.whiskerLeft G e.hom) (e.hom.app c.pt) ?_ ?_ ?_).1 h1
  · intro i
    exact e.hom.naturality (c.π.app i)
  · intro i
    exact hb.1 _ _ _ inferInstance
  · exact hb.1 _ _ _ inferInstance

theorem contCone_bc_qcqsOver : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (S : Scheme.{0}) (E : Spc) (p : E ⟶ sch.obj S), QcqsOver p → (∀ (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Over S) (c : Cone G), IsLimit c → (∀ i, IsAffine (G.obj i).left) → ContCone R F ((bc p).mapCone c)) := by
  intro R _ F hF S E p hp I _ _ G c hc hG
  refine GlobalTheory.T.cohomologyContinuous_base_change_of_levels R F S E p I G c ?_
  intro k
  obtain ⟨X, r, e, hqc, hqs, he⟩ := hp k
  exact ⟨X, r, e, he, contCone_bc_sch_qcqs R F hF S X r hqc hqs I G c hc hG⟩

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankHomologyResolutionsResidueField
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem finrank_add_le_of_image_mem {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (A : V →ₗ[K] W) (Z R : Submodule K V) (Z' R' : Submodule K W) (hR' : R' ≤ Z')
    (hZ : ∀ x ∈ Z, A x ∈ Z') (hk : ∀ x ∈ Z, A x ∈ R' → x ∈ R) :
    Module.finrank K Z + Module.finrank K R' ≤ Module.finrank K Z' + Module.finrank K R := by
  let g : (Z × R') →ₗ[K] W := LinearMap.coprod (A ∘ₗ Z.subtype) R'.subtype
  have h1 := LinearMap.finrank_range_add_finrank_ker g
  rw [Module.finrank_prod] at h1
  have h2 : Module.finrank K (LinearMap.range g) ≤ Module.finrank K Z' := by
    apply Submodule.finrank_mono
    rintro _ ⟨⟨x, r⟩, rfl⟩
    simp only [g, LinearMap.coprod_apply, LinearMap.comp_apply, Submodule.subtype_apply]
    exact Z'.add_mem (hZ x x.2) (hR' r.2)
  have h3 : Module.finrank K (LinearMap.ker g) ≤ Module.finrank K R := by
    let φ : LinearMap.ker g →ₗ[K] R :=
      LinearMap.codRestrict R (Z.subtype ∘ₗ LinearMap.fst K Z R' ∘ₗ (LinearMap.ker g).subtype) (by
        rintro ⟨⟨x, r⟩, hx⟩
        simp only [LinearMap.mem_ker, g, LinearMap.coprod_apply, LinearMap.comp_apply,
          Submodule.subtype_apply] at hx
        simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.fst_apply]
        apply hk x x.2
        have : A x = -(r : W) := eq_neg_of_add_eq_zero_left hx
        rw [this]; exact R'.neg_mem r.2)
    refine LinearMap.finrank_le_finrank_of_injective (f := φ) ?_
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    rintro ⟨⟨x, r⟩, hx⟩ h0
    simp only [LinearMap.mem_ker, g, LinearMap.coprod_apply, LinearMap.comp_apply,
      Submodule.subtype_apply] at hx
    have hx0 : x = 0 := by
      apply Subtype.ext
      have := congrArg Subtype.val h0
      simpa [φ] using this
    subst hx0
    have hr : r = 0 := by
      apply Subtype.ext
      simpa using hx
    subst hr
    rfl
  omega

theorem finrank_homology_base_change_resolutions : ∀ (O : Type) [CommRing O] (K : Type) [Field K] [Algebra O K] (N : Type) [AddCommGroup N] [Module O N] (F₀ : Type) [AddCommGroup F₀] [Module O F₀] [Module.Free O F₀] [Module.Finite O F₀] (F₁ : Type) [AddCommGroup F₁] [Module O F₁] [Module.Free O F₁] [Module.Finite O F₁] (F₂ : Type) [AddCommGroup F₂] [Module O F₂] [Module.Free O F₂] [Module.Finite O F₂] (F₃ : Type) [AddCommGroup F₃] [Module O F₃] [Module.Free O F₃] [Module.Finite O F₃] (G₀ : Type) [AddCommGroup G₀] [Module O G₀] [Module.Free O G₀] [Module.Finite O G₀] (G₁ : Type) [AddCommGroup G₁] [Module O G₁] [Module.Free O G₁] [Module.Finite O G₁] (G₂ : Type) [AddCommGroup G₂] [Module O G₂] [Module.Free O G₂] [Module.Finite O G₂] (ε : F₀ →ₗ[O] N) (d₁ : F₁ →ₗ[O] F₀) (d₂ : F₂ →ₗ[O] F₁) (d₃ : F₃ →ₗ[O] F₂) (ν : G₀ →ₗ[O] N) (e₁ : G₁ →ₗ[O] G₀) (e₂ : G₂ →ₗ[O] G₁), Function.Surjective ε → Function.Exact d₁ ε → Function.Exact d₂ d₁ → Function.Exact d₃ d₂ → Function.Surjective ν → Function.Exact e₁ ν → Function.Exact e₂ e₁ → Module.finrank K (LinearMap.ker (d₁.baseChange K)) + Module.finrank K (LinearMap.range (e₂.baseChange K)) = Module.finrank K (LinearMap.ker (e₁.baseChange K)) + Module.finrank K (LinearMap.range (d₂.baseChange K)) ∧ Module.finrank K (LinearMap.ker (d₂.baseChange K)) ≤ Module.finrank K (LinearMap.range (d₃.baseChange K)) + Module.finrank K (K ⊗[O] G₂) := by
  intro O _ K _ _ N _ _ F₀ _ _ _ _ F₁ _ _ _ _ F₂ _ _ _ _ F₃ _ _ _ _ G₀ _ _ _ _ G₁ _ _ _ _
    G₂ _ _ _ _ ε d₁ d₂ d₃ ν e₁ e₂ hε hd₁ hd₂ hd₃ hν he₁ he₂
  obtain ⟨a₀, a₁, a₂, b₀, b₁, b₂, h₀, h₁, h₂, k₀, k₁, c1, c2, c3, c4, c5, c6, c7⟩ :=
    _root_.GlobalTheory.resolutions_homotopy_equivalent O N F₀ F₁ F₂ F₃ G₀ G₁ G₂ ε d₁ d₂ d₃ ν e₁ e₂ hε hd₁ hd₂ hd₃ hν he₁ he₂
  have bc : ∀ {P Q : Type} [AddCommGroup P] [Module O P] [AddCommGroup Q] [Module O Q]
      {f g : P →ₗ[O] Q}, f = g → ∀ x, f.baseChange K x = g.baseChange K x := by
    intro P Q _ _ _ _ f g h x; rw [h]
  have z12 : ∀ x, d₁.baseChange K (d₂.baseChange K x) = 0 := by
    intro x; have := bc hd₂.linearMap_comp_eq_zero x
    simpa [LinearMap.baseChange_comp] using this
  have ze12 : ∀ x, e₁.baseChange K (e₂.baseChange K x) = 0 := by
    intro x; have := bc he₂.linearMap_comp_eq_zero x
    simpa [LinearMap.baseChange_comp] using this
  have q1 : ∀ x, e₁.baseChange K (a₁.baseChange K x) = a₀.baseChange K (d₁.baseChange K x) := by
    intro x; have := bc c1 x; simpa [LinearMap.baseChange_comp] using this
  have q2 : ∀ x, e₂.baseChange K (a₂.baseChange K x) = a₁.baseChange K (d₂.baseChange K x) := by
    intro x; have := bc c2 x; simpa [LinearMap.baseChange_comp] using this
  have q3 : ∀ x, d₁.baseChange K (b₁.baseChange K x) = b₀.baseChange K (e₁.baseChange K x) := by
    intro x; have := bc c3 x; simpa [LinearMap.baseChange_comp] using this
  have q4 : ∀ x, d₂.baseChange K (b₂.baseChange K x) = b₁.baseChange K (e₂.baseChange K x) := by
    intro x; have := bc c4 x; simpa [LinearMap.baseChange_comp] using this
  have q5 : ∀ x, x - b₁.baseChange K (a₁.baseChange K x) =
      d₂.baseChange K (h₁.baseChange K x) + h₀.baseChange K (d₁.baseChange K x) := by
    intro x; have := bc c5 x
    simpa [LinearMap.baseChange_comp, LinearMap.baseChange_sub, LinearMap.baseChange_add,
      LinearMap.baseChange_id] using this
  have q6 : ∀ x, x - b₂.baseChange K (a₂.baseChange K x) =
      d₃.baseChange K (h₂.baseChange K x) + h₁.baseChange K (d₂.baseChange K x) := by
    intro x; have := bc c6 x
    simpa [LinearMap.baseChange_comp, LinearMap.baseChange_sub, LinearMap.baseChange_add,
      LinearMap.baseChange_id] using this
  have q7 : ∀ x, x - a₁.baseChange K (b₁.baseChange K x) =
      e₂.baseChange K (k₁.baseChange K x) + k₀.baseChange K (e₁.baseChange K x) := by
    intro x; have := bc c7 x
    simpa [LinearMap.baseChange_comp, LinearMap.baseChange_sub, LinearMap.baseChange_add,
      LinearMap.baseChange_id] using this
  refine ⟨le_antisymm ?_ ?_, ?_⟩
  · refine finrank_add_le_of_image_mem (a₁.baseChange K) _ _ _ _ ?_ ?_ ?_
    · rintro _ ⟨y, rfl⟩; exact ze12 y
    · intro x hx; rw [LinearMap.mem_ker] at hx ⊢; rw [q1, hx, map_zero]
    · rintro x hx ⟨y, hy⟩
      rw [LinearMap.mem_ker] at hx
      refine ⟨b₂.baseChange K y + h₁.baseChange K x, ?_⟩
      have := q5 x
      rw [hx, map_zero, add_zero, ← hy, ← q4] at this
      rw [map_add (f := _), ← this]; abel
  · refine finrank_add_le_of_image_mem (b₁.baseChange K) _ _ _ _ ?_ ?_ ?_
    · rintro _ ⟨y, rfl⟩; exact z12 y
    · intro x hx; rw [LinearMap.mem_ker] at hx ⊢; rw [q3, hx, map_zero]
    · rintro x hx ⟨y, hy⟩
      rw [LinearMap.mem_ker] at hx
      refine ⟨a₂.baseChange K y + k₁.baseChange K x, ?_⟩
      have := q7 x
      rw [hx, map_zero, add_zero, ← hy, ← q2] at this
      rw [map_add (f := _), ← this]; abel
  · have := finrank_add_le_of_image_mem (a₂.baseChange K) (LinearMap.ker (d₂.baseChange K))
      (LinearMap.range (d₃.baseChange K)) ⊤ ⊥ bot_le (fun _ _ => Submodule.mem_top) (by
        intro x hx h0
        rw [LinearMap.mem_ker] at hx
        rw [Submodule.mem_bot] at h0
        refine ⟨h₂.baseChange K x, ?_⟩
        have := q6 x
        rw [hx, h0, map_zero, map_zero, add_zero, sub_zero] at this
        exact this.symm)
    simp only [finrank_top, finrank_bot, add_zero] at this
    omega

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrPt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VacRealForm

open GlobalTheory.FockCompare

variable {D : D7}

def frPt {m n : ℕ} (B : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (B' : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ)
    (Z : D.what₂.Tau → Fin m → Fin n → ℂ) : D.what₂.Tau → Fin m → Fin n → ℂ :=
  fun τ => (B' τ * Matrix.of (Z τ) * (B τ)⁻¹ : Matrix (Fin m) (Fin n) ℂ)

def sqSum {m n : ℕ} (Z : D.what₂.Tau → Fin m → Fin n → ℂ) : ℝ := ∑ τ, ∑ a, ∑ b, ‖Z τ a b‖ ^ 2

def gZ (σ : (D.what₂.Tau → ℂ) →+ AE D) (S T : HSp D) (B : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (B' : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ) (Z : D.what₂.Tau → Fin T.rank → Fin S.rank → ℂ) : ℂ :=
  f (iotaW σ T S (frPt B B' Z)) * Complex.exp ((Real.pi * Formalism.L2.Pj.xiR D * sqSum Z : ℝ) : ℂ)

def thY (σ : (D.what₂.Tau → ℂ) →+ AE D) (S T : HSp D) (B : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (B' : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ) (δ : ℂ)
    (Y : D.what₂.Tau → Fin T.rank → Fin S.rank → ℂ) : ℂ :=
  gZ σ S T B B' f (δ⁻¹ • Y)

end GlobalTheory.VacRealForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionalIdealNormEqFiniteIdeleModule
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.LatVal.InvIdealNorm

open scoped GlobalTheory.Idele

variable {K : Type} [Field K] [NumberField K]

theorem eq_inv_smul_one {t : (Af K)ˣ} {𝔞 : FractionalIdeal (𝓞 K)⁰ K} (h : IsInvIdealOf t 𝔞) :
    𝔞 = t⁻¹ • (1 : FractionalIdeal (𝓞 K)⁰ K) := by
  have h' := GlobalTheory.LatVal.CurveTransport.isInvIdealOf_inv_smul_one t
  ext x
  rw [h x, h' x]

theorem finprod_absNorm_zpow_count {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 K), ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ FractionalIdeal.count K v I =
      ((FractionalIdeal.absNorm I : ℚ) : ℝ) := by
  let g : FractionalIdeal (𝓞 K)⁰ K →*₀ ℝ :=
    (Rat.castHom ℝ).toMonoidWithZeroHom.comp FractionalIdeal.absNorm
  have hg : ∀ J, g J = ((FractionalIdeal.absNorm J : ℚ) : ℝ) := fun _ => rfl
  conv_rhs => rw [← hg, ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI]
  rw [map_finprod g]
  · refine finprod_congr fun v => ?_
    rw [map_zpow₀, hg, FractionalIdeal.coeIdeal_absNorm]
    simp
  · refine (Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors I)).subset fun v hv h0 => hv ?_
    simp only [h0, zpow_zero]

end GlobalTheory.LatVal.InvIdealNorm


open GlobalTheory.LatVal.InvIdealNorm in
open scoped GlobalTheory.Idele in
theorem GlobalTheory.LatVal.nrm_eq_modF_of_isInvIdealOf : ∀ {K : Type} [Field K] [NumberField K] (t : (Af K)ˣ)
    (𝔞 : FractionalIdeal (𝓞 K)⁰ K) (h : IsInvIdealOf t 𝔞), nrm 𝔞 = modF t := by
  intro K _ _ t 𝔞 h
  have e := eq_inv_smul_one h
  rw [GlobalTheory.Idele.smul_one_eq] at e
  have h0 : 𝔞 ≠ 0 := e ▸ GlobalTheory.Idele.idealOf_ne_zero _
  rw [nrm, ← finprod_absNorm_zpow_count h0, modF]
  refine finprod_congr fun v => ?_
  congr 1
  rw [e, GlobalTheory.Idele.count_idealOf, GlobalTheory.Idele.ord_vw_inv, GlobalTheory.Idele.ord_vw, neg_neg]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFrobAtRestrictFiniteAbelianSubextensionStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Neutral.B1
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFrobAt_restrict_finiteAbelian_subextension : ∀ {K : Type} [Field K] [NumberField K] {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (e : Ω ≃ₐ[K] AlgebraicClosure K) (L : IntermediateField K (AlgebraicClosure K)) (h : IsFiniteAbelian K L) (v : HeightOneSpectrum (𝓞 K)) (A : ValuationSubring Ω), Formalism.ConjugateSelfDual.IsPlaceOver A v → ∀ σ : Formalism.ConjugateSelfDual.G K Ω, Formalism.ConjugateSelfDual.IsFrob (F := K) A (Formalism.ConjugateSelfDual.normV v) σ → ∀ Q : Ideal (𝓞 L), Q.IsPrime → Q.LiesOver v.asIdeal → haveI := h.finiteDimensional; haveI := h.isGalois; IsFrobAt K L (AlgEquiv.restrictNormalHom L ((e.symm.trans σ).trans e)) Q := by
  first | exact @GlobalTheory.FrobRestrict.isFrobAt_restrict | exact GlobalTheory.FrobRestrict.isFrobAt_restrict | (intros; apply GlobalTheory.FrobRestrict.isFrobAt_restrict <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHeckeTranslateHarrisTaylorPullbackBaseStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHeckeTranslate_harrisTaylor_pullback_base : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), k.Coprime p → 3 ≤ N → N.Coprime p → ∀ (S S' : Scheme.{0}) (s : S ⟶ Sp R) (f : S' ⟶ S) (o : Obj b (N * k) s) (o' : Obj b N s) (ψ : o.A ⟶ o'.A) (o₁ : Obj b (N * k) (f ≫ s)) (o₁' : Obj b N (f ≫ s)), IsHecke g c k N o o' ψ → ObjMap o₁ o f → ObjMap o₁' o' f → ∃ ψ₁ : o₁.A ⟶ o₁'.A, IsHecke g c k N o₁ o₁' ψ₁ := by
  first | (exact @GlobalTheory.UPel.HT.Hecke.PullHecke.isHecke_pull) | (exact GlobalTheory.UPel.HT.Hecke.PullHecke.isHecke_pull) | (intros; apply GlobalTheory.UPel.HT.Hecke.PullHecke.isHecke_pull  <;> assumption)
end

