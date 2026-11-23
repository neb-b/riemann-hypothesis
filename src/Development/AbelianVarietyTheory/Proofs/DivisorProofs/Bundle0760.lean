module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0737
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0351
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0485
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0456
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0740
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0727
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0713
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsNormRconvLeSiegel
public import GroundTheory.AutomorphicForms.ReductionSiegel
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyCompactDualHaar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0057
public import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0400
public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0743
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0754
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0742
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyFieldEqGaloisCohomology
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.FieldTw

theorem res_ofRings_sec {R : Type} [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R))
    {V U : Scheme.{0}} (j : V ⟶ U) (x : M.obj Γ(U, ⊤)) :
    Sec.res j (ofRings.sec M U x) = ofRings.sec M V ((M.map (Scheme.Γ.map j.op)).hom x) := by
  have h := congrArg (fun f => f.hom x) ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).naturality j.op)
  exact h.symm

theorem twF_map_mk {q : ℕ} (i : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) (ζ : Prim q A) :
    ((twF q i).map f).hom (Submodule.Quotient.mk (Finsupp.single ζ 1)) =
      Submodule.Quotient.mk (Finsupp.single (Prim.map f.hom ζ) 1) := by
  change (Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map f.hom) (Finsupp.single ζ 1)) :
    (Prim q B →₀ ULift.{1} (ZMod q)) ⧸ twRel q i B) = _
  rw [Finsupp.mapDomain_single]

theorem res_twGen {q : ℕ} (i : ℤ) {V U : Scheme.{0}} (j : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res j (twGen i ζ) = twGen i (Prim.map (Scheme.Γ.map j.op).hom ζ) := by
  unfold twGen
  refine (res_ofRings_sec (twF q i) j _).trans ?_
  exact congrArg (ofRings.sec (twF q i) V) (twF_map_mk i (Scheme.Γ.map j.op) ζ)

theorem quot_pow {q : ℕ} (i : ℤ) {A : Type} [CommRing A] (ζ ξ : Prim q A) (a : (ZMod q)ˣ)
    (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    (Submodule.Quotient.mk (Finsupp.single ξ 1) : (Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q i A) =
      (ULift.up ((a ^ i : (ZMod q)ˣ) : ZMod q) : ULift.{1} (ZMod q)) • Submodule.Quotient.mk (Finsupp.single ζ 1) := by
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, Finsupp.smul_single, smul_eq_mul, mul_one]
  exact Submodule.subset_span ⟨ζ, ξ, a, h, rfl⟩

theorem twGen_pow {q : ℕ} (i : ℤ) {U : Scheme.{0}} (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ)
    (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    twGen i ξ = (ULift.up ((a ^ i : (ZMod q)ˣ) : ZMod q) : ULift.{1} (ZMod q)) • twGen i ζ := by
  have := congrArg (((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op U)).hom) (quot_pow i ζ ξ a h)
  exact this.trans (LinearMap.map_smul _ _ _)

theorem res_id' {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.res (𝟙 U) x = x := by
  simp [Sec.res]

end GlobalTheory.EtC.FieldTw

namespace GlobalTheory.EtC.FieldTw

theorem cyclotomic_aeval_eq_zero {Ω : Type} [Field Ω] {q : ℕ} [NeZero q] {ζ : Ω} (hζ : IsPrimitiveRoot ζ q) :
    Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0 := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact hζ.isRoot_cyclotomic (Nat.pos_of_ne_zero (NeZero.ne q))

theorem field_tw_coh_eq_galois : B7 := by
  intro q _ K Ω _ _ _ _ hq i M _ ζ hζ b hM n
  have hqΩ : IsUnit (q : Ω) := by simpa using hq.map (algebraMap K Ω)
  let S : Scheme.{0} := Spec (CommRingCat.of Ω)
  let ι : Ω →+* Γ(S, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom
  let ζ0 : Prim q Ω := ⟨ζ, hqΩ, cyclotomic_aeval_eq_zero hζ⟩
  let ζ' : Prim q Γ(S, ⊤) := Prim.map ι ζ0
  let g : Sec (tw q (i : ℤ)) S := twGen (i : ℤ) ζ'
  obtain ⟨e, he1, -⟩ := _root_.GlobalTheory.EtC.gen_locallyConstant (ZMod q) (tw q (i : ℤ)) S g (GlobalTheory.T.tateTwist_isFreeRankOne_on_generatorSection q i S ζ')
  have hconst := GlobalTheory.T.locallyConstant_spec_localRing_const_bijective (ZMod q) Ω
  let φ : ZMod q →+ Sec (tw q (i : ℤ)) S :=
    { toFun := fun c => (ULift.up c : ULift.{1} (ZMod q)) • g
      map_zero' := by
        show (ULift.up (0 : ZMod q) : ULift.{1} (ZMod q)) • g = 0
        exact zero_smul _ _
      map_add' := fun a c => by
        show (ULift.up (a + c) : ULift.{1} (ZMod q)) • g = _
        rw [show (ULift.up (a + c) : ULift.{1} (ZMod q)) = ULift.up a + ULift.up c from rfl, add_smul] }
  have hφ : Function.Bijective φ := by
    have : (φ : ZMod q → Sec (tw q (i : ℤ)) S) = e S (𝟙 S) ∘ fun c => LocallyConstant.const S c := by
      funext c
      simp only [Function.comp_apply, he1, res_id']
      rfl
    rw [this]
    exact (e S (𝟙 S)).bijective.comp hconst
  let E1 : ZMod q ≃+ Sec (tw q (i : ℤ)) S := AddEquiv.ofBijective φ hφ
  let E0 : M ≃+ ZMod q := (b.equivFun.trans (LinearEquiv.funUnique Unit (ZMod q) (ZMod q))).toAddEquiv
  have hE0 : ∀ m, E0 m = b.repr m () := fun m => rfl
  refine GlobalTheory.T.nonempty_cohomology_addEquiv_galois_cohomology (ZMod q) (tw q (i : ℤ)) (GlobalTheory.T.tateTwist_finitary q i) K Ω M (E0.trans E1) ?_ n
  intro σ m

  have hσ : IsPrimitiveRoot (σ ζ) q := hζ.map_of_injective σ.injective
  obtain ⟨a, ha, hpow⟩ := hζ.eq_pow_of_pow_eq_one hσ.pow_eq_one
  have hcop : a.Coprime q := (hζ.pow_iff_coprime (Nat.pos_of_ne_zero (NeZero.ne q)) a).1 (hpow ▸ hσ)
  let u : (ZMod q)ˣ := ZMod.unitOfCoprime a hcop
  have hu : (u : ZMod q) = a := ZMod.coe_unitOfCoprime a hcop
  have hmρ := hM σ a hpow.symm

  have hm : m = b.repr m () • b () := by
    simpa using (b.sum_repr m).symm
  have hrep : b.repr (M.ρ σ m) () = b.repr m () * (a : ZMod q) ^ i := by
    have h1 : M.ρ σ m = (b.repr m () * (a : ZMod q) ^ i) • b () := by
      conv_lhs => rw [hm]
      rw [LinearMap.map_smul, hmρ, smul_smul]
    rw [h1, LinearEquiv.map_smul, b.repr_self]
    simp

  let ξ : Prim q Γ(S, ⊤) := Prim.map (Scheme.Γ.map (Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω))).op).hom ζ'
  have hξ : ξ.1 = ζ'.1 ^ (u : ZMod q).val := by
    rw [hu, ZMod.val_natCast, Nat.mod_eq_of_lt ha]
    show (Scheme.Γ.map (Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω))).op).hom (ι ζ) = (ι ζ) ^ a
    have hnat := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (σ : Ω →+* Ω))
    have := congrArg (fun f => f.hom ζ) hnat
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    rw [← map_pow, hpow]
    try exact this.symm
  have hg : Sec.res (Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω))) g =
      (ULift.up ((a : ZMod q) ^ i) : ULift.{1} (ZMod q)) • g := by
    rw [res_twGen, twGen_pow (i : ℤ) ζ' ξ u hξ]
    congr 2
  show (ULift.up (E0 (M.ρ σ m)) : ULift.{1} (ZMod q)) • g = Sec.res _ ((ULift.up (E0 m) : ULift.{1} (ZMod q)) • g)
  have hlin : ∀ c : ULift.{1} (ZMod q), Sec.res (Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω))) (c • g) =
      c • Sec.res (Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω))) g := fun c => LinearMap.map_smul _ _ _
  rw [hE0, hE0, hrep, hlin, hg, smul_smul]
  rfl

end GlobalTheory.EtC.FieldTw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmCurveTorsionTransportSecondPeriodStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Neutral.B1
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cmCurve_torsionTransport_secondPeriod : ∀ {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ (ι : K →+* ℂ) (Λ₀ : PeriodPair) (Ω₀ : ℂ), GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsLatOf ι 1 Λ₀ → Ω₀ ≠ 0 → letI : Algebra K ℂ := ι.toAlgebra; ∃ (X : WeierstrassCurve ℂ) (_ : X.IsElliptic) (ξ : (ℂ ⧸ GlobalTheory.EllipticCM.idealSub (1 : FractionalIdeal (𝓞 K)⁰ K)) ≃+ X.toAffine.Point), GlobalTheory.EllipticCM.IsAnalyticIso ξ ∧ ∀ (σ : ℂ ≃ₐ[K] ℂ) (t : (Af K)ˣ), GlobalTheory.EllipticCM.Transports σ t one_ne_zero ξ → ∃ (Λ₁ : PeriodPair) (Ω₁ : ℂ), TorsTransport ι σ.toRingEquiv t Λ₀ Λ₁ Ω₀ Ω₁ := by
  first | exact @GlobalTheory.LatVal.CurveTransport.exists_curve_torsTransport | exact GlobalTheory.LatVal.CurveTransport.exists_curve_torsTransport | (intros; apply GlobalTheory.LatVal.CurveTransport.exists_curve_torsTransport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonHermitianGramDetTwoVectorsNeStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.PlaneNorm
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_hermitianGramDetTwoVectors_ne : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → ∀ x y : Fin M → E, hE σ J x x ≠ 0 → hE σ J y y ≠ 0 → ∃ w : Fin M → E, gram2E σ J x w ≠ 0 ∧ gram2E σ J w y ≠ 0 := by
  first | exact @GlobalTheory.exists_common_hermitianGramDetTwoVectors_ne' | exact GlobalTheory.exists_common_hermitianGramDetTwoVectors_ne' | (intros; apply GlobalTheory.exists_common_hermitianGramDetTwoVectors_ne' <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjFiniteUnipotentMemOpenSubgroup
section
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped NumberField.AdeleRing

namespace GlobalTheory.FinConj

open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

theorem finEmb_eq_finGL (E : Type) [Field E] [NumberField E] (a : ℕ) (l : GL (Fin a) (Af E)) :
    finEmb E a l = finGL E a l := by
  have k1 : ∀ (c : Ad E) (x y : Af E), (c - sFin E y + sFin E x).1 = c.1 - 0 + 0 := fun _ _ _ => rfl
  have k2 : ∀ (c : Ad E) (x y : Af E), (c - sFin E y + sFin E x).2 = c.2 - y + x := fun _ _ _ => rfl
  apply (AdelicGLn.prodEquiv E a).injective
  rw [prodEquiv_finEmb]
  refine Prod.ext (Units.ext (Matrix.ext fun i j => ?_)) (Units.ext (Matrix.ext fun i j => ?_))
  · rw [AdelicGLn.prodEquiv_apply_fst]
    change (1 : Matrix (Fin a) (Fin a) (InfiniteAdeleRing E)) i j = ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j - (sFin E) ((1 : Matrix (Fin a) (Fin a) (Af E)) i j) + sFin E (l i j)).1
    rw [k1, sub_zero, add_zero, Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · rfl
    · rfl
  · rw [AdelicGLn.prodEquiv_apply_snd]
    change (l : Matrix (Fin a) (Fin a) (Af E)) i j = ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j - (sFin E) ((1 : Matrix (Fin a) (Fin a) (Af E)) i j) + sFin E (l i j)).2
    rw [k2, Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · rw [adele_one_snd, sub_self, zero_add]
    · rw [adele_zero_snd, sub_self, zero_add]

theorem unip_eq_unipGL (E : Type) [Field E] [NumberField E] (a r : ℕ) (z : BlockIx a r → Ad E) :
    (unip z : GA E a) = unipGL z := Units.ext rfl

theorem exists_conj_unip_mem :
    ∀ (E : Type) [Field E] [NumberField E] (a r : ℕ) (L : Subgroup (GL (Fin a) (Af E))),
    IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ ω : Set (GA E a), IsCompact ω →
    ∃ M : ℕ, 0 < M ∧ ∀ b ∈ ω, ∀ (ρ : Fin a → ℝ) (hρ : ∀ i, 0 < ρ i), ∀ k ∈ (GroundTheory.Automorphic.Reduction.maxCompact (K := E) (n := a)),
      ∀ z : BlockIx a r → Ad E, (∀ p, (z p).1 = 0) →
      (∀ p, ∃ c ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E, (z p).2 = (M : Af E) * c) →
      ∃ l ∈ L, (b * GroundTheory.Automorphic.Reduction.diagUnits a (fun i => GroundTheory.Automorphic.Reduction.posIdele (K := E) (ρ i) (hρ i)) * k)⁻¹ * unip z *
        (b * GroundTheory.Automorphic.Reduction.diagUnits a (fun i => GroundTheory.Automorphic.Reduction.posIdele (K := E) (ρ i) (hρ i)) * k) = finGL E a l := by
  intro E _ _ a r L hL ω hω
  set U : Subgroup (AdelicGLn.integralFiniteGL E a) := L.comap (AdelicGLn.integralFiniteGL E a).subtype
  have hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL E a)) := hL.preimage continuous_subtype_val
  obtain ⟨M, hM, h⟩ := exists_natCast_conj_unipGL_mem (K := E) (n := a) U hU hω r
  refine ⟨M, hM, fun b hb ρ hρ k hk z hz1 hz2 => ?_⟩
  obtain ⟨u, hu⟩ := h b hb ρ hρ k hk z hz1 hz2
  refine ⟨((u : AdelicGLn.integralFiniteGL E a) : GL (Fin a) (Af E)), u.2, ?_⟩
  rw [unip_eq_unipGL, ← finEmb_eq_finGL]
  exact hu

end GlobalTheory.FinConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDensityOfImmersion
section
noncomputable section

namespace GlobalTheory.SUVol

open MeasureTheory Filter Topology Matrix Metric Set
open scoped ENNReal NNReal

theorem exists_density_of_immersion (V M G : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (lam : Measure V) [lam.IsAddHaarMeasure] (μ : Measure G) [μ.IsHaarMeasure]
    (e : V → G) (m : G → M) (j : V →L[ℝ] M) (hj : Function.Injective j) (L : G → M →L[ℝ] M) (he : Continuous e)
    (h0 : e 0 = 1) (hd : HasStrictFDerivAt (fun x => m (e x)) j 0)
    (hL : ContinuousAt L 1) (hL1 : L 1 = ContinuousLinearMap.id ℝ M)
    (hm : ∀ g h, m (g * h) = L g (m h)) (hn : ∀ r : ℝ, 0 < r → e '' ball 0 r ∈ 𝓝 (1 : G)) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      Tendsto (fun r : ℝ => μ (e '' ball 0 r) / lam (ball 0 r)) (𝓝[>] 0) (𝓝 c) := by
  obtain ⟨p₀, hp₀⟩ := (j : V →ₗ[ℝ] M).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hj)
  let p : M →L[ℝ] V := LinearMap.toContinuousLinearMap p₀
  have hp : ∀ v, p (j v) = v := fun v => LinearMap.congr_fun hp₀ v
  let E : M →L[ℝ] V × M := p.prod (ContinuousLinearMap.id ℝ M - j.comp p)
  let D : V × M →L[ℝ] M := j.coprod (ContinuousLinearMap.id ℝ M)
  have hDE : ∀ x, D (E x) = x := fun x => by simp [D, E]
  let J : V →ₗᵢ[ℝ] V × M := ⟨LinearMap.inl ℝ V M, fun v => by simp⟩
  have hJ : E.comp j = J.toContinuousLinearMap := by
    ext v <;> simp [E, J, hp]
  refine GlobalTheory.CompactDualExists.exists_density_of_chart V (V × M) G lam μ e (fun g => E (m g)) J
    (fun g => ContinuousLinearMap.id ℝ _ + E.comp ((L g - ContinuousLinearMap.id ℝ M).comp D)) he h0
    (hJ ▸ E.hasStrictFDerivAt.comp 0 hd) ?_ (by simp [hL1]) (fun g h => ?_) hn
  · exact continuousAt_const.add (continuousAt_const.clm_comp ((hL.sub continuousAt_const).clm_comp
      continuousAt_const))
  · simp [hm, hDE]

section OneMatrix

variable {r : ℕ}

theorem det_exp (X : Matrix (Fin r) (Fin r) ℂ) : (NormedSpace.exp X).det = Complex.exp X.trace := by
  have hder : HasDerivAt (fun t : ℝ => (NormedSpace.exp (t • X)).det) X.trace 0 := by
    have h1 : ∀ a b, HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X) a b) (X a b) 0 := by
      intro a b
      open scoped Matrix.Norms.Operator in
      have h2 := ((Matrix.entryLinearMap ℝ ℂ a b).toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt 0
        (hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0)
      rw [zero_smul, NormedSpace.exp_zero, one_mul] at h2
      exact h2
    have h3 := ReciprocityTheory.GeometryOfNumbersTheory.hasDerivAt_det (fun t : ℝ => NormedSpace.exp (t • X)) X 0 h1
    simpa only [zero_smul, NormedSpace.exp_zero, Matrix.adjugate_one, Matrix.one_mul] using h3
  have hadd : ∀ s t : ℝ,
      NormedSpace.exp ((s + t) • X) = NormedSpace.exp (s • X) * NormedSpace.exp (t • X) := by
    intro s t
    rw [add_smul]
    exact Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left s).smul_right t)
  set f : ℝ → ℂ := fun t => (NormedSpace.exp (t • X)).det with hf
  have hd : ∀ t, HasDerivAt f (f t * X.trace) t := by
    intro t
    have h0 : HasDerivAt f X.trace (t - t) := by
      rw [sub_self]; exact hder
    have h1 := (h0.comp_sub_const t t).const_mul (f t)
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    simp only [hf]
    rw [← Matrix.det_mul, ← hadd, add_sub_cancel]
  have hg : ∀ t : ℝ, HasDerivAt (fun s : ℝ => f s * Complex.exp (-(s * X.trace))) 0 t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => -((s : ℂ) * X.trace)) (-X.trace) t := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const X.trace).fun_neg
    exact ((hd t).fun_mul h1.cexp).congr_deriv (by ring)
  have h2 := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) 1 0
  simp only [hf, one_smul, zero_smul, NormedSpace.exp_zero, Matrix.det_one, Complex.ofReal_one, one_mul,
    Complex.ofReal_zero, zero_mul, neg_zero, Complex.exp_zero, Complex.exp_neg] at h2
  exact (mul_inv_eq_one₀ (Complex.exp_ne_zero _)).1 h2

theorem map_conj_eq (A : Matrix (Fin r) (Fin r) ℂ) : A.map (starRingEnd ℂ) = Aᴴᵀ := rfl

theorem exp_map_conj (A : Matrix (Fin r) (Fin r) ℂ) :
    NormedSpace.exp (A.map (starRingEnd ℂ)) = (NormedSpace.exp A).map (starRingEnd ℂ) := by
  rw [map_conj_eq, map_conj_eq, Matrix.exp_transpose, Matrix.exp_conjTranspose]

def twist (H X : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  (H * (-X).map (starRingEnd ℂ) * H⁻¹)ᵀ

theorem continuous_twist (H : Matrix (Fin r) (Fin r) ℂ) : Continuous (twist H) :=
  ((continuous_const.matrix_mul (continuous_neg.matrix_map Complex.continuous_conj)).matrix_mul
    continuous_const).matrix_transpose

variable {H : Matrix (Fin r) (Fin r) ℂ}

theorem twist_transpose_mul (hH : H.det ≠ 0) (X : Matrix (Fin r) (Fin r) ℂ) :
    (twist H X)ᵀ * H = -(H * X.map (starRingEnd ℂ)) := by
  rw [twist, transpose_transpose, Matrix.nonsing_inv_mul_cancel_right _ _ hH.isUnit,
    Matrix.map_neg _ (map_neg _), Matrix.mul_neg]

theorem twist_eq_iff (hH : H.det ≠ 0) (X : Matrix (Fin r) (Fin r) ℂ) :
    twist H X = X ↔ Xᵀ * H + H * X.map (starRingEnd ℂ) = 0 := by
  constructor
  · intro h
    have := twist_transpose_mul hH X
    rw [h] at this
    rw [this, neg_add_cancel]
  · intro h
    rw [twist, Matrix.map_neg _ (map_neg _), Matrix.mul_neg, ← eq_neg_of_add_eq_zero_left h,
      Matrix.mul_nonsing_inv_cancel_right _ _ hH.isUnit, transpose_transpose]

theorem exp_twist (hH : H.det ≠ 0) (X : Matrix (Fin r) (Fin r) ℂ) :
    (NormedSpace.exp (twist H X))ᵀ * H * (NormedSpace.exp X).map (starRingEnd ℂ) = H := by
  rw [twist, Matrix.exp_transpose, transpose_transpose,
    Matrix.exp_conj _ _ ((Matrix.isUnit_iff_isUnit_det _).2 hH.isUnit),
    Matrix.nonsing_inv_mul_cancel_right _ _ hH.isUnit, exp_map_conj, Matrix.mul_assoc, ← Matrix.map_mul,
    GlobalTheory.UpqExpChart.exp_neg_mul_exp]
  simp

theorem exp_twist_eq (hH : H.det ≠ 0) {X : Matrix (Fin r) (Fin r) ℂ}
    (h : (NormedSpace.exp X)ᵀ * H * (NormedSpace.exp X).map (starRingEnd ℂ) = H) :
    NormedSpace.exp (twist H X) = NormedSpace.exp X := by
  have h1 := (exp_twist hH X).trans h.symm
  have h2 := congrArg (fun A => A * (NormedSpace.exp (-X)).map (starRingEnd ℂ) * H⁻¹) h1
  simp only [Matrix.mul_assoc _ ((NormedSpace.exp X).map (starRingEnd ℂ)), ← Matrix.map_mul,
    GlobalTheory.UpqExpChart.exp_mul_exp_neg, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
    Matrix.mul_nonsing_inv_cancel_right _ _ hH.isUnit] at h2
  exact transpose_injective h2

end OneMatrix

variable {ι : Type} {r : ℕ} {H : ι → Matrix (Fin r) (Fin r) ℂ}


end GlobalTheory.SUVol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleNbhdKillingCurveCohomologyClass
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.CurveNbhdExcision

theorem ht_subsingleton_of_subsingleton (q : ℕ) (Z : Type) [CommRing Z] [Subsingleton Z] (n i : ℤ) :
    Subsingleton (Ht q (sp Z) n i) := by
  refine ⟨fun a b => ?_⟩
  have hfs : RingHom.fst Z Z = RingHom.snd Z Z := RingHom.ext fun _ => Subsingleton.elim _ _
  have key : ∀ z : Ht q (sp Z) n i, z = 0 := by
    intro z
    obtain ⟨y, hy⟩ := (GlobalTheory.T.etaleCohomology_prod_ring_projections_bijective q Z Z n i).2 (z, 0)
    simp only [Prod.mk.injEq] at hy
    rw [← hy.1, ← hy.2, hfs]
  rw [key a, key b]

theorem away_zero_subsingleton (B : Type) [CommRing B] : Subsingleton (Localization.Away (0 : B)) := by
  have h : IsUnit (algebraMap B (Localization.Away (0 : B)) 0) := IsLocalization.Away.algebraMap_isUnit _
  rw [map_zero, isUnit_zero_iff] at h
  exact subsingleton_of_zero_eq_one h

theorem main : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (n i : ℤ), 0 < n → ∀ x : Ht q (sp B) n i, ∃ (A' : Type) (_ : CommRing A') (_ : Algebra B A'), IsExcisionNbhd B A' f ∧ pull _ (spMap (algebraMap B A')) _ _ x = 0 := by
  intro q _ k B _ _ _ _ _ _ hq f hf n i hn x
  by_cases hu : IsUnit f
  · haveI := away_zero_subsingleton B
    refine ⟨Localization.Away (0 : B), inferInstance, inferInstance, ⟨Algebra.Etale.of_isLocalizationAway 0, ?_, ?_⟩, ?_⟩
    · intro a'
      exact ⟨0, by rw [Subsingleton.elim (a' - _) 0]; exact Ideal.zero_mem _⟩
    · intro a _
      rw [Ideal.span_singleton_eq_top.mpr hu]
      exact Submodule.mem_top
    · haveI := ht_subsingleton_of_subsingleton q (Localization.Away (0 : B)) n i
      exact Subsingleton.elim _ _
  · obtain ⟨A', i1, i2, i3, hN, hx⟩ := GlobalTheory.T.etale_local_vanishing_cohomology q k B hq f hf hu n i (by omega) x
    exact ⟨A', i1, i2, ⟨i3, hN.1, hN.2⟩, hx⟩

end GlobalTheory.EtC.CurveNbhdExcision
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisStableTorsionFamilyKer
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem mulStable_intCast_add_sub (L : PeriodPair) (s : ℂ) (a : ℤ) (h : MulStable L s) :
    MulStable L (a + s) ∧ MulStable L (a - s) := by
  have ha : ∀ ω ∈ L.lattice, (a : ℂ) * ω ∈ L.lattice := fun ω hω => by
    have := L.lattice.smul_mem a hω
    rwa [zsmul_eq_mul] at this
  refine ⟨fun ω hω => ?_, fun ω hω => ?_⟩
  · rw [add_mul]; exact add_mem (ha ω hω) (h ω hω)
  · rw [sub_mul]; exact sub_mem (ha ω hω) (h ω hω)

theorem normSq_natCast_add_sub_sqrtNegNat (p a : ℕ) :
    Complex.normSq (((a : ℤ) : ℂ) + sqrtNegNat p) = ((a ^ 2 + p : ℕ) : ℝ) ∧
      Complex.normSq (((a : ℤ) : ℂ) - sqrtNegNat p) = ((a ^ 2 + p : ℕ) : ℝ) := by
  have h : √(p : ℝ) * √(p : ℝ) = p := Real.mul_self_sqrt (Nat.cast_nonneg p)
  constructor <;> simp [sqrtNegNat, Complex.normSq_apply, h, sq]

theorem exists_stable_family_ker : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → ∀ V : ValuationSubring ℂ, ∃ (N : ℕ) (ι : Type) (_ : Fintype ι) (T : ι → ℂ), Odd N ∧ N % 3 = 2 ∧ V.valuation (N : ℂ) = 1 ∧ Fintype.card ι = 2 * (N - 1) ∧ Stable L F T ∧ ∀ i, T i ∉ L.lattice ∧ (N : ℂ) * T i ∈ L.lattice := by
  intro p F L t hp _ h3 hD V
  obtain ⟨a, N, hN, hodd, hmod, hv⟩ := _root_.GlobalTheory.CMModel.exists_sq_add_prime_odd_mod_three_unit p V hp h3
  obtain ⟨hs, hs'⟩ := mulStable_intCast_add_sub L (sqrtNegNat p) (a : ℤ) hD.mul
  obtain ⟨hn, hn'⟩ := normSq_natCast_add_sub_sqrtNegNat p a
  rw [← hN] at hn hn'
  have hN0 : (N : ℝ) ≠ 0 := by
    have : N ≠ 0 := by omega
    exact_mod_cast this
  have h0 : ((a : ℤ) : ℂ) + sqrtNegNat p ≠ 0 := fun h => hN0 (by rw [← hn, h, map_zero])
  have h0' : ((a : ℤ) : ℂ) - sqrtNegNat p ≠ 0 := fun h => hN0 (by rw [← hn', h, map_zero])
  obtain ⟨S, hS⟩ := kerRepsExist L _ h0 hs
  obtain ⟨S', hS'⟩ := kerRepsExist L _ h0' hs'
  have hc := kerRepsCard L _ S h0 hs hS
  have hc' := kerRepsCard L _ S' h0' hs' hS'
  rw [hn] at hc
  rw [hn'] at hc'
  have hc1 : S.card + 1 = N := by exact_mod_cast hc
  have hc1' : S'.card + 1 = N := by exact_mod_cast hc'
  have hfac : (N : ℂ) = (((a : ℤ) : ℂ) - sqrtNegNat p) * (((a : ℤ) : ℂ) + sqrtNegNat p) := by
    have := sqrtNegNat_sq p
    rw [hN]; push_cast
    linear_combination this
  refine ⟨N, S ⊕ S', inferInstance, Sum.elim (fun t : S => (t : ℂ)) (fun t : S' => (t : ℂ)), hodd, hmod, hv,
    ?_, _root_.GlobalTheory.CMModel.stable_kerReps_add_sub p F L a S S' hD.g₂_mem hD.g₃_mem hD.mul hS hS', ?_⟩
  · rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_coe]; omega
  · rintro (⟨x, hx⟩ | ⟨x, hx⟩)
    · refine ⟨(hS.1 x hx).2, ?_⟩
      show (N : ℂ) * x ∈ _
      rw [hfac, mul_assoc]
      exact hs' _ (hS.1 x hx).1
    · refine ⟨(hS'.1 x hx).2, ?_⟩
      show (N : ℂ) * x ∈ _
      rw [hfac, mul_comm (_ - _), mul_assoc]
      exact hs _ (hS'.1 x hx).1

end GlobalTheory.CMModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarSpecialUnitaryLyingOverFlagDomainStatement
section
open NumberField MeasureTheory Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_haar_specialUnitary_lying_over_flagDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) [MeasurableSpace (realSU X.Ψ X.Gm)] [BorelSpace (realSU X.Ψ X.Gm)], 1 ≤ r → IsOrth X x → ∃ ν : Measure (realSU X.Ψ X.Gm), ν.IsHaarMeasure ∧ ∀ φ : Frame X.Ψ r → ℝ≥0∞, Measurable φ → (∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul y b) = φ y) → ∫⁻ g, φ (X.lmulC (fun τ => (((g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x) ∂ν = ∫⁻ z, φ (cpt X x z) ∂muF X x := by
  first | exact @GlobalTheory.SUHaarOver.exists_haar_lying_over | exact GlobalTheory.SUHaarOver.exists_haar_lying_over | (intros; apply GlobalTheory.SUHaarOver.exists_haar_lying_over <;> assumption)
end

