module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0828
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0252
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualCLatP
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0374
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneSubIdempotentSmulMemCompletionPrimeMul
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

namespace GlobalTheory.ComplOffPlace

open IsDedekindDomain
open scoped TensorProduct

private theorem valued_v_coe_inv_le_one_of_not_mem {E : Type} [Field E] [NumberField E] (Q : HeightOneSpectrum (𝓞 E))
    {x : 𝓞 E} (hx : x ∉ Q.asIdeal) : Valued.v ((((x : E)⁻¹ : E)) : Q.adicCompletion E) ≤ 1 := by
  rw [HeightOneSpectrum.adicCompletion.valued_coe, map_inv₀, RingOfIntegers.coe_eq_algebraMap,
    (HeightOneSpectrum.valuation_eq_one_iff_notMem (v := Q) (K := E)).mpr hx, inv_one]

private theorem adicCompletion_coe_inv_mul_coe {E : Type} [Field E] [NumberField E] (Q : HeightOneSpectrum (𝓞 E))
    {x : E} (hx : x ≠ 0) : ((x⁻¹ : E) : Q.adicCompletion E) * ((x : E) : Q.adicCompletion E) = 1 := by
  rw [← HeightOneSpectrum.adicCompletion.coe_mul, inv_mul_cancel₀ hx, HeightOneSpectrum.adicCompletion.coe_one]

theorem exists_comb {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
    (f : FiniteAdeleRing (𝓞 E) E) (h1 : f P = 1) (h0 : ∀ Q, Q ≠ P → f Q = 0) :
    ∃ x ∈ P.asIdeal, ∃ y ∈ P.asIdeal, ∃ b c : FiniteAdeleRing (𝓞 E) E, (∀ Q, Valued.v (b Q) ≤ 1) ∧
      (∀ Q, Valued.v (c Q) ≤ 1) ∧
      1 - f = b * algebraMap E _ (x : E) + c * algebraMap E _ (y : E) := by
  classical
  obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot

  have hfin : {Q : HeightOneSpectrum (𝓞 E) | Q.asIdeal ∣ Ideal.span {x}}.Finite :=
    Ideal.finite_factors (by rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot])

  have hcov : ¬ ((P.asIdeal : Set (𝓞 E)) ⊆
      ⋃ Q ∈ ((hfin.toFinset.erase P : Finset (HeightOneSpectrum (𝓞 E))) : Set (HeightOneSpectrum (𝓞 E))),
        ((fun Q : HeightOneSpectrum (𝓞 E) => Q.asIdeal) Q : Set (𝓞 E))) := by
    rw [Ideal.subset_union_prime (f := fun Q : HeightOneSpectrum (𝓞 E) => Q.asIdeal) P P
      (fun Q _ _ _ => Q.isPrime)]
    rintro ⟨Q, hQS, hle⟩
    exact (Finset.mem_erase.mp hQS).1
      (HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top hle).symm)
  obtain ⟨y, hyP, hyS⟩ := Set.not_subset.mp hcov
  have hy : ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → x ∈ Q.asIdeal → y ∉ Q.asIdeal := by
    intro Q hQ hxQ hyQ
    apply hyS
    refine Set.mem_biUnion (x := Q) ?_ hyQ
    rw [Finset.coe_erase, Set.mem_diff, Set.Finite.coe_toFinset]
    exact ⟨Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hxQ), hQ⟩

  let bf : ∀ Q : HeightOneSpectrum (𝓞 E), Q.adicCompletion E := fun Q =>
    if Q = P then 0 else if x ∈ Q.asIdeal then 0 else (((x : E)⁻¹ : E) : Q.adicCompletion E)
  let cf : ∀ Q : HeightOneSpectrum (𝓞 E), Q.adicCompletion E := fun Q =>
    if Q = P then 0 else if x ∈ Q.asIdeal then (((y : E)⁻¹ : E) : Q.adicCompletion E) else 0
  have hbf : ∀ Q, Valued.v (bf Q) ≤ 1 := by
    intro Q
    show Valued.v (if Q = P then 0 else if x ∈ Q.asIdeal then 0 else (((x : E)⁻¹ : E) : Q.adicCompletion E)) ≤ 1
    split_ifs with h1 h2
    · simp
    · simp
    · exact valued_v_coe_inv_le_one_of_not_mem Q h2
  have hcf : ∀ Q, Valued.v (cf Q) ≤ 1 := by
    intro Q
    show Valued.v (if Q = P then 0 else if x ∈ Q.asIdeal then (((y : E)⁻¹ : E) : Q.adicCompletion E) else 0) ≤ 1
    split_ifs with h1 h2
    · simp
    · exact valued_v_coe_inv_le_one_of_not_mem Q (hy Q h1 h2)
    · simp
  let b : FiniteAdeleRing (𝓞 E) E := Subtype.mk bf (Filter.Eventually.of_forall hbf)
  let c : FiniteAdeleRing (𝓞 E) E := Subtype.mk cf (Filter.Eventually.of_forall hcf)
  refine ⟨x, hxP, y, hyP, b, c, hbf, hcf, ?_⟩
  ext1 Q
  show (1 : Q.adicCompletion E) - f Q = bf Q * ((x : E) : Q.adicCompletion E) + cf Q * ((y : E) : Q.adicCompletion E)
  by_cases hQ : Q = P
  · subst hQ
    simp [bf, cf, h1]
  · have hxQ' : ∀ hxQ : x ∉ Q.asIdeal, (x : E) ≠ 0 := fun hxQ h =>
      hxQ (by rw [show x = 0 from by exact_mod_cast h]; exact Q.asIdeal.zero_mem)
    by_cases hxQ : x ∈ Q.asIdeal
    · have hyQ := hy Q hQ hxQ
      have hy0 : (y : E) ≠ 0 := fun h =>
        hyQ (by rw [show y = 0 from by exact_mod_cast h]; exact Q.asIdeal.zero_mem)
      simp only [bf, cf, if_neg hQ, if_pos hxQ, h0 Q hQ, sub_zero, zero_mul, zero_add]
      exact (adicCompletion_coe_inv_mul_coe Q hy0).symm
    · simp only [bf, cf, if_neg hQ, if_neg hxQ, h0 Q hQ, sub_zero, zero_mul, add_zero]
      exact (adicCompletion_coe_inv_mul_coe Q (hxQ' hxQ)).symm

theorem mul_smul_mem_hat (D : D7) {n : ℕ} (I : Ideal (𝓞 D.host.E)) (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    {a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E} (ha : a ∈ intAE D) {t : 𝓞 D.host.E} (ht : t ∈ I)
    {y : Fin n → GlobalTheory.AdLat.RA D.host.F D.host.E} (hy : y ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E))) :
    (a * (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (t : D.host.E)) • y ∈
      GlobalTheory.AdLat.hat D.host.F ((I • L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E)) := by
  unfold intAE at ha
  unfold GlobalTheory.AdLat.hat at hy ⊢
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, hb, x, hx, rfl⟩ := hz
    induction ha using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨c, hc, s, rfl⟩ := hw
      refine AddSubgroup.subset_closure ⟨c * b, fun v => mul_mem (hc v) (hb v),
        (s * t) • x, Submodule.smul_mem_smul (I.mul_mem_left s ht) hx, ?_⟩
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, Algebra.smul_def,
        map_mul, ← RingOfIntegers.coe_eq_algebraMap]
    | zero => simp
    | add u w _ _ hu hw =>
      rw [add_mul, add_smul]
      exact AddSubgroup.add_mem _ hu hw
    | neg u _ hu =>
      rw [neg_mul, neg_smul]
      exact AddSubgroup.neg_mem _ hu
  | zero =>
    rw [smul_zero]
    exact AddSubgroup.zero_mem _
  | add u w _ _ hu hw =>
    rw [smul_add]
    exact AddSubgroup.add_mem _ hu hw
  | neg u _ hu =>
    rw [smul_neg]
    exact AddSubgroup.neg_mem _ hu

theorem one_sub_smul_mem : ∀ (D : D7) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D) (n : ℕ) (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)),
    Formalism.L2.NTheta.IsIdemAt e P → ∀ y ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E)),
      (1 - finPart D e) • y ∈ GlobalTheory.AdLat.hat D.host.F ((P.asIdeal • L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E)) := by
  intro D P e n L he y hy
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨-, h1, h0⟩ := GlobalTheory.IdemSupport.delta_of_isIdemAt hΦ he
  obtain ⟨x, hx, x', hx', b, c, hb, hc, hbc⟩ := exists_comb P (Φ e) h1 h0
  obtain ⟨zb, -, hzb⟩ := hΦ.surj b
  obtain ⟨zc, -, hzc⟩ := hΦ.surj c
  have hzbi : finPart D zb ∈ intAE D := (hΦ.int zb).mpr fun Q => by rw [hzb]; exact hb Q
  have hzci : finPart D zc ∈ intAE D := (hΦ.int zc).mpr fun Q => by rw [hzc]; exact hc Q

  set s : AE D := (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA D.host.F 0 1) ⊗ₜ[D.host.F] (1 : D.host.E) with hs
  have hsi : infPart D s = 0 := by
    rw [hs]
    show Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA D.host.F) (AlgHom.id D.host.F D.host.E)
      ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA D.host.F 0 1) ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
    rw [Algebra.TensorProduct.map_tmul]
    exact TensorProduct.zero_tmul _ _
  have hsf : finPart D s = 1 := by
    rw [hs]
    show Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F) (AlgHom.id D.host.F D.host.E)
      ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA D.host.F 0 1) ⊗ₜ[D.host.F] (1 : D.host.E)) = 1
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    exact Algebra.TensorProduct.one_def.symm
  have hinc : ∀ z : D.host.E, finPart D (incA D z) = (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] z := by
    intro z
    show Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F) (AlgHom.id D.host.F D.host.E)
      ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ⊗ₜ[D.host.F] z) = _
    rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
  have key : (1 - e) * s = (zb * incA D (x : D.host.E) + zc * incA D (x' : D.host.E)) * s := by
    apply hΦ.ext'
    · simp only [map_mul, hsi, mul_zero]
    · intro Q
      have hΦe : Φ ((1 - e) * s) = Φ ((zb * incA D (x : D.host.E) + zc * incA D (x' : D.host.E)) * s) := by
        simp only [map_mul, map_sub, map_one, map_add (f := _), hΦ.inc, hzb, hzc, hbc]
      rw [hΦe]
  have key' : 1 - finPart D e =
      finPart D zb * ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (x : D.host.E)) +
        finPart D zc * ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (x' : D.host.E)) := by
    have h := congrArg (finPart D) key
    simpa only [map_mul, map_sub, map_one, map_add (f := _), hsf, mul_one, hinc] using h
  rw [key', add_smul]
  exact AddSubgroup.add_mem _ (mul_smul_mem_hat D P.asIdeal L hzbi hx hy)
    (mul_smul_mem_hat D P.asIdeal L hzci hx' hy)

end GlobalTheory.ComplOffPlace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OrientedPairFockMapsLieEquivariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

namespace GlobalTheory.RealQuot

theorem oriented_maps : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X) (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ),
  IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
  ∀ (Pi : ModuleCat.{0} ℂ) (rf : GA D X → Module.End ℂ Pi) (rl : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pi)
    (p : (WO M X → ℂ) →ₗ[ℂ] Pi), IsCoinvMap θ ω (algF ψ θ ε A B) Pi rf rl p →
  (∀ f, IsFinF ψ θ ε A B f → ∀ τ, ∀ Y ∈ lieAt X τ, ∀ P,
      p (fockF ψ θ ε A B f (GlobalTheory.RealQuot.actT ε A B eS τ Y P)) = rl τ Y (p (fockF ψ θ ε A B f P))) ∧
  (∀ f, IsFinF ψ θ ε A B f → ∀ P ∈ GlobalTheory.RealQuot.coinv ε A B eT, p (fockF ψ θ ε A B f P) = 0) ∧
  ∀ h ∈ GfC X, ∀ f, IsFinF ψ θ ε A B f → ∃ f', IsFinF ψ θ ε A B f' ∧
    ∀ P, rf h (p (fockF ψ θ ε A B f P)) = p (fockF ψ θ ε A B f' P) := by
  intro D ψ θ hθ ε M X A B χS χT ω eS eT hW hexp Pi rf rl p hp
  have hW' : IsWeilDatumO ψ (sgn ε M) X χS χT (ω.toSgn ε) := hW
  have hmem : ∀ f P, IsFinF ψ θ ε A B f → fockF ψ θ ε A B f P ∈ algF ψ θ ε A B :=
    fun f P hf => Submodule.subset_span ⟨f, P, hf, rfl⟩
  have e1 : ∀ h : GA D X, (ω.toSgn ε) (1, h) = ω (1, h) := by
    intro h
    show ω ((ofSgn ε M) 1, h) = ω (1, h)
    rw [map_one]
  have hL := fun f τ (hf : IsFinF ψ θ ε A B f) =>
    GlobalTheory.LieScalar.lieFockAll D (sgn ε M) X (frSgn ε A) B θ ψ χS χT (ω.toSgn ε) f τ (eS τ) (eT τ) hθ hW'
      (hexp τ).1 (hexp τ).2 hf
  refine ⟨?_, ?_, ?_⟩
  · intro f hf τ Y hY P
    refine hp.eql τ Y hY _ (hmem f P hf) _ (hmem f _ hf) ?_
    intro z
    have h := (hL f τ hf).2 Y hY P z
    simp only [e1] at h
    have e2 : actT ε A B eS τ Y P =
        GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ ((frSgn ε A).ε τ) (B.ε τ) (B.fr τ * Y * (B.fr τ)⁻¹) P + ((eS τ : ℂ) * Y.trace) • P := by
      rw [actT, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
    rw [e2]
    exact h
  · intro f hf P hP
    have hle : coinv ε A B eT ≤ LinearMap.ker (p ∘ₗ fockF ψ θ ε A B f) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨τ, Z, hZ, P₀, rfl⟩
      have hZ' : Z ∈ lieAt (sgn ε M) τ := by rw [GlobalTheory.SgnIdent.lieAt_sgn]; exact hZ
      show p (fockF ψ θ ε A B f (actS ε A B eT τ Z P₀)) = 0
      refine hp.invl τ Z hZ _ (hmem f P₀ hf) _ (hmem f _ hf) ?_
      intro z
      have h := (hL f τ hf).1 Z hZ' P₀ z
      have e : ∀ t : ℝ, (ω.toSgn ε) (oneP θ (sgn ε M) τ Z t, 1) = ω (oneP θ M τ Z t, 1) := by
        intro t
        show ω ((ofSgn ε M) (oneP θ (sgn ε M) τ Z t), 1) = _
        unfold oneP
        rw [GlobalTheory.SgnIdent.atTau_sgn θ hθ]
      simp only [e] at h
      have e3 : actS ε A B eT τ Z P₀ =
          GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS τ ((frSgn ε A).ε τ) (B.ε τ) ((A.fr τ * Z * (A.fr τ)⁻¹).map (starRingEnd ℂ)) P₀ +
            (-((eT τ : ℂ) * Z.trace)) • P₀ := by
        rw [actS, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, neg_smul, sub_eq_add_neg]
      rw [e3]
      exact h
    exact hle hP
  · intro h hh f hf
    refine ⟨ω (1, h) f, ?_, fun P => ?_⟩
    · obtain ⟨hth, hvac⟩ := hf
      have e : ∀ τ z, Formalism.IndefR.Datum.dRho (heisO ψ (sgn ε M) X) θ τ z (ω (1, h) f) =
          ω (1, h) (Formalism.IndefR.Datum.dRho (heisO ψ (sgn ε M) X) θ τ z f) := by
        intro τ z
        rw [← e1, GlobalTheory.OrientedHeis.om_dRho hW' hθ 1 h τ z hth, GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ X hh,
          GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ (sgn ε M) (inv_mem (one_mem _)), Matrix.one_mul, Matrix.mul_one]
      refine ⟨?_, fun τ z => ?_⟩
      · rw [← e1]; exact hW'.om_pres _ f hth
      · have h0 := hvac τ z
        unfold annih at h0 ⊢
        rw [e, e, ← map_smul, ← map_add (f := _), h0, map_zero]
    · have ht := GlobalTheory.OrientedHeis.om_fin_pureTensorO ψ (sgn ε M) X χS χT (ω.toSgn ε) hW' θ hθ 1 (one_mem _) h hh
        (frSgn ε A).cart B.cart A.onb B.onb f P hf.1
      rw [e1] at ht
      rw [← hp.eqf h hh _ (hmem f P hf)]
      exact congrArg p ht

end GlobalTheory.RealQuot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceModelIndicatorThetaFockLatticeVacuum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IndVac

variable {D : D7} {S T : HSp D}

theorem mem_of_indL_ne {L : AddSubgroup (WO S T)} {t : WO S T} (h : GlobalTheory.LiftLevel.indL L t ≠ 0) : t ∈ L := by
  by_contra hn
  exact h (by simp only [GlobalTheory.LiftLevel.indL, hn, if_false])

theorem isSBHalf_indL (a : AE D) (Λ L : AddSubgroup (WO S T)) (hL : ∀ x ∈ L, IsHalf a x)
    (h1 : ∃ m : ℕ, 0 < m ∧ ∀ x ∈ L, m • x ∈ Λ) (h2 : ∃ m : ℕ, 0 < m ∧ ∀ x ∈ Λ, IsHalf a x → m • x ∈ L) :
    IsSBHalf a Λ (GlobalTheory.LiftLevel.indL L) := by
  obtain ⟨m, hm, hm1⟩ := h1
  obtain ⟨n, hn, hn2⟩ := h2
  refine ⟨fun t ht => hL t (mem_of_indL_ne ht), m * n, Nat.mul_pos hm hn, fun u hu hu' t => ?_, fun t ht => ?_⟩
  · have hk : (m * n) • u ∈ L := by
      rw [← smul_smul]
      exact L.nsmul_mem (hn2 u hu hu') m
    simp only [GlobalTheory.LiftLevel.indL, L.add_mem_cancel_right hk]
  · rw [mul_comm, ← smul_smul]
    exact Λ.nsmul_mem (hm1 t (mem_of_indL_ne ht)) n

theorem partAt_eq (a : AE D) (w : WO S T) : GlobalTheory.LiftLevel.partAt a w = a • w := rfl

theorem symplO_half_eq_zero {a b : AE D} (hab : cA D b * a = 0) {r x : WO S T}
    (hr : r ∈ GlobalTheory.PlaceModel.half S T b) (hx : x ∈ GlobalTheory.PlaceModel.half S T a) : symplO S T r x = 0 := by
  rw [← (GlobalTheory.PlaceModel.mem_half S T).1 hr, ← (GlobalTheory.PlaceModel.mem_half S T).1 hx, GlobalTheory.PlaceModel.symplO_smul,
    smul_smul, hab, zero_smul, GlobalTheory.PlaceModel.symplO_zero_right]

theorem heisO_fix {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {a : AE D} (ha : a * a = a) (hinf : infPart D a = 0)
    {f₀ : WO S T → ℂ} {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm)
    (r : WO S T) (hr0 : heisO ψ S T r f₀ = f₀) (hx : ∀ x, IsHalf a x → symplO S T r x = 0)
    (hy : ∀ y, IsHalf (cA D a) y → symplO S T r y = 0)
    {Φ : WO S T → ℂ} (hΦ : IsSBHalf a (latO S T ΛS ΛT fun _ => True) Φ) : heisO ψ S T r (Tm Φ) = Tm Φ := by
  have hc : ∀ w, symplO S T r w = 0 → ∀ g, heisO ψ S T r (heisO ψ S T w g) = heisO ψ S T w (heisO ψ S T r g) :=
    fun w hw g => by
      have := GlobalTheory.PlaceModel.heisL_comm S T ψ r w g
      rw [hw, AddChar.map_zero_eq_one, one_smul] at this
      exact this
  have h' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀
      ((GlobalTheory.PlaceModel.heisL S T ψ r).comp Tm) :=
    { trans := fun Φ hΦ x hxa => by
        change heisO ψ S T r (Tm _) = heisO ψ S T x (heisO ψ S T r (Tm Φ))
        rw [hTm.trans Φ hΦ x hxa, hc x (hx x hxa)]
      modul := fun Φ hΦ y hya => by
        change heisO ψ S T r (Tm _) = heisO ψ S T y (heisO ψ S T r (Tm Φ))
        rw [hTm.modul Φ hΦ y hya, hc y (hy y hya)]
      vac := by
        change heisO ψ S T r (Tm _) = f₀
        rw [hTm.vac, hr0] }
  exact GlobalTheory.PlaceVec.placeModel_unique hψ hS hT ha hinf h' hTm hΦ

theorem heisenbergTranslate_add_three_fixes_of_trivial_phase (ψ : AddChar (AF D.host.F) ℂ) {f : WO S T → ℂ} {x y z : WO S T}
    (hx : heisO ψ S T x f = f) (hy : heisO ψ S T y f = f) (hz : heisO ψ S T z f = f)
    (p1 : ψ (symplOH S T y z) = 1) (p2 : ψ (symplOH S T x (y + z)) = 1) : heisO ψ S T (x + (y + z)) f = f := by
  have e1 := GlobalTheory.PlaceModel.heisL_heisL S T ψ y z f
  have e2 := GlobalTheory.PlaceModel.heisL_heisL S T ψ x (y + z) f
  change heisO ψ S T y (heisO ψ S T z f) = _ • heisO ψ S T (y + z) f at e1
  change heisO ψ S T x (heisO ψ S T (y + z) f) = _ • heisO ψ S T (x + (y + z)) f at e2
  rw [hz, hy, p1, one_smul] at e1
  rw [← e1, hx, p2, one_smul] at e2
  exact e2.symm


set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem indL_theta_fock_latVac : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (B : C.Bas), C.IsB B → ∀ (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → ∀ f₀ : WO S T → ℂ, IsVacO C.ψ C.θ S T (fun _ => 1) (C.sB B) (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) f₀ → ∀ Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ), IsPlaceModel C.ψ (symplO S T) (heisO C.ψ S T) (cA D e) (latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Tm → ∀ L : AddSubgroup (WO S T), (∀ x ∈ L, IsHalf (cA D e) x) → (∃ m : ℕ, 0 < m ∧ ∀ x ∈ L, m • x ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) → (∃ m : ℕ, 0 < m ∧ ∀ x ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True, IsHalf (cA D e) x → m • x ∈ L) → IsSBHalf (cA D e) (latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) (GlobalTheory.LiftLevel.indL L) ∧ C.IsTh (Tm (GlobalTheory.LiftLevel.indL L)) ∧ C.IsFock B (Tm (GlobalTheory.LiftLevel.indL L)) ∧ ∀ Λ'' : AddSubgroup (WO S T), (∀ u ∈ Λ'', GlobalTheory.LiftLevel.partAt (cA D e) u ∈ L ∧ (∀ t ∈ L, C.ψ (symplO S T t (GlobalTheory.LiftLevel.partAt e u)) = 1) ∧ GlobalTheory.LiftLevel.partAt (1 - e - cA D e) u ∈ latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) → IsLatVac (heisO C.ψ S T) Λ'' (Tm (GlobalTheory.LiftLevel.indL L)) := by
  intro D S T C B hB ΛT hT P e he f₀ hvac Tm hTm L hL hm1 hm2
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he
  have hee : e * e = e := ho.idem
  have hea : e * cA D e = 0 := he.2
  have ha : cA D e * cA D e = cA D e := ho.conj.idem
  have hcc : cA D (cA D e) = e := cA_cA e
  have hS := GlobalTheory.Ker.Base.selfDualC_stdL C.m.gS
  have hψ := C.std
  have hinf : infPart D (cA D e) = 0 := ho.conj.infPart_eq
  have hinf' : infPart D (cA D (cA D e)) = 0 := ho.conj.conj.infPart_eq
  have hSB := isSBHalf_indL (cA D e) _ L hL hm1 hm2
  have hth : IsThetaAt C.ψ (symplO S T) (heisO C.ψ S T) (cA D e)
      (latO S T (stdL D.host.E S.rank : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
      1 f₀ (GlobalTheory.LiftLevel.indL L) (Tm (GlobalTheory.LiftLevel.indL L)) :=
    ⟨⟨Tm, hTm⟩, fun T' hT' => GlobalTheory.PlaceVec.placeModel_unique hψ hS hT ha hinf hTm hT' hSB⟩
  have hθf := GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hψ C.inf hth hvac.2.theta
  refine ⟨hSB, hθf, fun τ => GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hψ.1.1 C.inf hinf hinf' hth hvac.2.theta hθf
    (hvac.2.fock τ), ?_⟩
  obtain ⟨b, hbd⟩ : ∃ b : AE D, b = 1 - e - cA D e := ⟨_, rfl⟩
  have hb : b * b = b := by rw [hbd]; linear_combination hee + ha + 2 * hea
  have hcb : cA D b = b := by rw [hbd, map_sub, map_sub, map_one, hcc]; ring
  have hba : cA D b * cA D e = 0 := by rw [hcb, hbd]; linear_combination -hea - ha
  have hbe : cA D b * e = 0 := by rw [hcb, hbd]; linear_combination -hee - hea
  have hfix_a : ∀ x ∈ L, heisO C.ψ S T x (Tm (GlobalTheory.LiftLevel.indL L)) = Tm (GlobalTheory.LiftLevel.indL L) := fun x hx => by
    rw [← hTm.trans _ hSB x (hL x hx)]
    congr 1
    funext t
    simp only [GlobalTheory.LiftLevel.indL, L.add_mem_cancel_right hx]
  have hfix_e : ∀ y, IsHalf e y → (∀ t ∈ L, C.ψ (symplO S T t y) = 1) →
      heisO C.ψ S T y (Tm (GlobalTheory.LiftLevel.indL L)) = Tm (GlobalTheory.LiftLevel.indL L) := fun y hy ht => by
    rw [← hTm.modul _ hSB y (by rw [hcc]; exact hy)]
    congr 1
    funext t
    by_cases h : t ∈ L
    · simp only [GlobalTheory.LiftLevel.indL, h, if_true, ht t h, one_mul]
    · simp only [GlobalTheory.LiftLevel.indL, h, if_false, mul_zero]
  have hfix_r : ∀ r ∈ GlobalTheory.PlaceModel.half S T b, heisO C.ψ S T r f₀ = f₀ →
      heisO C.ψ S T r (Tm (GlobalTheory.LiftLevel.indL L)) = Tm (GlobalTheory.LiftLevel.indL L) := fun r hr hr0 =>
    heisO_fix hψ hS hT ha hinf hTm r hr0
      (fun x hx => symplO_half_eq_zero hba hr ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hx))
      (fun y hy => symplO_half_eq_zero (by rw [hcc]; exact hbe) hr ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hy)) hSB
  have hdec : ∀ u : WO S T, u = cA D e • u + (e • u + b • u) := fun u => by
    rw [← add_smul, ← add_smul, show cA D e + (e + b) = 1 by rw [hbd]; ring, one_smul]
  have hbmem : ∀ u : WO S T, b • u ∈ GlobalTheory.PlaceModel.half S T b := fun u => by
    show b • b • u = b • u
    rw [smul_smul, hb]
  have hemem : ∀ u : WO S T, e • u ∈ GlobalTheory.PlaceModel.half S T e := fun u => by
    show e • e • u = e • u
    rw [smul_smul, hee]
  have hamem : ∀ u : WO S T, cA D e • u ∈ GlobalTheory.PlaceModel.half S T (cA D e) := fun u => by
    show cA D e • cA D e • u = cA D e • u
    rw [smul_smul, ha]
  have hez : ∀ u : WO S T, symplO S T (e • u) (b • u) = 0 := fun u => by
    rw [GlobalTheory.PlaceModel.symplO_skew, symplO_half_eq_zero hbe (hbmem u) (hemem u), neg_zero]
  have haz : ∀ u : WO S T, symplO S T (cA D e • u) (b • u) = 0 := fun u => by
    rw [GlobalTheory.PlaceModel.symplO_skew, symplO_half_eq_zero hba (hbmem u) (hamem u), neg_zero]
  intro Λ'' hΛ''
  refine ⟨fun u hu => ?_, fun e' he' u hu hh => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hΛ'' u hu
    rw [partAt_eq] at h1 h3
    simp only [partAt_eq] at h2
    rw [← hbd] at h3
    have e2u : 2 • u = 2 • (cA D e • u) + (2 • (e • u) + 2 • (b • u)) := by
      conv_lhs => rw [hdec u]
      rw [smul_add, smul_add]
    rw [e2u]
    have h2' : algebraMap D.host.F (AF D.host.F) (1 / 2) * 2 = 1 := by
      rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
      norm_num
    refine heisenbergTranslate_add_three_fixes_of_trivial_phase C.ψ (hfix_a _ (L.nsmul_mem h1 2))
      (hfix_e _ ((GlobalTheory.PlaceModel.isHalf_iff S T).2 ((GlobalTheory.PlaceModel.half S T e).nsmul_mem (hemem u) 2))
        fun t ht => by rw [two_nsmul, GlobalTheory.PlaceModel.symplO_add_right, AddChar.map_add_eq_mul, h2 t ht, one_mul])
      (hfix_r _ ((GlobalTheory.PlaceModel.half S T _).nsmul_mem (hbmem u) 2) (hvac.2.lat.1 _ h3)) ?_ ?_
    · simp only [symplOH, two_nsmul, GlobalTheory.PlaceModel.symplO_add_left, GlobalTheory.PlaceModel.symplO_add_right, hez, add_zero,
        mul_zero, AddChar.map_zero_eq_one]
    · have hs : symplOH S T (2 • (cA D e • u)) (2 • (e • u) + 2 • (b • u)) =
          symplO S T (cA D e • u) (e • u) + symplO S T (cA D e • u) (e • u) := by
        simp only [symplOH, two_nsmul, GlobalTheory.PlaceModel.symplO_add_left, GlobalTheory.PlaceModel.symplO_add_right, haz, add_zero]
        linear_combination (2 * symplO S T (cA D e • u) (e • u)) * h2'
      rw [hs, AddChar.map_add_eq_mul, h2 _ h1, one_mul]
  · obtain ⟨h1, h2, h3⟩ := hΛ'' u hu
    rw [partAt_eq] at h1 h3
    simp only [partAt_eq] at h2
    rw [← hbd] at h3
    have hu' : u ∈ GlobalTheory.PlaceModel.half S T e' := (GlobalTheory.PlaceModel.isHalf_iff S T).1 hh
    have hin : ∀ c : AE D, c • u ∈ GlobalTheory.PlaceModel.half S T e' := fun c => by
      rw [GlobalTheory.PlaceModel.mem_half, smul_comm, (GlobalTheory.PlaceModel.mem_half S T).1 hu']
    have hae : symplO S T (cA D e • u) (e • u) = 0 :=
      symplO_half_eq_zero (by rw [mul_comm]; exact he'.2.1) (hin _) (hin _)
    rw [hdec u]
    refine heisenbergTranslate_add_three_fixes_of_trivial_phase C.ψ (hfix_a _ h1) (hfix_e _ ((GlobalTheory.PlaceModel.isHalf_iff S T).2 (hemem u)) h2)
      (hfix_r _ (hbmem u) (hvac.2.lat.2 e' he' _ h3 ((GlobalTheory.PlaceModel.isHalf_iff S T).2 (hin _)))) ?_ ?_
    · rw [symplOH, hez, mul_zero, AddChar.map_zero_eq_one]
    · rw [symplOH, GlobalTheory.PlaceModel.symplO_add_right, hae, haz, add_zero, mul_zero, AddChar.map_zero_eq_one]

end GlobalTheory.IndVac

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzDatumEqOfThetaFunctionEqStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzDatum_eq_of_thetaFunction_eq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ {Z : Type} (crd : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Z), ∀ (Φ₁ Φ₂ : (Fin n × Fin d → AF F) → ℂ) (f : Z → ℂ), IsDatum M ψ crd Φ₁ f → IsDatum M ψ crd Φ₂ f → Φ₁ = Φ₂ := by
  first | exact @GlobalTheory.ThetaInj.theta_inj | exact GlobalTheory.ThetaInj.theta_inj | (intros; apply GlobalTheory.ThetaInj.theta_inj <;> assumption)
end

