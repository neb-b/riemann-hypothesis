module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0066
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1206
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0414
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0442
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0179
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0284
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0235
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0830
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitLastBlockActX

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardPairAlongChain
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.StdSteps

theorem even_N (R : Ranks) (j : ℕ) : Even (R.N j) :=
  R.k_even.add (R.t_odd.add_one.mul_left j)

theorem N_lt_succ (R : Ranks) (j : ℕ) : R.N j < R.N (j + 1) := by
  unfold Ranks.N
  rw [Nat.add_mul]
  omega

theorem realPlace_cmTrace_zero_element_eq_I_mul_abs (D : D7) (h : D.host.ccK = ⊤) (τ : D.what₂.Tau) :
    tauE D τ D.host.xi0 = Complex.I * ((Real.sqrt D.host.d)⁻¹ : ℝ) := by
  have h1 : tauE D τ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) :=
    ((factEmb D.R D.host).2 _).2 (D.eTau τ).2
  have h2 : (0 : ℝ) < Real.sqrt D.host.d := Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)
  have h3 : ((Real.sqrt D.host.d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h2.ne'
  rw [Host.xi0, h, Ideal.absNorm_top, map_div₀, map_neg, map_one, map_mul, h1, Nat.cast_one, map_one, one_mul, Complex.ofReal_inv]
  field_simp
  rw [Complex.I_sq]

theorem scale_eq (D : D7) {δ : ℂ} (hδ : δ ≠ 0) :
    (Formalism.MainNotions.TaylorLogMetric.area (Formalism.MainNotions.TaylorLogMetric.lamOf D ⊤ δ))⁻¹ * ‖δ‖ ^ 2 = 2 * (Real.sqrt D.host.d)⁻¹ := by
  have h2 : (0 : ℝ) < Real.sqrt D.host.d := Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)
  have h3 : ‖δ‖ ≠ 0 := norm_ne_zero_iff.2 hδ
  rw [GlobalTheory.MomDict.area_lamOf D ⊤ δ top_ne_bot, Ideal.absNorm_top, Complex.normSq_eq_norm_sq]
  field_simp
  simp

end GlobalTheory.AdForm.StdSteps
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StdCharSymplecticHalfPeriodLatticeEqOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.HalfPairing
open GlobalTheory.LatVac

variable {D : D7} {S T : HSp D} {N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem toMatrix_mem_latRat (hc : D.host.ccK = ⊤) (hN : IsSelfDualC S N) {x : Formalism.L2.Col.HomE D.host.E S.rank T.rank}
    (hx : x ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') :
    LinearMap.toMatrix' x ∈ latRat S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) := by
  have hA : D.host.AA = D.host.AA0 := by
    rw [Formalism.BasicNotions.Host.AA, Formalism.BasicNotions.Host.ccE, hc, Ideal.map_top, FractionalIdeal.coeIdeal_top, one_mul]
  obtain ⟨n, s, s', hs, hss⟩ := GlobalTheory.LatVacDual.dualFamily D S N hN
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨r, hr, x, hx, rfl⟩ := hz
    have e : LinearMap.toMatrix' (r • x) = ∑ k, genMap S T r (s' k) (x (s k)) := by
      refine Matrix.ext fun i j => ?_
      have h1 : (Pi.single j 1 : Fin S.rank → D.host.E) = ∑ k, (∑ l, star (s' k l) * S.gram l j) • s k := by
        funext a
        rw [Finset.sum_apply, Pi.single_apply, ← hss a j]
        exact Finset.sum_congr rfl fun k _ => mul_comm _ _
      rw [Matrix.sum_apply, LinearMap.toMatrix'_apply]
      change r * x (Pi.single j 1) i = _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [h1, map_sum, Finset.sum_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, Pi.smul_apply, smul_eq_mul, genMap, Matrix.of_apply]
      ring
    rw [e]
    exact sum_mem fun k _ => AddSubgroup.subset_closure ⟨r, hA ▸ hr, _, (hs k).2, _, hx _ (hs k).1, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx =>
    have e : LinearMap.toMatrix' (c • x) = (c : D.host.E) • LinearMap.toMatrix' x := by
      ext i j; rfl
    rw [e]
    exact smul_mem_latRat c hx

theorem smul_mem_locP {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ} {SS : Finset (HeightOneSpectrum (𝓞 E))}
    {M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)} {c : ℕ} (hc : 0 < c) {y : Formalism.L2.Col.HomE E a b} (hy : y ∈ halfBO SS M c)
    (Q : HeightOneSpectrum (𝓞 E)) : (c : E) • y ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M := by
  have h : ((c : E) ^ expS SS Q)⁻¹ • y ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M := (Submodule.mem_iInf _).1 hy Q
  have hc' : (c : E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  have key : ∀ k : ℕ, (c : E) = (c : E) ^ k * ((c : E) ^ expS SS Q)⁻¹ → (c : E) • y ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M := fun k hk => by
    have := nsmul_mem h (c ^ k)
    rwa [← Nat.cast_smul_eq_nsmul E, smul_smul, Nat.cast_pow, ← hk] at this
  unfold expS at key
  split_ifs at key
  · exact key 2 (by field_simp)
  · exact key 0 (by simp)
  · exact key 1 (by simp)

theorem conj_comp_mem (hc : D.host.ccK = ⊤) (hN : IsSelfDualC S N) {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)}
    (he : Formalism.L2.NTheta.IsIdemAt e P) (h0 : infPart D e = 0) {x : Formalism.L2.Col.HomE D.host.E S.rank T.rank}
    (hx : x ∈ Formalism.HermitianLatticesTheory.localization₂ (Formalism.L2.Col.conjPrime₂ P).asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N')) :
    ((LinearMap.toMatrix' x).map fun r => cA D e * incA D r : WO S T) ∈
      latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True := by
  obtain ⟨s, hs, hsx⟩ := hx
  have hs' : Formalism.L2.Col.cO D.host.E s ∉ P.asIdeal := hs
  have hne : Formalism.L2.Col.cO D.host.E s ≠ 0 := fun h => hs' (h ▸ zero_mem _)
  have hs0 : (s : D.host.E) ≠ 0 := fun h => hne (by rw [show s = 0 from RingOfIntegers.ext h, map_zero])
  have h1 : finPart D (e * incA D ((Formalism.L2.Col.cO D.host.E s : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra h
    exact hs' ((he.2 _ hne).2 h)
  have h2 := GlobalTheory.PlaceVec.cF_mem_int (GlobalTheory.IdemIntegral.toEAf_mem_of_finPart h1)
  rw [← GlobalTheory.AdelicLatMove.toEAf_cA, RingHom.map_mul (cA D)] at h2
  have h3 : cA D (incA D ((Formalism.L2.Col.cO D.host.E s : D.host.E)⁻¹)) = incA D (s : D.host.E)⁻¹ := by
    change incA D (star (star (s : D.host.E))⁻¹) = _
    rw [star_inv₀, star_star]
  rw [h3] at h2
  have h4 := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ (GlobalTheory.PlaceVec.finPart_mem_intAE h2) _
    (finTens_mem_latO (one_mem_intAf _) (toMatrix_mem_latRat hc hN hsx))
  convert h4 using 1
  ext i j
  have h5 := GlobalTheory.PlaceVec.infPart_cA h0
  rw [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  refine GlobalTheory.SplitScalar.adele_ext (by simp only [RingHom.map_mul, h5, zero_mul]) ?_
  have h6 : finPart D (finTens 1 (LinearMap.toMatrix' (s • x)) i j) =
      finPart D (incA D ((s : D.host.E) * LinearMap.toMatrix' x i j)) := rfl
  rw [RingHom.map_mul (finPart D) (_ * _), h6, ← RingHom.map_mul, mul_assoc, ← RingHom.map_mul (incA D),
    inv_mul_cancel_left₀ hs0]

theorem char_sympl_halfB : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (c : ℕ), 0 < c → Odd c → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → LaFacts (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' → (∃ ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E), IsSelfDualC S ΛS ∧ (ΛS : Set (Fin S.rank → D.host.E)) = latFr S hS N) → (∃ ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E), IsSelfDualC T ΛT ∧ (ΛT : Set (Fin T.rank → D.host.E)) = latFr T hT N') → ∀ y' ∈ halfBO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, ∀ u ∈ (latO S T (latFr S hS N) (latFr T hT N') fun _ => True), ψ (symplO S T (c • u) (((LinearMap.toMatrix' (y')).reindex (finCongr hT.symm) (finCongr hS.symm)).map fun r => cA D e * incA D r)) = 1 := by
  intro D ψ θ S T a b hS hT δ sc hP e SS hE N N' c hc _ _ _ ⟨ΛS, dS, eS⟩ ⟨ΛT, dT, eT⟩ y hy u hu
  subst hS hT
  obtain rfl : ΛS = N := SetLike.coe_injective eS
  obtain rfl : ΛT = N' := SetLike.coe_injective eT
  rw [← eS, ← eT] at hu
  change ψ (symplO S T (c • u) ((LinearMap.toMatrix' y).map fun r => cA D e * incA D r)) = 1
  have hmem : c • ((LinearMap.toMatrix' y).map fun r => cA D e * incA D r : WO S T) ∈
      latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True := by
    obtain ⟨⟨es, hes, rfl⟩, -⟩ := hE
    have e1 : c • ((LinearMap.toMatrix' y).map fun r => cA D (∑ PP ∈ SS, es PP) * incA D r : WO S T) =
        ∑ PP ∈ SS, ((LinearMap.toMatrix' ((c : D.host.E) • y)).map fun r => cA D (es PP) * incA D r : WO S T) := by
      ext i j
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Matrix.smul_apply, Matrix.map_apply, Matrix.sum_apply, map_sum, nsmul_eq_mul, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun PP _ => ?_
      change _ = cA D (es PP) * incA D ((c : D.host.E) * LinearMap.toMatrix' y i j)
      rw [RingHom.map_mul (incA D), map_natCast, mul_left_comm]
    rw [e1]
    refine sum_mem fun PP hPP => conj_comp_mem hP.cc dS (hes PP hPP) ?_ (smul_mem_locP hc hy _)
    refine GlobalTheory.PlaceVec.idemSum_infPart (P := {PP}) ⟨⟨es, fun Q hQ => ?_, (Finset.sum_singleton _ _).symm⟩, (hes PP hPP).1.2.1⟩
    rw [Finset.mem_singleton.1 hQ]
    exact hes PP hPP
  have h := char_sympl_eq_one hP.std dS dT hu hmem
  rw [← symplHom_apply, map_nsmul] at h
  rw [← symplHom_apply, map_nsmul]
  exact h

end GlobalTheory.AdForm.HalfPairing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepVectorExistsNonzeroVacuum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.StepVecOK

theorem stepVec_exists_vac : ∀ (D : D7) (c : Com D), c.Is → ∀ (k : Fin D.R.m) (s s' : PiLocalization₂ D), s.Is c k → s'.Is c (k + 1) → (∃ ξ f₀ f, IsStepVecOf c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) s.Λ s'.Λ s.β s'.β s.L (c.chi (k + 1)) ∅ ξ f₀ f) ∧ ∀ ξ f₀ f, IsStepVecOf c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) s.Λ s'.Λ s.β s'.β s.L (c.chi (k + 1)) ∅ ξ f₀ f → IsThetaFunO c.ψ s.V s'.V f ∧ f ≠ 0 ∧ (∀ τ, IsFockVacAt (heisO c.ψ s.V s'.V) c.θ τ (cplxO (cart s.M τ) (cart s'.M τ)) f) ∧ ∀ φ, IsThetaFunO c.ψ s.V s'.V (pureTensorO c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) (onb s.M) (onb s'.M) f φ) := open GlobalTheory.PlaceDatum in by
  classical
  intro D c hc k s s' hs hs'
  have hr : s.V.rank ≤ s'.V.rank := by
    rw [hs.rank, hs'.rank]
    show D.R.r + (k : ℕ) * D.R.t ≤ D.R.r + ((k : ℕ) + 1) * D.R.t
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ _)) _
  refine ⟨?_, fun ξ f₀ f h => ?_⟩
  · obtain ⟨f₀, hf₀⟩ := GlobalTheory.VacuumO.vacExists D c.ψ c.θ hc.std hc.inf s.V s'.V (cart s.M) (cart s'.M) hs.sigOK hs'.sigOK
      (GlobalTheory.Chain.VacVec.cart_isCartanInv s.M) (GlobalTheory.Chain.VacVec.cart_isCartanInv s'.M) s.Λ s'.Λ hs.selfDual hs'.selfDual
    obtain ⟨_, ξL, hL⟩ := hs.lev
    have hsp : ∃ e : AE D, IsIdemSum e (s.L.Pg ∪ ∅) := by
      obtain ⟨e, he⟩ := hc.split
      refine ⟨e, ?_⟩
      rw [Finset.union_empty, hL]
      exact he
    have hstep : StepVecExists D := by
      intro ψ θ S T sS sT ΛS ΛT βS βT LS χj Q ξ hS hT _ _ _ ⟨e, he⟩ f₀ hf
      have hinf := infPart_idemSum he
      obtain ⟨K, hK, hC⟩ := exists_nsmul_of_frMapO (GlobalTheory.PlaceVec.selfDual_isFullLattice S ΛS hS)
        (GlobalTheory.PlaceVec.selfDual_isFullLattice T ΛT hT) βS βT
      obtain ⟨f, h⟩ := exists_isThetaAt hf.1 hS hT (idemSum_mul_self he) hinf
        (GlobalTheory.PlaceModelSum.placeModelExistsSum D ψ hf.1 S T ΛS ΛT hS hT _ e he f₀ hf.2.theta hf.2.lat).1
        (isSBHalf_of_red e _ (frMapO S T βS βT) (frMapO_add βS βT) (exists_den_frMapO hS.1.fg hT.1.fg βS βT)
          ⟨K, hK, fun t ht => hC t (infPart_of_half hinf ht)⟩ (LS.Pg ∪ Q)
          (fun y => omegaG LS χj y * omegaQ Q LS.r ξ 1 y) fun y y' h => by
            rw [omegaG_congr LS χj y y' fun PP hP => h PP (Finset.mem_union_left _ hP),
              omegaQ_congr Q LS.r ξ 1 y y' fun PP hP => h PP (Finset.mem_union_right _ hP)])
      exact ⟨f, hf, e, he, h⟩
    obtain ⟨f, hf⟩ := hstep c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) s.Λ s'.Λ s.β s'.β s.L
      (c.chi ((k : ℕ) + 1)) ∅ 1 hs.selfDual hs'.selfDual hs.frame hs'.frame (Finset.disjoint_empty_right _) hsp f₀ hf₀
    exact ⟨1, f₀, f, hf⟩
  · obtain ⟨h1, h2, h3⟩ := GlobalTheory.Chain.StepVac.stepVec_vac hs.selfDual hs'.selfDual hr h
    exact ⟨h1, h2, h3, fun φ => GlobalTheory.FockTheta.ptStable D c.ψ c.θ hc.std hc.inf s.V s'.V _ _ _ _ f φ h1⟩

end GlobalTheory.ChainOnto.StepVecOK
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepWeilDatumNonzeroFockVacuum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.StepExp

variable {D : D7}

theorem chrStep_exp' {c : Com D} (hc : c.Is) (k : Fin D.R.m) (τ : D.what₂.Tau) :
    HasInfExp D (c.chS ((k : ℕ) + 1)) τ (expS D k τ) ∧ HasInfExp D (c.chT ((k : ℕ) + 1)) τ (expT D k τ) := by
  have h1 : HasInfExp D (c.μ ((k : ℕ) + 1)) τ (-(D.hc τ).e k) := hc.exp k τ
  have h2 : HasInfExp D c.η τ (1 / 2) := hc.chars.2.2.2.1 τ
  have h3 := GlobalTheory.Chain.StepVac.hasInfExp_mul h1 (GlobalTheory.Chain.StepVac.hasInfExp_inv h2)
  unfold Com.chS Com.chT Lift.chrStep expS expT
  by_cases hk : Even (k : ℕ)
  · rw [if_pos hk.add_one, if_pos hk, if_pos hk, sub_zero, sub_eq_add_neg]
    exact ⟨h3, h1⟩
  · rw [if_neg (by rwa [Nat.odd_add_one, Nat.not_odd_iff_even]), if_neg hk, if_neg hk, sub_zero, sub_eq_add_neg]
    exact ⟨h1, h3⟩

theorem stepExpVac : ∀ D : D7, GlobalTheory.ChainOnto.ForStep D fun c k s s' p => ∀ hk : k < D.R.m,
    IsWeilExp c.ψ s.V s'.V (expS D ⟨k, hk⟩) (expT D ⟨k, hk⟩) p.ω ∧ IsVacVec c.ψ c.θ s.M s'.M p.f := by
  intro D _ c hc k _ s s' hs hs' p hp hk
  refine ⟨⟨c.chS (k + 1), c.chT (k + 1), hp.weil, fun τ => chrStep_exp' hc ⟨k, hk⟩ τ⟩, ?_⟩
  obtain ⟨ξ, f₀, hv⟩ := hp.vec
  have hr : s.V.rank ≤ s'.V.rank := by
    rw [hs.rank, hs'.rank]
    show D.R.r + k * D.R.t ≤ D.R.r + (k + 1) * D.R.t
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ k)) _
  obtain ⟨a, b, d⟩ := GlobalTheory.Chain.StepVac.stepVec_vac hs.selfDual hs'.selfDual hr hv
  exact ⟨a, b, d⟩

end GlobalTheory.ChainOnto.StepExp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedLevelRelIndexEqProdParabolicIndices
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section

namespace GlobalTheory.TwistIndex

open Classical

theorem index_pi_univ {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] (H : ∀ i, Subgroup (G i)) :
    (Subgroup.pi Set.univ H).index = ∏ i, (H i).index := by
  simp_rw [Subgroup.index, ← Nat.card_pi]
  refine Nat.card_congr ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientGroup.leftRel_pi]

theorem restrictedBlock_self_apply {κ : Type} [CommRing κ] {n : ℕ} (g : GL (Fin n) κ) : Formalism.L2.DIV.upperLeftBlock (le_refl n) g = g := by
  have hg : g ∈ (Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 n) : Subgroup (GL (Fin n) κ)) := by
    show (g : Matrix (Fin n) (Fin n) κ).BlockTriangular _
    intro i j hij
    simp [Formalism.L2.DIV.blk2] at hij
  apply Units.ext
  rw [Formalism.L2.DIV.upper_block_val_submatrix _ hg]
  ext i j
  simp [Fin.castLE]

variable {D : D7}

theorem mem_datY_iff (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) {r t j : ℕ} (hr hr' : r ≤ V.rank) (Pg Q : Finset (Pl D.host.E))
    (χ χ' : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (x : GL (Fin V.rank) (Lev.EAf D)) :
    x ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Lev.datY V.rank r t j hr Pg Q (LevelP.triv _ _ _) χ ξ Lev.Frm.B) ↔
      x ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Lev.datY V.rank r t j hr' Pg ∅ (LevelP.triv _ _ _) χ' ξ' Lev.Frm.B) ∧
        ∀ PP ∈ Q, Formalism.L2.DIV.redFn β PP x ∈ (Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) : Subgroup (GL (Fin V.rank) (kP PP))) := by
  constructor
  · rintro ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
    refine ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, ?_⟩, h5⟩, fun PP hP => ?_⟩
    · exact Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => absurd hP (Finset.notMem_empty _)
    · exact (Formalism.L2.DIV.mem_parah.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h4 PP) hP)).2
  · rintro ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, -⟩, h5⟩, h6⟩
    refine ⟨⟨⟨⟨h1, h2⟩, h3⟩, ?_⟩, h5⟩
    exact Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => Formalism.L2.DIV.mem_parah.2 ⟨h2, h6 PP hP⟩

theorem relIndex_twist : ∀ (D : D7) (c : Com D) (w : Twist D) (j : ℕ) (s : PiLocalization₂ D), w.Is c → j ≤ D.R.m → IsStage c w j s → ∀ hr χ ξ, Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L ≤ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β (Lev.datY s.V.rank D.R.r D.R.t j hr w.Pg ∅ (LevelP.triv _ _ _) χ ξ Lev.Frm.B) ∧ (((Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L).relIndex (Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β (Lev.datY s.V.rank D.R.r D.R.t j hr w.Pg ∅ (LevelP.triv _ _ _) χ ξ Lev.Frm.B)) : ℕ) : ℝ) = ∏ PP ∈ w.Q, idxQ PP j := by
  intro D c w j s hw _ hs hr' χ ξ
  obtain ⟨hr, hL, hflat⟩ := hs
  rw [hL]
  have hmem := fun x => mem_datY_iff s.V s.β hr hr' w.Pg w.Q w.chi χ w.ξ ξ (r := D.R.r) (t := D.R.t) (j := j) x
  refine ⟨fun x hx => ((hmem x).1 hx).1, ?_⟩
  have hSt : Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β (Lev.datY s.V.rank D.R.r D.R.t j hr' w.Pg ∅ (LevelP.triv _ _ _) χ ξ Lev.Frm.B) ≤
      Formalism.L2.DIV.St s.β := fun x hx => Formalism.L2.DIV.parLev_St hx.1
  let φ : Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β (Lev.datY s.V.rank D.R.r D.R.t j hr' w.Pg ∅ (LevelP.triv _ _ _) χ ξ Lev.Frm.B) →*
      (∀ PP : w.Q, GL (Fin s.V.rank) (kP PP.1)) :=
    MonoidHom.pi fun PP => (Formalism.L2.DIV.redAt s.β PP.1).comp (Subgroup.inclusion hSt)
  have hφ : ∀ x PP, φ x PP = Formalism.L2.DIV.redFn s.β PP.1 x.1 := by
    intro x PP
    unfold Formalism.L2.DIV.redFn
    rw [Formalism.L2.DIV.extendOne_of_mem _ (hSt x.2)]
    rfl
  have hcomap : (Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β (Lev.datY s.V.rank D.R.r D.R.t j hr w.Pg w.Q (LevelP.triv _ _ _) w.chi w.ξ Lev.Frm.B)).subgroupOf
      (Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β (Lev.datY s.V.rank D.R.r D.R.t j hr' w.Pg ∅ (LevelP.triv _ _ _) χ ξ Lev.Frm.B)) =
      (Subgroup.pi Set.univ fun PP : w.Q =>
        (Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 D.R.r) : Subgroup (GL (Fin s.V.rank) (kP PP.1)))).comap φ := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_pi, hmem]
    simp only [hφ]
    constructor
    · rintro ⟨-, h⟩ PP -
      exact h PP.1 PP.2
    · intro h
      exact ⟨x.2, fun PP hP => h ⟨PP, hP⟩ (Set.mem_univ _)⟩
  have hsurj : Function.Surjective φ := by
    intro g
    obtain ⟨N, hN, -⟩ := hflat.base
    obtain ⟨e, he⟩ := hw.com.split
    have hnc := GlobalTheory.ChainOnto.FlagAct.not_isConjPl_of_idemSum he
    let L' : LevDat D.host.E ℂ s.V.rank := Lev.datW s.V.rank c.Pg (LevelP.triv c.Pg s.V.rank ℂ) Lev.Frm.B
    have hlift : Lev.LiftsExist s.V s.β L' :=
      GlobalTheory.ParahoricLift.liftsExist s.V s.β L' s.Λ N hN (fun PP hP PP' hP' => by
        rcases hP' with h | h
        · exact hnc PP hP PP' h
        · exact absurd h (Finset.notMem_empty _)) (Finset.disjoint_empty_right _)
    let g0 : Formalism.L2.DIV.G0 L'.Pg L'.r := fun PP => if h : PP.1 ∈ w.Q then g ⟨PP.1, h⟩ else 1
    have h0 := hlift g0
    have hκ := h0.choose_spec
    have hκ1 : Lev.finE s.V h0.choose ∈ Formalism.L2.DIV.parLev D.sp.cm s.V.gram s.β L' := hκ.2.1
    have hκ2 : Formalism.L2.DIV.rTup s.β L' (Lev.finE s.V h0.choose) = g0 := hκ.2.2
    have hred : ∀ PP (h : PP ∈ c.Pg), Formalism.L2.DIV.redFn s.β PP (Lev.finE s.V h0.choose) = g0 ⟨PP, h⟩ := by
      intro PP h
      exact (restrictedBlock_self_apply _).symm.trans (congrFun hκ2 ⟨PP, h⟩)
    have hPg : ∀ PP ∈ w.Pg, Formalism.L2.DIV.redFn s.β PP (Lev.finE s.V h0.choose) = 1 := by
      intro PP hP
      have hc : PP ∈ c.Pg := by rw [hw.union]; exact Finset.mem_union_left _ hP
      rw [hred PP hc]
      have hq : PP ∉ w.Q := Finset.disjoint_left.1 hw.disj hP
      show (if h : PP ∈ w.Q then g ⟨PP, h⟩ else (1 : GL (Fin s.V.rank) (kP PP))) = 1
      exact dif_neg hq
    have hSt' := Formalism.L2.DIV.parLev_St hκ1
    have hxbig : Lev.finE s.V h0.choose ∈
        Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β (Lev.datY s.V.rank D.R.r D.R.t j hr' w.Pg ∅ (LevelP.triv _ _ _) χ ξ Lev.Frm.B) := by
      refine ⟨⟨⟨⟨Formalism.L2.DIV.parLev_UA hκ1, hSt'⟩, ?_⟩, ?_⟩, ?_⟩
      · exact Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP =>
          Formalism.L2.DIV.mem_parah.2 ⟨hSt', by rw [hPg PP hP]; exact Subgroup.one_mem _⟩
      · exact Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => absurd hP (Finset.notMem_empty _)
      · show Formalism.L2.DIV.rTup s.β (Lev.datY s.V.rank D.R.r D.R.t j hr' w.Pg ∅ (LevelP.triv _ _ _) χ ξ Lev.Frm.B) (Lev.finE s.V h0.choose) ∈
          (⊥ : Subgroup (Formalism.L2.DIV.G0 w.Pg D.R.r))
        refine Subgroup.mem_bot.2 (funext fun PP => ?_)
        show Formalism.L2.DIV.upperLeftBlock hr' (Formalism.L2.DIV.redFn s.β PP.1 (Lev.finE s.V h0.choose)) = 1
        rw [hPg PP.1 PP.2]
        exact Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _
    refine ⟨⟨_, hxbig⟩, funext fun PP => ?_⟩
    rw [hφ]
    have hc : PP.1 ∈ c.Pg := by rw [hw.union]; exact Finset.mem_union_right _ PP.2
    rw [hred PP.1 hc]
    show (if h : PP.1 ∈ w.Q then g ⟨PP.1, h⟩ else 1) = g PP
    rw [dite_eq_left PP.2]
  have hn : s.V.rank = D.R.r + j * D.R.t := hflat.rank
  rw [Subgroup.relIndex, hcomap, Subgroup.index_comap_of_surjective _ hsurj, index_pi_univ, Nat.cast_prod]
  refine Eq.trans ?_ (Finset.prod_coe_sort w.Q (fun PP => idxQ PP j))
  refine Finset.prod_congr rfl fun PP _ => ?_
  refine (GlobalTheory.ParabIndex.index_maxParabolic_GL_finiteField (kP PP.1) s.V.rank D.R.r (j * D.R.t) hn).trans ?_
  have hq : Nat.card (kP PP.1) = Ideal.absNorm PP.1.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [hq, hn]
  rfl

end GlobalTheory.TwistIndex

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDataDifferBySplittingFactorQuotient
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker

namespace GlobalTheory.WeilChange

theorem weilData_differ_by_splitFac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT χS' χT' : (AE D)ˣ →* Circle) (om om' : Om S T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S T χS' χT' om' → ∀ g h x y, IsDetRoot S g x → IsDetRoot T h y → ∀ f, IsThetaFunO ψ S T f → om' (g, h) f = ((splitFacO χS' χT' x y : ℂ) * (splitFacO χS χT x y : ℂ)⁻¹) • om (g, h) f := by
  intro D ψ S T χS χT χS' χT' om om' H H' g h x y hx hy f hf
  have rS : ResEta D (χS⁻¹ * χS') 0 :=
    resEta_parity (resEta_mul (resEta_inv H.resS) H'.resS) (by omega)
  have rT : ResEta D (χT⁻¹ * χT') 0 :=
    resEta_parity (resEta_mul (resEta_inv H.resT) H'.resT) (by omega)
  obtain ⟨om₂, H₂, h₂⟩ := exists_weilDatum_twist D ψ H.std S T χS χT (χS⁻¹ * χS') (χT⁻¹ * χT') om H
    (hecke_mul (hecke_inv H.hecS) H'.hecS) (hecke_mul (hecke_inv H.hecT) H'.hecT) rS rT
  rw [mul_inv_cancel_left, mul_inv_cancel_left] at H₂
  rw [GlobalTheory.WeilUniq.weilDatum_unique D ψ H.std S T χS' χT' om' om₂ H' H₂ (g, h) f hf, h₂ g h x y hx hy, LinearMap.smul_apply]
  congr 1
  rw [← Circle.coe_inv, ← Circle.coe_mul]
  congr 1
  simp only [splitFacO, MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv, inv_inv]
  generalize (χT' x)⁻¹ = a, (χS y)⁻¹ = b, χS' y = c, χT x = d
  apply Circle.ext
  simp only [Circle.coe_mul]
  ring

end GlobalTheory.WeilChange
end

