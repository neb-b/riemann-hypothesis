module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryMassLatticeEqGenusMass
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0191
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntEasy
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntPull

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TotallyDefiniteMass
section
noncomputable section

namespace GlobalTheory.Proof.TotallyDefiniteMass

open NumberField IsDedekindDomain Formalism.UG Formalism.UG.CS Formalism.BasicNotions Formalism.L2.Herm
open scoped TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke

theorem mass_tMap {K V V' : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V']
    [IsScalarTower (𝓞 K) K V'] {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
    (e : V ≃ₗ[K] V') (he : ∀ x y, h' (e x) (e y) = h x y) (L : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.mass h L = Formalism.HermitianLatticesTheory.mass h' (Formalism.MainNotions.StandardLattice.tMap e L) := by
  by_cases hex : ∃ s', Formalism.ThetaLiftIndependence.IsClassReps h' (Formalism.MainNotions.StandardLattice.tMap e L) s'
  · refine Formalism.MainNotions.StandardLattice.mass_transport e he L hex fun s hs => ?_
    rw [Formalism.HermitianLatticesTheory.massBasic_mass_eq h' _ hex]
    apply Complex.ofReal_injective
    rw [Formalism.HermitianLatticesTheory.massBasic_sum_cast, Formalism.HermitianLatticesTheory.massBasic_sum_cast]
    exact Formalism.ThetaLiftIndependence.latLiftIndep K V' h' _ _ _ (fun _ _ _ => rfl) (fun _ _ _ => rfl) _ _ hex.choose_spec hs
  · have hex' : ¬ ∃ s, Formalism.ThetaLiftIndependence.IsClassReps h L s := fun ⟨s, hs⟩ => hex ⟨_, Formalism.MainNotions.StandardLattice.tMap_reps e he L s hs⟩
    unfold Formalism.HermitianLatticesTheory.mass
    rw [dite_eq_right hex, dite_eq_right hex']

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem isTotDef_gram (hc : CMData F E) (S : HSpace E) (h1 : S.SigOK) (h2 : S.IsPosDef) :
    IsTotDef hc.sig S.gram := by
  obtain ⟨hσ, hJ⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND F E hc
  refine ⟨hc.totReal, fun ι => ?_⟩
  letI : Algebra F ℂ := ((algebraMap ℝ ℂ).comp ι).toAlgebra
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let τ : E →ₐ[F] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine (Formalism.UG.Final.DefSig F E _ hc.sig S.gram ι (τ : E →+* ℂ) (RingHom.ext (hσ.2.2.2 (τ : E →+* ℂ)))
    (RingHom.ext fun a => τ.commutes a) (fun e he => (hc.fixed e).1 he)
    (Matrix.ext fun i j => (hJ S).1 i j) (hJ S).2.isUnit).2 (Or.inl ?_)
  have := h1 (τ : E →+* ℂ)
  rw [h2] at this
  simpa using this

private theorem span_eq_top_of_unimodular (S : HSpace E) (N : Submodule (𝓞 E) S.V)
    (hN : N.FG) (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT N) :
    Submodule.span E (N : Set S.V) = ⊤ := by
  classical
  by_contra hspan
  obtain ⟨φ, hφ₀, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hspan)
  obtain ⟨bs, hbs⟩ := Formalism.HermitianLatticesTheory.dualLattice_dualBasis S.hT S.nondeg S.frame
  let μ := ∑ j, star (φ (S.frame j)) • bs j
  have hμ : ∀ v, S.hT μ v = φ v := by
    have key : S.hT μ = φ := by
      apply S.frame.ext
      intro i
      dsimp only [μ]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, LinearMap.sum_apply]
      have hs : ∀ j, S.hT (star (φ (S.frame j)) • bs j) (S.frame i) =
          φ (S.frame j) * (if i = j then 1 else 0) := by
        intro j
        rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star]
        congr 1
        rw [← S.herm.eq (S.frame i) (bs j), hbs]
        split_ifs <;> simp
      simp only [hs, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    intro v
    rw [key]
  have hμ₀ : μ ≠ 0 := by
    intro h
    apply hφ₀
    ext y
    simpa [h] using (hμ y).symm
  have hline (a : E) : a • μ ∈ N := by
    rw [← hU]
    change a • μ ∈ Formalism.E.hdual S.hT N
    simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
    intro y hy
    have hy₀ := LinearMap.mem_ker.mp (hφ (Submodule.subset_span hy))
    simp [← S.herm.eq (a • μ) y, LinearMap.map_smulₛₗ, hμ, hy₀]
  obtain ⟨ψ, hψ, -⟩ := Submodule.exists_le_ker_of_notMem
    (show μ ∉ (⊥ : Submodule E S.V) by simpa using hμ₀)
  let f := ψ.restrictScalars (𝓞 E)
  have hmap (x : E) : x ∈ N.map f := by
    refine ⟨(x / ψ μ) • μ, hline _, ?_⟩
    change ψ ((x / ψ μ) • μ) = x
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hψ]
  obtain ⟨d, hd₀, hd⟩ := FractionalIdeal.isFractional_of_fg
    (S := nonZeroDivisors (𝓞 E)) (hN.map f)
  have hinj := IsFractionRing.injective (𝓞 E) E
  have hne {a : 𝓞 E} (ha : a ≠ 0) : algebraMap (𝓞 E) E a ≠ 0 :=
    fun h => ha (hinj (h.trans (map_zero _).symm))
  have hinteger (x : E) : IsLocalization.IsInteger (𝓞 E) x := by
    have hx := hd _ (hmap ((algebraMap (𝓞 E) E d)⁻¹ * x))
    rwa [Algebra.smul_def, ← mul_assoc, mul_inv_cancel₀ (hne (nonZeroDivisors.ne_zero hd₀)),
      one_mul] at hx
  apply RingOfIntegers.not_isField E
  refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, ?_⟩
  intro a ha
  obtain ⟨b, hb⟩ := hinteger ((algebraMap (𝓞 E) E a)⁻¹)
  refine ⟨b, hinj ?_⟩
  rw [map_mul, hb, map_one, mul_inv_cancel₀ (hne ha)]

theorem cosetSum (hc : CMData F E) (S : HSpace E) (h1 : S.SigOK) (h2 : S.IsPosDef)
    (N : Submodule (𝓞 E) S.V) (hN : Submodule.IsLattice E N)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT N) :
    CosetGroupMembership.CosetSum (UFin hc S) (CosetGroupMembership.stabHat hc S N) (Formalism.HermitianLatticesTheory.mass S.hT N) := by
  obtain ⟨hσ, hJ⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND F E hc
  have hd := isTotDef_gram hc S h1 h2
  have hτ : ∀ τ : E →+* ℂ, τ.comp (hc.sig : E →+* E) = (starRingEnd ℂ).comp τ :=
    fun τ => RingHom.ext (hσ.2.2.2 τ)
  have hH : IsHerm (hc.sig : E →+* E) S.gram := Matrix.ext fun i j => (hJ S).1 i j
  have hL : Submodule.IsLattice E (crdLat S N) := Formalism.MainNotions.StandardLattice.tMap_lattice (crd S) N hN
  have hspan : Submodule.span E (crdLat S N : Set (Fin S.rank → E)) = ⊤ := by
    rw [← LinearEquiv.range (crd S), ← Submodule.map_top, ← span_eq_top_of_unimodular S N hN.fg hU,
      Submodule.map_span]
    congr 1
  have hf : Module.Finite (𝓞 E) (crdLat S N) := Module.Finite.iff_fg.2 hL.fg
  have hs : ∀ e, (hc.sig : E →+* E) ((hc.sig : E →+* E) e) = e := fun e => star_star e
  have hm := GlobalTheory.Mass.classMass_lattice_eq_genus_mass hσ (hJ S) hd hs (crdLat S N) hf hspan
  have ht : Formalism.HermitianLatticesTheory.mass S.hT N =
      Formalism.HermitianLatticesTheory.mass (formJ (hc.sig : E →+* E) hs S.gram 1 :
        (Fin S.rank → E) →ₗ⋆[E] (Fin S.rank → E) →ₗ[E] E) (crdLat S N) := by
    refine mass_tMap (crd S) (fun x y => ?_) N
    rw [hT_crd hc]
    change Matrix.toLinearMapₛₗ₂' E (starRingEnd E) (RingHom.id E) ((1 : E) • S.gram) (crd S x) (crd S y) = _
    unfold hform
    rw [Matrix.toLinearMapₛₗ₂'_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [one_smul, smul_eq_mul, RingHom.id_apply]
    change star _ * _ = star _ * _ * _
    ring
  rw [CosetGroupMembership.stabHat_eq]
  refine ⟨Formalism.UG.Final.ClassSetFiniteL F E _ hc.sig S.gram hτ hH (hJ S).2.isUnit hd _ hf hspan,
    fun y => (CosetGroupEquiv.cosetGrpEquiv _ _ y).finite_iff.2
      (Formalism.UG.Final.AdelicStabFiniteL F E _ hc.sig S.gram hτ hH (hJ S).2.isUnit hd _ hf hspan y),
    fun ι _ y hy => ?_⟩
  simp only [CosetGroupEquiv.card_cosetGrp]
  exact (GlobalTheory.Mass.classMass_eq_sum_of_bijective y hy).symm.trans (hm.trans ht.symm)

theorem generalForm : CosetGroupMembership.GeneralForm :=
  fun _ _ _ _ _ _ _ _ hc S h1 h2 N hN hU => cosetSum hc S h1 h2 N hN hU

theorem massAsCosetSum : CosetGroupMembership.MassAsCosetSum :=
  ⟨generalForm, CosetGroupEquiv.column_of_general generalForm⟩

end GlobalTheory.Proof.TotallyDefiniteMass

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TotallyRealSelfAnnihilatorAdeleCharacter
section
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.SWQ.Annihilator

variable {F : Type} [Field F] [NumberField F]

private theorem ext_lemma {x y : AF F} (h1 : fstA F x = fstA F y) (h2 : sndA F x = sndA F y) :
    x = y :=
  Prod.ext h1 h2

private theorem mul_pairA_zero (x : AF F) (z : Ainf F) :
    x * pairA F z 0 = pairA F (fstA F x * z) 0 := by
  apply ext_lemma
  · rw [map_mul]
    rfl
  · rw [map_mul]
    show sndA F x * 0 = 0
    exact mul_zero _

private theorem mul_pairA_singleV (x : AF F) (v : HeightOneSpectrum (𝓞 F)) (t : Fv F v) :
    x * pairA F 0 (singleV F v t) = pairA F 0 (singleV F v (sndA F x v * t)) := by
  apply ext_lemma
  · rw [map_mul]
    show fstA F x * 0 = 0
    exact mul_zero _
  · rw [map_mul]
    show sndA F x * singleV F v t = singleV F v (sndA F x v * t)
    unfold singleV
    classical
    exact (RestrictedProduct.mul_single _ v t (sndA F x)).symm

theorem eq_zero_of_forall [IsTotallyReal F] {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) (x : AF F)
    (hx : ∀ y, ψ (x * y) = 1) : x = 0 := by
  obtain ⟨hloc, -, hinf⟩ := GlobalTheory.GaugeEx.CharLoc.char_local F ψ hψ
  apply ext_lemma
  ·
    have h0 : fstA F x = 0 := hinf _ fun y => by
      have h := hx (pairA F y 0)
      rw [mul_pairA_zero] at h
      exact h
    rw [h0, map_zero]
  ·
    have key : ∀ v, sndA F x v = 0 := by
      intro v
      by_contra hne
      obtain ⟨s, hs⟩ := hloc v
      apply hs
      have h := hx (pairA F 0 (singleV F v ((sndA F x v)⁻¹ * s)))
      rw [mul_pairA_singleV, mul_inv_cancel_left₀ hne] at h
      exact h
    rw [map_zero]
    exact DFunLike.ext _ _ fun v => (key v).trans rfl

theorem exists_eq_of_forall [IsTotallyReal F] {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) (x : AF F)
    (hx : ∀ ξ : F, ψ (x * algebraMap F (AF F) ξ) = 1) : ∃ ξ : F, x = algebraMap F (AF F) ξ := by
  by_cases htriv : ∀ y, ψ (x * y) = 1
  · exact ⟨0, by rw [map_zero]; exact eq_zero_of_forall hψ x htriv⟩
  · push_neg at htriv
    obtain ⟨hc, hn, -, -⟩ := id hψ

    have hχ : IsCharAF F (ψ.compAddMonoidHom (AddMonoidHom.mulLeft x)) := by
      unfold IsCharAF
      exact ⟨hc.comp (continuous_const.mul continuous_id), fun y => hn _, hx, htriv⟩
    obtain ⟨a, -, ha⟩ := GlobalTheory.AdeleCharTwist.exists_mul_eq F ψ _ hψ hχ
    refine ⟨a, sub_eq_zero.mp (eq_zero_of_forall hψ _ fun y => ?_)⟩
    have h1 : ψ (x * y) = ψ (algebraMap F (AF F) a * y) := ha y
    rw [sub_mul, sub_eq_add_neg, AddChar.map_add_eq_mul, h1, ← AddChar.map_add_eq_mul,
      add_neg_cancel, AddChar.map_zero_eq_one]

theorem self_annihilator : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → (∀ x : AF F, (∀ y, ψ (x * y) = 1) → x = 0) ∧ ∀ x : AF F, (∀ ξ : F, ψ (x * algebraMap F (AF F) ξ) = 1) → ∃ ξ : F, x = algebraMap F (AF F) ξ := by
  intro F _ _ hF ψ hψ
  haveI := hF
  exact ⟨fun x hx => eq_zero_of_forall hψ x hx, fun x hx => exists_eq_of_forall hψ x hx⟩

end GlobalTheory.SWQ.Annihilator
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryPairPullbackLatticesTranslates
section
noncomputable section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

namespace GlobalTheory.MomPull

variable {D : D7} {N N' : ℕ}

def tPullL (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) : VC D N N' →ₗ[ℂ] VC D N N' where
  toFun := Formalism.L2.KerInert.tPull D (tor0 D cc δ) γ γ'
  map_add' := Formalism.L2.KerInert.ie_tPull_add cc δ γ γ'
  map_smul' := Formalism.L2.KerInert.ie_tPull_smul cc δ γ γ'

theorem hf_tPull (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) (hγ : (letI := D.host.cmStar; γ * star γ) = 1)
    (hγ' : (letI := D.host.cmStar; γ' * star γ') = 1) (z w : VC D N N') :
    Hf D (tor0 D cc δ) (Formalism.L2.KerInert.tPull D (tor0 D cc δ) γ γ' z)
      (Formalism.L2.KerInert.tPull D (tor0 D cc δ) γ γ' w) = Hf D (tor0 D cc δ) z w := by
  letI := D.host.cmStar
  unfold Hf
  congr 1
  refine Finset.sum_congr rfl fun τ _ => ?_
  have h1 := Formalism.L2.KerInert.PullbackComparison.map_mul_star D (embT D τ) γ hγ
  have h2 := Formalism.L2.KerInert.PullbackComparison.map_mul_star D (embT D τ) γ' hγ'
  rw [Matrix.star_eq_conjTranspose] at h1 h2
  exact Formalism.L2.KerInert.PullbackComparison.sum_mul_star_conj (γ.map (embT D τ)) (γ'.map (embT D τ)) h1 h2
    (Matrix.of (z τ)) (Matrix.of (w τ))

end GlobalTheory.MomPull


open GlobalTheory.MomPull in
theorem GlobalTheory.MomPull.pull_unitary : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' : ℕ), letI := D.host.cmStar; ∀ (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E) (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), ∃ g : VC D N N' →L[ℂ] VC D N N', (∀ x ∈ La D (tor0 D cc δ) (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) M) (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) M'), g x ∈ La D (tor0 D cc δ) M M') ∧ ∀ (t : VC D N N') (G : VC D N N' → ℂ), U D (tor0 D cc δ) t (pull D (tor0 D cc δ) (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) G) = fun z => U D (tor0 D cc δ) (g t) G (g z) := by
  intro D cc δ N N'
  letI := D.host.cmStar
  intro γ γ' M M'
  have h1' : star (γ' : Matrix (Fin N') (Fin N') D.host.E) * γ' = 1 := Matrix.mem_unitaryGroup_iff'.mp γ'.2
  have hγ : (γ : Matrix (Fin N) (Fin N) D.host.E) * star (γ : Matrix (Fin N) (Fin N) D.host.E) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp γ.2
  have hγ' : (γ' : Matrix (Fin N') (Fin N') D.host.E) * star (γ' : Matrix (Fin N') (Fin N') D.host.E) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp γ'.2
  refine ⟨LinearMap.toContinuousLinearMap (tPullL cc δ (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E)), fun x hx => ?_, fun t G => ?_⟩
  · have h := Formalism.L2.KerInert.ie_La_pull cc δ _ _ h1' M M' hx
    exact h
  · funext z
    show G (Formalism.L2.KerInert.tPull D (tor0 D cc δ) (γ : Matrix (Fin N) (Fin N) D.host.E)
        (γ' : Matrix (Fin N') (Fin N') D.host.E) (z + t)) * _ =
      G (Formalism.L2.KerInert.tPull D (tor0 D cc δ) (γ : Matrix (Fin N) (Fin N) D.host.E)
        (γ' : Matrix (Fin N') (Fin N') D.host.E) z + Formalism.L2.KerInert.tPull D (tor0 D cc δ)
        (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) t) * _
    have e : ∀ y, (LinearMap.toContinuousLinearMap (tPullL cc δ (γ : Matrix (Fin N) (Fin N) D.host.E)
        (γ' : Matrix (Fin N') (Fin N') D.host.E))) y = Formalism.L2.KerInert.tPull D (tor0 D cc δ)
        (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) y := fun _ => rfl
    simp only [e]
    rw [hf_tPull cc δ _ _ hγ hγ', hf_tPull cc δ _ _ hγ hγ', Formalism.L2.KerInert.ie_tPull_add]
end
end

