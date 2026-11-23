module

public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0010
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0016
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0007
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0008
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.InfiniteNormOneField
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0012
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0017
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinMultiplicativity
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1458
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1402
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1413
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1464
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0015
public import Development.WeilBound.ThetaLifts.LeviDeterminants.Bundle0009
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0010

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ParsevalPolK
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace PositivityTheory.ThKW.AdelicSchwartzProperties
open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation GlobalTheory.ThetaTransform
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
open scoped Pointwise in
theorem parseval_pol_k {σ : E →ₐ[F] E} {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {nS nT : ℕ} (N : ℕ)
    (e : WOF F E nS (nT + nT) ≃ₗ[AF F] VA F N) (hec : Continuous e) (hes : Continuous e.symm)
    (hrat : ∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : Fin N → F,
        e (ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z))
    (hrat' : ∀ y z : Fin N → F, ∃ x : Matrix (Fin (nT + nT)) (Fin nS) E, e (ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z)) :
    ∃ (μN : Measure (Fin N → AF F)) (μW : Measure (WOF F E nS (nT + nT))) (𝓕W : Set (WOF F E nS (nT + nT))) (c : ℝ),
      μN.IsAddHaarMeasure ∧ μW.IsAddHaarMeasure ∧ IsAddFundamentalDomain (ratLF F E nS (nT + nT)) 𝓕W μW ∧ 0 < c ∧
      ∀ Φ₁ ∈ schA F (Fin N), ∀ Φ₂ ∈ schA F (Fin N),
        ∫ w in 𝓕W, thV B.ψ Φ₁ (e w) * starRingEnd ℂ (thV B.ψ Φ₂ (e w)) ∂μW =
          (c : ℂ) * ∫ x, Φ₁ x * starRingEnd ℂ (Φ₂ x) ∂μN := by
  obtain ⟨μW, 𝓕W, hμW, h𝓕W⟩ := GlobalTheory.TowerFD.exists_fd_any F E nS (nT + nT)
  obtain ⟨i1, i2, -, -, -, -⟩ := _root_.GlobalTheory.AdelicMatrixLatticeF.lattice F E nS (nT + nT)
  haveI := i1
  haveI := i2
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  have hb : (MeasurableSpace.pi : MeasurableSpace (Fin N → AF F)) = borel _ := BorelSpace.measurable_eq
  letI mP : MeasurableSpace (VA F N) := borel _
  haveI : BorelSpace (VA F N) := ⟨rfl⟩
  haveI : BorelSpace (WOF F E nS (nT + nT)) := ⟨rfl⟩
  let ca : WOF F E nS (nT + nT) ≃ₜ+ VA F N :=
    { e.toAddEquiv with continuous_toFun := hec, continuous_invFun := hes }
  let me : WOF F E nS (nT + nT) ≃ᵐ VA F N := ca.toHomeomorph.toMeasurableEquiv
  have hme : ∀ w, me w = e w := fun _ => rfl
  have into : ∀ g ∈ ratLF F E nS (nT + nT), e g ∈ GlobalTheory.WeilUnitaryTransport.ratPair F (Fin N) := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, z, h⟩ := hrat x
    exact (GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff _).2 ⟨y, z, h⟩
  have onto' : ∀ p ∈ GlobalTheory.WeilUnitaryTransport.ratPair F (Fin N), e.symm p ∈ ratLF F E nS (nT + nT) := by
    intro p hp
    obtain ⟨y, z, rfl⟩ := (GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff _).1 hp
    obtain ⟨x, hx⟩ := hrat' y z
    have : e.symm (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z) = ratWF x := by rw [← hx]; exact e.symm_apply_apply _
    rw [show ((fun i => algebraMap F (AF F) (y i)), fun i => algebraMap F (AF F) (z i)) =
      (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z) from rfl, this]
    exact ⟨x, rfl⟩
  have hν : (μW.map me).IsAddHaarMeasure := ca.isAddHaarMeasure_map μW
  have h𝓕 : IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair F (Fin N)) (me '' 𝓕W) (μW.map me) := by
    refine ⟨?_, ?_, ?_⟩
    · have hqmp : Measure.QuasiMeasurePreserving me.symm (μW.map me) μW :=
        (MeasurePreserving.mk me.symm.measurable (MeasurableEquiv.map_symm_map me)).quasiMeasurePreserving
      have hpre : me '' 𝓕W = me.symm ⁻¹' 𝓕W :=
        Set.ext fun y => ⟨by rintro ⟨w, hw, rfl⟩; simpa using hw, fun hy => ⟨me.symm y, hy, me.apply_symm_apply y⟩⟩
      rw [hpre]
      exact h𝓕W.nullMeasurableSet.preimage hqmp
    · rw [me.measurableEmbedding.ae_map_iff]
      filter_upwards [h𝓕W.ae_covers] with x ⟨g, hg⟩
      refine ⟨⟨e g, into g g.2⟩, g +ᵥ x, hg, ?_⟩
      show e ((g : WOF F E nS (nT + nT)) + x) = e g + e x
      rw [map_add (f := _)]
    · intro p q hpq
      let g : ratLF F E nS (nT + nT) := ⟨e.symm p, onto' p p.2⟩
      let h : ratLF F E nS (nT + nT) := ⟨e.symm q, onto' q q.2⟩
      have hgh : g ≠ h := by
        intro eq
        apply hpq
        apply Subtype.ext
        have := congrArg (fun t : ratLF F E nS (nT + nT) => e (t : WOF F E nS (nT + nT))) eq
        simpa [g, h] using this
      have himg : ∀ (r : GlobalTheory.WeilUnitaryTransport.ratPair F (Fin N)) (k : ratLF F E nS (nT + nT)),
          (k : WOF F E nS (nT + nT)) = e.symm r → r +ᵥ me '' 𝓕W = me '' (k +ᵥ 𝓕W) := by
        intro r k hk
        rw [← Set.image_vadd, ← Set.image_vadd, Set.image_image, Set.image_image]
        refine Set.image_congr fun w _ => ?_
        show (r : VA F N) + e w = e ((k : WOF F E nS (nT + nT)) + w)
        rw [map_add (f := _), hk, LinearEquiv.apply_symm_apply]
      show MeasureTheory.AEDisjoint (μW.map me) (p +ᵥ me '' 𝓕W) (q +ᵥ me '' 𝓕W)
      rw [himg p g rfl, himg q h rfl, MeasureTheory.AEDisjoint, ← Set.image_inter me.injective, me.map_apply,
        me.preimage_image]
      exact h𝓕W.aedisjoint hgh
  have key : ∀ m : MeasurableSpace (Fin N → AF F), m = borel _ →
      ∃ (μ : @Measure _ m) (c : ℝ), @Measure.IsAddHaarMeasure _ _ _ m μ ∧ 0 < c ∧
        ∀ Φ₁ ∈ schA F (Fin N), ∀ Φ₂ ∈ schA F (Fin N),
          ∫ w in me '' 𝓕W, thV B.ψ Φ₁ w * starRingEnd ℂ (thV B.ψ Φ₂ w) ∂(μW.map me) =
            (c : ℂ) * ∫ x, Φ₁ x * starRingEnd ℂ (Φ₂ x) ∂μ := by
    rintro m rfl
    exact _root_.PositivityTheory.ThKW.ParsevalPolarization.parseval_rational_pairing hB N (μW.map me) hν (me '' 𝓕W) h𝓕
  obtain ⟨μN, c, hμN, hc, hK⟩ := key _ hb
  refine ⟨μN, μW, 𝓕W, c, hμN, hμW, h𝓕W, hc, fun Φ₁ hΦ₁ Φ₂ hΦ₂ => ?_⟩
  rw [← hK Φ₁ hΦ₁ Φ₂ hΦ₂, MeasurableEquiv.restrict_map, MeasurableEquiv.preimage_image, integral_map_equiv]
  rfl
end PositivityTheory.ThKW.AdelicSchwartzProperties
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RedWpAutGen
section
section
noncomputable section
open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
namespace PositivityTheory.ThKW
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
  {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ}
  {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)}
  {s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ}
theorem infinite_norm_one_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) : {t : E | t * σ t = 1}.Infinite :=
  _root_.UpperTheory.Reformulated.B.InfiniteNormOneField.infinite_norm_one_k C
theorem det_kron_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) {g : GAF σ JS} {h : GAF σ JT} {a b}
    (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b) :
    (b ⊗ₖ aᵀ).det * σ (b ⊗ₖ aᵀ).det = 1 ∧
      (b ⊗ₖ aᵀ).det * σ (b ⊗ₖ aᵀ - 1).det = (-1) ^ Fintype.card (Fin nT × Fin nS) * (b ⊗ₖ aᵀ - 1).det := by
  have hu : IsUnit JS.det := isUnit_iff_ne_zero.2 C.hS.2
  have hP : (JT ⊗ₖ JS⁻¹ᵀ).det ≠ 0 := by
    rw [det_kronecker, det_transpose]
    exact mul_ne_zero (pow_ne_zero _ C.hT.2) (pow_ne_zero _ (Matrix.isUnit_nonsing_inv_det JS hu).ne_zero)
  have hunitary {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {g : GAF σ J} {a}
      (h : IsRatF σ J g a) : (a.map σ)ᵀ * J * a = J := by
    have e := GenA.mt_unitary σ J g
    rw [show mtF σ J g = _ from h, GenA.map_unitary] at e
    exact Matrix.map_injective GenA.incAF_injective e
  exact GenA.det_unit_sig σ hP (GenA.kron_unit_sig σ hu (hunitary ha) (hunitary hb))
namespace GenR
theorem compAt_rat_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {g : GAF σ J} {a}
    (h : IsRatF σ J g a) (w : InfinitePlace F) : compAtF θ w (mtF σ J g) = a.map (tauB B w) := by
  rw [show mtF σ J g = _ from h]
  ext i j
  show θ w (infPartF F E (incAF F E (a i j))) = tauB B w (a i j)
  rw [GenA.infPart_incAF]
  exact (C.inf w).1 (a i j)
theorem cart_blk_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) {sS : InfinitePlace F → Matrix (Fin nS) (Fin nS) ℂ}
    {sT : InfinitePlace F → Matrix (Fin nT) (Fin nT) ℂ}
    (hS : ∀ w, Formalism.IndefR.Datum.IsCartanInv (JS.map (tauB B w)) (sS w))
    (hT : ∀ w, Formalism.IndefR.Datum.IsCartanInv (((2 * (tauB B w ξ₀).im : ℝ) : ℂ) • JT.map (tauB B w)) (sT w)) :
    CartF σ JS JT ξ₀ B θ (GlobalTheory.RealWeil.blk sT sS) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [GlobalTheory.RealWeil.blk_mul]
    simp only [fun w => (hS w).1, fun w => (hT w).1]
    exact GlobalTheory.RealWeil.blk_one
  · unfold HMF
    rw [GlobalTheory.RealWeil.blk_mul]
    refine GlobalTheory.RealWeil.blk_posDef (fun w => (hT w).2.2) fun w => ?_
    rw [← GlobalTheory.RealSymplForm.cartan_inv_mul (hS w)]
    exact (hS w).2.2.inv
  · intro k t hk
    rw [mMF_apply]
    refine GenA.blk_comm (fun w => ?_) (fun w => ?_)
    · rw [_root_.PositivityTheory.ThKW.GenR.compAt_rat_k C hk]
      have e : (t • (1 : Matrix (Fin nT) (Fin nT) E)).map (tauB B w) = tauB B w t • 1 := by
        ext i j
        by_cases hij : i = j <;> simp [hij]
      rw [e, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
    · have hone : compAtF θ w (mtF σ JS 1) = 1 := by
        rw [GenA.mt_one, compAtF, Matrix.map_one _ (map_zero _) (map_one _)]
      rw [inv_one, hone, Matrix.one_mul, Matrix.mul_one]
end GenR
theorem rat_gen_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (Q : GAF σ JS × GAF σ JT → Prop)
    (hm : ∀ p q, p.1 ∈ GQF σ JS → p.2 ∈ GQF σ JT → q.1 ∈ GQF σ JS → q.2 ∈ GQF σ JT → Q p → Q q → Q (p * q))
    (hs : ∀ p s, p.1 ∈ GQF σ JS → p.2 ∈ GQF σ JT → CartF σ JS JT ξ₀ B θ s →
      s * mMF σ JS JT θ p = mMF σ JS JT θ p * s → Q p) :
    ∀ p, p.1 ∈ GQF σ JS → p.2 ∈ GQF σ JT → Q p := by
  have hcm := C.good.cm
  have hσ := GlobalTheory.SplitDetCharF.sig_invol hcm
  obtain ⟨c, hc⟩ : ∃ c : E ≃ₐ[F] E, (c : E →ₐ[F] E) = σ :=
    ⟨AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσ) (AlgHom.ext hσ), rfl⟩
  subst hc
  have hmem {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {g : GAF (c : E →ₐ[F] E) J} {a}
      (hJ : IsHermND (c : E →ₐ[F] E) J) (h : IsRatF (c : E →ₐ[F] E) J g a) :
      g ∈ GQF (c : E →ₐ[F] E) J := by
    have e := GenA.mt_unitary (c : E →ₐ[F] E) J g
    rw [show mtF (c : E →ₐ[F] E) J g = _ from h, GenA.map_unitary] at e
    have hu : (a.map (c : E →ₐ[F] E))ᵀ * J * a = J :=
      Matrix.map_injective GenA.incAF_injective e
    exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero a (GenA.det_ne_of_unitary hJ hu), hu, Units.ext h.symm⟩
  have hone {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (w : InfinitePlace F) :
      compAtF θ w (mtF (c : E →ₐ[F] E) J 1) = 1 := by
    rw [GenA.mt_one, compAtF, Matrix.map_one _ (map_zero _) (map_one _)]
  have hr : ∀ w, (2 * (tauB B w ξ₀).im : ℝ) ≠ 0 := fun w => mul_ne_zero two_ne_zero (GenA.im_ne hcm C.h0 C.hξ _)
  have hcS : ∀ w, ∃ s, Formalism.IndefR.Datum.IsCartanInv (JS.map (tauB B w)) s := fun w => by
    simpa using GenA.cart_exists _ (GenA.herm_map hcm C.hS (tauB B w)) (GenA.det_map_ne C.hS (tauB B w)) 1 one_ne_zero
  have hcT : ∀ w, ∃ s, Formalism.IndefR.Datum.IsCartanInv (((2 * (tauB B w ξ₀).im : ℝ) : ℂ) • JT.map (tauB B w)) s :=
    fun w => GenA.cart_exists _ (GenA.herm_map hcm C.hT (tauB B w)) (GenA.det_map_ne C.hT (tauB B w)) _ (hr w)
  choose sS0 hS0 using hcS
  choose sT0 hT0 using hcT
  have Q11 : Q (1, 1) := hs (1, 1) (GlobalTheory.RealWeil.blk sT0 sS0) (one_mem _) (one_mem _) (_root_.PositivityTheory.ThKW.GenR.cart_blk_k C hS0 hT0)
    (by
      show _ * mMF _ JS JT θ 1 = mMF _ JS JT θ 1 * _
      rw [map_one, Matrix.mul_one, Matrix.one_mul])
  have hT : ∀ h ∈ GQF (c : E →ₐ[F] E) JT, Q (1, h) := by
    refine GenR.rat_ind c hcm C.hT (fun h => Q (1, h)) Q11 (fun g hg g' hg' a b => ?_) (fun g x u hx hg => ?_)
    · have := hm (1, g) (1, g') (one_mem _) hg (one_mem _) hg' a b
      rwa [Prod.mk_mul_mk, mul_one] at this
    · have := fun w => GenA.cart_refl (JT.map (tauB B w)) (GenA.herm_map hcm C.hT (tauB B w))
        (GenA.det_map_ne C.hT (tauB B w)) _ (hr w) (tauB B w ∘ x)
        (by rw [GenA.quad_map hcm c rfl]; exact (map_ne_zero _).2 hx) (tauB B w ((u - 1) / GlobalTheory.UnRep.hermE c JTᵀ x x))
      choose sT hT1 hT2 using this
      refine hs (1, g) (GlobalTheory.RealWeil.blk sT sS0) (one_mem _) (hmem C.hT hg) (_root_.PositivityTheory.ThKW.GenR.cart_blk_k C hS0 hT1) ?_
      rw [mMF_apply]
      refine GenA.blk_comm (fun w => ?_) (fun w => ?_)
      · rw [_root_.PositivityTheory.ThKW.GenR.compAt_rat_k C hg, GenA.refl_map hcm c rfl]
        exact hT2 w
      · rw [inv_one, hone, Matrix.one_mul, Matrix.mul_one]
  have hS : ∀ g ∈ GQF (c : E →ₐ[F] E) JS, Q (g⁻¹, 1) := by
    refine GenR.rat_ind c hcm C.hS (fun g => Q (g⁻¹, 1)) (by rw [inv_one]; exact Q11) (fun g hg g' hg' a b => ?_)
      (fun g x u hx hg => ?_)
    · have := hm (g'⁻¹, 1) (g⁻¹, 1) (inv_mem hg') (one_mem _) (inv_mem hg) (one_mem _) b a
      rwa [Prod.mk_mul_mk, mul_one, ← _root_.mul_inv_rev] at this
    · have := fun w => GenA.cart_refl (JS.map (tauB B w)) (GenA.herm_map hcm C.hS (tauB B w))
        (GenA.det_map_ne C.hS (tauB B w)) 1 one_ne_zero (tauB B w ∘ x)
        (by rw [GenA.quad_map hcm c rfl]; exact (map_ne_zero _).2 hx) (tauB B w ((u - 1) / GlobalTheory.UnRep.hermE c JSᵀ x x))
      choose sS hS1 hS2 using this
      have hS1' : ∀ w, Formalism.IndefR.Datum.IsCartanInv (JS.map (tauB B w)) (sS w) := fun w => by simpa using hS1 w
      refine hs (g⁻¹, 1) (GlobalTheory.RealWeil.blk sT0 sS) (inv_mem (hmem C.hS hg)) (one_mem _) (_root_.PositivityTheory.ThKW.GenR.cart_blk_k C hS1' hT0) ?_
      rw [mMF_apply, inv_inv]
      refine GenA.blk_comm (fun w => ?_) (fun w => ?_)
      · rw [hone, Matrix.one_mul, Matrix.mul_one]
      · rw [_root_.PositivityTheory.ThKW.GenR.compAt_rat_k C hg, GenA.refl_map hcm c rfl]
        exact (hS2 w).symm
  intro p h1 h2
  have e : p = (p.1, 1) * (1, p.2) := by
    rw [Prod.mk_mul_mk, mul_one, one_mul]
  have a1 : Q (p.1, 1) := by
    have := hS _ (inv_mem h1)
    rwa [inv_inv] at this
  rw [e]
  exact hm _ _ h1 (one_mem _) (one_mem _) h2 a1 (hT _ h2)
end PositivityTheory.ThKW
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RedWpAutProdA
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
namespace PositivityTheory.ThKW
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
  {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ}
  {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)}
variable {η : (AEF F E)ˣ →* Circle} {ε : AEF F E} {of oi : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ)}
theorem cut_char_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J)
    {χ : (AEF F E)ˣ →* Circle} {m : ℕ} (hres : ResEtaF χ m) (hε : IsHalfF σ ε) {e : AEF F E} (he : IsSplitIdemF σ e)
    {g : GAF σ J} {x : (AEF F E)ˣ} (hg : SuppAtF σ e J g) (hx : IsDetAtF σ e J g x) :
    χ (GlobalTheory.SplitDetCharF.cutDet σ J ε hε.idem g) = χ x := by
  rcases hε.split e he with ⟨a1, a2⟩ | ⟨a1, a2⟩
  · rw [GlobalTheory.SplitDetCharF.cutDet_same ε hε.idem a1 a2 hg hx]
  · exact GlobalTheory.SplitDetCharF.char_eq_of_mul_conj hB.cm hres _ x
      (GlobalTheory.SplitDetCharF.cutDet_conj hJ ε hε.idem he.1 a1 a2 hg hx)
theorem fin_inf_comm_A_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (hO : _root_.UpperTheory.TP.W.IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om)
    (hof : ∀ p, ∃ z : ℂ, ∀ f : thetaSubF σ JS JT ξ₀ B.ψ, of p f = z • (Om p f : WOF F E nS nT → ℂ))
    (hi : IsInfWeilF σ JS JT ξ₀ B.ψ oi) (p q : GAF σ JS × GAF σ JT) (f : WOF F E nS nT → ℂ)
    (hf : IsThetaFunOF σ JS JT ξ₀ B.ψ f) : of p (oi q f) = oi q (of p f) := by
  obtain ⟨z, hz⟩ := hof p
  have hσ : ∀ x, σ (σ x) = x := _root_.PositivityTheory.ThKW.LatA.sig_sig_k C.good
  obtain ⟨a, ha, k, hk, e1, -⟩ := _root_.GlobalTheory.WeilPartsF.exists_real_finite_mul F E σ nS JS q.1
  obtain ⟨b, hb, l, hl, e2, -⟩ := _root_.GlobalTheory.WeilPartsF.exists_real_finite_mul F E σ nT JT q.2
  have hoi : ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → oi q f = oi (a, b) f := fun f h => by
    rw [show q = (a, b) * (k, l) from Prod.ext e1 e2, map_mul, Module.End.mul_apply, hi.triv k hk l hl f h]
  let L : thetaSubF σ JS JT ξ₀ B.ψ →ₗ[ℂ] thetaSubF σ JS JT ξ₀ B.ψ := (oi q).restrict fun f hf => hi.pres q f hf
  have hL : ∀ m, (L m : WOF F E nS nT → ℂ) = oi q m := fun _ => rfl
  have := congrArg Subtype.val ((_root_.PositivityTheory.ThKW.LatA.rep_k hO).comm (_root_.PositivityTheory.ThKW.LatA.sys_k hσ C.hS C.hT C.hξ hO) L (fun x v => Subtype.ext (by
    have e3 : actOF σ JS JT a b x = x := by
      have := congrArg (fun y : XFF F E nS nT => (y : WOF F E nS nT)) (LatA.rhoFF_real ha hb x)
      rwa [coe_rhoFF] at this
    rw [hL, coe_opFF, coe_opFF, hL, map_smul, hoi _ (hc _ _ v.2), hi.Heisenberg₂ a ha b hb _ _ v.2, e3, ← hoi _ v.2])) p ⟨f, hf⟩)
  rw [hz ⟨f, hf⟩, map_smul, ← hL, ← this]
  exact hz (L ⟨f, hf⟩)
theorem eventually_smul_A_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (hO : _root_.UpperTheory.TP.W.IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om)
    (hof : ∀ p, ∃ z : ℂ, ∀ f : thetaSubF σ JS JT ξ₀ B.ψ, of p f = z • (Om p f : WOF F E nS nT → ℂ))
    {f : WOF F E nS nT → ℂ} (h1 : IsThetaFunOF σ JS JT ξ₀ B.ψ f) :
    ∀ᶠ p in 𝓝 (1 : GAF σ JS × GAF σ JT), ∃ c : ℂ, of p f = c • f := by
  filter_upwards [_root_.PositivityTheory.ThKW.LatA.eventually_fix_k (_root_.PositivityTheory.ThKW.LatA.sig_sig_k C.good) C.hS C.hT C.hξ hO ⟨f, h1⟩] with p hp
  obtain ⟨c, hc'⟩ := hof p
  exact ⟨c, by rw [hc' ⟨f, h1⟩, hp]⟩
theorem continuous_product_A_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (hO : _root_.UpperTheory.TP.W.IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om)
    (hf : IsFinWeilF σ JS JT ξ₀ B.ψ (η ^ nS) (η ^ nT) of)
    (hof : ∀ p, ∃ z : ℂ, ∀ f : thetaSubF σ JS JT ξ₀ B.ψ, of p f = z • (Om p f : WOF F E nS nT → ℂ))
    (hi : IsInfWeilF σ JS JT ξ₀ B.ψ oi) {f : WOF F E nS nT → ℂ} (h1 : IsThetaFunOF σ JS JT ξ₀ B.ψ f)
    (u : WOF F E nS nT) : Continuous fun p : GAF σ JS × GAF σ JT => of p (oi p f) u := by
  haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  haveI : IsTopologicalGroup (GAF σ JS) := inferInstanceAs (IsTopologicalGroup (HR (AF F) σ JS))
  haveI : IsTopologicalGroup (GAF σ JT) := inferInstanceAs (IsTopologicalGroup (HR (AF F) σ JT))
  refine continuous_iff_continuousAt.2 fun q => ?_
  have h2 : Filter.Tendsto (fun p => p * q⁻¹) (𝓝 q) (𝓝 1) :=
    (continuous_id.mul continuous_const).tendsto' q 1 (mul_inv_cancel q)
  have h3 := hf.pres q f h1
  have h4 : ∀ᶠ p in 𝓝 q, ∃ c : ℂ, of p f = c • of q f := by
    filter_upwards [h2.eventually (_root_.PositivityTheory.ThKW.eventually_smul_A_k C hO hof h3)] with p hp
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right] at hp
  by_cases h0 : of q f = 0
  · refine continuousAt_const.congr (f := fun _ => (0 : ℂ)) ?_
    filter_upwards [h4] with p hp
    obtain ⟨c, hc'⟩ := hp
    rw [_root_.PositivityTheory.ThKW.fin_inf_comm_A_k C hO hof hi p p f h1, hc', h0, smul_zero, map_zero]
    rfl
  · obtain ⟨x, hx⟩ := Function.ne_iff.1 h0
    have hx' : of q f x ≠ 0 := hx
    refine (((hf.cont f h1 x).div_const (of q f x)).mul (hi.cont _ h3 u)).continuousAt.congr ?_
    filter_upwards [h4] with p hp
    obtain ⟨c, hc'⟩ := hp
    show of p f x / of q f x * oi p (of q f) u = _
    rw [_root_.PositivityTheory.ThKW.fin_inf_comm_A_k C hO hof hi p p f h1, hc', map_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      mul_div_cancel_right₀ _ hx']
theorem datum_of_aut_A_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) (hO : _root_.UpperTheory.TP.W.IsLatRepL σ JS JT ξ₀ B.ψ hc Λ w lam Om)
    (hη : IsHeckeCharF η) (hres : ResEtaF η 1) (hf : IsFinWeilF σ JS JT ξ₀ B.ψ (η ^ nS) (η ^ nT) of)
    (hof : ∀ p, ∃ z : ℂ, ∀ f : thetaSubF σ JS JT ξ₀ B.ψ, of p f = z • (Om p f : WOF F E nS nT → ℂ))
    (hi : IsInfWeilF σ JS JT ξ₀ B.ψ oi)
    (haut : ∀ γ ∈ GQF σ JS, ∀ γ' ∈ GQF σ JT, ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → of (γ, γ') (oi (γ, γ') f) 0 = f 0) :
    ∃ ω, IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ (η ^ nS) (η ^ nT) ω := by
  have hB := C.good
  have hψ := _root_.GlobalTheory.T.standard_additive_character_sign F E σ B hB
  have hcomm : ∀ p q f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → of p (oi q f) = oi q (of p f) :=
    fun p q f h => _root_.PositivityTheory.ThKW.fin_inf_comm_A_k C hO hof hi p q f h
  have hth : ∀ (w₀ : WOF F E nS nT) f, IsThetaFunOF σ JS JT ξ₀ B.ψ f →
      IsThetaFunOF σ JS JT ξ₀ B.ψ (heisOF σ JS JT ξ₀ B.ψ w₀ f) :=
    fun w₀ f h => _root_.GlobalTheory.HeisKeepF.isThetaFunOF_heisOF F E σ nS nT JS JT ξ₀ B.ψ hB.std.1 w₀ f h
  let Th := thetaSubF σ JS JT ξ₀ B.ψ
  let Om2 : GAF σ JS × GAF σ JT →* Module.End ℂ Th :=
    { toFun := fun p => (of p * oi p).restrict (p := Th) (q := Th) fun f h1 => hf.pres p _ (hi.pres p f h1)
      map_one' := LinearMap.ext fun f => Subtype.ext (by
        show of 1 (oi 1 f) = f
        simp only [map_one, Module.End.one_apply])
      map_mul' := fun p q => LinearMap.ext fun f => Subtype.ext (by
        show of (p * q) (oi (p * q) f) = of p (oi p (of q (oi q (f : WOF F E nS nT → ℂ))))
        simp only [map_mul, Module.End.mul_apply]
        rw [hcomm q p _ (hi.pres q _ f.2)]) }
  obtain ⟨om, hom⟩ := exists_extend Th Om2
  have ho : ∀ p f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → om p f = of p (oi p f) := fun p f h1 => hom p ⟨f, h1⟩
  have hp : ∀ p f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → IsThetaFunOF σ JS JT ξ₀ B.ψ (om p f) := fun p f h1 => by
    rw [ho p f h1]
    exact hf.pres p _ (hi.pres p f h1)
  refine ⟨om, hψ, isHeckeCharF_pow hη _, isHeckeCharF_pow hη _, resEtaF_pow hres _, resEtaF_pow hres _, hp,
    fun g h w₀ f h1 => ?_, fun γ hγ γ' hγ' f h1 => ?_, fun f h1 w => ?_, fun μ 𝓕 hμ h𝓕 p f h1 => ?_,
    fun e he g h hg hh x y hx hy => ?_⟩
  · obtain ⟨a, ha, k, hk, e1, e1'⟩ := _root_.GlobalTheory.WeilPartsF.exists_real_finite_mul F E σ nS JS g
    obtain ⟨b, hb, l, hl, e2, e2'⟩ := _root_.GlobalTheory.WeilPartsF.exists_real_finite_mul F E σ nT JT h
    have key : ∀ x, IsThetaFunOF σ JS JT ξ₀ B.ψ x → om (g, h) x = of (k, l) (oi (a, b) x) := fun x hx => by
      rw [ho _ x hx]
      have E1 : ((g, h) : GAF σ JS × GAF σ JT) = (a, b) * (k, l) := Prod.ext e1 e2
      have E2 : ((g, h) : GAF σ JS × GAF σ JT) = (k, l) * (a, b) := Prod.ext e1' e2'
      have E3 : oi (g, h) x = oi (a, b) x := by rw [E1, map_mul, Module.End.mul_apply, hi.triv k hk l hl x hx]
      rw [E3, E2, map_mul, Module.End.mul_apply, hf.triv a ha b hb _ (hi.pres _ x hx)]
    rw [key _ (hth w₀ f h1), key f h1, hi.Heisenberg₂ a ha b hb w₀ f h1, hf.Heisenberg₂ k hk l hl _ _ (hi.pres _ f h1),
      ← actOF_mul, ← e1', ← e2']
  · rw [ho _ f h1]
    exact haut γ hγ γ' hγ' f h1
  · have e : (fun p => om p f w) = fun p => of p (oi p f) w := funext fun p => by rw [ho p f h1]
    rw [e]
    exact _root_.PositivityTheory.ThKW.continuous_product_A_k C hO hf hof hi h1 w
  · rw [ho p f h1, hf.unit μ 𝓕 hμ h𝓕 p _ (hi.pres p f h1), hi.unit μ 𝓕 hμ h𝓕 p f h1]
  · obtain ⟨r, hr, h2⟩ := hf.split e he g h hg hh x y hx hy
    refine ⟨r, hr, fun ℓ hℓ f h1 => ?_⟩
    rw [ho _ f h1, hi.triv g (mem_GfCF_of_suppAt he hg) h (mem_GfCF_of_suppAt he hh) f h1]
    exact h2 ℓ hℓ f h1
end PositivityTheory.ThKW
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelMultiplicityOfLaws
section
set_option synthInstance.maxHeartbeats 200000

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_multiplicity_of_laws : PositivityTheory.RgEis.SecLaw → PositivityTheory.RgEis.WallLaw → PositivityTheory.RgEis.Dict → PositivityTheory.RgEis.DictInf → PositivityTheory.RgEis.CMGood → PositivityTheory.RgEis.GrpTop → PositivityTheory.RgEis.BdetLaw → PositivityTheory.RgEis.ExtLaw → PositivityTheory.RgEis.ParLaw → PositivityTheory.RgEis.SgAll → _root_.SiegelEisensteinSeries.BRoad.SiegelMult_k := by
  first | exact @_root_.GlobalTheory.CompanionTheory.SiegelFrame.siegelMult_of_k | exact _root_.GlobalTheory.CompanionTheory.SiegelFrame.siegelMult_of_k | (intros; apply _root_.GlobalTheory.CompanionTheory.SiegelFrame.siegelMult_of_k <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaDoublingInnerProduct
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_doubling_inner_product : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (w : Formalism.IndefR.DatumF.WOF F E nS (nT + nT)) (f₁ f₂ : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ w (GlobalTheory.DblTargetDelta.deltaT f₁ f₂) =
          GlobalTheory.DblTargetDelta.deltaT (Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (GlobalTheory.DblTargetDelta.topR w) f₁)
            (Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (-GlobalTheory.DblTargetDelta.botR w) f₂) := by
  first | exact @_root_.GlobalTheory.DblHeis.heisOF_dblG_deltaT_k | exact _root_.GlobalTheory.DblHeis.heisOF_dblG_deltaT_k | (intros; apply _root_.GlobalTheory.DblHeis.heisOF_dblG_deltaT_k <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaInnerProductFormula
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_inner_product_formula : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ f₁ f₂ : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ,
        Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₁ → Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₂ →
        Formalism.IndefR.DatumF.IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ (GlobalTheory.DblTargetDelta.deltaT f₁ f₂) := by
  first | exact @_root_.GlobalTheory.DblTargetThetaF.main_k | exact _root_.GlobalTheory.DblTargetThetaF.main_k | (intros; apply _root_.GlobalTheory.DblTargetThetaF.main_k <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.WeilSchwartzDecayBound
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
theorem PositivityTheory.ThKF0.weil_schwartz_decay_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∀ N : ℕ, ∃ (C : ℝ) (k : ℕ), ∀ g h (x : Fin n × Fin d → AF F),
    ‖om (g, h) Φ x‖ * (1 + ‖fun i => evI F (x i)‖) ^ N ≤ C * ((ht g : ℝ) * ht h) ^ k :=
  _root_.PositivityTheory.ThKF0.Grow.schwartz_decay_uniform PositivityTheory.ThKF0.Grow.htBd PositivityTheory.ThKF0.Grow.finInv
    (PositivityTheory.ThKF0.Grow.sob_of PositivityTheory.ThKF0.Grow.derivOK) PositivityTheory.ThKF0.Grow.trBd
end
end

