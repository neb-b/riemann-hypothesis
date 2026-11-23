module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0287
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfCommuteOfSeparable
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.ThetaBasic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureOfCongruentForm
public import Development.WeilBound.CoreStatements.ThetaDilations.Bundle0001
public import Development.WeilBound.CoreStatements.ThetaDilations.SdTransport
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0291
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0307
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArtinReesClosedSystem
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.WeilBound.CoreStatements.ThetaDilations.ThetaLint

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NilradicalChangeOfVariables
section
open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc GlobalTheory.CompanionTheory.NilChangeVar

namespace GlobalTheory.CompanionTheory.LocVan

theorem nilChange_of_flag : NilChange := by
  intro n d W₁ W₂ hreg _ hle h1 h2
  let L : nilrad W₁ W₂ ≃ₗ[ℝ] nilrad W₁ W₂ :=
    LinearEquiv.ofInjectiveEndo (slinN d h1 h2 - LinearMap.id) (slinN_injective d h1 h2 hreg)
  have hLval (X : nilrad W₁ W₂) : (L X).1 = slin d X.1 - X.1 := by
    simp only [L, LinearEquiv.coe_ofInjectiveEndo, LinearMap.sub_apply, LinearMap.id_apply,
      Submodule.coe_sub] <;> rfl
  have hLc : Continuous L := L.toContinuousLinearEquiv.continuous
  let Q : nilrad W₁ W₂ → nilrad W₁ W₂ := fun X =>
    ⟨quad d X.1, two_mem hle (quadratic_term_nilradical_mem d h1 h2 X.2).1 (quadratic_term_nilradical_mem d h1 h2 X.2).2⟩
  have hQc : Continuous Q :=
    Continuous.subtype_mk ((continuous_quad d).comp continuous_subtype_val) _
  have hLF : ∀ y ∈ nilrad2 W₁ W₂, L y ∈ nilrad2 W₁ W₂ := fun y hy => by
    have hT := semilinear_term_nilradical_mem d h1 h2 hy.1 hy.2
    refine ⟨fun z => ?_, fun z hz => ?_⟩
    · rw [hLval, Matrix.sub_mulVec]
      exact W₁.sub_mem (hT.1 z) (hy.1 z)
    · rw [hLval, Matrix.sub_mulVec, hT.2 z hz, hy.2 z hz, sub_zero]
  have hQF : ∀ X, Q X ∈ nilrad2 W₁ W₂ := fun X => quadratic_term_nilradical_mem d h1 h2 X.2
  have hQinv : ∀ X, ∀ Y ∈ nilrad2 W₁ W₂, Q (X + Y) = Q X := fun X Y hY =>
    Subtype.ext (quad_add d h1 h2 X.2 hle hY.1 hY.2)
  refine ⟨fun X => L X + Q X, hLc.add hQc, fun X => ?_, ?_⟩
  · rw [eq_inv_mul_iff_mul_eq]
    refine Units.ext ?_
    have e : (uOf (L X + Q X)).val = 1 + (slin d X.1 - X.1 + quad d X.1) := by
      rw [uOf_val, Submodule.coe_add, hLval]
    rw [Units.val_mul, e]
    exact twist_val d h1 h2 (uOf X) X.1 X.2 rfl
  · intro _ _ ν _
    obtain ⟨Φ, c, _, hΦ, hmap⟩ := exists_homeo_map_eq_smul ν (nilrad2 W₁ W₂) L hLF Q hQc hQF hQinv
    refine ⟨c, ?_⟩
    have e : (fun X => L X + Q X) = Φ := funext fun X => (hΦ X).symm
    rw [e]
    exact hmap

end GlobalTheory.CompanionTheory.LocVan
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormCVPosIdele
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1 PositivityTheory.Rg.BcB.E1
open GroundTheory.Automorphic.Reduction

namespace GlobalTheory.CompanionTheory.TorNorm

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem norm_cV (v : InfinitePlace E) (u : Ad E) : ‖cV v u‖ = ‖u.1 v‖ :=
  (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex v)).isometry.norm_map_of_map_zero (map_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex v))) _

theorem cW_posIdele (w : HeightOneSpectrum (𝓞 E)) (ρ : ℝ) (hρ : 0 < ρ) :
    cW w ((posIdele (K := E) ρ hρ : (Ad E)ˣ) : Ad E) = 1 :=
  posIdele_finite ρ hρ w

theorem norm_cV_posIdele (v : InfinitePlace E) (ρ : ℝ) (hρ : 0 < ρ) :
    ‖cV v ((posIdele (K := E) ρ hρ : (Ad E)ˣ) : Ad E)‖ = ρ := by
  rw [norm_cV]; exact norm_posIdele_infinite ρ hρ v

theorem two_card : 2 * (Fintype.card (InfinitePlace E) : ℝ) = Module.finrank ℚ E := by
  rw [IsTotallyComplex.finrank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyComplex.nrRealPlaces_eq_zero]
  push_cast; ring

theorem logAbs_of (u : Ad E) (t : ℝ) (h1 : ∀ v, ‖cV v u‖ = Real.exp t) (h2 : ∀ w, ‖cW w u‖ = 1) :
    logAbs u = Module.finrank ℚ E * t := by
  have : ∀ v : InfinitePlace E, Real.log (‖cV v u‖ ^ 2) = 2 * t := fun v => by
    rw [h1, Real.log_pow, Real.log_exp]; norm_num
  simp only [logAbs, this, h2, Real.log_one, finsum_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, add_zero]
  rw [← two_card]; ring

theorem tor_neg {n : ℕ} (x : Fin n → ℝ) : (An.tor E x : GA E n)⁻¹ = An.tor E (-x) := by
  refine (eq_inv_of_mul_eq_one_left ?_).symm
  have : ∀ i, posIdele (K := E) (Real.exp ((-x) i)) (Real.exp_pos _) * posIdele (K := E) (Real.exp (x i)) (Real.exp_pos _) = 1 := fun i => by
    have h : (⟨Real.exp ((-x) i), Real.exp_pos _⟩ : {r : ℝ // 0 < r}) *
        ⟨Real.exp (x i), Real.exp_pos _⟩ = 1 := by
      apply Subtype.ext
      simp [← Real.exp_add]
    have := congrArg (posIdeleHom E) h
    simpa only [map_mul, map_one, posIdeleHom_apply] using this
  change diagUnits n _ * diagUnits n _ = 1
  rw [← map_mul]
  convert map_one (diagUnits n (R := Ad E))
  exact funext this

theorem logSizeM_tor {n : ℕ} (x : Fin n → ℝ) :
    logSizeM (An.tor E x : GA E n).val ≤ Module.finrank ℚ E * ‖x‖ := by
  have entry : ∀ i j, (An.tor E x : GA E n).val i j =
      if i = j then ((posIdele (K := E) (Real.exp (x i)) (Real.exp_pos _) : (Ad E)ˣ) : Ad E) else 0 := fun i j => by
    change (diagUnits n _ : GL (Fin n) (Ad E)).val i j = _
    rw [coe_diagUnits, Matrix.diagonal_apply]
  have hx : 0 ≤ ‖x‖ := norm_nonneg _
  have inf : ∀ v : InfinitePlace E,
      Real.posLog (⨆ p : Fin n × Fin n, ‖cV v ((An.tor E x : GA E n).val p.1 p.2)‖ ^ 2) ≤ 2 * ‖x‖ := fun v => by
    have hle : (⨆ p : Fin n × Fin n, ‖cV v ((An.tor E x : GA E n).val p.1 p.2)‖ ^ 2) ≤ Real.exp (2 * ‖x‖) := by
      refine Real.iSup_le (fun p => ?_) (Real.exp_pos _).le
      rw [entry]
      split_ifs
      · rw [norm_cV_posIdele, ← Real.exp_nat_mul]
        have : x p.1 ≤ ‖x‖ := (le_abs_self _).trans (norm_le_pi_norm x p.1)
        exact Real.exp_le_exp.2 (by push_cast; linarith)
      · simp [(Real.exp_pos _).le]
    calc _ ≤ Real.posLog (Real.exp (2 * ‖x‖)) :=
          Real.posLog_le_posLog (le_trans (by norm_num) (Real.iSup_nonneg fun _ => by positivity)) hle
      _ = 2 * ‖x‖ := by
          rw [Real.posLog, Real.log_exp]
          exact max_eq_right (by positivity)
  have fin : ∀ w : HeightOneSpectrum (𝓞 E),
      Real.posLog (⨆ p : Fin n × Fin n, ‖cW w ((An.tor E x : GA E n).val p.1 p.2)‖) = 0 := fun w => by
    rw [Real.posLog_eq_zero_iff, abs_of_nonneg (Real.iSup_nonneg fun _ => norm_nonneg _)]
    refine Real.iSup_le (fun p => ?_) zero_le_one
    rw [entry]
    split_ifs
    · rw [cW_posIdele, norm_one]
    · simp
  unfold logSizeM
  simp only [fin, finsum_zero, add_zero]
  calc _ ≤ ∑ _v : InfinitePlace E, 2 * ‖x‖ := Finset.sum_le_sum fun v _ => inf v
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← two_card]; ring

theorem logAbs_det_tor {n : ℕ} (x : Fin n → ℝ) :
    logAbs (An.tor E x : GA E n).val.det = Module.finrank ℚ E * ∑ i, x i := by
  have d : (An.tor E x : GA E n).val.det =
      ∏ i, ((posIdele (K := E) (Real.exp (x i)) (Real.exp_pos _) : (Ad E)ˣ) : Ad E) := by
    change (diagUnits n _ : GL (Fin n) (Ad E)).val.det = _
    rw [coe_diagUnits, det_diagonal]
  rw [d]
  refine logAbs_of _ _ (fun v => ?_) (fun w => ?_)
  · rw [map_prod, norm_prod, Real.exp_sum]
    exact Finset.prod_congr rfl fun i _ => norm_cV_posIdele v _ _
  · rw [map_prod, norm_prod]
    exact Finset.prod_eq_one fun i _ => by rw [cW_posIdele, norm_one]

theorem torNorm : LogAbsBasic → TorNorm := fun _ E _ _ _ =>
  ⟨fun t => logAbs_of _ t (fun v => norm_cV_posIdele v _ _) (fun w => by rw [cW_posIdele, norm_one]),
    fun n x => ⟨logAbs_det_tor x, by
      have h1 := logSizeM_tor (E := E) x
      have h2 := logSizeM_tor (E := E) (-x)
      rw [norm_neg] at h2
      rw [logSize, tor_neg]
      linarith⟩⟩

end GlobalTheory.CompanionTheory.TorNorm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OperatorSequenceSumEpi
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.KerSeq

theorem epi_sumMap_of_opSeq {X : Scheme.{0}} {k : ℕ} {M : ℕ → X.Modules}
    {T : Fin k → ∀ e, M e ⟶ M (e + 1)} {d : ℕ} (h : OpSeq k M T d) (e : ℕ) :
    Epi (KerSeq.sumMap T d e) := by
  haveI : ∀ n, (M n).IsQuasicoherent := fun n => (h.coherent n).1
  haveI : (KerSeq.sumN M k d e).IsQuasicoherent := by
    unfold KerSeq.sumN
    exact GlobalTheory.QCoh.isQuasicoherent_biproduct _
  rw [GlobalTheory.QCoh.epi_iff_forall_affine]
  intro U hU
  have hg := h.gen (d + e) (Nat.le_add_right d e) ⟨U, hU⟩
  have hr : (GlobalTheory.QCoh.appLinear (KerSeq.sumMap T d e) U).range = ⊤ := by
    rw [eq_top_iff, ← hg, Submodule.span_le]
    intro y hy
    simp only [Set.mem_iUnion, Set.mem_range] at hy
    obtain ⟨i, x, rfl⟩ := hy
    refine ⟨(biproduct.ι (fun _ : Fin k => M (d + e)) i).app U x, ?_⟩
    rw [GlobalTheory.QCoh.appLinear_apply, GlobalTheory.QCoh.app_app]
    simp [KerSeq.sumMap]
  rw [← GlobalTheory.QCoh.coe_appLinear]
  exact LinearMap.range_eq_top.1 hr

end GlobalTheory.CompanionTheory.GE.KerSeq
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalHHermScal
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.MassSimil

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def scalH (σ : E →ₐ[F] E) {n : ℕ} (l : R) (S : HermR R σ n) : HermR R σ n :=
  ⟨(algebraMap R (R ⊗[F] E) l) • (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)), by
    intro a b
    have h : sigR R σ (algebraMap R (R ⊗[F] E) l) = algebraMap R (R ⊗[F] E) l := by
      simp [sigR, Algebra.TensorProduct.algebraMap_apply]
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul, h, S.2 a b]⟩

theorem scalH_coe (σ : E →ₐ[F] E) {n : ℕ} (l : R) (S : HermR R σ n) :
    (scalH R σ l S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) =
      (algebraMap R (R ⊗[F] E) l) • (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := rfl

theorem scalH_hermScal (σ : E →ₐ[F] E) (l s : R) :
    scalH R σ l (hermScal R σ s) = hermScal R σ (l * s) := by
  apply Subtype.ext
  funext a b
  change (algebraMap R (R ⊗[F] E) l) * (s ⊗ₜ[F] (1 : E)) = (l * s) ⊗ₜ[F] (1 : E)
  simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]

end Alg

theorem euler_move_c : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (minf minf' : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (m m' : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (e : (Fin n → Fin M → AF F ⊗[F] E) → (Fin n → Fin M → AF F ⊗[F] E)) (einf : (Fin n → Fin M → Ainf F ⊗[F] E) → (Fin n → Fin M → Ainf F ⊗[F] E)) (ev : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → (Fin n → Fin M → Fv F v ⊗[F] E)), Measurable e → Measurable einf → (∀ v, Measurable (ev v)) → (∀ X, projInf (e X) = einf (projInf X) ∧ ∀ v, projV v (projFin (e X)) = ev v (projV v (projFin X))) → (∀ᶠ v in Filter.cofinite, ∀ X, ev v X ∈ latV b v ↔ X ∈ latV b v) → ∀ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c → minf.map einf = cinf • minf' → (∀ v, (m v).map (ev v) = c v • m' v) → (∀ v, m' v (latV b v) < ⊤) → ∀ κ : ℝ≥0, IsEulerProd b I κ minf m → IsEulerProd b (I.map e) κ minf' m' := by
  intro F E _ _ _ _ _ σ hcm d b n M I mi mi' m m' e ei ev me mei mev hpr hG ci c hc h1 h2 hf κ hE
  have tr : ∀ (J : Measure (Fin n → Fin M → AF F ⊗[F] E)) (a : Measure (Fin n → Fin M → Ainf F ⊗[F] E))
      (w : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)),
      IsEulerProd b J κ a w ↔ IsEulerProd b J 1 (κ • a) w := fun J a w => by
    have e1 : ∀ φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞, ∫⁻ X, φ X ∂(κ • a) = (κ : ℝ≥0∞) * ∫⁻ X, φ X ∂a := fun φ => by
      rw [ENNReal.smul_def, lintegral_smul_measure, smul_eq_mul]
    simp only [IsEulerProd, e1, ENNReal.coe_one, one_mul, mul_assoc]
  rw [tr] at hE ⊢
  refine PositivityTheory.PlacePermOperatorBicommutantSpan.euler_move F E σ hcm d b n M I _ _ m m' e ei ev me mei mev hpr hG ci c hc ?_ h2 hf hE
  rw [Measure.map_smul κ mei.aemeasurable, h1, smul_comm]

end GlobalTheory.CompanionTheory.SW.MassSimil

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionsEqUnivOffBadSupport
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

set_option autoImplicit false
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.GE.PSupp

noncomputable section

variable {X : Scheme.{0}}

lemma eq_zero_basicOpen_of_affine (F : X.Modules) [F.IsQuasicoherent] {V : X.Opens}
    (hV : IsAffineOpen V) (h0 : ∀ s : Γ(F, V), s = 0) (f : Γ(X, V)) (m : Γ(F, X.basicOpen f)) :
    m = 0 := by
  have hunit : IsUnit (resO (X.basicOpen_le f) f) := X.toRingedSpace.isUnit_res_basicOpen f
  obtain ⟨e, m', hm'⟩ := qcoh_exists_res_eq F hV f m
  refine eq_zero_of_isUnit_smul (hunit.pow e) ?_
  rw [← hm', h0 m', map_zero]

lemma eq_zero_of_le_affine (F : X.Modules) [F.IsQuasicoherent] {V W : X.Opens}
    (hV : IsAffineOpen V) (h0 : ∀ s : Γ(F, V), s = 0) (hW : W ≤ V) (m : Γ(F, W)) : m = 0 := by
  refine TopCat.Sheaf.eq_of_locally_eq' (⟨F.presheaf, F.isSheaf⟩ : TopCat.Sheaf Ab X)
    (fun i : {f : Γ(X, V) // X.basicOpen f ≤ W} => X.basicOpen i.1) W
    (fun i => homOfLE i.2) ?_ m 0 ?_
  · intro x hx
    obtain ⟨f, hfW, hxf⟩ := hV.exists_basicOpen_le (V := W) ⟨x, hx⟩ (hW hx)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, hfW⟩, hxf⟩
  · intro i
    rw [map_zero]
    exact eq_zero_basicOpen_of_affine F hV h0 i.1 _

lemma cokernel_sections_eq_zero {P : X.Modules} [P.IsQuasicoherent] (S : Subobject P)
    [(S : X.Modules).IsQuasicoherent] {V : X.Opens} (hV : IsAffineOpen V)
    (hS : secs S V = Set.univ) (s : Γ(cokernel S.arrow, V)) : s = 0 := by
  obtain ⟨y, rfl⟩ := surjective_cokernel_π_app S.arrow hV s
  have hmem : y ∈ secs S V := by rw [hS]; trivial
  exact (mem_range_app_iff S.arrow hV y).1 hmem

lemma supportedIn_badSet {P : X.Modules} [P.IsQuasicoherent] (S : Subobject P)
    [(S : X.Modules).IsQuasicoherent] :
    Scheme.Modules.SupportedIn (cokernel S.arrow) (badSet S) := by
  intro U hU s
  refine TopCat.Sheaf.eq_of_locally_eq'
    (⟨(cokernel S.arrow).presheaf, (cokernel S.arrow).isSheaf⟩ : TopCat.Sheaf Ab X)
    (fun i : {V : X.affineOpens // secs S (V : X.Opens) = Set.univ} => U ⊓ (i.1 : X.Opens)) U
    (fun i => homOfLE inf_le_left) ?_ s 0 ?_
  · intro x hx
    have hxb : x ∉ badSet S := fun hb => Set.disjoint_left.1 hU hx hb
    have hxc : x ∈ (badSet S)ᶜ := hxb
    rw [badSet_compl_eq] at hxc
    simp only [Set.mem_iUnion, exists_prop] at hxc
    obtain ⟨V, hV, hxV⟩ := hxc
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨V, hV⟩, ⟨hx, hxV⟩⟩
  · intro i
    rw [map_zero]
    exact eq_zero_of_le_affine _ i.1.2 (cokernel_sections_eq_zero S i.1.2 i.2) inf_le_right _

theorem secs_eq_univ_of_disjoint_badSet {X : Scheme.{0}} {P : X.Modules} (hP : P.IsQuasicoherent)
    (S : Subobject P) (hS : (S : X.Modules).IsQuasicoherent) (U : X.Opens) (hU : IsAffineOpen U)
    (hd : Disjoint (U : Set X) (badSet S)) : secs S U = Set.univ := by
  haveI : P.IsQuasicoherent := hP
  haveI : (S : X.Modules).IsQuasicoherent := hS
  exact GlobalTheory.CompanionTheory.GE.Comb.secs_eq_univ_of_supportedIn hP hS (supportedIn_badSet S) hU hd

end

end GlobalTheory.CompanionTheory.GE.PSupp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreVanishingFirstCohomology
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.Step

namespace GlobalTheory.CompanionTheory.GE.Step

theorem serre_vanishing_coh_one : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H → ∀ {F : X.Modules}, IsCoherent F → ∃ n₂ : ℤ, ∀ n, n₂ ≤ n → Subsingleton (GlobalTheory.coh (GlobalTheory.twistZ F H n) 1) := by
  intro A _ _ X _ _ H hH F hF
  letI : Algebra A ↑(X.presheaf.obj (Opposite.op ⊤)) :=
    ((X ↘ Spec (.of A)).appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom).toAlgebra
  obtain ⟨hq, hfin⟩ := hF
  haveI : GlobalTheory.QCoh.IsFiniteQC F := GlobalTheory.QCoh.IsFiniteQC.mk hq hfin
  haveI : IsProper ((X ↘ Spec (.of A)) : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp A) := ‹IsProper (X ↘ Spec (.of A))›
  have hev := GlobalTheory.IsAmpleLB.eventually_subsingleton_coh_twistZ (R := A)
    (f := ((X ↘ Spec (.of A)) : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp A)) (fun _ => rfl) F hH
  obtain ⟨n₂, hn⟩ := Filter.eventually_atTop.1 hev
  exact ⟨n₂, fun n hn' => hn n hn' 1 Nat.one_pos⟩

end GlobalTheory.CompanionTheory.GE.Step
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimilitudeBetweenNonemptySpheres
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SimilExists

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def frame (σ : E →ₐ[F] E) (J : Matrix (Fin 2) (Fin 2) E) (x : Fin 2 → E) : Matrix (Fin 2) (Fin 2) E :=
  !![x 0, -(σ (x 0) * J 0 1 + σ (x 1) * J 1 1); x 1, σ (x 0) * J 0 0 + σ (x 1) * J 1 0]

theorem frame_det (σ : E →ₐ[F] E) (J : Matrix (Fin 2) (Fin 2) E) (x : Fin 2 → E) :
    (frame σ J x).det = hE σ J x x := by
  simp [frame, Matrix.det_fin_two, hE, hform, Fin.sum_univ_two]
  ring

theorem frame_gram {σ : E →ₐ[F] E} (hσ : ∀ e, σ (σ e) = e) {J : Matrix (Fin 2) (Fin 2) E}
    (hJ : IsHermND σ J) (x : Fin 2 → E) :
    cT (σ : E →+* E) (frame σ J x) * J * frame σ J x =
      hE σ J x x • Matrix.diagonal ![1, J.det] := by
  have h00 : σ (J 0 0) = J 0 0 := hJ.1 0 0
  have h11 : σ (J 1 1) = J 1 1 := hJ.1 1 1
  have h01 : σ (J 1 0) = J 0 1 := hJ.1 0 1
  have h10 : σ (J 0 1) = J 1 0 := hJ.1 1 0
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [frame, cT, Matrix.mul_apply, Fin.sum_univ_two, hE, hform, Matrix.det_fin_two, hσ, h00, h11,
      h01, h10] <;> ring

theorem exists_similitude_of_vectors {σ : E →ₐ[F] E} (hσ : ∀ e, σ (σ e) = e)
    {J : Matrix (Fin 2) (Fin 2) E} (hJ : IsHermND σ J) {x x' : Fin 2 → E} {b b' : E}
    (hx : hE σ J x x = b) (hx' : hE σ J x' x' = b') (hb : b ≠ 0) (hb' : b' ≠ 0) :
    ∃ γ : GL (Fin 2) E, cT (σ : E →+* E) (γ : Matrix (Fin 2) (Fin 2) E) * J *
      (γ : Matrix (Fin 2) (Fin 2) E) = (b' / b) • J := by
  set P := frame σ J x with hP
  set P' := frame σ J x' with hP'
  have hdet : P.det = b := by rw [hP, frame_det, hx]
  have hdet' : P'.det = b' := by rw [hP', frame_det, hx']
  have hu : IsUnit P.det := by rw [hdet]; exact hb.isUnit
  have hinv : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hu
  have hc : cT (σ : E →+* E) P⁻¹ * cT (σ : E →+* E) P = 1 := by
    rw [← cT_mul, hinv, cT_one]
  have hg : cT (σ : E →+* E) P * J * P = b • Matrix.diagonal ![1, J.det] := by
    rw [hP, frame_gram hσ hJ, hx]
  have hg' : cT (σ : E →+* E) P' * J * P' = b' • Matrix.diagonal ![1, J.det] := by
    rw [hP', frame_gram hσ hJ, hx']
  have hJ' : J = b • (cT (σ : E →+* E) P⁻¹ * Matrix.diagonal ![1, J.det] * P⁻¹) := by
    calc J = (cT (σ : E →+* E) P⁻¹ * cT (σ : E →+* E) P) * J * (P * P⁻¹) := by
          rw [hc, hinv, Matrix.one_mul, Matrix.mul_one]
      _ = cT (σ : E →+* E) P⁻¹ * (cT (σ : E →+* E) P * J * P) * P⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [hg, Matrix.mul_smul, Matrix.smul_mul]
  have hdetG : (P' * P⁻¹).det ≠ 0 := by
    rw [Matrix.det_mul, Matrix.det_nonsing_inv, hdet', hdet]
    simpa using ⟨hb', hb⟩
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (P' * P⁻¹) hdetG, ?_⟩
  change cT (σ : E →+* E) (P' * P⁻¹) * J * (P' * P⁻¹) = (b' / b) • J
  calc cT (σ : E →+* E) (P' * P⁻¹) * J * (P' * P⁻¹)
      = cT (σ : E →+* E) P⁻¹ * (cT (σ : E →+* E) P' * J * P') * P⁻¹ := by
        rw [cT_mul]; simp only [Matrix.mul_assoc]
    _ = b' • (cT (σ : E →+* E) P⁻¹ * Matrix.diagonal ![1, J.det] * P⁻¹) := by
        rw [hg', Matrix.mul_smul, Matrix.smul_mul]
    _ = (b' / b) • (b • (cT (σ : E →+* E) P⁻¹ * Matrix.diagonal ![1, J.det] * P⁻¹)) := by
        rw [smul_smul, div_mul_cancel₀ _ hb]
    _ = (b' / b) • J := by rw [← hJ']

theorem exists_similitude : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ J : Matrix (Fin 2) (Fin 2) E, IsHermND σ J → ∀ β β' : F, β ≠ 0 → β' ≠ 0 → (PositivityTheory.Rg.Mass.sph σ J β).Nonempty → (PositivityTheory.Rg.Mass.sph σ J β').Nonempty → ∃ γ : GL (Fin 2) E, cT (σ : E →+* E) (γ : Matrix (Fin 2) (Fin 2) E) * J * (γ : Matrix (Fin 2) (Fin 2) E) = (algebraMap F E (β' / β)) • J := by
  intro F E _ _ _ _ _ σ hcm J hJ β β' hβ hβ' ⟨X, hX⟩ ⟨X', hX'⟩
  have hσ : ∀ e, σ (σ e) = e := fun e => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hcm.2.2.2, hcm.2.2.2]
    simp
  have hx : hE σ J (X 0) (X 0) = algebraMap F E β := congrFun (congrFun hX 0) 0
  have hx' : hE σ J (X' 0) (X' 0) = algebraMap F E β' := congrFun (congrFun hX' 0) 0
  have hb : algebraMap F E β ≠ 0 := by simpa using hβ
  have hb' : algebraMap F E β' ≠ 0 := by simpa using hβ'
  rw [map_div₀]
  exact exists_similitude_of_vectors hσ hJ hx hx' hb hb'

end GlobalTheory.CompanionTheory.SimilExists

end
end

