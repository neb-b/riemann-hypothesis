module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0482
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0494
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanHaarScalingNorm
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0025
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0086
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0075
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0659
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1567
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0657
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0660
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0041
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0498
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0656
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedFormsMutualShuffleEq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0662
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0365
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0353
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0616
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0023
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0589
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0627
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0351
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0363
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0576
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0629
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0597
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0063

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianCoordinatesMeasurePreserving
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.CoordMeas

theorem map_comp_comap {H Y Z : Type} [MeasurableSpace H] [MeasurableSpace Y] [MeasurableSpace Z]
    (e : H ≃ᵐ Y) (ν : Measure Y) {c : Y → Z} (hc : Measurable c) :
    (Measure.comap e ν).map (c ∘ e) = ν.map c := by
  rw [← MeasurableEquiv.map_symm, ← Measure.map_map hc e.measurable,
    Measure.map_map e.measurable e.symm.measurable]
  have : (⇑e ∘ ⇑e.symm) = id := funext e.apply_symm_apply
  rw [this, Measure.map_id]

theorem map_prod_box {R K P : Type} [MeasurableSpace R] [MeasurableSpace K] [Fintype P] {n d : ℕ}
    (lam : Measure R) [SigmaFinite lam] (κ : Measure K) [SigmaFinite κ] (r : K → Fin d → R)
    (hr : Measurable r) (hκ : κ.map r = Measure.pi fun _ => lam) :
    ((Measure.pi fun _ : Fin n => lam).prod (Measure.pi fun _ : P => κ)).map
        (fun x : (Fin n → R) × (P → K) =>
          (Sum.elim x.1 (fun q : Fin d × P => r (x.2 q.2) q.1) : Fin n ⊕ (Fin d × P) → R)) =
      Measure.pi fun _ : Fin n ⊕ (Fin d × P) => lam := by
  have hc : Measurable (fun x : (Fin n → R) × (P → K) =>
      (Sum.elim x.1 (fun q : Fin d × P => r (x.2 q.2) q.1) : Fin n ⊕ (Fin d × P) → R)) := by
    refine measurable_pi_iff.2 fun i => ?_
    rcases i with i | q
    · exact (measurable_pi_apply i).comp measurable_fst
    · exact (measurable_pi_apply q.1).comp
        (hr.comp ((measurable_pi_apply q.2).comp measurable_snd))
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply hc (MeasurableSet.univ_pi hs)]
  have hset : (fun x : (Fin n → R) × (P → K) =>
      (Sum.elim x.1 (fun q : Fin d × P => r (x.2 q.2) q.1) : Fin n ⊕ (Fin d × P) → R)) ⁻¹'
        Set.pi Set.univ s =
      (Set.pi Set.univ fun i : Fin n => s (Sum.inl i)) ×ˢ
        (Set.pi Set.univ fun p : P => r ⁻¹' Set.pi Set.univ fun k : Fin d => s (Sum.inr (k, p))) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_prod,
      Sum.forall, Sum.elim_inl, Sum.elim_inr, Prod.forall]
    exact and_congr Iff.rfl ⟨fun h p k => h k p, fun h k p => h p k⟩
  have hκs : ∀ p : P, κ (r ⁻¹' Set.pi Set.univ fun k : Fin d => s (Sum.inr (k, p))) =
      ∏ k : Fin d, lam (s (Sum.inr (k, p))) := fun p => by
    rw [← Measure.map_apply hr (MeasurableSet.univ_pi fun k => hs _), hκ, Measure.pi_pi]
  rw [hset, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, Fintype.prod_sum_type,
    Fintype.prod_prod_type]
  simp only [hκs]
  rw [Finset.prod_comm]

end GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.CoordMeas

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.TestN

open GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.CoordMeas

theorem coordHerm_map_hCo : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ n : ℕ, (GlobalTheory.CompanionTheory.SW.coordHerm R σ b lam n).map (hCo R σ b) = Measure.pi fun _ : Idx n d => lam := by
  intro F E _ _ _ _ _ σ hcm R _ _ _ _ _ _ _ _ _ d b lam hlam n
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, -, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm R
  have h2 : Module.finrank F E = 2 := hcm.2.2.1
  obtain ⟨hinv, δ, hδ, hσδ⟩ := GlobalTheory.CompanionTheory.SW.HaarCoord.conj_facts hcm
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul R _
  haveI : BorelSpace (HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ n) := ⟨rfl⟩
  obtain ⟨hK, -, -⟩ := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hcm R d b lam hlam
  haveI : SigmaFinite (GlobalTheory.CompanionTheory.SW.coordK R b lam) := inferInstance

  let r : R ⊗[F] E → Fin d → R := fun y k => (Algebra.TensorProduct.basis R b).repr y k
  let Tr : (R ⊗[F] E) ≃ₜ (Fin d → R) := (t7 d b).homeomorph r
  have hr : Measurable r := Tr.toMeasurableEquiv.measurable
  have hκ : (GlobalTheory.CompanionTheory.SW.coordK R b lam).map r = Measure.pi fun _ => lam := by
    have := map_comp_comap Tr.toMeasurableEquiv (Measure.pi fun _ => lam) (c := id) measurable_id
    rw [Measure.map_id] at this
    exact this

  let T := (GlobalTheory.CompanionTheory.SW.HaarCoord.hermCoord_isHomeomorph R hinv h2 hδ hσδ n t5 t6).homeomorph
    (GlobalTheory.CompanionTheory.SW.HaarCoord.hermCoord R σ n)
  have hbox := map_prod_box (n := n) (P := {p : Fin n × Fin n // p.1 < p.2}) lam
    (GlobalTheory.CompanionTheory.SW.coordK R b lam) r hr hκ
  have hc : Measurable (fun x : (Fin n → R) × ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E) =>
      (Sum.elim x.1 (fun q : Fin d × {p : Fin n × Fin n // p.1 < p.2} => r (x.2 q.2) q.1) : Idx n d → R)) := by
    refine measurable_pi_iff.2 fun i => ?_
    rcases i with i | q
    · exact (measurable_pi_apply i).comp measurable_fst
    · exact (measurable_pi_apply q.1).comp
        (hr.comp ((measurable_pi_apply q.2).comp measurable_snd))
  have hm := map_comp_comap T.toMeasurableEquiv
    ((Measure.pi fun _ : Fin n => lam).prod
      (Measure.pi fun _ : {p : Fin n × Fin n // p.1 < p.2} => GlobalTheory.CompanionTheory.SW.coordK R b lam)) hc
  rw [hbox] at hm
  have hfun : hCo R σ b = (fun x : (Fin n → R) × ({p : Fin n × Fin n // p.1 < p.2} → R ⊗[F] E) =>
      (Sum.elim x.1 (fun q : Fin d × {p : Fin n × Fin n // p.1 < p.2} => r (x.2 q.2) q.1) : Idx n d → R)) ∘
      T.toMeasurableEquiv := by
    funext S i
    rcases i with i | q <;> rfl
  rw [hfun]
  exact hm

end GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPairingInCoordinates
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef GlobalTheory.CompanionTheory.SiegelND.Coef.TestN
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.PairCoord

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem trace_mul_sig {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x y : E) :
    Algebra.trace F E (σ x * y) = Algebra.trace F E (x * σ y) := by
  have hinv : Function.Involutive σ := GlobalTheory.CompanionTheory.SiegelND.Coef.sig_invol h
  have key := Algebra.trace_eq_of_algEquiv (AlgEquiv.ofBijective σ hinv.bijective) (σ x * y)
  rw [← key]
  simp [hinv x]

theorem trace_sigR_mul {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R] {d : ℕ}
    (b : Module.Basis (Fin d) F E) (u w : R ⊗[F] E) :
    Algebra.trace R (R ⊗[F] E) (sigR R σ u * w) =
      ∑ k, (Algebra.TensorProduct.basis R b).repr u k *
        ∑ l, algebraMap F R (Algebra.trace F E (b k * σ (b l))) * (Algebra.TensorProduct.basis R b).repr w l := by
  set C := Algebra.TensorProduct.basis R b with hC
  have hC' : ∀ (r : R) (k : Fin d), r • C k = r ⊗ₜ[F] b k := by
    intro r k
    simp [hC, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul']
  conv_lhs => rw [← C.sum_repr u, ← C.sum_repr w]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hC', map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  have hs : sigR R σ (C.repr u k ⊗ₜ[F] b k) = C.repr u k ⊗ₜ[F] σ (b k) := by simp [sigR]
  rw [hs, Algebra.TensorProduct.tmul_mul_tmul, GlobalTheory.GaussMean.OneVec.trace_tmul, trace_mul_sig h]
  ring

theorem mulVec_inl (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] {d : ℕ}
    (b : Module.Basis (Fin d) F E) {n : ℕ} (v : Idx n d → R) (i : Fin n) :
    (((coordForm σ b n).map (algebraMap F R)).mulVec v) (Sum.inl i) = v (Sum.inl i) := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, coordForm, Matrix.one_apply]

theorem mulVec_inr (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] {d : ℕ}
    (b : Module.Basis (Fin d) F E) {n : ℕ} (v : Idx n d → R) (k : Fin d)
    (q : {p : Fin n × Fin n // p.1 < p.2}) :
    (((coordForm σ b n).map (algebraMap F R)).mulVec v) (Sum.inr (k, q)) =
      ∑ l, algebraMap F R (Algebra.trace F E (b k * σ (b l))) * v (Sum.inr (l, q)) := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type, coordForm, Matrix.map_apply,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, map_zero, zero_mul,
    Finset.sum_const_zero, zero_add, Matrix.blockDiagonal_apply, Matrix.of_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single q]
  · simp
  · intro x _ hx
    simp [hx, Ne.symm hx]
  · simp

theorem pairHerm_eq_coordForm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] (d : ℕ)
    (b : Module.Basis (Fin d) F E) (n : ℕ) (S T : HermR R σ n),
    pairHerm R σ n S T = dotProduct (hCo R σ b S) (((coordForm σ b n).map (algebraMap F R)).mulVec (hCo R σ b T)) := by
  intro F E _ _ _ _ _ σ h R _ _ d b n S T
  rw [GlobalTheory.HermCoordEquiv.pair_eq R h S T]
  unfold GlobalTheory.HermSD.coordPair
  rw [dotProduct, Fintype.sum_sum_type]
  simp only [mulVec_inl, Fintype.sum_prod_type, mulVec_inr]
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [trace_sigR_mul h]
  rfl

end GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.PairCoord
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralEqFundamentalDomainLatticeSumStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_eq_fundamental_domain_lattice_sum : ∀ {D : D7} {ρ p : ℕ} (m : Meas D ρ p) (P : Mx D ρ p → ℂ), Integrable P m.μ → ∫ y, P y ∂m.μ = ∫ y in m.𝓕, ∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, P (GlobalTheory.CompanionTheory.FJE.rt ξ + y) ∂m.μ := by
  first | exact @GlobalTheory.CompanionTheory.FJE.integral_fold | exact GlobalTheory.CompanionTheory.FJE.integral_fold | (intros; apply GlobalTheory.CompanionTheory.FJE.integral_fold <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsotropicFreeVectorsSameGram
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.FreeTrans

section Form

variable {A : Type} [CommRing A] {n : ℕ} (s : A →+* A) (J : Matrix (Fin n) (Fin n) A)

theorem hform_add_right (x y z : Fin n → A) :
    hform s J x (y + z) = hform s J x y + hform s J x z := by
  simp only [hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hform_add_left (x y z : Fin n → A) :
    hform s J (x + y) z = hform s J x z + hform s J y z := by
  simp only [hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hform_smul_right (t : A) (x y : Fin n → A) :
    hform s J x (t • y) = t * hform s J x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hform_smul_left (t : A) (x y : Fin n → A) :
    hform s J (t • x) y = s t * hform s J x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end Form

theorem exists_hyperbolic_partner {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : IsHermND σ J) (R : Type) [CommRing R] [Algebra F R] (x y : Fin M → R ⊗[F] E)
    (hxx : hR R σ J x x = 0) (hxy : hR R σ J x y = 1) :
    ∃ y₁ : Fin M → R ⊗[F] E, hR R σ J x y₁ = 1 ∧ hR R σ J y₁ x = 1 ∧ hR R σ J y₁ y₁ = 0 := by
  have herm : ∀ u v : Fin M → R ⊗[F] E, sigR R σ (hR R σ J u v) = hR R σ J v u := by
    intro u v
    have h : ∀ a b, sigR R σ (gramR R σ J ![u, v] b a) = gramR R σ J ![u, v] a b :=
      GlobalTheory.CompanionTheory.SW.HermTop.gramR_mem R (GlobalTheory.CompanionTheory.SW.HermTop.sigma_sigma hσ) hJ.1 ![u, v]
    simpa [gramR] using h 1 0
  have hyx : hR R σ J y x = 1 := by rw [← herm, hxy, map_one]
  set c : R ⊗[F] E := algebraMap F (R ⊗[F] E) (1 / 2) with hc
  have hcc : c + c = 1 := by
    rw [hc, ← map_add (f := _), ← map_one (algebraMap F (R ⊗[F] E))]
    norm_num
  have hsc : sigR R σ c = c := AlgHom.commutes (Algebra.TensorProduct.map (AlgHom.id F R) σ) _
  set q := hR R σ J y y with hq
  have hsq : sigR R σ q = q := herm y y
  refine ⟨y + (-(c * q)) • x, ?_, ?_, ?_⟩
  · have : hR R σ J x (y + (-(c * q)) • x) = hR R σ J x y + -(c * q) * hR R σ J x x := by
      simp only [hR, hform_add_right, hform_smul_right]
    rw [this, hxx, hxy]
    ring
  · have : hR R σ J (y + (-(c * q)) • x) x =
        hR R σ J y x + sigR R σ (-(c * q)) * hR R σ J x x := by
      simp only [hR, hform_add_left, hform_smul_left]
    rw [this, hxx, hyx]
    ring
  · have : hR R σ J (y + (-(c * q)) • x) (y + (-(c * q)) • x) =
        hR R σ J y y + -(c * q) * hR R σ J y x + (sigR R σ (-(c * q)) * hR R σ J x y +
          sigR R σ (-(c * q)) * (-(c * q) * hR R σ J x x)) := by
      simp only [hR, hform_add_left, hform_add_right, hform_smul_left, hform_smul_right]
      ring
    rw [this, hxx, hxy, hyx, ← hq, map_neg, map_mul, hsc, hsq]
    linear_combination (-q) * hcc

theorem transitive_free_isotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ X Y : Fin 1 → Fin M → R ⊗[F] E, LinearIndependent (R ⊗[F] E) X → LinearIndependent (R ⊗[F] E) Y → gramR R σ J X = 0 → gramR R σ J Y = 0 → ∃ h : HA R σ J, actW R σ J h X = Y := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hL X Y hX hY gX gY
  haveI : IsArtinianRing R := hL.2.2.2.2.1
  haveI : IsReduced R := hL.2.2.2.2.2.1
  have hconst : ∀ Z : Fin 1 → Fin M → R ⊗[F] E, (fun _ : Fin 1 => Z 0) = Z := by
    intro Z
    funext a
    rw [Subsingleton.elim a 0]
  have hlx : LinearIndependent (R ⊗[F] E) (fun _ : Fin 1 => X 0) := by rwa [hconst]
  have hly : LinearIndependent (R ⊗[F] E) (fun _ : Fin 1 => Y 0) := by rwa [hconst]
  have hxx : hR R σ J (X 0) (X 0) = 0 := congrFun (congrFun gX 0) 0
  have hyy : hR R σ J (Y 0) (Y 0) = 0 := congrFun (congrFun gY 0) 0
  obtain ⟨y, hy⟩ := _root_.GlobalTheory.CompanionTheory.WeilSiegel.FreePartner.exists_partner F E σ hσ M J hJ R hL (X 0) hlx
  obtain ⟨y', hy'⟩ := _root_.GlobalTheory.CompanionTheory.WeilSiegel.FreePartner.exists_partner F E σ hσ M J hJ R hL (Y 0) hly
  obtain ⟨u, hu1, hu2, hu3⟩ := exists_hyperbolic_partner hσ hJ R (X 0) y hxx hy
  obtain ⟨u', hu1', hu2', hu3'⟩ := exists_hyperbolic_partner hσ hJ R (Y 0) y' hyy hy'
  have hG : gramR R σ J ![X 0, u] = !![0, 1; 1, 0] := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [gramR, hxx, hu1, hu2, hu3]
  have hG' : gramR R σ J ![Y 0, u'] = !![0, 1; 1, 0] := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [gramR, hyy, hu1', hu2', hu3']
  have hdet : IsUnit (gramR R σ J ![X 0, u]).det := by
    rw [hG, Matrix.det_fin_two_of]
    simp
  obtain ⟨h, hh⟩ := _root_.GlobalTheory.CompanionTheory.SW.WittTuples.exists_actW_eq_of_gramR_eq F E σ hσ M J hJ R 2 ![X 0, u] ![Y 0, u'] (hG.trans hG'.symm) hdet
  refine ⟨h, ?_⟩
  funext a
  rw [Subsingleton.elim a 0]
  simpa [actW, actTup] using congrFun hh 0

end GlobalTheory.CompanionTheory.WeilSiegel.FreeTrans
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsInjectiveOfSocle
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace GlobalTheory.CompanionTheory.Multisegment

theorem inShW_of_wd_cosocle {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hSeg : LSegJacquet k)
    {𝔫 : Multiset (Segment k)} {N h h' : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin N) k) V} (Δ : Fin h → Segment k) (Γ : Fin h' → Segment k)
    (v : Fin h' → IrrGL (k := k)) (hd : ∑ a, (v a).1 = N) (hΓ : IsOrderedForm Γ 𝔫)
    (hv : ∀ i, IsLSeg (Γ i) (v i).rep) (hc : IsCosocle π (prodIrr v hd)) (hw : Wd π (wtW Δ)) :
    InShW 𝔫 (wtW Δ) := by
  have h1 : Wd (prodIrr v hd) (wtW Δ) :=
    GlobalTheory.T.word_occurs_of_subquotient (prodIrr v hd) π (isSmooth_prodIrr v hd) hc.isSubquotient _ hw
  have h2 := GlobalTheory.T.segment_product_word_in_shuffle hA hSeg v hd Γ hv (wtW Δ) (_root_.GlobalTheory.CompanionTheory.ZcWords.wtW_isCusp Δ) h1
  rwa [hΓ.1] at h2

theorem lInjective {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hSoc : LSocleGL k) (hSeg : LSegJacquet k) : LInjective k := by
  intro 𝔪 𝔫 x h𝔪 h𝔫
  obtain ⟨h, u, hd, ⟨Δ, hΔ, hu⟩, hc⟩ := id h𝔪
  obtain ⟨h', v, hd', ⟨Γ, hΓ, hv⟩, hc'⟩ := id h𝔫
  have wΔ : Wd x.rep (wtW Δ) := _root_.GlobalTheory.CompanionTheory.ZWordL.wd_wtW_of_isL hA hSoc hSeg 𝔪 x.rep h𝔪 h Δ hΔ
  have wΓ : Wd x.rep (wtW Γ) := _root_.GlobalTheory.CompanionTheory.ZWordL.wd_wtW_of_isL hA hSoc hSeg 𝔫 x.rep h𝔫 h' Γ hΓ
  exact _root_.GlobalTheory.CompanionTheory.ZcWords.eq_of_inShW_wtW hA 𝔪 𝔫 h h' Δ Γ hΔ hΓ
    (inShW_of_wd_cosocle hA hSeg Δ Γ v hd' hΓ hv hc' wΔ)
    (inShW_of_wd_cosocle hA hSeg Γ Δ u hd hΔ hu hc wΓ)

end GlobalTheory.CompanionTheory.Multisegment
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSumSubquotientProduct
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace GlobalTheory.CompanionTheory.LangSumSub

theorem isL_of_exhaust {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hEx : ∀ x : IrrGL (k := k), ∃ 𝔪 : Multiset (Segment k), IsL 𝔪 x.rep) {N : ℕ} (τ : IrrRep (GL (Fin N) k)) :
    ∃ 𝔭 : Multiset (Segment k), IsL 𝔭 τ.ρ := by
  obtain ⟨𝔭, h𝔭⟩ := hEx (IrrGL.of τ.ρ τ.smooth τ.irr)
  exact ⟨𝔭, h𝔭.of_equiv (IrrGL.equivOf τ.ρ τ.smooth τ.irr).symm⟩


set_option maxHeartbeats 1000000 in
theorem isSubquotient_prodIrr {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hSoc : LSocleGL k)
    (hSeg : LSegJacquet k) (hFree : LOrderFree k) (hEx : ∀ x : IrrGL (k := k), ∃ 𝔪 : Multiset (Segment k), IsL 𝔪 x.rep)
    (𝔪 𝔫 : Multiset (Segment k)) (x : Fin 2 → IrrGL (k := k)) (y : IrrGL (k := k)) (hd : ∑ a, (x a).1 = y.1)
    (h0 : IsL 𝔪 (x 0).rep) (h1 : IsL 𝔫 (x 1).rep) (hy : IsL (𝔪 + 𝔫) y.rep) : IsSubquotient y.rep (prodIrr x hd) := by
  obtain ⟨n, c⟩ := y
  obtain rfl : (x 0).1 + (x 1).1 = n := (Fin.sum_univ_two _).symm.trans hd
  obtain ⟨φ⟩ := nonempty_prod₂_equiv_prodIrr_rep x hd
  have hPs : IsSmooth (prodIrr x hd) := isSmooth_prodIrr x hd
  have hPf := GlobalTheory.CompanionTheory.ProdFL.hasFiniteLength_prodIrr hA x hd
  obtain ⟨h₁, h₂, h, Δ₁, Δ₂, Δ, hΔ₁, hΔ₂, hΔ, hI⟩ := _root_.GlobalTheory.CompanionTheory.ZcMerge.exists_common_orderedForm hA 𝔪 𝔫
  have w0 : Wd (x 0).rep (wtW Δ₁) := _root_.GlobalTheory.CompanionTheory.ZWordL.wd_wtW_of_isL hA hSoc hSeg 𝔪 (x 0).rep h0 h₁ Δ₁ hΔ₁
  have w1 : Wd (x 1).rep (wtW Δ₂) := _root_.GlobalTheory.CompanionTheory.ZWordL.wd_wtW_of_isL hA hSoc hSeg 𝔫 (x 1).rep h1 h₂ Δ₂ hΔ₂
  have wp : Wd (prod₂ (x 0).rep (x 1).rep) (wtW Δ) :=
    GlobalTheory.T.word_occurs_product_interleave hA (x 0) (x 1) _ _ _ (_root_.GlobalTheory.CompanionTheory.ZcWords.wtW_isCusp Δ₁) (_root_.GlobalTheory.CompanionTheory.ZcWords.wtW_isCusp Δ₂) w0 w1 hI
  have wP : Wd (prodIrr x hd) (wtW Δ) := GlobalTheory.T.word_occurs_of_subquotient (prodIrr x hd) (prod₂ (x 0).rep (x 1).rep) hPs
    (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective) _ wp
  have hτ := GlobalTheory.T.word_occurs_irreducible_subquotient hA (prodIrr x hd) hPs hPf (wtW Δ) wP
  obtain ⟨τ, hτP, hτW⟩ := hτ
  obtain ⟨𝔭, hτL⟩ := isL_of_exhaust hEx τ
  obtain ⟨h', z, hz, ⟨Γ, hΓ, hzL⟩, hcos⟩ := id hτL
  have s1 : InShW 𝔭 (wtW Δ) := by
    have := GlobalTheory.T.segment_product_word_in_shuffle hA hSeg z hz Γ hzL (wtW Δ) (_root_.GlobalTheory.CompanionTheory.ZcWords.wtW_isCusp Δ)
      (GlobalTheory.T.word_occurs_of_subquotient _ _ (isSmooth_prodIrr z hz) hcos.isSubquotient _ hτW)
    rwa [hΓ.1] at this
  have wΓ : Wd τ.ρ (wtW Γ) := _root_.GlobalTheory.CompanionTheory.ZWordL.wd_wtW_of_isL hA hSoc hSeg 𝔭 τ.ρ hτL h' Γ hΓ
  have wΓP : Wd (prodIrr x hd) (wtW Γ) := GlobalTheory.T.word_occurs_of_subquotient _ _ hPs hτP _ wΓ
  have wΓ2 : Wd (prod₂ (x 0).rep (x 1).rep) (wtW Γ) := GlobalTheory.T.word_occurs_of_subquotient _ _ (isSmooth_prod₂ _ _)
    (.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective) _ wΓP
  obtain ⟨h'', z', Δ', hz', hz'L, hmap, hsub⟩ := GlobalTheory.T.product_langlands_subquotient_segments hA 𝔪 𝔫 (x 0) (x 1) h0 h1
  have s2 : InShW (𝔪 + 𝔫) (wtW Γ) := by
    have := GlobalTheory.T.segment_product_word_in_shuffle hA hSeg z' hz' Δ' hz'L (wtW Γ) (_root_.GlobalTheory.CompanionTheory.ZcWords.wtW_isCusp Γ)
      (GlobalTheory.T.word_occurs_of_subquotient _ _ (isSmooth_prodIrr z' hz') hsub _ wΓ2)
    rwa [hmap] at this
  have he : 𝔪 + 𝔫 = 𝔭 := _root_.GlobalTheory.CompanionTheory.ZcWords.eq_of_inShW_wtW hA (𝔪 + 𝔫) 𝔭 h h' Δ Γ hΔ hΓ s1 s2
  obtain ⟨ψ⟩ := _root_.GlobalTheory.CompanionTheory.LUniq.isL_unique hFree (𝔪 + 𝔫) τ.ρ (IrrGL.rep ⟨_, c⟩) (he ▸ hτL) hy
  exact (IsSubquotient.of_surjective ψ.toIntertwiningMap ψ.toLinearEquiv.surjective).trans hτP

theorem main : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), LSocleGL k → LSegJacquet k → LOrderFree k →
    (∀ x : IrrGL (k := k), ∃ 𝔪 : Multiset (Segment k), IsL 𝔪 x.rep) →
    ∀ (𝔪 𝔫 : Multiset (Segment k)) (x : Fin 2 → IrrGL (k := k)) (y : IrrGL (k := k)) (hd : ∑ a, (x a).1 = y.1),
      IsL 𝔪 (x 0).rep → IsL 𝔫 (x 1).rep → IsL (𝔪 + 𝔫) y.rep → IsSubquotient y.rep (prodIrr x hd) :=
  fun hA hSoc hSeg hFree hEx 𝔪 𝔫 x y hd h0 h1 hy =>
    isSubquotient_prodIrr hA hSoc hSeg hFree hEx 𝔪 𝔫 x y hd h0 h1 hy

end GlobalTheory.CompanionTheory.LangSumSub

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearIndependentExtendByUnitVectorStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndependent_extend_by_unit_vector : ∀ (K : Type) [CommRing K] (M n : ℕ) (α : K), IsUnit α → ∀ (c : Fin n → K) (X : Fin n → Fin M → K), LinearIndependent K (vec α c X : Fin (n + 1) → Fin (M + 1) → K) ↔ LinearIndependent K X := by
  first | exact @GlobalTheory.CompanionTheory.SW.PiLocalization₂.VecFree.linearIndependent_vec_iff | exact GlobalTheory.CompanionTheory.SW.PiLocalization₂.VecFree.linearIndependent_vec_iff | (intros; apply GlobalTheory.CompanionTheory.SW.PiLocalization₂.VecFree.linearIndependent_vec_iff <;> assumption)
end

