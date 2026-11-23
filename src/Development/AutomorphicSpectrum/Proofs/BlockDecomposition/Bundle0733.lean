module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
public import Development.AutomorphicArithmetic.LocalEmbeddings.OppLagr
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1567
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0657
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0658
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0729
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0683
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0728
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0675
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0690
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0662
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0667
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0660
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0661
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0666
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0685
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.SchurEigenProjections.EigA
public import Development.WeilBound.CoreStatements.BranchingTraces.ContinuousEmb
public import Development.WeilBound.CoreStatements.BranchingTraces.HilbertSchmidtTraces.Bundle0003
public import GroundTheory.AutomorphicForms.Bundle0006
public import GroundTheory.AutomorphicForms.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantMultiplierGood
section
noncomputable section

namespace GlobalTheory.CompanionTheory.RgEisCM

open scoped TensorProduct NNReal Matrix NumberField.AdeleRing
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open PositivityTheory.RgEis

section Transport

variable {R R' : Type} [CommRing R] [CommRing R'] {ι : Type} [Fintype ι] [DecidableEq ι]

def glEquiv (e : R ≃+* R') : GL ι R ≃* GL ι R' := Units.mapEquiv (RingEquiv.mapMatrix e).toMulEquiv

theorem coe_glEquiv (e : R ≃+* R') (g : GL ι R) :
    ((glEquiv e g : GL ι R') : Matrix ι ι R') = (g : Matrix ι ι R).map e := rfl

theorem coe_glEquiv_inv (e : R ≃+* R') (g : GL ι R) :
    (((glEquiv e g)⁻¹ : GL ι R') : Matrix ι ι R') = ((g⁻¹ : GL ι R) : Matrix ι ι R).map e := by
  rw [← map_inv]; rfl

theorem mem_stab_iff (e : R ≃+* R') (s : Set ι) (g : GL ι R) :
    g ∈ stab R s ↔ glEquiv e g ∈ stab R' s := by
  change (∀ r ∉ s, ∀ c ∈ s, _ ∧ _) ↔ (∀ r ∉ s, ∀ c ∈ s, _ ∧ _)
  simp only [coe_glEquiv, coe_glEquiv_inv, Matrix.map_apply, EmbeddingLike.map_eq_zero_iff]

variable {E : Type} [Field E]

theorem mem_kGL_iff (A : Ad E R) (B : Ad E R') (e : R ≃+* R') (hO : ∀ x, x ∈ A.O ↔ e x ∈ B.O)
    (hφ : ∀ w, ∃ w', ∀ x, A.φ w x = B.φ w' (e x)) (hφ' : ∀ w', ∃ w, ∀ x, A.φ w x = B.φ w' (e x)) (g : GL ι R) :
    g ∈ A.kGL ι ↔ glEquiv e g ∈ B.kGL ι := by
  change ((∀ r c, _ ∧ _) ∧ ∀ w, _) ↔ ((∀ r c, _ ∧ _) ∧ ∀ w, _)
  simp only [coe_glEquiv, coe_glEquiv_inv, Matrix.map_apply, hO]
  refine and_congr_right fun _ => ⟨fun h w' => ?_, fun h w => ?_⟩
  · obtain ⟨w, hw⟩ := hφ' w'
    have : ((g : Matrix ι ι R).map e).map (B.φ w') = (g : Matrix ι ι R).map (A.φ w) := by
      ext r c; simp [hw]
    rw [this]; exact h w
  · obtain ⟨w', hw⟩ := hφ w
    have : (g : Matrix ι ι R).map (A.φ w) = ((g : Matrix ι ι R).map e).map (B.φ w') := by
      ext r c; simp [hw]
    rw [this]; exact h w'

theorem iwa_transport (A : Ad E R) (B : Ad E R') (e : R ≃+* R') (hk : ∀ g : GL ι R, g ∈ A.kGL ι ↔ glEquiv e g ∈ B.kGL ι)
    (s : Set ι) (h : Iwa (stab R' s) (B.kGL ι)) : Iwa (stab R s) (A.kGL ι) := by
  intro g
  obtain ⟨p, hp, k, hk', hg⟩ := h (glEquiv e g)
  refine ⟨(glEquiv e).symm p, ?_, (glEquiv e).symm k, ?_, ?_⟩
  · rw [mem_stab_iff e]; simpa using hp
  · rw [hk]; simpa using hk'
  · apply (glEquiv e).injective
    simp [hg]

variable [TopologicalSpace R] [TopologicalSpace R']

theorem continuous_glEquiv (e : R ≃+* R') (h : Continuous e) : Continuous (glEquiv (ι := ι) e) :=
  Continuous.units_map _ (Continuous.matrix_map continuous_id h)

theorem kcpt_transport (A : Ad E R) (B : Ad E R') (e : R ≃+* R') (h1 : Continuous e) (h2 : Continuous e.symm)
    (hk : ∀ g : GL ι R, g ∈ A.kGL ι ↔ glEquiv e g ∈ B.kGL ι) (h : IsCompact (B.kGL ι : Set (GL ι R'))) :
    IsCompact (A.kGL ι : Set (GL ι R)) := by
  let H : GL ι R ≃ₜ GL ι R' :=
    { toEquiv := (glEquiv e).toEquiv
      continuous_toFun := continuous_glEquiv e h1
      continuous_invFun := continuous_glEquiv e.symm h2 }
  have : (A.kGL ι : Set (GL ι R)) = H ⁻¹' (B.kGL ι : Set (GL ι R')) := by
    ext g; exact hk g
  rw [this]
  exact H.isCompact_preimage.2 h

end Transport

section CM

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cA_inclR (σ : E →ₐ[F] E) (x : E) :
    cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := by
  simp [cA, inclR, Algebra.TensorProduct.map_tmul]

theorem cA_cA {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (z : AE F E) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.inductionOn with
  | tmul a x => simp [cA, Algebra.TensorProduct.map_tmul, GlobalTheory.OppLagr.conj_conj h]
  | add x y hx hy => simp [map_add (f := _), hx, hy]

theorem continuous_cA (σ : E →ₐ[F] E) : Continuous (cA σ) := by
  haveI : Module.Finite (AF F) (AE F E) := inferInstance
  exact IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap

theorem cA_mem_intHat (σ : E →ₐ[F] E) {z : AE F E} (hz : z ∈ intHat F E) : cA σ z ∈ intHat F E := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, h1, h2, o, rfl⟩ := hz
    have ho : IsIntegral ℤ (σ (o : E)) := (RingOfIntegers.isIntegral_coe o).map σ
    refine AddSubgroup.subset_closure ⟨a, h1, h2, (⟨σ o, ho⟩ : 𝓞 E), ?_⟩
    rw [map_smul, cA_inclR]
    rfl
  | zero => simp [zero_mem]
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

end CM

theorem cmGood : StdGood → Dict → DictInf → CMGood := by
  intro hS hD hI F E _ _ _ _ _ σ χ c hcm _ hχ hres
  have hs := hS E
  obtain ⟨d1, d2, d3, d4, -⟩ := hD F E
  have hO : ∀ x, x ∈ (adCM σ χ).O ↔ eqv F E x ∈ (adStd E).O := fun x => Iff.rfl
  have hk : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (g : GL ι (AE F E)),
      g ∈ (adCM σ χ).kGL ι ↔ glEquiv (eqv F E) g ∈ (adStd E).kGL ι := fun ι _ _ g =>
    mem_kGL_iff _ _ _ hO (fun w => ⟨w, fun _ => rfl⟩) (fun w => ⟨w, fun _ => rfl⟩) g
  have hu : Continuous (Units.map (eqv F E).toRingHom.toMonoidHom) := Continuous.units_map _ d1
  have hi : ∀ x : Eˣ, Units.map (eqv F E).toRingHom.toMonoidHom (Units.map (inclR (F := F) (AF F)).toMonoidHom x) =
      Units.map (adStd E).i.toMonoidHom x := fun x => Units.ext (d3 x)
  obtain ⟨ξ, hξ⟩ := GlobalTheory.OppLagr.exists_isQuad hcm
  refine ⟨⟨?_, ?_, ?_, ?_, hχ.1, hχ.2, ?_, ?_⟩, cA_cA hcm, continuous_cA σ, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    apply hs.iinj
    change algebraMap E 𝔸[E] x = algebraMap E 𝔸[E] y
    rw [← d3, ← d3]
    exact congrArg _ hxy
  · intro x y
    change (adStd E).lg (Units.map _ (x * y)) = _
    rw [map_mul]
    exact hs.lgmul _ _
  · exact hs.lgcont.comp hu
  · intro x
    exact (congrArg (adStd E).lg (hi x)).trans (hs.lgi x)
  · intro ι _ _
    exact kcpt_transport _ _ (eqv F E) d1 d2 (hk ι) (hs.kcpt ι)
  · intro ι _ _ s
    exact iwa_transport _ _ (eqv F E) (hk ι) s (hs.iwa ι s)
  · intro x hx
    have h1 : finOne F • x ∈ intHat F E := (d4 x).1 hx
    refine (d4 _).2 ?_
    have h2 := cA_mem_intHat σ h1
    rwa [map_smul] at h2
  · intro w x
    exact (hI F E σ hcm).1 w x
  · intro x
    exact ⟨σ x, cA_inclR σ x⟩
  · intro x
    exact ResEtaPow.map_conj hξ hres x

end GlobalTheory.CompanionTheory.RgEisCM
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierJacobiEisenstein
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.CompanionTheory.FJE in
theorem GlobalTheory.CompanionTheory.FJE.fjEis : ZUnfold → ThTwist → FJEis := by
  intro hZ hTw D n ρ p hn M m ψ hψ b₀ hb χ χ' hχ hχ' θ hθ Ω hΩ s f hf hl hs g
  obtain ⟨i1, i2, i3, i4, -⟩ := lattice_Mx D ρ p
  haveI : BorelSpace (Mx D ρ p) := ⟨rfl⟩
  haveI : m.μ.IsAddHaarMeasure := m.hμ.1
  obtain ⟨hcM, hcC⟩ := _root_.GlobalTheory.CompanionTheory.FJE.countable_mat_cosets D ρ p
  have hsum := fun g' => (hZ D n ρ p hn M m ψ hψ b₀ hb χ hχ s f hf hl hs g').1
  have hC := (hZ D n ρ p hn M m ψ hψ b₀ hb χ hχ s f hf hl hs g).2
  obtain ⟨t, ht, hT⟩ := GlobalTheory.T.fourier_jacobi_terms_summable M m ψ hψ b₀ χ s f hl g hC
  have hF : LeftInv (GF D n) (eisS f) := GlobalTheory.Eis.leftInv_cosetSum (_root_.GlobalTheory.CompanionTheory.FJE.leftInv_of_isLaw χ s f hχ hl)
  have hTr := fun q : GlobalTheory.Eis.Cosets (P D p) (GF D p) => GlobalTheory.T.lattice_translation_preserved M ((q.out : GF D p) : G D p) q.out.2
  choose T hT1 hT2 hT3 using hTr

  have hterm := fun (q : GlobalTheory.Eis.Cosets (P D p) (GF D p)) (v : Mx D ρ p × Mx D ρ p) =>
    _root_.GlobalTheory.CompanionTheory.FJE.term_after M m ψ hψ b₀ hb hTw χ' hχ' θ hθ Ω hΩ χ s f hl g ((q.out : GF D p) : G D p) q.out.2 (T q) (hT3 q) v

  set A : GlobalTheory.Eis.Cosets (P D p) (GF D p) → Matrix (Fin ρ) (Fin p) D.host.E → Mx D ρ p × Mx D ρ p → ℂ :=
    fun q η v => Wz M m ψ b₀ f (M.sh (rt η) * M.emb (q.out : GF D p) * (M.nzx 0 v.2 * (M.sh v.1 * g))) with hA
  set Sq : GlobalTheory.Eis.Cosets (P D p) (GF D p) → Mx D ρ p × Mx D ρ p → ℂ := fun q v => ∑' η, A q η v with hSq
  have hAs : ∀ q v, Summable (fun η => ‖A q η v‖) := fun q v =>
    (summable_congr fun η => (hterm q v).1 η).2 (hT q (T q v).1).1
  have hSqle : ∀ q v, ‖Sq q v‖ ≤ t q := fun q v => by
    refine (norm_tsum_le_tsum_norm (hAs q v)).trans ?_
    rw [tsum_congr fun η => (hterm q v).1 η]
    exact (hT q (T q v).1).2
  have hAm : ∀ q η, StronglyMeasurable (A q η) := fun q η =>
    _root_.GlobalTheory.CompanionTheory.FJE.Wz_stronglyMeasurable M m ψ hψ b₀ f hf _ (by
      have h1 : Continuous fun v : Mx D ρ p × Mx D ρ p => M.nzx 0 v.2 :=
        M.nzx_cont.comp (continuous_const.prodMk continuous_snd)
      have h2 : Continuous fun v : Mx D ρ p × Mx D ρ p => M.sh v.1 := M.sh_cont.comp continuous_fst
      exact continuous_const.mul (h1.mul (h2.mul continuous_const)))
  have hSqm : ∀ q, StronglyMeasurable (Sq q) := fun q =>
    GlobalTheory.CompanionTheory.FJE.tsum_meas (fun η => hAm q η) fun v => (hAs q v).of_norm
  set Fz : Mx D ρ p × Mx D ρ p → ℂ := fun v => zc M m ψ b₀ (eisS f) (M.nzx 0 v.2 * (M.sh v.1 * g)) with hFz
  have hq : ∀ v, HasSum (fun q => Sq q v) (Fz v) := fun v =>
    (hsum (M.nzx 0 v.2 * (M.sh v.1 * g))).prod_fiberwise fun q => (hAs q v).of_norm.hasSum
  have hqn : ∀ v, Summable fun q => ‖Sq q v‖ := fun v => .of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => hSqle q v) ht
  have hFzm : StronglyMeasurable Fz := by
    have : Fz = fun v => ∑' q, Sq q v := funext fun v => (hq v).tsum_eq.symm
    rw [this]
    exact GlobalTheory.CompanionTheory.FJE.tsum_meas hSqm fun v => (hqn v).of_norm
  have hFzb : ∀ y x, ‖zc M m ψ b₀ (eisS f) (M.nzx 0 x * (M.sh y * g))‖ ≤ ∑' q, t q := fun y x => by
    have := (hq (y, x)).tsum_eq
    simp only [hFz] at this
    rw [← this]
    exact (norm_tsum_le_tsum_norm (hqn _)).trans ((hqn _).tsum_le_tsum (fun q => hSqle q _) ht)
  have h1 := _root_.GlobalTheory.CompanionTheory.FJE.fj_fold_mean M m ψ hψ b₀ (eisS f) hF g θ hθ (Ω 1) (hΩ.mem 1) _ hFzb hFzm

  have hcont : ∀ h, Continuous (Ω h) := fun h => hΩ.cont.comp (continuous_const.prodMk continuous_id)
  have hsm : ∀ h, StronglyMeasurable (Ω h) := fun h => (hcont h).stronglyMeasurable
  have hbd := fun h => _root_.GlobalTheory.CompanionTheory.FJE.periodisation_bound θ hθ (Ω h) (hΩ.mem h)
  obtain ⟨Bθ, hBθ⟩ := hbd 1
  have hthm : StronglyMeasurable fun v : Mx D ρ p × Mx D ρ p => conj (th ψ b₀ (Ω 1) 0 v.2 v.1) := by
    simp only [th_zero]
    exact Complex.continuous_conj.comp_stronglyMeasurable
      (_root_.GlobalTheory.CompanionTheory.FJE.dsum_stronglyMeasurable ψ hψ b₀ (Ω 1) (hsm 1) fun y => (hBθ y).1)
  have hthb : ∀ v : Mx D ρ p × Mx D ρ p, ‖conj (th ψ b₀ (Ω 1) 0 v.2 v.1)‖ ≤ Bθ := fun v => by
    rw [RCLike.norm_conj, th_zero]
    have hn1 : ∀ ξ : Matrix (Fin ρ) (Fin p) D.host.E, ‖chv ψ b₀ v.2 (rt ξ) * Ω 1 (rt ξ + v.1)‖ = ‖Ω 1 (rt ξ + v.1)‖ := fun ξ => by
      rw [norm_mul, (_root_.GlobalTheory.CompanionTheory.FJE.chv_facts ψ hψ b₀).2.2.1, one_mul]
    refine (norm_tsum_le_tsum_norm ((summable_congr hn1).2 (hBθ v.1).1)).trans ?_
    rw [tsum_congr hn1]
    exact (hBθ v.1).2

  have hI : ∀ q, ∫ v in m.𝓕 ×ˢ m.𝓕, Sq q v * conj (th ψ b₀ (Ω 1) 0 v.2 v.1) ∂(m.μ.prod m.μ) =
      Rsec M m ψ b₀ f g Ω (((q.out : GF D p) : G D p) * 1) := fun q => by
    have hΦm : StronglyMeasurable fun y => Wz M m ψ b₀ f (M.sh y * M.emb (q.out : GF D p) * g) :=
      _root_.GlobalTheory.CompanionTheory.FJE.Wz_stronglyMeasurable M m ψ hψ b₀ f hf _ ((M.sh_cont.mul continuous_const).mul continuous_const)
    obtain ⟨B₂, hB₂⟩ := hbd ((q.out : GF D p) : G D p)
    have e1 : ∀ v, Sq q v * conj (th ψ b₀ (Ω 1) 0 v.2 v.1) =
        Ap ψ b₀ (fun y => Wz M m ψ b₀ f (M.sh y * M.emb (q.out : GF D p) * g)) (Ω ((q.out : GF D p) : G D p)) (T q v) :=
      fun v => (hterm q v).2
    simp only [e1]
    rw [_root_.GlobalTheory.CompanionTheory.FJE.TransportInt.transport_int m (T q) (hT1 q) (hT2 q) _ (fun ξ₁ ξ₂ v => _root_.GlobalTheory.CompanionTheory.FJE.ap_periodic_all ψ hψ b₀ _ _ ξ₁ ξ₂ v),
      _root_.GlobalTheory.CompanionTheory.FJE.fold_parseval m ψ hψ b₀ hb _ _ (t q) B₂ hΦm (hsm _) (fun y => hT q y) hB₂, mul_one]
    rfl

  set ν := (m.μ.prod m.μ).restrict (m.𝓕 ×ˢ m.𝓕) with hν
  have hmass : ν Set.univ = 1 := by
    rw [hν, Measure.restrict_apply_univ, Measure.prod_prod, m.hμ.2.2, one_mul]
  haveI : IsFiniteMeasure ν := ⟨by rw [hmass]; exact ENNReal.one_lt_top⟩
  have hbound : ∀ q v, ‖Sq q v * conj (th ψ b₀ (Ω 1) 0 v.2 v.1)‖ ≤ t q * Bθ := fun q v => by
    rw [norm_mul]
    exact mul_le_mul (hSqle q v) (hthb v) (norm_nonneg _) ((norm_nonneg _).trans (hSqle q v))
  have hint : ∀ q, Integrable (fun v => Sq q v * conj (th ψ b₀ (Ω 1) 0 v.2 v.1)) ν := fun q =>
    Integrable.of_bound ((hSqm q).mul hthm).aestronglyMeasurable (t q * Bθ) (.of_forall (hbound q))
  have hnorm : ∀ q, ∫ v, ‖Sq q v * conj (th ψ b₀ (Ω 1) 0 v.2 v.1)‖ ∂ν ≤ t q * Bθ := fun q => by
    have h2 := norm_integral_le_of_norm_le_const (μ := ν)
      (f := fun v => ‖Sq q v * conj (th ψ b₀ (Ω 1) 0 v.2 v.1)‖) (C := t q * Bθ)
      (.of_forall fun v => by simpa using hbound q v)
    have h3 : ν.real Set.univ = 1 := by simp [Measure.real, hmass]
    rw [h3, mul_one] at h2
    exact (le_abs_self _).trans (by simpa using h2)
  have hfs : Summable fun q => ∫ v, ‖Sq q v * conj (th ψ b₀ (Ω 1) 0 v.2 v.1)‖ ∂ν :=
    .of_nonneg_of_le (fun q => integral_nonneg fun _ => norm_nonneg _) hnorm (ht.mul_right Bθ)
  have hfin2 := hasSum_integral_of_summable_integral_norm hint hfs
  have e : (fun v => ∑' q, Sq q v * conj (th ψ b₀ (Ω 1) 0 v.2 v.1)) =
      fun v => Fz v * conj (th ψ b₀ (Ω 1) 0 v.2 v.1) := funext fun v => by
    rw [tsum_mul_right, (hq v).tsum_eq]
  rw [e] at hfin2
  rw [h1, ← hfin2.tsum_eq, eisS, GlobalTheory.Eis.cosetSum]
  exact tsum_congr fun q => hI q
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableMulInner
section
noncomputable section

open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.RgHeA

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ]
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem integrable_smul_rep {ν : Measure Γ} {τ : Γ → (H →L[ℂ] H)} (hτ : IsU τ) {f : Γ → ℂ} (hf : Integrable f ν) (b : H) :
    Integrable (fun g => f g • τ g b) ν := by
  refine (hf.norm.mul_const ‖b‖).mono' (hf.aestronglyMeasurable.smul (hτ.4 b).aestronglyMeasurable)
    (.of_forall fun g => ?_)
  rw [norm_smul, hτ.norm]

theorem integrable_mul_inner {ν : Measure Γ} {τ : Γ → (H →L[ℂ] H)} (hτ : IsU τ) {f : Γ → ℂ} (hf : Integrable f ν) (a b : H) :
    Integrable (fun g => f g * ⟪a, τ g b⟫_ℂ) ν := by
  refine (hf.norm.mul_const (‖a‖ * ‖b‖)).mono'
    (hf.aestronglyMeasurable.mul (continuous_const.inner (hτ.4 b)).aestronglyMeasurable)
    (.of_forall fun g => ?_)
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc ‖⟪a, τ g b⟫_ℂ‖ ≤ ‖a‖ * ‖τ g b‖ := norm_inner_le_norm _ _
    _ = ‖a‖ * ‖b‖ := by rw [hτ.norm]

def coefOp (ν : Measure Γ) (τ : Γ → (H →L[ℂ] H)) (hτ : IsU τ) (f : Γ → ℂ) (hf : Integrable f ν) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := fun b => ∫ g, f g • τ g b ∂ν
      map_add' := fun x y => by
        rw [← integral_add (integrable_smul_rep hτ hf x) (integrable_smul_rep hτ hf y)]
        simp only [map_add (f := _), smul_add]
      map_smul' := fun c x => by
        simp only [RingHom.id_apply]
        rw [← integral_smul]
        simp only [map_smul, smul_comm c] }
    (∫ g, ‖f g‖ ∂ν) fun b => by
      refine (norm_integral_le_of_norm_le (hf.norm.mul_const ‖b‖) (.of_forall fun g => ?_)).trans_eq ?_
      · rw [norm_smul, hτ.norm]
      · rw [integral_mul_const]

theorem coefOp_apply (ν : Measure Γ) (τ : Γ → (H →L[ℂ] H)) (hτ : IsU τ) (f : Γ → ℂ) (hf : Integrable f ν) (b : H) :
    coefOp ν τ hτ f hf b = ∫ g, f g • τ g b ∂ν := rfl

theorem inner_coefOp (ν : Measure Γ) (τ : Γ → (H →L[ℂ] H)) (hτ : IsU τ) (f : Γ → ℂ) (hf : Integrable f ν) (a b : H) :
    ⟪a, coefOp ν τ hτ f hf b⟫_ℂ = ∫ g, f g * ⟪a, τ g b⟫_ℂ ∂ν := by
  rw [coefOp_apply, ← integral_inner (integrable_smul_rep hτ hf b)]
  simp only [inner_smul_right]

end GlobalTheory.CompanionTheory.RgHeA
end
end

