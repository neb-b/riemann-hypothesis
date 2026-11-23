module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.Bundle0001

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.AvgHolPf
section
noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.AStep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

namespace COneB

theorem fcBd' (d : SD σ) {nb lam 𝓖} (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) (T : nF σ d.Y d.b) :
    ∃ K : Set (nA σ d.Y d.b), IsCompact K ∧ ∀ (f : d.G → ℂ) (M : ℝ), (∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) →
      ∀ y : d.G, (∀ β ∈ K, ‖f (nb β * y)‖ ≤ M) → ‖fc d.B.ψ d.b nb lam 𝓖 f T y‖ ≤ M := by
  obtain ⟨hnb, hlam, hfd, hvol⟩ := hc
  have hB := d.ok.good
  have hσ : ∀ a, σ (σ a) = a := kfour.sigma_sigma_of_good hB
  have hb := d.ok.frame
  have hψ := GlobalTheory.StdCharWeilDatum.isCharAF hB.std
  obtain ⟨K, hK, hKc⟩ := kfour.nF_cocompact hσ hb
  refine ⟨K, hK, fun f M hf y hM => ?_⟩
  have hfin : lam 𝓖 < ⊤ := by rw [hvol]; exact ENNReal.one_lt_top
  have hbd : ∀ β, ‖f (nb β * y) * d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1))))‖ ≤ M := by
    intro β
    obtain ⟨γ, hγ, hk⟩ := hKc β
    rw [norm_mul, hψ.2.1 _, mul_one]
    have e : f (nb β * y) = f (nb (γ + β) * y) := by
      rw [kfour.nb_add hnb, mul_assoc, hf _ (kfour.nb_rat hnb γ hγ)]
    rw [e]
    exact hM _ hk
  have h1 := norm_setIntegral_le_of_norm_le_const hfin (fun β _ => hbd β)
  have hr : lam.real 𝓖 = 1 := by simp [Measure.real, hvol]
  rw [hr, mul_one] at h1
  exact h1

end COneB

section Deg

variable (H : Hyps) {d : SD σ} (R : RD d) (L : LD d) (R' : RD L.sd) (hmn : d.m < d.n) (hIH : MainV 2 R') {Φ : d.Fn}
  (hΦ : Φ ∈ d.sch) (hv : d.T Φ ∈ R.vac) {U : Set ℂ} {p : Polynomial ℂ} {Ê : ℂ → d.G → ℂ} {t : ℝ}
  (hE : EData d (d.sec0 Φ) (s0 d.m d.n) (s0 d.m d.n) U p Ê t)


include H hE in
theorem avgHol_pf {nb lam 𝓖} (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) (T : nF σ d.Y d.b) {T' : nF σ L.Y L.b}
    (hT : L.IsSub T T') {uM ν 𝓤} (hu : L.UData uM ν 𝓤) (x : d.G) :
    DifferentiableOn ℂ (fun z => avg d L uM ν 𝓤 nb lam 𝓖 (Ê z) T x) U ∧ ∀ i : ℕ,
      iteratedDeriv i (fun z => avg d L uM ν 𝓤 nb lam 𝓖 (Ê z) T x) (s0 d.m d.n) =
        avg d L uM ν 𝓤 nb lam 𝓖 (fun g => iteratedDeriv i (Ê · g) (s0 d.m d.n)) T x := by
  obtain ⟨hUo, hR, hs, hp, hd, hcont, hinv, hfar⟩ := hE
  have hσ := kfour.sigma_sigma_of_good d.ok.good
  have hb := d.ok.frame
  have hnbc := kfour.nb_continuous hσ hb hc.1
  obtain ⟨iTG, -, -, -⟩ := kfour.doubled_group_topological_properties σ d.Y
  obtain ⟨KN, hKN, hKNb⟩ := COneB.fcBd' d hc T
  obtain ⟨KU, hKU, hKUc⟩ := COneB.ratV_cocompact L
  have huc := COneB.uM_cont L hu
  let C : Set d.G := (fun q : nA σ d.Y d.b × (Fin L.n → AE F E) => nb q.1 * uM q.2 * x) '' (KN ×ˢ KU)
  have hCc : IsCompact C :=
    (hKN.prod hKU).image (((hnbc.comp continuous_fst).mul (huc.comp continuous_snd)).mul continuous_const)
  have hper : ∀ φ : d.G → ℂ, Continuous φ → (∀ γ ∈ rat2 σ d.Y, ∀ g, φ (γ * g) = φ g) → ∀ u, ∃ k ∈ KU,
      fc d.B.ψ d.b nb lam 𝓖 φ T (uM u * x) = fc d.B.ψ d.b nb lam 𝓖 φ T (uM k * x) := by
    intro φ hφ hi u
    obtain ⟨r, hr, hk⟩ := hKUc u
    refine ⟨r + u, hk, ?_⟩
    rw [COneB.uM_add L hu, mul_assoc, (H.fcConj F E σ d L nb lam 𝓖 hc).2 uM ν 𝓤 hu T T' hT φ hφ hi r hr]
  have hbound : ∀ (φ : d.G → ℂ) (M : ℝ), Continuous φ → (∀ γ ∈ rat2 σ d.Y, ∀ g, φ (γ * g) = φ g) →
      (∀ y ∈ C, ‖φ y‖ ≤ M) → ∀ u, ‖fc d.B.ψ d.b nb lam 𝓖 φ T (uM u * x)‖ ≤ M := by
    intro φ M hφ hi hM u
    obtain ⟨k, hk, e⟩ := hper φ hφ hi u
    rw [e]
    refine hKNb φ M hi _ fun β hβ => hM _ ⟨(β, k), ⟨hβ, hk⟩, ?_⟩
    simp only [mul_assoc]
  have hmeas : ∀ φ : d.G → ℂ, Continuous φ → (∀ γ ∈ rat2 σ d.Y, ∀ g, φ (γ * g) = φ g) →
      AEStronglyMeasurable (fun u => fc d.B.ψ d.b nb lam 𝓖 φ T (uM u * x)) ν := by
    intro φ hφ hi
    exact ((fcCont d hc T φ hφ hi).comp (huc.mul continuous_const)).aestronglyMeasurable
  have hfin : ν 𝓤 < ⊤ := by rw [hu.2.2.2]; exact ENNReal.one_lt_top
  have hint : ∀ φ : d.G → ℂ, Continuous φ → (∀ γ ∈ rat2 σ d.Y, ∀ g, φ (γ * g) = φ g) →
      IntegrableOn (fun u => fc d.B.ψ d.b nb lam 𝓖 φ T (uM u * x)) 𝓤 ν := by
    intro φ hφ hi
    obtain ⟨M, hM⟩ := hCc.exists_bound_of_continuousOn hφ.continuousOn
    exact Measure.integrableOn_of_bounded (M := M) hfin.ne (hmeas φ hφ hi)
      (Filter.Eventually.of_forall fun u => hbound φ M hφ hi hM u)
  have hadd : ∀ (a : ℂ) (f f' : d.G → ℂ), Continuous f → Continuous f' → (∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) →
      (∀ γ ∈ rat2 σ d.Y, ∀ g, f' (γ * g) = f' g) → avg d L uM ν 𝓤 nb lam 𝓖 (a • f + f') T x =
        a * avg d L uM ν 𝓤 nb lam 𝓖 f T x + avg d L uM ν 𝓤 nb lam 𝓖 f' T x := by
    intro a f f' hf hf' hi hi'
    simp only [avg]
    have e : (fun u => fc d.B.ψ d.b nb lam 𝓖 (a • f + f') T (uM u * x)) =
        fun u => a * fc d.B.ψ d.b nb lam 𝓖 f T (uM u * x) + fc d.B.ψ d.b nb lam 𝓖 f' T (uM u * x) :=
      funext fun u => (fcAll d hc T (uM u * x)).1 a f f' hf hf' hi hi'
    rw [e, integral_add ((hint f hf hi).const_mul a) (hint f' hf' hi'), integral_const_mul]
  have hbd : ∃ C : Set d.G, IsCompact C ∧ ∀ (f : d.G → ℂ) (M : ℝ), Continuous f →
      (∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) → (∀ y ∈ C, ‖f y‖ ≤ M) → ‖avg d L uM ν 𝓤 nb lam 𝓖 f T x‖ ≤ M := by
    refine ⟨C, hCc, fun f M hf hi hM => ?_⟩
    have h1 := norm_setIntegral_le_of_norm_le_const hfin (fun u _ => hbound f M hf hi hM u)
    have hr : ν.real 𝓤 = 1 := by simp [Measure.real, hu.2.2.2]
    rw [hr, mul_one] at h1
    exact h1
  obtain ⟨hDiff, hComm⟩ := lamDeriv (rat2 σ d.Y) (fun φ => avg d L uM ν 𝓤 nb lam 𝓖 φ T x) hadd hbd U Ê hUo hd hcont hinv
  exact ⟨hDiff, fun i => hComm _ hs i⟩

end Deg

end PositivityTheory.SiegelWeilFormula.AStep

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.FinOneSmulAdr
section
noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.AStep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def adrU [IsTotallyReal F] (w : InfinitePlace F) (τ : ℝ) : (AF F)ˣ :=
  ⟨adr w (Real.exp τ), adr w (Real.exp (-τ)),
    by rw [adr_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, adr_one],
    by rw [adr_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, adr_one]⟩

theorem evInf_adr [IsTotallyReal F] (w u : InfinitePlace F) (r : ℝ) : evInf F u (adr w r) = (adr w r).1 u := rfl

theorem evFin_adr [IsTotallyReal F] (w : InfinitePlace F) (v : HeightOneSpectrum (𝓞 F)) (r : ℝ) :
    evFin F v (adr w r) = 1 := by
  show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (adr w r).2 = 1
  rw [adr_snd, map_one]

theorem norm_adr [IsTotallyReal F] (w u : InfinitePlace F) (r : ℝ) : ‖(adr w r).1 u‖ = |if u = w then r else 1| := by
  rw [← (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding u).norm_map_of_map_zero (map_zero _),
    ext_adr, Complex.norm_real, Real.norm_eq_abs]

theorem piInf_adr (h : IsCMExt F E σ) (τ' : ∀ w : InfinitePlace F, EmbOver E w) (w u : InfinitePlace F) (r : ℝ) :
    haveI := h.1
    piInf (τ' u) (algebraMap (AF F) (AE F E) (adr w r)) = ((if u = w then r else 1 : ℝ) : ℂ) := by
  haveI := h.1
  show GlobalTheory.AdelicU.infEmb (τ' u) (GlobalTheory.AdelicU.compInf F E u (algebraMap (AF F) (AE F E) (adr w r))) = _
  rw [Algebra.TensorProduct.algebraMap_apply]
  show GlobalTheory.AdelicU.infEmb (τ' u)
    (Algebra.TensorProduct.map (GlobalTheory.AdelicU.evInf F u) (AlgHom.id F E) (adr w r ⊗ₜ[F] (1 : E))) = _
  rw [Algebra.TensorProduct.map_tmul, evInf_adr, AlgHom.id_apply]
  simp only [GlobalTheory.AdelicU.infEmb, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one]
  exact ext_adr w u r

theorem finOne_smul_adr (h : IsCMExt F E σ) (w : InfinitePlace F) (r : ℝ) :
    haveI := h.1
    finOne F • algebraMap (AF F) (AE F E) (adr w r) = finOne F • (1 : AE F E) := by
  haveI := h.1
  rw [Algebra.smul_def, Algebra.smul_def, ← map_mul, finOne_adr, mul_one]

theorem absE_adrU (h : IsCMExt F E σ) (w : InfinitePlace F) (τ : ℝ) :
    haveI := h.1
    ((absE F E (Units.map (algebraMap (AF F) (AE F E)).toMonoidHom (adrU w τ)) : ℝ≥0) : ℝ) = Real.exp (2 * τ) := by
  haveI := h.1
  have hfin : ∀ v, GlobalTheory.Doubling.absEv F E v (GlobalTheory.Doubling.unitFin F E v
      (Units.map (algebraMap (AF F) (AE F E)).toMonoidHom (adrU w τ))) = 1 := by
    intro v
    have h1 : GlobalTheory.Doubling.unitFin F E v
        (Units.map (algebraMap (AF F) (AE F E)).toMonoidHom (adrU w τ)) = 1 := by
      apply Units.ext
      show GlobalTheory.AdelicU.compFin F E v (algebraMap (AF F) (AE F E) (adr w (Real.exp τ))) = 1
      rw [Algebra.TensorProduct.algebraMap_apply]
      show Algebra.TensorProduct.map (GlobalTheory.AdelicU.evFin F v) (AlgHom.id F E)
        (adr w (Real.exp τ) ⊗ₜ[F] (1 : E)) = 1
      rw [Algebra.TensorProduct.map_tmul, evFin_adr, AlgHom.id_apply, ← Algebra.TensorProduct.one_def]
    rw [h1, map_one]
  have hinf : ∀ u, (GlobalTheory.Doubling.absEw F E u (GlobalTheory.Doubling.unitInf F E u
      (Units.map (algebraMap (AF F) (AE F E)).toMonoidHom (adrU w τ))) : ℝ) =
      |if u = w then Real.exp τ else 1| ^ 2 := by
    intro u
    have hval : ((GlobalTheory.Doubling.unitInf F E u
        (Units.map (algebraMap (AF F) (AE F E)).toMonoidHom (adrU w τ)) : (TensorProduct F u.Completion E)ˣ) :
          TensorProduct F u.Completion E) =
        algebraMap u.Completion (TensorProduct F u.Completion E) ((adr w (Real.exp τ)).1 u) := by
      show GlobalTheory.AdelicU.compInf F E u (algebraMap (AF F) (AE F E) (adr w (Real.exp τ))) = _
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply]
      show Algebra.TensorProduct.map (GlobalTheory.AdelicU.evInf F u) (AlgHom.id F E)
        (adr w (Real.exp τ) ⊗ₜ[F] (1 : E)) = _
      rw [Algebra.TensorProduct.map_tmul, evInf_adr, AlgHom.id_apply]
      rfl
    have hmult : u.mult = 1 := by
      rw [NumberField.InfinitePlace.mult, if_pos (NumberField.IsTotallyReal.isReal u)]
    show ((‖Algebra.norm u.Completion ((GlobalTheory.Doubling.unitInf F E u
        (Units.map (algebraMap (AF F) (AE F E)).toMonoidHom (adrU w τ)) : (TensorProduct F u.Completion E)ˣ) :
          TensorProduct F u.Completion E)‖₊ ^ u.mult : ℝ≥0) : ℝ) = _
    rw [hval, hmult, pow_one, Algebra.norm_algebraMap, Module.finrank_baseChange, h.2.2.1, coe_nnnorm,
      norm_pow, norm_adr]
  show (((∏ u, GlobalTheory.Doubling.absEw F E u (GlobalTheory.Doubling.unitInf F E u
      (Units.map (algebraMap (AF F) (AE F E)).toMonoidHom (adrU w τ)))) *
      ∏ᶠ v, GlobalTheory.Doubling.absEv F E v (GlobalTheory.Doubling.unitFin F E v
      (Units.map (algebraMap (AF F) (AE F E)).toMonoidHom (adrU w τ))) : ℝ≥0) : ℝ) = _
  rw [finprod_eq_one_of_forall_eq_one hfin, mul_one, NNReal.coe_prod, Finset.prod_eq_single w]
  · rw [hinf, if_pos rfl, Real.abs_exp, sq, ← Real.exp_add, two_mul]
  · intro b _ hb
    rw [hinf, if_neg hb, abs_one, one_pow]
  · intro hw
    exact absurd (Finset.mem_univ w) hw

theorem chi_adrU (d : SD σ) (w : InfinitePlace F) (τ : ℝ) :
    haveI := d.cm.1
    (d.χ (Units.map (algebraMap (AF F) (AE F E)).toMonoidHom (adrU w τ)) : ℂ) = 1 := by
  haveI := d.cm.1
  have hmem : adrU w τ ∈ (Units.map (Algebra.norm (AF F) (S := AE F E))).range := by
    refine ⟨Units.map (algebraMap (AF F) (AE F E)).toMonoidHom (adrU w (τ / 2)), ?_⟩
    apply Units.ext
    show Algebra.norm (AF F) (algebraMap (AF F) (TensorProduct F (AF F) E) (adr w (Real.exp (τ / 2)))) =
      adr w (Real.exp τ)
    rw [Algebra.norm_algebraMap_of_basis (Algebra.TensorProduct.basis (AF F) d.bs), Fintype.card_fin, pow_two,
      adr_mul, ← Real.exp_add, add_halves]
  have h2 := d.ok.res (adrU w τ)
  split_ifs at h2 with hc
  · exact h2
  · exact absurd (Subgroup.mem_sup_right hmem) hc

end PositivityTheory.SiegelWeilFormula.AStep

end
end

