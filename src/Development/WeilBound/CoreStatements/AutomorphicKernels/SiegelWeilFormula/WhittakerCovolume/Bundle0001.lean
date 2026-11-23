module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.WhitKOfSteps
public import Development.WeilBound.ThetaLifts.LatticeBasics.IsCompactIntV

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.GramZeroLeft
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem om_mem_sch (d : SD σ) (x : d.G) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) : d.om x Φ ∈ d.sch :=
  d.ok.dbl.weil.2.1.pres x Φ hΦ

theorem T_zero (d : SD σ) {Φ : d.Fn} (_hΦ : Φ ∈ d.sch) : d.T Φ 0 = d.l Φ := by
  unfold SD.T
  rw [Matrix.zero_mul]
  congr 1
  funext y
  simp [Darboux.rho, schr]

theorem gram_zero_left (d : SD σ) (Z : Mx F E d.m d.n) : d.gram 0 Z = 0 := by
  simp [SD.gram]

theorem cellFormula : CellFormula := by
  intro hT F E _ _ _ _ _ σ d ν hν ε w hw Φ hΦ g x β hg
  have hΨ : d.om x Φ ∈ d.sch := om_mem_sch d x hΦ
  have hΨ' : d.om g (d.om x Φ) ∈ d.sch := om_mem_sch d g hΨ
  have hW := hT.2.2.1 F E σ d ν hν ε w hw _ hΨ' 0
  have hP := (hT.2.1 F E σ d _ hΨ).1 g β hg
  calc d.sec0 Φ (w * g * x) = d.l (d.om w (d.om g (d.om x Φ))) := by
        show d.l (d.om (w * g * x) Φ) = _
        rw [map_mul, map_mul]
        rfl
    _ = d.T (d.om w (d.om g (d.om x Φ))) 0 := (T_zero d (om_mem_sch d w hΨ')).symm
    _ = ∫ Z, d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram 0 Z)) * d.T (d.om g (d.om x Φ)) Z ∂ν := hW
    _ = _ := by
        congr 1
        funext Z
        rw [gram_zero_left d Z, hP Z]
        simp [SD.tt]

end PositivityTheory.SiegelWeilFormula.KWhit

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.HolValueAtConstMulCpow
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem holValueAt_const_mul_cpow (c : ℂ) {C : ℝ} (hC : 0 < C) (s₀ : ℂ) :
    HolValueAt (fun z => c * (C : ℂ) ^ (z - s₀)) s₀ c := by
  have h := holValueAt_self (h := fun z => c * (C : ℂ) ^ (z - s₀)) (σ := s₀.re - 1) (s₀ := s₀)
    (fun z _ => analyticAt_const.mul (analyticAt_const.cpow (analyticAt_id.sub analyticAt_const)
      (Complex.ofReal_mem_slitPlane.2 hC))) (by linarith)
  convert h using 1
  simp

end PositivityTheory.SiegelWeilFormula.KWhit

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.IsPureTIff
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def toMx {m n : ℕ} (Y : Fin n → Fin m → AF F ⊗[F] E) : Mx F E m n := Matrix.of fun a j => Y j a

def IsPureBy {d : SD σ} (R : RD d) (Φ : d.Fn) (P : InfinitePlace F → PX d.m d.n)
    (gf : ∀ v : HeightOneSpectrum (𝓞 F), (Fin d.m × Fin d.n × Fin 2 → v.adicCompletion F) → ℂ) : Prop :=
  (∀ v, IsLocallyConstant (gf v) ∧ HasCompactSupport (gf v)) ∧
    (∀ᶠ v in cofinite, gf v = Set.indicator {c | ∀ k, c k ∈ v.adicCompletionIntegers F} 1) ∧
    d.T Φ = fun X => (∏ w, fP (P w) (R.loc w X)) * ∏ᶠ v, gf v (fun k => HeckeCharacterZeroLocus.SiegelWeilU.evalV F v (d.crd X k).2)

def Jd (d : SD σ) (η : E) : Matrix (Fin d.m) (Fin d.m) E := (η • d.A.J)ᵀ

def Td {n : ℕ} (η : E) (T₀ : Matrix (Fin n) (Fin n) E) : Matrix (Fin n) (Fin n) E := ((-2 * η) • T₀)ᵀ

structure Rel (d : SD σ) (R : RD d) (x : d.G) (t u : GL (Fin d.n) (AE F E)) (T : nF σ d.Y d.b) (η : E)
    (T₀ : Matrix (Fin d.n) (Fin d.n) E) (hOf : nA σ d.Y d.b → HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n)
    (θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ)) (fr : InfinitePlace F → GL (Fin d.m) ℂ)
    (g : InfinitePlace F → GL (Fin d.n) ℂ) : Prop where
  levi : inFrame d.b x = Matrix.fromBlocks t.1 0 0 u.1
  rat : T.1.1 = incM F T₀
  ne : η ≠ 0
  herm : ∀ i j, σ (η * d.A.J j i) = η * d.A.J i j
  hof : ∀ β, β.1 = -(incM F (Matrix.scalar (Fin d.n) η) * ((hOf β).1 : Mx F E d.n d.n)ᵀ)
  th : ∀ w y, θ w (Algebra.TensorProduct.map (HeckeCharacterZeroLocus.SiegelWeilU.fstA F) (AlgHom.id F E) y) = star (piInf (d.B.emb w) y)
  frc : ∀ w, (fr w).1 = ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • (R.fr w).1.map star
  gc : ∀ w, (g w).1 * ((d.cw w u.1)ᵀ).map star = ((‖(d.B.emb w).1 η‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • 1

def RelEx : Prop := TAll → AuxiliaryPrimeFunction → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (d : SD σ) (R : RD d), ∀ Φ, d.KFin Φ → ∀ P gf, IsPureBy R Φ P gf →
  ∀ x t u, inFrame d.b x = Matrix.fromBlocks t.1 0 0 u.1 → ∀ T : nF σ d.Y d.b, IsND T →
  ∃ (η : E) (T₀ : Matrix (Fin d.n) (Fin d.n) E) (hOf : nA σ d.Y d.b → HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n)
    (θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ)) (fr : InfinitePlace F → GL (Fin d.m) ℂ)
    (g : InfinitePlace F → GL (Fin d.n) ℂ) (l : InfinitePlace F → ℝ) (εs : InfinitePlace F → Fin d.m → Bool)
    (Φg : (Fin d.n → Fin d.m → AF F ⊗[F] E) → ℂ) (Φf : (Fin d.n → Fin d.m → HeckeCharacterZeroLocus.SiegelWeilU.Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin d.n → Fin d.m → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) → ℂ)
    (μ : Measure (Fin d.n → Fin d.m → AF F ⊗[F] E)) (ν : Measure (HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n)),
    Rel d R x t u T η T₀ hOf θ fr g ∧ (∀ Y, Φg Y = d.T Φ (toMx Y * ((u⁻¹ : GL (Fin d.n) (AE F E)).1)ᵀ)) ∧
    (∀ y : Fin d.m → E, HeckeCharacterZeroLocus.SiegelWeilU.hE σ (Jd d η) y y = 0 → y = 0) ∧ (∃ e : InfinitePlace F → Bool, εs = fun i _ => e i) ∧
    HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ ∧ HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ (Jd d η) ∧ (∀ a b, σ (Td η T₀ b a) = Td η T₀ a b) ∧
    (Td η T₀).det ≠ 0 ∧ HeckeCharacterZeroLocus.SiegelWeilU.IsCharAF F d.B.ψ ∧ Gen.IsPlaces σ d.B.ψ θ l ∧ Gen.IsFrames (Jd d η) θ εs fr ∧
    HeckeCharacterZeroLocus.SiegelWeilU.IsPureFin d.bs Φf Φv ∧ HeckeCharacterZeroLocus.SiegelWeilU.IsProdInfFin Φg (Gen.phiInf θ l fr g P) Φf ∧
    HeckeCharacterZeroLocus.SiegelWeilU.SdW F E σ d.m (Jd d η) (AF F) d.B.ψ d.n μ ∧
    HeckeCharacterZeroLocus.SiegelWeilU.SdHerm F E σ (AF F) d.B.ψ d.n ν

def HeightDict : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (d : SD σ) (R : RD d) x t u T η T₀ hOf θ fr g, Rel d R x t u T η T₀ hOf θ fr g →
  ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → ∀ ε w, d.IsW ε w →
  ∃ (lv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin d.n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E))
    (L₁ L₂ : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (Fin d.n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) (C : ℝ), 0 < C ∧
    (∀ v, (lv v).IsAddHaarMeasure) ∧ (∀ v, Gen.IsCO (L₁ v) ∧ Gen.IsCO (L₂ v)) ∧
    (∀ᶠ v in cofinite, (L₁ v : Set (Fin d.n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) = PositivityTheory.PfSWUS.Loc.latO d.bs v ∧
      (L₂ v : Set (Fin d.n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) = PositivityTheory.PfSWUS.Loc.latO d.bs v) ∧
    ∀ β, 0 < Gen.nuA θ g lv L₁ L₂ (hOf β).1 ∧ d.a (w * nb β * x) = C * (Gen.nuA θ g lv L₁ L₂ (hOf β).1)⁻¹

def MeasDict : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (d : SD σ) (R : RD d) x t u T η T₀ hOf θ fr g, Rel d R x t u T η T₀ hOf θ fr g →
  (∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → ∀ ν,
    HeckeCharacterZeroLocus.SiegelWeilU.SdHerm F E σ (AF F) d.B.ψ d.n ν → MeasurableEmbedding hOf ∧ MeasurePreserving hOf lam ν) ∧
  ∀ μ νc, HeckeCharacterZeroLocus.SiegelWeilU.SdW F E σ d.m (Jd d η) (AF F) d.B.ψ d.n μ → d.IsCov νc →
    MeasurableEmbedding (toMx (F := F) (E := E) (m := d.m) (n := d.n)) ∧ MeasurePreserving toMx μ νc

def ThetaDict : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (d : SD σ) (η : E), η ≠ 0 → (∀ i j, σ (η * d.A.J j i) = η * d.A.J i j) →
  ∃ μH 𝓕, HeckeCharacterZeroLocus.SiegelWeilU.IsHaarH F E σ d.m (Jd d η) μH ∧ HeckeCharacterZeroLocus.SiegelWeilU.IsFDH F E σ d.m (Jd d η) μH 𝓕 ∧
    ∀ (T : nF σ d.Y d.b) T₀, T.1.1 = incM F T₀ → ∀ Φ ∈ d.sch,
      d.orb T Φ = HeckeCharacterZeroLocus.SiegelWeilU.meanC μH 𝓕 (HeckeCharacterZeroLocus.SiegelWeilU.thetaS F E σ d.m (Jd d η) (fun Y => d.T Φ (toMx Y))
        {X | HeckeCharacterZeroLocus.SiegelWeilU.gramE σ (Jd d η) X = Td η T₀})

end PositivityTheory.SiegelWeilFormula.KWhit

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.PureGenSubFock
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def schrL {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (w : (κ → R) × (κ → R)) : ((κ → R) → ℂ) →ₗ[ℂ] ((κ → R) → ℂ) where
  toFun := schr ψ w
  map_add' f g := by funext x; simp only [schr, Pi.add_apply]; ring
  map_smul' c f := by funext x; simp only [schr, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem T_eq_lin (d : SD σ) (Φ : d.Fn) (X : Mx F E d.m d.n) :
    d.T Φ X = (d.l ∘ₗ schrL d.B.ψ (d.dd.e (X * (incM F d.b.1.toCols₂)ᵀ))) Φ := rfl

theorem T_sum (d : SD σ) {k : ℕ} (c : Fin k → ℂ) (Φs : Fin k → d.Fn) :
    d.T (∑ i, c i • Φs i) = ∑ i, c i • d.T (Φs i) := by
  funext X
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [T_eq_lin, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply]

theorem T_sub (d : SD σ) (Φ Ψ : d.Fn) : d.T (Φ - Ψ) = d.T Φ - d.T Ψ := by
  funext X
  simp only [T_eq_lin, map_sub, Pi.sub_apply]

def genF {d : SD σ} (R : RD d) (P : InfinitePlace F → PX d.m d.n) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ)
    (X : Mx F E d.m d.n) : ℂ :=
  (∏ w, fP (P w) (R.loc w X)) * g fun k => (d.crd X k).2

def genL {d : SD σ} (R : RD d) (P : InfinitePlace F → PX d.m d.n) :
    ((Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) →ₗ[ℂ] (Mx F E d.m d.n → ℂ) where
  toFun := genF R P
  map_add' f g := by funext X; simp only [genF, Pi.add_apply]; ring
  map_smul' c f := by funext X; simp only [genF, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

def pureGen {d : SD σ} (R : RD d) : Set (Mx F E d.m d.n → ℂ) :=
  {f | ∃ P φ, Dense.Good φ ∧ f = genF R P (Dense.pf φ)}

theorem pureGen_sub_fock {d : SD σ} (R : RD d) : pureGen R ⊆ R.fock := by
  rintro f ⟨P, φ, hφ, rfl⟩
  exact Submodule.subset_span ⟨P, Dense.pf φ, Dense.pf_mem hφ, rfl⟩

theorem fock_le_span {d : SD σ} (R : RD d) : R.fock ≤ Submodule.span ℂ (pureGen R) := by
  show Submodule.span ℂ _ ≤ _
  refine Submodule.span_le.2 ?_
  rintro f ⟨P, g, hg, rfl⟩
  have hg' := Dense.mem_span_pf hg
  have hmap : genL R P g ∈ Submodule.span ℂ (genL R P '' {h | ∃ φ, Dense.Good φ ∧ h = Dense.pf φ}) := by
    rw [Submodule.span_image]
    exact Submodule.mem_map_of_mem hg'
  refine Submodule.span_mono ?_ hmap
  rintro _ ⟨h, ⟨φ, hφ, rfl⟩, rfl⟩
  exact ⟨P, φ, hφ, rfl⟩

theorem isPureT_of {d : SD σ} (R : RD d) (P : InfinitePlace F → PX d.m d.n)
    (φ : ∀ u : HeightOneSpectrum (𝓞 F), (Fin d.m × Fin d.n × Fin 2 → Fv F u) → ℂ) (hφ : Dense.Good φ) (Φ : d.Fn)
    (h : d.T Φ = genF R P (Dense.pf φ)) : IsPureT R Φ := by
  refine ⟨P, φ, fun v => hφ.1 v, ?_, ?_⟩
  · filter_upwards [hφ.2] with v hv
    rw [hv]
    rfl
  · rw [h]
    rfl

theorem pureSpan : PureSpan := by
  intro hT hF hP F E _ _ _ _ _ σ d R Φ hK hfock
  have hspan := fock_le_span R hfock
  obtain ⟨k, c, gs, hgs⟩ := Submodule.mem_span_set'.1 hspan
  have hmem : ∀ i, ∃ Ψ ∈ d.sch, d.T Ψ = (gs i : Mx F E d.m d.n → ℂ) ∧ IsPureT R Ψ := by
    intro i
    obtain ⟨P, φ, hφ, hg⟩ := (gs i).2
    have hfk : (gs i : Mx F E d.m d.n → ℂ) ∈ R.fock := pureGen_sub_fock R (gs i).2
    obtain ⟨Ψ, hΨ, hTΨ⟩ := (hT.1 F E σ d).2.1 _ ((hF F E σ d R).1 hfk)
    exact ⟨Ψ, hΨ, hTΨ, isPureT_of R P φ hφ Ψ (hTΨ.trans hg)⟩
  choose Ψ hΨ hTΨ hpure using hmem
  refine ⟨k, c, Ψ, fun i => ⟨hP F E σ d R (Ψ i) (hΨ i) (by rw [hTΨ i]; exact pureGen_sub_fock R (gs i).2), hpure i⟩, ?_⟩
  have hsum : ∑ i, c i • Ψ i ∈ d.sch := Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hΨ i)
  have hzero : d.T (Φ - ∑ i, c i • Ψ i) = 0 := by
    rw [T_sub, T_sum]
    simp only [hTΨ]
    rw [hgs, sub_self]
  exact sub_eq_zero.1 ((hT.1 F E σ d).2.2 _ (Submodule.sub_mem _ hK.1 hsum) hzero)

end PositivityTheory.SiegelWeilFormula.KWhit

end
end

