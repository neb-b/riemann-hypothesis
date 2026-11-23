module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.Bundle0001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenLowOf
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LowerRankDatum

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.ThInclRInjective
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem th_inclR_injective : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
  Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F)

theorem th_incM_injective {m n : Type} : Function.Injective (incM F : Matrix m n E → Matrix m n (AE F E)) :=
  fun _ _ h => Matrix.map_injective th_inclR_injective h

omit [NumberField E] in
theorem th_inclR_eq (x : E) : HeckeCharacterZeroLocus.SiegelWeilU.inclR (F := F) (AF F) x = inclR (F := F) (E := E) (AF F) x := rfl

omit [NumberField E] in
theorem th_sigR_eq (x : AE F E) : HeckeCharacterZeroLocus.SiegelWeilU.sigR (AF F) σ x = cA σ x := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem th_JR (d : SD σ) (η : E) :
    HeckeCharacterZeroLocus.SiegelWeilU.JR (AF F) (Jd d η) = inclR (F := F) (E := E) (AF F) η • (incM F d.A.J)ᵀ := by
  ext i j
  simp [HeckeCharacterZeroLocus.SiegelWeilU.JR, Jd, incM, th_inclR_eq, Matrix.transpose_apply, map_mul]

theorem th_mem_iff (d : SD σ) {η : E} (hη : η ≠ 0) (g : GL (Fin d.m) (AE F E)) :
    g ∈ UG (cA σ) (incM F d.A.J) ↔ g ∈ HeckeCharacterZeroLocus.SiegelWeilU.HR (AF F) σ (Jd d η) := by
  have hc : IsUnit (inclR (F := F) (E := E) (AF F) η) := (Ne.isUnit hη).map _
  have hm : (g : Matrix (Fin d.m) (Fin d.m) (AE F E)).map (HeckeCharacterZeroLocus.SiegelWeilU.sigR (AF F) σ) =
      (g : Matrix (Fin d.m) (Fin d.m) (AE F E)).map (cA σ) := by
    ext i j; exact th_sigR_eq _
  show (g : Matrix (Fin d.m) (Fin d.m) (AE F E))ᵀ * incM F d.A.J * (g : Matrix (Fin d.m) (Fin d.m) (AE F E)).map (cA σ) =
      incM F d.A.J ↔ HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR (AF F) σ) (g : Matrix (Fin d.m) (Fin d.m) (AE F E)) *
      HeckeCharacterZeroLocus.SiegelWeilU.JR (AF F) (Jd d η) * (g : Matrix (Fin d.m) (Fin d.m) (AE F E)) = HeckeCharacterZeroLocus.SiegelWeilU.JR (AF F) (Jd d η)
  rw [th_JR, HeckeCharacterZeroLocus.SiegelWeilU.cT, hm]
  set L := (g : Matrix (Fin d.m) (Fin d.m) (AE F E))ᵀ * incM F d.A.J * (g : Matrix (Fin d.m) (Fin d.m) (AE F E)).map (cA σ)
  have hL : ((g : Matrix (Fin d.m) (Fin d.m) (AE F E)).map (cA σ))ᵀ *
      (inclR (F := F) (E := E) (AF F) η • (incM F d.A.J)ᵀ) * (g : Matrix (Fin d.m) (Fin d.m) (AE F E)) =
      inclR (F := F) (E := E) (AF F) η • Lᵀ := by
    simp only [L, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  rw [hL]
  constructor
  · intro h; rw [h]
  · intro h
    have h2 := congrArg (fun M => (hc.unit⁻¹ : (AE F E)ˣ) • M) h
    simp only [Units.smul_def, smul_smul] at h2
    have h3 : ((hc.unit⁻¹ : (AE F E)ˣ) : AE F E) * inclR (F := F) (E := E) (AF F) η = 1 := by
      exact hc.val_inv_mul
    rw [h3, one_smul, one_smul] at h2
    have := congrArg Matrix.transpose h2
    simpa using this

def thE (d : SD σ) {η : E} (hη : η ≠ 0) : UA σ d.A.J ≃* HeckeCharacterZeroLocus.SiegelWeilU.HA (AF F) σ (Jd d η) :=
  MulEquiv.subgroupCongr (Subgroup.ext (th_mem_iff d hη))

theorem thE_cont (d : SD σ) {η : E} (hη : η ≠ 0) : Continuous (thE d hη) :=
  continuous_subtype_val.subtype_mk _

theorem thE_symm_cont (d : SD σ) {η : E} (hη : η ≠ 0) : Continuous (thE d hη).symm :=
  continuous_subtype_val.subtype_mk _

theorem th_haar_map {G H : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] [MeasurableMul G] [Group H]
    [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H] (μ : Measure G) [hμ : μ.IsHaarMeasure] (e : G ≃* H)
    (he : Continuous e) (hs : Continuous e.symm) : (μ.map e).IsHaarMeasure := by
  let f : G ≃ᵐ H := (Homeomorph.mk e.toEquiv he hs).toMeasurableEquiv
  have hf : ∀ x, f x = e x := fun _ => rfl
  have hfe : μ.map e = μ.map f := rfl
  have hmeas : ∀ g : G, AEMeasurable (fun x => g * x) μ := by
    intro g
    exact (measurable_const_mul g).aemeasurable
  rw [hfe]
  refine { lt_top_of_isCompact := ?_, map_mul_left_eq_self := ?_, open_pos := ?_ }
  · intro K hK
    rw [MeasurableEquiv.map_apply]
    have : f ⁻¹' K = e.symm '' K := by
      ext x; simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · intro hx; exact ⟨e x, by rw [← hf]; exact hx, e.symm_apply_apply x⟩
      · rintro ⟨y, hy, rfl⟩; rw [hf, e.apply_symm_apply]; exact hy
    rw [this]
    exact (hK.image hs).measure_lt_top
  · intro h
    have hg : AEMeasurable (fun x => e.symm h * x) μ := hmeas _
    have hcomp : (fun y => h * y) ∘ f = f ∘ (fun x => e.symm h * x) := by
      funext x; simp only [Function.comp, hf, map_mul, MulEquiv.apply_symm_apply]
    have hh : AEMeasurable (fun y => h * y) (μ.map f) := by
      rw [aemeasurable_map_equiv_iff, hcomp]
      exact f.measurable.comp_aemeasurable hg
    ext S hS
    rw [Measure.map_apply_of_aemeasurable hh hS, MeasurableEquiv.map_apply, MeasurableEquiv.map_apply]
    have hpre : f ⁻¹' ((fun y => h * y) ⁻¹' S) = (fun x => e.symm h * x) ⁻¹' (f ⁻¹' S) := by
      rw [← Set.preimage_comp, ← Set.preimage_comp, hcomp]
    rw [hpre, ← Measure.map_apply_of_aemeasurable hg (f.measurableSet_preimage.mpr hS),
      map_mul_left_eq_self μ]
  · intro U hU hne'
    rw [MeasurableEquiv.map_apply]
    exact (hU.preimage he).measure_ne_zero μ (hne'.preimage f.surjective)

end PositivityTheory.SiegelWeilFormula.KWhit

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.WhitAtCOneIff
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def WhitAtC (c : ℂ) (d : SD σ) (Φ : d.Fn) (x : d.G) : Prop :=
  ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → ∀ ε w, d.IsW ε w → ∀ T, IsND T →
    HolValueAt (fun z => ∫ β, flat d.a (d.sec0 Φ) (s0 d.m d.n) z (w * nb β * x) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam)
      (s0 d.m d.n) (c * d.orb T (d.om x Φ))

theorem asc_whitAt_iff (c : ℂ) (d : SD σ) (Φ : d.Fn) : PositivityTheory.SiegelWeilFormula.WhitAt c d Φ ↔ ∀ x, WhitAtC c d Φ x := by
  constructor
  · intro h x nb lam 𝓖 hc ε w hw T hT
    exact h nb lam 𝓖 hc ε w hw T hT x
  · intro h nb lam 𝓖 hc ε w hw T hT x
    exact h x nb lam 𝓖 hc ε w hw T hT

def IwaRedC : Prop := TAll → ∀ (c : ℂ) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (d : SD σ) (Q : d.Fn → Prop), (∀ Φ, Q Φ → Φ ∈ d.sch) → (∀ Φ, Q Φ → ∀ k ∈ d.K, Q (d.om k Φ)) →
    (∀ Φ, Q Φ → ∀ x, IsLevi d x → WhitAtC c d Φ x) → ∀ Φ, Q Φ → ∀ x, WhitAtC c d Φ x

def LinRedC : Prop := TAll → ThetaCoef → LamBd → Unfold → SecK → ∀ (c : ℂ) (F E : Type) [Field F] [NumberField F]
  [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ), d.EisAll → ∀ (k : ℕ) (cs : Fin k → ℂ)
    (Φs : Fin k → d.Fn), (∀ i, d.KFin (Φs i)) → ∀ x, (∀ i, WhitAtC c d (Φs i) x) → WhitAtC c d (∑ i, cs i • Φs i) x

def VacSpan : Prop := TAll → FockMem → PolyKFin → VacK → ∀ (F E : Type) [Field F] [NumberField F] [Field E]
  [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (R : RD d), ∀ Φ ∈ d.sch, d.T Φ ∈ R.vac →
    ∃ (k : ℕ) (cs : Fin k → ℂ) (Φs : Fin k → d.Fn),
      (∀ i, d.KFin (Φs i) ∧ d.T (Φs i) ∈ R.vac ∧ ∃ gf, IsPureBy R (Φs i) (fun _ => 1) gf) ∧ Φ = ∑ i, cs i • Φs i

def GenDictX : Prop := TAll → AuxiliaryPrimeFunction → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (d : SD σ) (R : RD d), ∀ Φ, d.KFin Φ → ∀ P gf, IsPureBy R Φ P gf → ∀ x, IsLevi d x →
  ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → ∀ ε w, d.IsW ε w → ∀ T, IsND T →
  ∃ (dd : ℕ) (J : Matrix (Fin d.m) (Fin d.m) E) (T' : Matrix (Fin d.n) (Fin d.n) E) (bs : Module.Basis (Fin dd) F E)
    (ψ : AddChar (AF F) ℂ) (θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ)) (l : InfinitePlace F → ℝ)
    (εs : InfinitePlace F → Fin d.m → Bool) (fr : InfinitePlace F → GL (Fin d.m) ℂ) (g : InfinitePlace F → GL (Fin d.n) ℂ)
    (lv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin d.n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E))
    (L₁ L₂ : ∀ v : HeightOneSpectrum (𝓞 F), AddSubgroup (Fin d.n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E))
    (Φg : (Fin d.n → Fin d.m → AF F ⊗[F] E) → ℂ) (Φf : (Fin d.n → Fin d.m → HeckeCharacterZeroLocus.SiegelWeilU.Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin d.n → Fin d.m → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) → ℂ)
    (μ : Measure (Fin d.n → Fin d.m → AF F ⊗[F] E)) (ν : Measure (HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n)) (c : ℂ) (C : ℝ),
    Gen.Dat0 σ J T' bs ψ θ l εs fr g P lv L₁ L₂ Φg Φf Φv μ ν ∧
    (∀ y : Fin d.m → E, HeckeCharacterZeroLocus.SiegelWeilU.hE σ J y y = 0 → y = 0) ∧ (∃ e : InfinitePlace F → Bool, εs = fun i _ => e i) ∧
    0 < C ∧
    (∃ t : ℝ, ∀ z : ℂ, t < z.re →
      (Integrable (fun β => flat d.a (d.sec0 Φ) (s0 d.m d.n) z (w * nb β * x)) lam →
        Integrable (Gen.whI (AF F) σ J ψ μ Φg (Gen.nuA θ g lv L₁ L₂) (T'.map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (AF F))) z) ν) ∧
      ∫ β, flat d.a (d.sec0 Φ) (s0 d.m d.n) z (w * nb β * x) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam =
        c * (C : ℂ) ^ (z - s0 d.m d.n) *
          ∫ b, Gen.whI (AF F) σ J ψ μ Φg (Gen.nuA θ g lv L₁ L₂) (T'.map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (AF F))) z b ∂ν) ∧
    ∃ μH 𝓕, HeckeCharacterZeroLocus.SiegelWeilU.IsHaarH F E σ d.m J μH ∧ HeckeCharacterZeroLocus.SiegelWeilU.IsFDH F E σ d.m J μH 𝓕 ∧
      d.orb T (d.om x Φ) = c * HeckeCharacterZeroLocus.SiegelWeilU.meanC μH 𝓕
        (HeckeCharacterZeroLocus.SiegelWeilU.thetaS F E σ d.m J Φg {X | HeckeCharacterZeroLocus.SiegelWeilU.gramE σ J X = T'})

def CorePure (ok : ℕ → ℕ → Prop) (vac : Prop) (c : ℂ) : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E]
  [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ) (R : RD d), ok d.m d.n → d.EisAll → ∀ Φ, d.KFin Φ →
    ∀ P gf, IsPureBy R Φ P gf → (vac → P = fun _ => 1) → ∀ x, IsLevi d x → WhitAtC c d Φ x

def CoreX : Prop := ∀ (ok : ℕ → ℕ → Prop) (vac : Prop) (c : ℂ), TAll → AuxiliaryPrimeFunction → SecK → Unfold → Gen.WhitGenX ok vac c →
  GenDictX → CorePure ok vac c

def DictAsmX : Prop := CellFormula → RelEx → HeightDict → MeasDict → ThetaDict → GenDictX

theorem eisAll_of (hS : SecK) (hE : EisWk) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} (d : SD σ) : d.EisAll :=
  fun Φ hΦ => hE F E σ d _ _ (hS F E σ d Φ hΦ)

theorem levi_kfin (ok : ℕ → ℕ → Prop) (vac : Prop) (hv : ¬ vac) (c : ℂ) (hT : TAll) (hTC : ThetaCoef) (hLB : LamBd)
    (hR : RDEx) (hF : FockMem) (hK : KFinPoly) (hPK : PolyKFin) (hS : SecK) (hU : Unfold) (hP : PureSpan)
    (hL : LinRedC) (hC : CorePure ok vac c) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} (d : SD σ) (hok : ok d.m d.n) (hE : d.EisAll) :
    ∀ Φ, d.KFin Φ → ∀ x, IsLevi d x → WhitAtC c d Φ x := by
  intro Φ hΦ x hx
  obtain ⟨R⟩ := hR F E σ d
  obtain ⟨k, cs, Φs, hs, rfl⟩ := hP hT hF hPK F E σ d R Φ hΦ (hK F E σ d R Φ hΦ)
  refine hL hT hTC hLB hU hS c F E σ d hE k cs Φs (fun i => (hs i).1) x (fun i => ?_)
  obtain ⟨P, gf, hpg⟩ := (hs i).2
  exact hC F E σ d R hok hE (Φs i) (hs i).1 P gf hpg (fun h => absurd h hv) x hx

theorem all_kfin (ok : ℕ → ℕ → Prop) (vac : Prop) (hv : ¬ vac) (c : ℂ) (hI : IwaRedC) (hT : TAll) (hTC : ThetaCoef)
    (hLB : LamBd) (hR : RDEx) (hF : FockMem) (hK : KFinPoly) (hPK : PolyKFin) (hS : SecK) (hU : Unfold)
    (hP : PureSpan) (hL : LinRedC) (hC : CorePure ok vac c) (hKK : ∀ (F E : Type) [Field F] [NumberField F] [Field E]
      [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : SD σ), ∀ Φ, d.KFin Φ → ∀ k ∈ d.K, d.KFin (d.om k Φ))
    {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (d : SD σ)
    (hok : ok d.m d.n) (hE : d.EisAll) : ∀ Φ, d.KFin Φ → ∀ x, WhitAtC c d Φ x :=
  hI hT c F E σ d d.KFin (fun Φ h => h.1) (hKK F E σ d)
    (levi_kfin ok vac hv c hT hTC hLB hR hF hK hPK hS hU hP hL hC d hok hE)

def KFinK : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
  (d : SD σ), ∀ Φ, d.KFin Φ → ∀ k ∈ d.K, d.KFin (d.om k Φ)

theorem whitK_of_X (hI : IwaRedC) (hP : PureSpan) (hL : LinRedC) (hC : CoreX) (hD : GenDictX) (hKK : KFinK)
    (hT : TAll) (hA : AuxiliaryPrimeFunction) (hR : RDEx) (hF : FockMem) (hK : KFinPoly) (hS : SecK) (hU : Unfold) (hW : Gen.WhitGenLt)
    (hTC : ThetaCoef) (hLB : LamBd) (hPK : PolyKFin) : WhitK := by
  intro F E _ _ _ _ _ σ d hnm hE Φ hΦ nb lam 𝓖 hc ε w hw T hT' x
  have := all_kfin (fun M n => n < M) False not_false 1 hI hT hTC hLB hR hF hK hPK hS hU hP hL
    (hC _ _ _ hT hA hS hU hW hD) hKK d hnm hE Φ hΦ x nb lam 𝓖 hc ε w hw T hT'
  simpa only [one_mul] using this

theorem whitEq_of_X (hI : IwaRedC) (hP : PureSpan) (hL : LinRedC) (hC : CoreX) (hD : GenDictX) (hKK : KFinK)
    (hT : TAll) (hA : AuxiliaryPrimeFunction) (hR : RDEx) (hF : FockMem) (hK : KFinPoly) (hS : SecK) (hU : Unfold) (hEW : EisWk)
    (hW : Gen.WhitGenEq) (hTC : ThetaCoef) (hLB : LamBd) (hPK : PolyKFin) : WhitEq := by
  intro F E _ _ _ _ _ σ d hmn Φ hΦ
  rw [asc_whitAt_iff]
  exact all_kfin (fun M n => M = n ∧ 1 ≤ M) False not_false 2 hI hT hTC hLB hR hF hK hPK hS hU hP hL
    (hC _ _ _ hT hA hS hU hW hD) hKK d ⟨hmn, d.ok.hm⟩ (eisAll_of hS hEW d) Φ hΦ

theorem whitLow_of_X (hI : IwaRedC) (hV : VacSpan) (hL : LinRedC) (hC : CoreX) (hD : GenDictX) (hVK : VacK)
    (hT : TAll) (hA : AuxiliaryPrimeFunction) (hF : FockMem) (hS : SecK) (hU : Unfold) (hEW : EisWk) (hW : Gen.WhitGenLow)
    (hTC : ThetaCoef) (hLB : LamBd) (hPK : PolyKFin) : WhitLow := by
  intro F E _ _ _ _ _ σ d R hmn Φ hΦ hvac
  rw [asc_whitAt_iff]
  have hE := eisAll_of hS hEW d
  have hcore := hC _ _ _ hT hA hS hU hW hD
  refine hI hT 0 F E σ d (fun Φ => Φ ∈ d.sch ∧ d.T Φ ∈ R.vac) (fun Φ h => h.1)
    (fun Φ h k hk => ⟨d.ok.dbl.weil.2.1.pres k Φ h.1, (hVK F E σ d R).1 Φ h.1 h.2 k hk⟩) ?_ Φ ⟨hΦ, hvac⟩
  intro Φ' h' x hx
  obtain ⟨k, cs, Φs, hs, rfl⟩ := hV hT hF hPK hVK F E σ d R Φ' h'.1 h'.2
  refine hL hT hTC hLB hU hS 0 F E σ d hE k cs Φs (fun i => (hs i).1) x (fun i => ?_)
  obtain ⟨gf, hpg⟩ := (hs i).2.2
  exact hcore F E σ d R ⟨hmn, d.ok.hm⟩ hE (Φs i) (hs i).1 _ gf hpg (fun _ => rfl) x hx

end PositivityTheory.SiegelWeilFormula.KWhit

end
end

