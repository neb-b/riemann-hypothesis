module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0033
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.ParabolicLowerBlockZero
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.Bundle0001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitCutX
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def WhitAtC_k (c : ℂ) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Φ : d.Fn) (x : d.G) : Prop :=
  ∀ nb lam 𝓖, CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖 → ∀ ε w, d.IsW ε w → ∀ T, IsND T →
    HolValueAt (fun z => ∫ β, flat d.a (d.sec0 Φ) (s0 d.m d.n) z (w * nb β * x) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam)
      (s0 d.m d.n) (c * d.orb T (d.om x Φ))
theorem asc_whitAt_iff_k (c : ℂ) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Φ : d.Fn) : _root_.PositivityTheory.SiegelWeilFormula.WhitAt_k c d Φ ↔ ∀ x, _root_.PositivityTheory.SiegelWeilFormula.KWhit.WhitAtC_k c d Φ x := by
  constructor
  · intro h x nb lam 𝓖 hc ε w hw T hT
    exact h nb lam 𝓖 hc ε w hw T hT x
  · intro h nb lam 𝓖 hc ε w hw T hT x
    exact h x nb lam 𝓖 hc ε w hw T hT
def IwaRedC_k : Prop := _root_.PositivityTheory.SiegelWeilFormula.TAll_k → ∀ (c : ℂ) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Q : d.Fn → Prop), (∀ Φ, Q Φ → Φ ∈ d.sch) → (∀ Φ, Q Φ → ∀ k ∈ d.K, Q (d.om k Φ)) →
    (∀ Φ, Q Φ → ∀ x, _root_.PositivityTheory.SiegelWeilFormula.KWhit.IsLevi_k d x → _root_.PositivityTheory.SiegelWeilFormula.KWhit.WhitAtC_k c d Φ x) → ∀ Φ, Q Φ → ∀ x, _root_.PositivityTheory.SiegelWeilFormula.KWhit.WhitAtC_k c d Φ x
def LinRedC_k : Prop := _root_.PositivityTheory.SiegelWeilFormula.TAll_k → _root_.PositivityTheory.SiegelWeilFormula.ThetaCoef_k → _root_.PositivityTheory.SiegelWeilFormula.LamBd_k → _root_.PositivityTheory.SiegelWeilFormula.Unfold_k → _root_.PositivityTheory.SiegelWeilFormula.SecK_k → ∀ (c : ℂ) (F E : Type) [Field F] [NumberField F]
  [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), d.EisAll → ∀ (k : ℕ) (cs : Fin k → ℂ)
    (Φs : Fin k → d.Fn), (∀ i, d.KFin (Φs i)) → ∀ x, (∀ i, _root_.PositivityTheory.SiegelWeilFormula.KWhit.WhitAtC_k c d (Φs i) x) → _root_.PositivityTheory.SiegelWeilFormula.KWhit.WhitAtC_k c d (∑ i, cs i • Φs i) x
def VacSpan_k : Prop := _root_.PositivityTheory.SiegelWeilFormula.TAll_k → _root_.PositivityTheory.SiegelWeilFormula.FockMem_k → _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k → _root_.PositivityTheory.SiegelWeilFormula.VacK_k → ∀ (F E : Type) [Field F] [NumberField F] [Field E]
  [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), ∀ Φ ∈ d.sch, d.T Φ ∈ R.vac →
    ∃ (k : ℕ) (cs : Fin k → ℂ) (Φs : Fin k → d.Fn),
      (∀ i, d.KFin (Φs i) ∧ d.T (Φs i) ∈ R.vac ∧ ∃ gf, _root_.PositivityTheory.SiegelWeilFormula.KWhit.IsPureBy_k R (Φs i) (fun _ => 1) gf) ∧ Φ = ∑ i, cs i • Φs i
def GenDictX_k : Prop := _root_.PositivityTheory.SiegelWeilFormula.TAll_k → _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), ∀ Φ, d.KFin Φ → ∀ P gf, _root_.PositivityTheory.SiegelWeilFormula.KWhit.IsPureBy_k R Φ P gf → ∀ x, _root_.PositivityTheory.SiegelWeilFormula.KWhit.IsLevi_k d x →
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
def CorePure_k (ok : ℕ → ℕ → Prop) (vac : Prop) (c : ℂ) : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E]
  [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d), ok d.m d.n → d.EisAll → ∀ Φ, d.KFin Φ →
    ∀ P gf, _root_.PositivityTheory.SiegelWeilFormula.KWhit.IsPureBy_k R Φ P gf → (vac → P = fun _ => 1) → ∀ x, _root_.PositivityTheory.SiegelWeilFormula.KWhit.IsLevi_k d x → _root_.PositivityTheory.SiegelWeilFormula.KWhit.WhitAtC_k c d Φ x
def CoreX_k : Prop := ∀ (ok : ℕ → ℕ → Prop) (vac : Prop) (c : ℂ), _root_.PositivityTheory.SiegelWeilFormula.TAll_k → _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties → _root_.PositivityTheory.SiegelWeilFormula.SecK_k → _root_.PositivityTheory.SiegelWeilFormula.Unfold_k → Gen.WhitGenX ok vac c →
  _root_.PositivityTheory.SiegelWeilFormula.KWhit.GenDictX_k → _root_.PositivityTheory.SiegelWeilFormula.KWhit.CorePure_k ok vac c
def DictAsmX_k : Prop := _root_.PositivityTheory.SiegelWeilFormula.KWhit.CellFormula_k → _root_.PositivityTheory.SiegelWeilFormula.KWhit.RelEx_k → _root_.PositivityTheory.SiegelWeilFormula.KWhit.HeightDict_k → _root_.PositivityTheory.SiegelWeilFormula.KWhit.MeasDict_k → _root_.PositivityTheory.SiegelWeilFormula.KWhit.ThetaDict_k → _root_.PositivityTheory.SiegelWeilFormula.KWhit.GenDictX_k
theorem eisAll_of_k (hS : _root_.PositivityTheory.SiegelWeilFormula.SecK_k) (hE : _root_.PositivityTheory.SiegelWeilFormula.EisWk_k) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : d.EisAll :=
  fun Φ hΦ => hE F E σ d _ _ (hS F E σ d Φ hΦ)
theorem levi_kfin_k (ok : ℕ → ℕ → Prop) (vac : Prop) (hv : ¬ vac) (c : ℂ) (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hTC : _root_.PositivityTheory.SiegelWeilFormula.ThetaCoef_k) (hLB : _root_.PositivityTheory.SiegelWeilFormula.LamBd_k)
    (hR : _root_.PositivityTheory.SiegelWeilFormula.RDEx_k) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (hK : _root_.PositivityTheory.SiegelWeilFormula.KFinPoly_k) (hPK : _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k) (hS : _root_.PositivityTheory.SiegelWeilFormula.SecK_k) (hU : _root_.PositivityTheory.SiegelWeilFormula.Unfold_k) (hP : _root_.PositivityTheory.SiegelWeilFormula.KWhit.PureSpan_k)
    (hL : _root_.PositivityTheory.SiegelWeilFormula.KWhit.LinRedC_k) (hC : _root_.PositivityTheory.SiegelWeilFormula.KWhit.CorePure_k ok vac c) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (hok : ok d.m d.n) (hE : d.EisAll) :
    ∀ Φ, d.KFin Φ → ∀ x, _root_.PositivityTheory.SiegelWeilFormula.KWhit.IsLevi_k d x → _root_.PositivityTheory.SiegelWeilFormula.KWhit.WhitAtC_k c d Φ x := by
  intro Φ hΦ x hx
  obtain ⟨R⟩ := hR F E σ d
  obtain ⟨k, cs, Φs, hs, rfl⟩ := hP hT hF hPK F E σ d R Φ hΦ (hK F E σ d R Φ hΦ)
  refine hL hT hTC hLB hU hS c F E σ d hE k cs Φs (fun i => (hs i).1) x (fun i => ?_)
  obtain ⟨P, gf, hpg⟩ := (hs i).2
  exact hC F E σ d R hok hE (Φs i) (hs i).1 P gf hpg (fun h => absurd h hv) x hx
theorem all_kfin_k (ok : ℕ → ℕ → Prop) (vac : Prop) (hv : ¬ vac) (c : ℂ) (hI : _root_.PositivityTheory.SiegelWeilFormula.KWhit.IwaRedC_k) (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hTC : _root_.PositivityTheory.SiegelWeilFormula.ThetaCoef_k)
    (hLB : _root_.PositivityTheory.SiegelWeilFormula.LamBd_k) (hR : _root_.PositivityTheory.SiegelWeilFormula.RDEx_k) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (hK : _root_.PositivityTheory.SiegelWeilFormula.KFinPoly_k) (hPK : _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k) (hS : _root_.PositivityTheory.SiegelWeilFormula.SecK_k) (hU : _root_.PositivityTheory.SiegelWeilFormula.Unfold_k)
    (hP : _root_.PositivityTheory.SiegelWeilFormula.KWhit.PureSpan_k) (hL : _root_.PositivityTheory.SiegelWeilFormula.KWhit.LinRedC_k) (hC : _root_.PositivityTheory.SiegelWeilFormula.KWhit.CorePure_k ok vac c) (hKK : ∀ (F E : Type) [Field F] [NumberField F] [Field E]
      [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∀ Φ, d.KFin Φ → ∀ k ∈ d.K, d.KFin (d.om k Φ))
    {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
    (hok : ok d.m d.n) (hE : d.EisAll) : ∀ Φ, d.KFin Φ → ∀ x, _root_.PositivityTheory.SiegelWeilFormula.KWhit.WhitAtC_k c d Φ x :=
  hI hT c F E σ d d.KFin (fun Φ h => h.1) (hKK F E σ d)
    (_root_.PositivityTheory.SiegelWeilFormula.KWhit.levi_kfin_k ok vac hv c hT hTC hLB hR hF hK hPK hS hU hP hL hC d hok hE)
def KFinK_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
  (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∀ Φ, d.KFin Φ → ∀ k ∈ d.K, d.KFin (d.om k Φ)
theorem whitK_of_X_k (hI : _root_.PositivityTheory.SiegelWeilFormula.KWhit.IwaRedC_k) (hP : _root_.PositivityTheory.SiegelWeilFormula.KWhit.PureSpan_k) (hL : _root_.PositivityTheory.SiegelWeilFormula.KWhit.LinRedC_k) (hC : _root_.PositivityTheory.SiegelWeilFormula.KWhit.CoreX_k) (hD : _root_.PositivityTheory.SiegelWeilFormula.KWhit.GenDictX_k) (hKK : _root_.PositivityTheory.SiegelWeilFormula.KWhit.KFinK_k)
    (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hR : _root_.PositivityTheory.SiegelWeilFormula.RDEx_k) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (hK : _root_.PositivityTheory.SiegelWeilFormula.KFinPoly_k) (hS : _root_.PositivityTheory.SiegelWeilFormula.SecK_k) (hU : _root_.PositivityTheory.SiegelWeilFormula.Unfold_k) (hW : Gen.WhitGenLt)
    (hTC : _root_.PositivityTheory.SiegelWeilFormula.ThetaCoef_k) (hLB : _root_.PositivityTheory.SiegelWeilFormula.LamBd_k) (hPK : _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k) : _root_.PositivityTheory.SiegelWeilFormula.WhitK_k := by
  intro F E _ _ _ _ _ σ d hnm hE Φ hΦ nb lam 𝓖 hc ε w hw T hT' x
  have := _root_.PositivityTheory.SiegelWeilFormula.KWhit.all_kfin_k (fun M n => n < M) False not_false 1 hI hT hTC hLB hR hF hK hPK hS hU hP hL
    (hC _ _ _ hT hA hS hU hW hD) hKK d hnm hE Φ hΦ x nb lam 𝓖 hc ε w hw T hT'
  simpa only [one_mul] using this
theorem whitEq_of_X_k (hI : _root_.PositivityTheory.SiegelWeilFormula.KWhit.IwaRedC_k) (hP : _root_.PositivityTheory.SiegelWeilFormula.KWhit.PureSpan_k) (hL : _root_.PositivityTheory.SiegelWeilFormula.KWhit.LinRedC_k) (hC : _root_.PositivityTheory.SiegelWeilFormula.KWhit.CoreX_k) (hD : _root_.PositivityTheory.SiegelWeilFormula.KWhit.GenDictX_k) (hKK : _root_.PositivityTheory.SiegelWeilFormula.KWhit.KFinK_k)
    (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hR : _root_.PositivityTheory.SiegelWeilFormula.RDEx_k) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (hK : _root_.PositivityTheory.SiegelWeilFormula.KFinPoly_k) (hS : _root_.PositivityTheory.SiegelWeilFormula.SecK_k) (hU : _root_.PositivityTheory.SiegelWeilFormula.Unfold_k) (hEW : _root_.PositivityTheory.SiegelWeilFormula.EisWk_k)
    (hW : Gen.WhitGenEq) (hTC : _root_.PositivityTheory.SiegelWeilFormula.ThetaCoef_k) (hLB : _root_.PositivityTheory.SiegelWeilFormula.LamBd_k) (hPK : _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k) : _root_.PositivityTheory.SiegelWeilFormula.WhitEq_k := by
  intro F E _ _ _ _ _ σ d hmn Φ hΦ
  rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.asc_whitAt_iff_k]
  exact _root_.PositivityTheory.SiegelWeilFormula.KWhit.all_kfin_k (fun M n => M = n ∧ 1 ≤ M) False not_false 2 hI hT hTC hLB hR hF hK hPK hS hU hP hL
    (hC _ _ _ hT hA hS hU hW hD) hKK d ⟨hmn, d.ok.hm⟩ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.eisAll_of_k hS hEW d) Φ hΦ
theorem whitLow_of_X_k (hI : _root_.PositivityTheory.SiegelWeilFormula.KWhit.IwaRedC_k) (hV : _root_.PositivityTheory.SiegelWeilFormula.KWhit.VacSpan_k) (hL : _root_.PositivityTheory.SiegelWeilFormula.KWhit.LinRedC_k) (hC : _root_.PositivityTheory.SiegelWeilFormula.KWhit.CoreX_k) (hD : _root_.PositivityTheory.SiegelWeilFormula.KWhit.GenDictX_k) (hVK : _root_.PositivityTheory.SiegelWeilFormula.VacK_k)
    (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (hS : _root_.PositivityTheory.SiegelWeilFormula.SecK_k) (hU : _root_.PositivityTheory.SiegelWeilFormula.Unfold_k) (hEW : _root_.PositivityTheory.SiegelWeilFormula.EisWk_k) (hW : Gen.WhitGenLow)
    (hTC : _root_.PositivityTheory.SiegelWeilFormula.ThetaCoef_k) (hLB : _root_.PositivityTheory.SiegelWeilFormula.LamBd_k) (hPK : _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k) : _root_.PositivityTheory.SiegelWeilFormula.WhitLow_k := by
  intro F E _ _ _ _ _ σ d R hmn Φ hΦ hvac
  rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.asc_whitAt_iff_k]
  have hE := _root_.PositivityTheory.SiegelWeilFormula.KWhit.eisAll_of_k hS hEW d
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
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitIwa
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem incM_mul_inv_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : incM F d.b.1 * incM F (d.b⁻¹).1 = 1 := by
  simp only [incM, ← Matrix.map_mul, Units.mul_inv]
  exact Matrix.map_one _ (map_zero _) (map_one _)
theorem incM_inv_mul_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : incM F (d.b⁻¹).1 * incM F d.b.1 = 1 := by
  simp only [incM, ← Matrix.map_mul, Units.inv_mul]
  exact Matrix.map_one _ (map_zero _) (map_one _)
theorem inFrame_mul_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (x y : d.G) : inFrame d.b (x * y) = inFrame d.b x * inFrame d.b y := by
  have h1 := _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d
  have e : mat2 (x * y) = mat2 x * mat2 y := rfl
  simp only [inFrame, e]
  calc incM F (d.b⁻¹).1 * (mat2 x * mat2 y) * incM F d.b.1
      = incM F (d.b⁻¹).1 * mat2 x * (incM F d.b.1 * incM F (d.b⁻¹).1) * mat2 y * incM F d.b.1 := by
        rw [h1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]
theorem matrixRep_eq_frameConj_inFrame (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (x : d.G) : mat2 x = incM F d.b.1 * inFrame d.b x * incM F (d.b⁻¹).1 := by
  simp only [inFrame, ← Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d, Matrix.one_mul]
  rw [Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d, Matrix.mul_one]
theorem inFrame_injective_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : Function.Injective (inFrame (σ := σ) (Y := d.Y) d.b) := by
  intro x y h
  have : mat2 x = mat2 y := by rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.matrixRep_eq_frameConj_inFrame d x, _root_.PositivityTheory.SiegelWeilFormula.KWhit.matrixRep_eq_frameConj_inFrame d y, h]
  exact Subtype.ext (Units.ext this)
theorem om_mem_sch_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (g : d.G) {Φ : d.Fn} (h : Φ ∈ d.sch) : d.om g Φ ∈ d.sch :=
  d.ok.dbl.weil.2.1.pres g Φ h
theorem constantTerm_mul_right (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Φ : d.Fn) (g k : d.G) : d.sec0 Φ (g * k) = d.sec0 (d.om k Φ) g := by
  simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.sec0, map_mul, Module.End.mul_apply]
theorem a_mul_K_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (g k : d.G) (hk : k ∈ d.K) : d.a (g * k) = d.a g := by
  obtain ⟨p, t, hp, k', hk', rfl⟩ := d.ok.hgt.iwa g
  rw [mul_assoc, d.ok.hgt.val p t hp _ (d.K.mul_mem hk' hk), d.ok.hgt.val p t hp _ hk']
theorem kfin_om_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {Φ : d.Fn} (hΦ : d.KFin Φ) {k : d.G} (hk : k ∈ d.K) : d.KFin (d.om k Φ) := by
  refine ⟨_root_.PositivityTheory.SiegelWeilFormula.KWhit.om_mem_sch_k d k hΦ.1, ?_⟩
  have hfd : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : d.K => d.om k.1 Φ)) := hΦ.2
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun k : d.K => d.om k.1 Φ))
    (Submodule.span_le.2 ?_)
  rintro _ ⟨k', rfl⟩
  refine Submodule.subset_span ⟨⟨k'.1 * k, d.K.mul_mem k'.2 hk⟩, ?_⟩
  simp [map_mul, Module.End.mul_apply]
section Forms
variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
end Forms
theorem frame_form_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : ∃ C' : Matrix (Fin d.n) (Fin d.n) (AE F E),
    (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ) = Matrix.fromBlocks 0 1 C' 0 := by
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  refine ⟨incM F (((ε : ℤ) : E) • (1 : Matrix (Fin d.n) (Fin d.n) E)), ?_⟩
  have e1 : (incM F d.b.1).map (cA σ) = incM F (d.b.1.map σ) := by
    ext i j
    simp [incM, cA, inclR, Algebra.TensorProduct.map_tmul]
  have e2 : dbl (incM F d.Y.J) = incM F (dbl d.Y.J) := by
    simp [dbl, incM, Matrix.fromBlocks_map, Matrix.map_neg]
  have key : incM F (d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ) =
      (incM F d.b.1)ᵀ * incM F (dbl d.Y.J) * incM F (d.b.1.map σ) := by
    simp only [incM, Matrix.map_mul, Matrix.transpose_map]
  rw [e1, e2, ← key, hε]
  simp [incM, Matrix.fromBlocks_map]
theorem parabolic_lowerLeft_block_zero (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (p : d.G) (t : GL (Fin d.n) (AE F E)) (hp : IsPar p t) :
    (inFrame d.b p).toBlocks₂₁ = 0 := by
  obtain ⟨-, tb, htb⟩ := d.ok.frame
  let E1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E) := Matrix.fromRows 1 0
  let DC : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E) := diagCols (Fin d.n)
  have htb' : d.b.1.toCols₁ = (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) * tb.1 := htb
  have hp' : mat2 p * DC = DC * t.1 := hp
  have hcol : ∀ M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E), M * E1 = M.toCols₁ := by
    intro M
    ext i j
    simp [E1, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Matrix.toCols₁]
  have h1 : incM F d.b.1 * E1 = incM F (d.b.1.toCols₁) := by
    rw [hcol]
    ext i j
    rfl
  have h2 : incM F ((diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) * tb.1) = DC * incM F tb.1 := by
    rw [incM_mul']
    congr 1
    ext i j
    cases i <;> simp [DC, diagCols, incM, Matrix.one_apply, apply_ite] <;> split_ifs <;> simp_all
  have hb : incM F d.b.1 * E1 = DC * incM F tb.1 := h1.trans ((congrArg (incM F) htb').trans h2)
  have hTb : incM F tb.1 * incM F (tb⁻¹).1 = 1 := by
    rw [← incM_mul', Units.mul_inv]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hBB : incM F (d.b⁻¹).1 * incM F d.b.1 = 1 := _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d
  have hdc : DC = incM F d.b.1 * E1 * incM F (tb⁻¹).1 := by
    rw [hb, Matrix.mul_assoc, hTb, Matrix.mul_one]
  have key : inFrame d.b p * E1 = E1 * (incM F (tb⁻¹).1 * t.1 * incM F tb.1) := by
    have e0 : inFrame d.b p = incM F (d.b⁻¹).1 * mat2 p * incM F d.b.1 := rfl
    calc inFrame d.b p * E1 = incM F (d.b⁻¹).1 * (mat2 p * (incM F d.b.1 * E1)) := by
          rw [e0]; simp only [Matrix.mul_assoc]
      _ = incM F (d.b⁻¹).1 * ((mat2 p * DC) * incM F tb.1) := by
          rw [hb, Matrix.mul_assoc]
      _ = incM F (d.b⁻¹).1 * ((DC * t.1) * incM F tb.1) := by rw [hp']
      _ = (incM F (d.b⁻¹).1 * incM F d.b.1) * E1 * (incM F (tb⁻¹).1 * t.1 * incM F tb.1) := by
          rw [hdc]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hBB, Matrix.one_mul]
  ext i j
  have := congrFun (congrFun key (Sum.inr i)) j
  rw [hcol] at this
  simpa [E1, Matrix.toBlocks₂₁, Matrix.toCols₁, Matrix.mul_apply, Fintype.sum_sum_type] using this
theorem par_decomp_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (p : d.G) (t : GL (Fin d.n) (AE F E)) (hp : IsPar p t) :
    ∃ (n0 m0 : d.G) (β₀ : Mx F E d.n d.n), inFrame d.b n0 = Matrix.fromBlocks 1 β₀ 0 1 ∧ _root_.PositivityTheory.SiegelWeilFormula.KWhit.IsLevi_k d m0 ∧ p = n0 * m0 := by
  have h21 := _root_.PositivityTheory.SiegelWeilFormula.KWhit.parabolic_lowerLeft_block_zero d p t hp
  set g := inFrame d.b p with hg
  set A := g.toBlocks₁₁
  set B := g.toBlocks₁₂
  set D := g.toBlocks₂₂
  have hgb : g = Matrix.fromBlocks A B 0 D := by rw [← h21, Matrix.fromBlocks_toBlocks]
  have hBm : IsUnit (incM F d.b.1) := (Matrix.isUnit_iff_isUnit_det _).2
    (isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d, Matrix.det_one]⟩)
  have hBi : IsUnit (incM F (d.b⁻¹).1) := (Matrix.isUnit_iff_isUnit_det _).2
    (isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d, Matrix.det_one]⟩)
  have hug : IsUnit g := (hBi.mul (Units.isUnit p.1)).mul hBm
  have hdet : IsUnit (A.det * D.det) := by
    rw [← Matrix.det_fromBlocks_zero₂₁ A B D, ← hgb]
    exact (Matrix.isUnit_iff_isUnit_det g).1 hug
  have hA : IsUnit A.det := isUnit_of_mul_isUnit_left hdet
  have hD : IsUnit D.det := isUnit_of_mul_isUnit_right hdet
  set Md : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) := Matrix.fromBlocks A 0 0 D with hMd_def
  have hMd : IsUnit Md := (Matrix.isUnit_iff_isUnit_det _).2 (by rw [hMd_def, Matrix.det_fromBlocks_zero₂₁]; exact hA.mul hD)
  obtain ⟨C', hC'⟩ := _root_.PositivityTheory.SiegelWeilFormula.KWhit.frame_form_k d
  have hP : (mat2 p)ᵀ * dbl (incM F d.Y.J) * (mat2 p).map (cA σ).toRingHom = dbl (incM F d.Y.J) := p.2
  have hgf := form_conj_in (cA σ).toRingHom (_root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d) hP
  have hC'' : (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ).toRingHom =
      Matrix.fromBlocks 0 1 C' 0 := hC'
  rw [hC''] at hgf
  have hgf' : gᵀ * Matrix.fromBlocks 0 1 C' 0 * g.map (cA σ).toRingHom = Matrix.fromBlocks 0 1 C' 0 := hgf
  rw [hgb] at hgf'
  have hMdf := block_diag_form (cA σ).toRingHom A B D C' hgf'
  rw [← hC''] at hMdf
  have hM0mem := form_conj_out (cA σ).toRingHom (_root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d) hMdf
  have hM0u : IsUnit (incM F d.b.1 * Md * incM F (d.b⁻¹).1) := (hBm.mul hMd).mul hBi
  let u : GL (Fin d.n ⊕ Fin d.n) (AE F E) := hM0u.unit
  have hu : (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) =
      incM F d.b.1 * Md * incM F (d.b⁻¹).1 := IsUnit.unit_spec hM0u
  have hmem : u ∈ UG (cA σ) (dbl (incM F d.Y.J)) := by
    show (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E))ᵀ * dbl (incM F d.Y.J) *
      (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)).map (cA σ) = dbl (incM F d.Y.J)
    rw [hu]
    exact hM0mem
  let m0 : d.G := ⟨u, hmem⟩
  have hm0 : inFrame d.b m0 = Md := by
    show incM F (d.b⁻¹).1 * (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) * incM F d.b.1 = Md
    rw [hu]
    simp only [← Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d, Matrix.one_mul]
    rw [Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d, Matrix.mul_one]
  have hAu := (Matrix.isUnit_iff_isUnit_det A).2 hA
  have hDu := (Matrix.isUnit_iff_isUnit_det D).2 hD
  refine ⟨p * m0⁻¹, m0, B * D⁻¹, ?_, ⟨hAu.unit, hDu.unit, ?_⟩, (inv_mul_cancel_right p m0).symm⟩
  · have e := _root_.PositivityTheory.SiegelWeilFormula.KWhit.inFrame_mul_k d (p * m0⁻¹) m0
    rw [inv_mul_cancel_right, hm0] at e
    apply (hMd.mul_left_inj).1
    rw [← e, ← hg, hgb, hMd_def, Matrix.fromBlocks_multiply]
    simp [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hD]
  · rw [hm0, IsUnit.unit_spec, IsUnit.unit_spec]
theorem gram_mat_inv_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (g : UA σ d.A.J) (X : Mx F E d.m d.n) :
    d.gram (mat g⁻¹ * X) (mat g⁻¹ * X) = d.gram X X := by
  have hg : (mat g⁻¹)ᵀ * incM F d.A.J * (mat g⁻¹).map (cA σ) = incM F d.A.J := (g⁻¹).2
  have hm : (mat g⁻¹ * X).map (cA σ) = (mat g⁻¹).map (cA σ) * X.map (cA σ) :=
    Matrix.map_mul (f := (cA σ).toRingHom)
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram, Matrix.transpose_mul, hm]
  calc Xᵀ * (mat g⁻¹)ᵀ * incM F d.A.J * ((mat g⁻¹).map (cA σ) * X.map (cA σ))
      = Xᵀ * ((mat g⁻¹)ᵀ * incM F d.A.J * (mat g⁻¹).map (cA σ)) * X.map (cA σ) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hg]
theorem phase_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (T β₀ : Mx F E d.n d.n) :
    -(⅟(2 : AF F) * d.tt (β₀ * ((-2 : ℤ) • T))) = d.tt (T * β₀) := by
  have h1 : d.tt (β₀ * ((-2 : ℤ) • T)) = (-2 : AF F) * d.tt (T * β₀) := by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, Matrix.mul_smul, Matrix.trace_smul, map_zsmul, Matrix.trace_mul_comm β₀ T]
    rw [zsmul_eq_mul]
    push_cast
    ring
  rw [h1, ← mul_assoc, mul_neg, invOf_mul_self, neg_one_mul, neg_neg]
theorem orb_n_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (T : nF σ d.Y d.b) {Ψ : d.Fn} (hΨ : Ψ ∈ d.sch) (n0 : d.G) (β₀ : Mx F E d.n d.n)
    (hn : inFrame d.b n0 = Matrix.fromBlocks 1 β₀ 0 1) :
    d.orb T (d.om n0 Ψ) = d.B.ψ (d.tt (T.1.1 * β₀)) * d.orb T Ψ := by
  have hP := (hT.2.1 F E σ d Ψ hΨ).1 n0 β₀ hn
  have hpt : ∀ (g : UA σ d.A.J) (X : Matrix (Fin d.m) (Fin d.n) E),
      d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1 →
      d.T (d.om n0 Ψ) (mat g⁻¹ * incM F X) = d.B.ψ (d.tt (T.1.1 * β₀)) * d.T Ψ (mat g⁻¹ * incM F X) := by
    intro g X hX
    rw [hP, _root_.PositivityTheory.SiegelWeilFormula.KWhit.gram_mat_inv_k, hX, _root_.PositivityTheory.SiegelWeilFormula.KWhit.phase_k]
  have hs : ∀ g : UA σ d.A.J,
      (∑' X : {X : Matrix (Fin d.m) (Fin d.n) E // d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1},
        d.T (d.om n0 Ψ) (mat g⁻¹ * incM F X.1)) = d.B.ψ (d.tt (T.1.1 * β₀)) *
      ∑' X : {X : Matrix (Fin d.m) (Fin d.n) E // d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1},
        d.T Ψ (mat g⁻¹ * incM F X.1) := by
    intro g
    rw [← tsum_mul_left]
    exact tsum_congr fun X => hpt g X.1 X.2
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.orb]
  simp_rw [hs]
  simp only [MeasureTheory.average]
  exact integral_const_mul _ _
theorem int_n_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (nb : nA σ d.Y d.b → d.G) (lam : Measure (nA σ d.Y d.b)) (𝓖 : Set (nA σ d.Y d.b))
    (hcd : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) (T : nF σ d.Y d.b) (w n0 m0 : d.G) (β₀ : Mx F E d.n d.n)
    (hn : inFrame d.b n0 = Matrix.fromBlocks 1 β₀ 0 1) (f : d.G → ℂ) :
    ∫ β, f (w * nb β * (n0 * m0)) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam =
      d.B.ψ (d.tt (T.1.1 * β₀)) * ∫ β, f (w * nb β * m0) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam := by
  have := hcd.2.1
  have hβ₀ : β₀ ∈ nA σ d.Y d.b := AddSubgroup.subset_closure ⟨n0, hn⟩
  let b₀ : nA σ d.Y d.b := ⟨β₀, hβ₀⟩
  have hnb : ∀ β, nb β * n0 = nb (b₀ + β) := by
    intro β
    apply _root_.PositivityTheory.SiegelWeilFormula.KWhit.inFrame_injective_k d
    rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.inFrame_mul_k, hcd.1 β, hn, hcd.1 (b₀ + β)]
    simp [Matrix.fromBlocks_multiply, add_comm, b₀]
  have htt : ∀ β : nA σ d.Y d.b, d.tt (T.1.1 * (b₀ + β).1) = d.tt (T.1.1 * β₀) + d.tt (T.1.1 * β.1) := by
    intro β
    simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, Matrix.mul_add, Matrix.trace_add, map_add (f := _), b₀]
  calc ∫ β, f (w * nb β * (n0 * m0)) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam
      = ∫ β, (fun β' : nA σ d.Y d.b => f (w * nb β' * m0) * (d.B.ψ (-d.tt (T.1.1 * β'.1)) *
          d.B.ψ (d.tt (T.1.1 * β₀)))) (b₀ + β) ∂lam := by
        congr 1
        funext β
        dsimp only
        rw [← hnb β, htt β, ← AddChar.map_add_eq_mul,
          show -(d.tt (T.1.1 * β₀) + d.tt (T.1.1 * β.1)) + d.tt (T.1.1 * β₀) = -d.tt (T.1.1 * β.1) by abel]
        simp only [mul_assoc]
    _ = ∫ β, f (w * nb β * m0) * (d.B.ψ (-d.tt (T.1.1 * β.1)) * d.B.ψ (d.tt (T.1.1 * β₀))) ∂lam :=
        integral_add_left_haar lam b₀ (fun β' : nA σ d.Y d.b => f (w * nb β' * m0) *
          (d.B.ψ (-d.tt (T.1.1 * β'.1)) * d.B.ψ (d.tt (T.1.1 * β₀))))
    _ = _ := by
        rw [← integral_const_mul]
        congr 1
        funext β
        ring
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitPure
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem T_eq_lin_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Φ : d.Fn) (X : Mx F E d.m d.n) :
    d.T Φ X = (d.l ∘ₗ schrL d.B.ψ (d.dd.e (X * (incM F d.b.1.toCols₂)ᵀ))) Φ := rfl
theorem T_sum_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {k : ℕ} (c : Fin k → ℂ) (Φs : Fin k → d.Fn) :
    d.T (∑ i, c i • Φs i) = ∑ i, c i • d.T (Φs i) := by
  funext X
  set_option synthInstance.maxHeartbeats 100000 in
    rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.T_eq_lin_k, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Pi.smul_apply, _root_.PositivityTheory.SiegelWeilFormula.KWhit.T_eq_lin_k]
theorem T_sub_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Φ Ψ : d.Fn) : d.T (Φ - Ψ) = d.T Φ - d.T Ψ := by
  funext X
  rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.T_eq_lin_k, map_sub, Pi.sub_apply, _root_.PositivityTheory.SiegelWeilFormula.KWhit.T_eq_lin_k, _root_.PositivityTheory.SiegelWeilFormula.KWhit.T_eq_lin_k]
def genF_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (P : InfinitePlace F → PX d.m d.n) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ)
    (X : Mx F E d.m d.n) : ℂ :=
  (∏ w, fP (P w) (R.loc w X)) * g fun k => (d.crd X k).2
def genL_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (P : InfinitePlace F → PX d.m d.n) :
    ((Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) →ₗ[ℂ] (Mx F E d.m d.n → ℂ) where
  toFun := _root_.PositivityTheory.SiegelWeilFormula.KWhit.genF_k R P
  map_add' f g := by funext X; simp only [_root_.PositivityTheory.SiegelWeilFormula.KWhit.genF_k, Pi.add_apply]; ring
  map_smul' c f := by funext X; simp only [_root_.PositivityTheory.SiegelWeilFormula.KWhit.genF_k, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring
def pureGen_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : Set (Mx F E d.m d.n → ℂ) :=
  {f | ∃ P φ, Dense.Good φ ∧ f = _root_.PositivityTheory.SiegelWeilFormula.KWhit.genF_k R P (Dense.pf φ)}
theorem pureGen_sub_fock_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : _root_.PositivityTheory.SiegelWeilFormula.KWhit.pureGen_k R ⊆ R.fock := by
  rintro _ ⟨P, φ, hφ, rfl⟩
  exact Submodule.subset_span ⟨P, Dense.pf φ, Dense.pf_mem hφ, rfl⟩
theorem fock_le_span_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : R.fock ≤ Submodule.span ℂ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.pureGen_k R) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨P, g, hg, rfl⟩
  have := Dense.mem_span_pf hg
  clear hg
  have key : _root_.PositivityTheory.SiegelWeilFormula.KWhit.genL_k R P g ∈ Submodule.span ℂ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.pureGen_k R) := by
    induction this using Submodule.span_induction with
    | mem x hx => obtain ⟨φ, hφ, rfl⟩ := hx; exact Submodule.subset_span ⟨P, φ, hφ, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  exact key
theorem isPureT_of_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (P : InfinitePlace F → PX d.m d.n)
    (φ : ∀ u : HeightOneSpectrum (𝓞 F), (Fin d.m × Fin d.n × Fin 2 → Fv F u) → ℂ) (hφ : Dense.Good φ) (Φ : d.Fn)
    (h : d.T Φ = _root_.PositivityTheory.SiegelWeilFormula.KWhit.genF_k R P (Dense.pf φ)) : _root_.PositivityTheory.SiegelWeilFormula.KWhit.IsPureT_k R Φ := by
  refine ⟨P, φ, fun v => hφ.1 v, hφ.2.mono fun v hv => hv, ?_⟩
  rw [h]
  rfl
theorem pureSpan_k : _root_.PositivityTheory.SiegelWeilFormula.KWhit.PureSpan_k := by
  intro hT hF hPK F E _ _ _ _ _ σ d R Φ hΦ hTΦ
  have hB := hT.1 F E σ d
  have h1 : d.T Φ ∈ Submodule.span ℂ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.pureGen_k R) := _root_.PositivityTheory.SiegelWeilFormula.KWhit.fock_le_span_k R hTΦ
  obtain ⟨k, c, gs, hsum⟩ := Submodule.mem_span_set'.1 h1
  have hpre : ∀ i : Fin k, ∃ Ψ ∈ d.sch, d.T Ψ = (gs i : Mx F E d.m d.n → ℂ) := fun i =>
    hB.2.1 _ ((hF F E σ d R).1 (_root_.PositivityTheory.SiegelWeilFormula.KWhit.pureGen_sub_fock_k R (gs i).2))
  choose Φs hΦs hTs using hpre
  refine ⟨k, c, Φs, fun i => ⟨hPK F E σ d R (Φs i) (hΦs i) (hTs i ▸ _root_.PositivityTheory.SiegelWeilFormula.KWhit.pureGen_sub_fock_k R (gs i).2), ?_⟩, ?_⟩
  · obtain ⟨P, φ, hφ, e⟩ := (gs i).2
    exact _root_.PositivityTheory.SiegelWeilFormula.KWhit.isPureT_of_k R P φ hφ (Φs i) ((hTs i).trans e)
  · have hmem : Φ - ∑ i, c i • Φs i ∈ d.sch :=
      sub_mem hΦ.1 (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hΦs i))
    have h0 : d.T (Φ - ∑ i, c i • Φs i) = 0 := by
      rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.T_sub_k, _root_.PositivityTheory.SiegelWeilFormula.KWhit.T_sum_k, ← hsum]
      simp only [hTs, sub_self]
    exact (sub_eq_zero.1 (hB.2.2 _ hmem h0))
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitRelAlg
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
def RelAlg_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
  (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ), ∃ (η : E) (hOf : nA σ d.Y d.b → HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n),
    η ≠ 0 ∧ (∀ i j, σ (η * d.A.J j i) = η * d.A.J i j) ∧
    (∀ β, β.1 = -(incM F (Matrix.scalar (Fin d.n) η) * ((hOf β).1 : Mx F E d.n d.n)ᵀ)) ∧
    (∀ y : Fin d.m → E, HeckeCharacterZeroLocus.SiegelWeilU.hE σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) y y = 0 → y = 0) ∧
    HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ ∧ HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) ∧
    ∀ T : nF σ d.Y d.b, IsND T → ∃ T₀ : Matrix (Fin d.n) (Fin d.n) E, T.1.1 = incM F T₀ ∧
      (∀ a b, σ (Td η T₀ b a) = Td η T₀ a b) ∧ (Td η T₀).det ≠ 0
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
end

