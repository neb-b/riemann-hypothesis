module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0087
public import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SplitOffBadOfSuppSplitOff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeExtensionAlongFieldEmbeddingDuals
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0217
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.SecondStepGluing
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimeDvdAbsNormHalfDifferent
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0075
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.JacquetKernelEigenvectorEqZeroOfConstCharacter
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem eq_zero_of_isEig_const : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (χ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → IsSmoothChar χ → ∀ v ∈ twKer π (unipB k (Fin n)) 1, IsEig π (grp fun _ => χ) (theta fun _ => χ) v → v = 0 := by
  intro k _ _ _ _ n χ V _ _ π hπ hχ v hv he
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.PsType.const_family_main k n χ
  have hs : IsSmoothChar (detChar (Fin n) χ)⁻¹ := by
    have hc : Continuous (Matrix.GeneralLinearGroup.det : GL (Fin n) k → kˣ) :=
      Matrix.GeneralLinearGroup.continuous_det
    have ho : IsOpen ((χ.ker : Set kˣ)) := hχ
    have := ho.preimage hc
    unfold IsSmoothChar
    convert this using 1
    ext g
    simp [detChar, MonoidHom.mem_ker]
  have hk : twKer (twist π (detChar (Fin n) χ)⁻¹) (unipB k (Fin n)) 1 = twKer π (unipB k (Fin n)) 1 := by
    unfold twKer
    congr 1
    ext w
    refine exists_congr fun u => exists_congr fun x => ?_
    have hd : Matrix.GeneralLinearGroup.det (u : GL (Fin n) k) = 1 := det_eq_one_of_mem_unipRad k u.2
    have : twist π (detChar (Fin n) χ)⁻¹ (u : GL (Fin n) k) x = π (u : GL (Fin n) k) x := by
      simp [twist, detChar, hd]
    rw [this]
  refine _root_.GlobalTheory.PsType.eq_zero_of_fixed_KO_twKer_unipB k n V (twist π (detChar (Fin n) χ)⁻¹) (isSmooth_twist hπ hs) v (hk ▸ hv) ?_
  intro g hg
  have h3 := he g (by rw [h1]; exact hg)
  rw [h2 g hg] at h3
  show (((detChar (Fin n) χ)⁻¹ g : ℂˣ) : ℂ) • π g v = v
  rw [h3, smul_smul]
  simp

end GlobalTheory.PsType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelSpanOverClasses
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TraceClassRank

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open GlobalTheory.FormTies GlobalTheory.OnTies
open Formalism.HermitianLatticesTheory (localization₂)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lat

theorem fg_of_graph {R P X : Type} [CommRing R] [IsNoetherianRing R] [AddCommGroup P] [Module R P] [AddCommGroup X]
    [Module R X] {N : Submodule R P} (hN : N.FG) (Γ : Submodule R (P × X)) (hΓ : ∀ x, ((0 : P), x) ∈ Γ → x = 0)
    {s : Set X} (hs : ∀ x ∈ s, ∃ p ∈ N, (p, x) ∈ Γ) : (Submodule.span R s).FG := by
  have h1 : (Γ ⊓ N.comap (LinearMap.fst R P X)).FG := by
    refine Submodule.fg_of_fg_map_of_fg_inf_ker (LinearMap.fst R P X) (hN.of_le ?_) ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact hy.2
    · have : Γ ⊓ N.comap (LinearMap.fst R P X) ⊓ LinearMap.ker (LinearMap.fst R P X) = ⊥ := by
        refine eq_bot_iff.2 ?_
        rintro ⟨p, x⟩ ⟨⟨h, -⟩, hp⟩
        have hp' : p = 0 := hp
        subst hp'
        rw [hΓ x h]
        exact Submodule.zero_mem _
      rw [this]
      exact Submodule.fg_bot
  refine (h1.map (LinearMap.snd R P X)).of_le (Submodule.span_le.2 fun x hx => ?_)
  obtain ⟨p, hp, h⟩ := hs x hx
  exact ⟨(p, x), ⟨h, hp⟩, rfl⟩

variable {K : Type} [Field K] [NumberField K] {n n' : ℕ}

theorem localization_comap_le (v : HeightOneSpectrum (𝓞 K)) (f : (Fin n → K) →ₗ[K] (Fin n' → K))
    {A B : Submodule (𝓞 K) (Fin n' → K)} (h : localization₂ v.asIdeal A ≤ localization₂ v.asIdeal B) :
    localization₂ v.asIdeal (A.comap (f.restrictScalars (𝓞 K))) ≤ localization₂ v.asIdeal (B.comap (f.restrictScalars (𝓞 K))) := by
  rintro x ⟨s, hs, hx⟩
  obtain ⟨t, ht, hy⟩ := h (x := f x) ⟨s, hs, (f.restrictScalars (𝓞 K)).map_smul s x ▸ (hx : (f.restrictScalars (𝓞 K)) (s • x) ∈ A)⟩
  exact ⟨t, ht, by rwa [Submodule.mem_comap, map_smul]⟩

end Lat

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Adelic

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

def dataLevel (Q : Finset (Pl D.host.E)) : Subgroup (Bridge.Gf (Vc D i)) :=
  (levEnv (Vc D i) (R.βV i) (Lev.datY _ D.R.r D.R.t 1 (r_le_V i) R.Pg Q (LevelP.triv _ _ _) (fun _ _ => 1) (fun _ => 1)
    Lev.Frm.A)).J


variable {i} in
def MeetsClasses (J : Subgroup (Bridge.Gf (Vc D i))) {Cl : Type} (h : Cl → GA D (Vc D i)) : Prop :=
  (∀ c, h c ∈ GfC (Vc D i)) ∧
    ∀ x : Bridge.Gf (Vc D i), ∃ (c : Cl) (γ : GQ (Vc D i)) (k : J), x = Bridge.ratF (Vc D i) γ * fin (Vc D i) (h c) * k

def seriesAt (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (ph : ℂ) (ω : WeilRep D i) (φ : Datum.WO (Vc D i) (Wc D i) → ℂ)
    (h : GA D (Vc D i)) : Set (Fin (R.nW i) → D.what₂.LL) :=
  {x | ∃ w, InCoefLat R i h w ∧ ∀ v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ,
    adForm R i x (fun ρ => v ρ) = ph • levelTrace R i U ψ (singleSeries R i ω φ h w v)}

def IsBaseKernel (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (p : ℕ) (ω : WeilRep D i) (φ : Datum.WO (Vc D i) (Wc D i) → ℂ) : Prop :=
  IsKernel R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) (placesOver R (R.mu v) p) ω φ

def SpanOverClasses (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (ph : ℂ) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (p : ℕ) : Prop :=
  ∀ ω φ, IsBaseKernel R i v p ω φ → ∀ (Cl : Type) (h : Cl → GA D (Vc D i)),
    MeetsClasses (dataLevel R i (placesOver R (R.mu v) p)) h →
      thetaBase R i U ψ ph v p = Submodule.span (𝓞 D.what₂.LL) (⋃ c, seriesAt R i U ψ ph ω φ (h c))

def FormsDetermined : Prop :=
  ∀ x, (∀ v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, adForm R i x (fun ρ => v ρ) = 0) → x = 0

def BaseKernelUnique (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (p : ℕ) : Prop :=
  ∀ ω φ ω' φ', IsBaseKernel R i v p ω φ → IsBaseKernel R i v p ω' φ' → singleSeries R i ω φ = singleSeries R i ω' φ'

def KernelSpanOverClasses (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (ph : ℂ) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (p : ℕ) : Prop :=
  ∀ ω φ, IsBaseKernel R i v p ω φ → ∀ (Cl : Type) (h : Cl → GA D (Vc D i)),
    MeetsClasses (dataLevel R i (placesOver R (R.mu v) p)) h →
      Submodule.span (𝓞 D.what₂.LL) (seriesSet R i U ψ ph ω φ) =
        Submodule.span (𝓞 D.what₂.LL) (⋃ c, seriesAt R i U ψ ph ω φ (h c))

variable {R i}

theorem spanOverClasses_of {U : Subgroup G} {ψ : U →* D.what₂.LLˣ} {ph : ℂ} {v : HeightOneSpectrum (𝓞 D.what₂.LL)} {p : ℕ}
    (h1 : BaseKernelUnique R i v p) (h2 : KernelSpanOverClasses R i U ψ ph v p) : SpanOverClasses R i U ψ ph v p := by
  intro ω φ hk Cl h hh
  rw [← h2 ω φ hk Cl h hh]
  unfold thetaBase
  congr 1
  ext x
  refine ⟨?_, fun hx => ⟨ω, φ, hk, hx⟩⟩
  rintro ⟨ω', φ', hk', hx⟩
  unfold seriesSet at hx ⊢
  rwa [h1 ω φ ω' φ' hk hk']

theorem formsDetermined_of (hres : GlobalTheory.IndefiniteRowSideFullHecke.ResidueInjectivityAt.ResInjAt R) (hW : R.models_HW) (hu : R.LUnif) : FormsDetermined R i := by
  intro x hx
  obtain ⟨h1, h2, -⟩ := hW i (sg0 D A)
  have h3 : adForm R i x = 0 := hres i _ (h2 ▸ LinearMap.mem_range_self _ _) hx
  have h4 : (R.FW i).j (sg0 D A) x = 0 := h1 (h3.trans (map_zero _).symm)
  by_contra h0
  have h5 := (hu i (sg0 D A)).1 1 (fun _ => x) (linearIndependent_unique_iff.2 h0)
  exact h5.ne_zero 0 h4

theorem levJ_le_dataLevel (t : T0) {Q : Finset (Pl D.host.E)} (hQ : Q ⊆ R.Q t) : levJ R i t ≤ dataLevel R i Q := by
  intro x hx
  exact ⟨⟨hx.1.1, Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP =>
    Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx.1.2 PP) (hQ hP)⟩, hx.2⟩

theorem nabAtr_hLat_fg (g : Bridge.Gf (Vc D i)) : (nabAtr (labLL D) (lamV D i) (Bridge.hLat (Vc D i) g)).FG := by
  have hLat : Submodule.IsFullLattice D.host.E (Bridge.hLat (Vc D i) g) := by
    obtain ⟨-, -, hfg, hsp, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D (Vc D i)
    obtain ⟨Λ, hΛ, h1, h2, -⟩ := GlobalTheory.AdLat.exists_lattice_latOf D.host.F D.host.E (Vc D i).rank (GlobalTheory.Member.latC (Vc D i)) g.1 hfg hsp
    rw [SetLike.coe_injective ((GlobalTheory.RepsCompare.coe_hLat (Vc D i) g).trans hΛ.symm)]
    letI : Submodule.IsLattice D.host.E Λ := Submodule.IsLattice.of_fg D.host.E h1
    exact { span_eq_top := h2 }
  exact (GlobalTheory.TransLattice.nabDelLattice _ _ _ _ _ fun τ => (GlobalTheory.dualFrLattice_holds D.what₂.LL _ 1 _ (by simp)
    (GlobalTheory.TauLat.tauLatLattice _ _ _ _ (labLL D) τ _ hLat)).1).1.fg

theorem coefTie_class {V : HSp D} {C : Bridge.CoefDat D V} {S : CSD D.what₂.LL} {J : Subgroup (Bridge.Gf V)} {χ : J →* ℂˣ}
    {P : Bridge.ClassPres (Bridge.ratF V) S D.what₂.embLL C.ρ J χ} {lam : D.what₂.Tau → DomWeight V.rank}
    {c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] C.W}
    {pair : VV D.what₂.LL lam →ₗ⋆[D.what₂.LL] VV D.what₂.LL lam →ₗ[D.what₂.LL] D.what₂.LL}
    {nab del : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) → Submodule (𝓞 D.what₂.LL) (VV D.what₂.LL lam)}
    (h : Bridge.CoefTie V C P lam c0 pair nab del) (c : S.Cl) :
    ((nab (Bridge.hLat V (P.y c))).FG → (S.Nab c).FG) ∧
      ∀ x ∈ nab (Bridge.hLat V (P.y c)), ∃ y ∈ S.Nab c, c0 x = P.coef y := by
  obtain ⟨e, -, h2, -, h4, -⟩ := h
  refine ⟨fun hf => ?_, fun x hx => ?_⟩
  · rw [← h4 c] at hf
    exact Submodule.fg_of_fg_map_injective (e.toLinearMap.restrictScalars (𝓞 D.what₂.LL)) e.injective hf
  · rw [← h4 c] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, hy, (h2 y).symm⟩

theorem exists_coef_fg (t : T0) (c : (A.MtCSD i t).Cl) {h : GA D (Vc D i)} (hh : fin (Vc D i) h = (R.B.L i t).pres.y c) :
    ∃ N : Submodule (𝓞 D.what₂.LL) (A.MtCSD i t).V, N.FG ∧
      ∀ w, InCoefLat R i h w → ∃ P ∈ N, w = (R.B.L i t).pres.coef P := by
  by_cases hex : ∃ w, InCoefLat R i h w
  · obtain ⟨-, gramR, c0R, c0L, hT, -⟩ := hex
    refine ⟨(A.MtCSD i t).Nab c, ?_, ?_⟩
    · exact (coefTie_class (hT.coefL i t) c).1 (nabAtr_hLat_fg _)
    · rintro w ⟨gramR', c0R', c0L', hT', P, hP, rfl⟩
      rw [hh] at hP
      exact (coefTie_class (hT'.coefL i t) c).2 P hP
  · exact ⟨⊥, Submodule.fg_bot, fun w hw => absurd ⟨w, hw⟩ hex⟩

theorem singleSeries_add (ω : WeilRep D i) (φ : Datum.WO (Vc D i) (Wc D i) → ℂ) (h : GA D (Vc D i)) (w w' : (R.cV i).W)
    (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) :
    singleSeries R i ω φ h (w + w') v = singleSeries R i ω φ h w v + singleSeries R i ω φ h w' v := by
  funext g
  simp only [singleSeries, Datum.thetaKO, map_add (f := _), Pi.add_apply]

theorem singleSeries_smul (ω : WeilRep D i) (φ : Datum.WO (Vc D i) (Wc D i) → ℂ) (h : GA D (Vc D i)) (a : ℂ) (w : (R.cV i).W)
    (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) :
    singleSeries R i ω φ h (a • w) v = a • singleSeries R i ω φ h w v := by
  funext g
  simp only [singleSeries, Datum.thetaKO, map_smul, Pi.smul_apply]

theorem adForm_add (x y : Fin (R.nW i) → D.what₂.LL) : adForm R i (x + y) = adForm R i x + adForm R i y := by
  unfold adForm
  rw [map_add (f := _), map_add (f := _)]

theorem adForm_smul (a : D.what₂.LL) (x : Fin (R.nW i) → D.what₂.LL) : adForm R i (a • x) = D.what₂.embLL a • adForm R i x := by
  unfold adForm
  rw [LinearMap.map_smulₛₗ, map_smul]
  congr 1
  exact RingHom.congr_fun (sgAt_mk _ R.hv0) a

theorem seriesAt_fg (hd : FormsDetermined R i) (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (ph : ℂ) (ω : WeilRep D i)
    (φ : Datum.WO (Vc D i) (Wc D i) → ℂ) (t : T0) (c : (A.MtCSD i t).Cl) {h : GA D (Vc D i)}
    (hh : fin (Vc D i) h = (R.B.L i t).pres.y c) : (Submodule.span (𝓞 D.what₂.LL) (seriesAt R i U ψ ph ω φ h)).FG := by
  obtain ⟨N, hN, H⟩ := exists_coef_fg t c hh
  let cf : (A.MtCSD i t).V →ₛₗ[D.what₂.embLL] (R.cV i).W := (R.B.L i t).pres.coef
  let Γ : Submodule D.what₂.LL ((A.MtCSD i t).V × (Fin (R.nW i) → D.what₂.LL)) :=
    { carrier := {q | ∀ v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ,
        adForm R i q.2 (fun ρ => v ρ) = ph • levelTrace R i U ψ (singleSeries R i ω φ h (cf q.1) v)}
      add_mem' := fun {a b} ha hb v => by
        rw [Prod.fst_add, Prod.snd_add, adForm_add, map_add (f := _), singleSeries_add, map_add (f := _), smul_add, ← ha v, ← hb v]
        rfl
      zero_mem' := fun v => by
        have h1 := adForm_smul (R := R) (i := i) 0 0
        have h2 := singleSeries_smul (R := R) ω φ h 0 0 v
        rw [zero_smul, map_zero, zero_smul] at h1
        rw [zero_smul, zero_smul] at h2
        rw [Prod.fst_zero, Prod.snd_zero, h1, map_zero, h2, map_zero, smul_zero]
        rfl
      smul_mem' := fun a q hq v => by
        rw [Prod.smul_fst, Prod.smul_snd, adForm_smul, LinearMap.map_smulₛₗ, singleSeries_smul, map_smul, smul_comm, ← hq v]
        rfl }
  refine fg_of_graph hN (Γ.restrictScalars (𝓞 D.what₂.LL)) (fun x hx => hd x fun v => ?_) ?_
  · have h2 := singleSeries_smul (R := R) ω φ h 0 0 v
    rw [zero_smul, zero_smul] at h2
    have h3 : adForm R i x (fun ρ => v ρ) = ph • levelTrace R i U ψ (singleSeries R i ω φ h (cf 0) v) := hx v
    rw [h3, map_zero, h2, map_zero, smul_zero]
  · rintro x ⟨w, hw, hx⟩
    obtain ⟨P, hP, rfl⟩ := H w hw
    exact ⟨P, hP, hx⟩

theorem thetaBase_fg (hd : FormsDetermined R i) {U : Subgroup G} {ψ : U →* D.what₂.LLˣ} {ph : ℂ}
    {v : HeightOneSpectrum (𝓞 D.what₂.LL)} {p : ℕ} (hM : SpanOverClasses R i U ψ ph v p) : (thetaBase R i U ψ ph v p).FG := by
  classical
  by_cases hex : ∃ ω φ, IsBaseKernel R i v p ω φ
  · obtain ⟨ω, φ, hk⟩ := hex
    choose h hh using fun c => (GlobalTheory.RepsCompare.existsUnique_lift (Vc D i) ((R.B.L i (R.mu v)).pres.y c)).exists
    rw [hM ω φ hk _ h ⟨fun c => (hh c).1, fun x => ?_⟩, Submodule.span_iUnion]
    · exact Submodule.fg_iSup _ fun c => seriesAt_fg hd U ψ ph ω φ _ c (hh c).2
    · obtain ⟨c, γ, k, e⟩ := ((R.B.L i (R.mu v)).pres.reps x).exists
      exact ⟨c, γ, ⟨k, levJ_le_dataLevel (R.mu v) (Finset.filter_subset _ _) k.2⟩, by rw [(hh c).2]; exact e⟩
  · have : thetaBase R i U ψ ph v p = ⊥ := Submodule.span_eq_bot.2 fun x ⟨ω, φ, hk, _⟩ => absurd ⟨ω, φ, hk⟩ hex
    rw [this]
    exact Submodule.fg_bot

end Adelic

end GlobalTheory.TraceClassRank
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonarchimedeanGroupOfIsCompactIsOpen
section
noncomputable section

namespace GlobalTheory.Doubling

open scoped TensorProduct NNReal Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU

theorem eq_one_of_forall_norm_pow_sub_one_le {A : Type} [NormedRing A] [NormedAlgebra ℂ A] {x : A}
    (h : ∀ m : ℕ, ‖x ^ m - 1‖ ≤ 1 / 2) : x = 1 := by
  have h1 : ∀ k : ℕ, (3 / 2 : ℝ) ^ k * ‖x - 1‖ ≤ ‖x ^ (2 ^ k) - 1‖ := fun k => by
    induction k with
    | zero => simp
    | succ k ih =>
      obtain ⟨y, hy⟩ : ∃ y, y = x ^ (2 ^ k) - 1 := ⟨_, rfl⟩
      have e : (2 : ℂ) • y = (x ^ (2 ^ (k + 1)) - 1) - y * y := by
        rw [pow_succ 2, pow_mul, hy, two_smul, sq]; noncomm_ring
      have h2 : 2 * ‖y‖ ≤ ‖x ^ (2 ^ (k + 1)) - 1‖ + ‖y‖ * ‖y‖ := by
        have := norm_sub_le (x ^ (2 ^ (k + 1)) - 1) (y * y)
        rw [← e, norm_smul, Complex.norm_ofNat] at this
        linarith [norm_mul_le y y]
      have h3 : ‖y‖ * ‖y‖ ≤ 1 / 2 * ‖y‖ := mul_le_mul_of_nonneg_right (hy ▸ h _) (norm_nonneg y)
      rw [← hy] at ih
      rw [pow_succ]
      linarith
  by_contra hz
  have hp : 0 < ‖x - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (‖x - 1‖⁻¹) (show (1 : ℝ) < 3 / 2 by norm_num)
  have h4 := (h1 k).trans (h _)
  have h5 := mul_lt_mul_of_pos_right hk hp
  rw [inv_mul_cancel₀ hp.ne'] at h5
  linarith

theorem nonarchimedeanGroup_of_isCompact_isOpen {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TotallyDisconnectedSpace H] {K : Subgroup H} (hc : IsCompact (K : Set H)) (ho : IsOpen (K : Set H)) :
    NonarchimedeanGroup H :=
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hc
  haveI : NonarchimedeanGroup K := ⟨fun U hU => by
    obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one (isOpen_interior (s := U))
      (mem_interior_iff_mem_nhds.2 hU)
    exact ⟨N.toOpenSubgroup, hN.trans interior_subset⟩⟩
  NonarchimedeanGroup.nonarchimedean_of_emb K.subtype ho.isOpenEmbedding_subtypeVal

section General

variable {G : Type} [Group G] {K : Subgroup G} {Φ : G → ℂ}


variable [TopologicalSpace G] [ContinuousMul G]

end General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)

section Groups

variable {m : ℕ} (J : Matrix (Fin m) (Fin m) E)

theorem totallyDisconnectedSpace_GLoc (v : HeightOneSpectrum (𝓞 F)) : TotallyDisconnectedSpace (GLoc σ J v) := by
  haveI : TotallyDisconnectedSpace (Fv F v ⊗[F] E) := by
    obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (Fv F v)
    exact e.symm.totallyDisconnectedSpace
  haveI : TotallyDisconnectedSpace (Matrix (Fin m) (Fin m) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin m → Fin m → Fv F v ⊗[F] E))
  exact ⟨isTotallyDisconnected_of_image (f := fun g => (matHom _ σ J g).1)
    (Units.continuous_val.comp (isEmbedding_matHom _ σ J).continuous).continuousOn
    (Units.val_injective.comp (matHom_injective _ σ J)) (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

theorem totallyDisconnectedSpace_GFin : TotallyDisconnectedSpace (GFin σ J) :=
  haveI := totallyDisconnectedSpace_GLoc σ J
  ⟨isTotallyDisconnected_of_image (f := fun g v => projFinLoc σ J v g)
    (continuous_pi fun v => continuous_projFinLoc σ J v).continuousOn
    (fun _ _ e => GFin_ext σ J (congrFun e)) (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

theorem nonarchimedeanGroup_GLoc (v : HeightOneSpectrum (𝓞 F)) : NonarchimedeanGroup (GLoc σ J v) :=
  haveI := totallyDisconnectedSpace_GLoc σ J v
  haveI := isLattice_stdLattice (E := E) (n := m)
  nonarchimedeanGroup_of_isCompact_isOpen (isCompact_stabLoc σ J (stdLattice E m) v)
    (isOpen_stabLoc σ J (stdLattice E m) v)

theorem nonarchimedeanGroup_GFin : NonarchimedeanGroup (GFin σ J) :=
  haveI := totallyDisconnectedSpace_GFin σ J
  haveI := isLattice_stdLattice (E := E) (n := m)
  nonarchimedeanGroup_of_isCompact_isOpen (isCompact_levelOffFin σ J (stdLattice E m) ∅)
    (isOpen_levelOffFin_empty σ J (stdLattice E m))

variable {σ J}

end Groups

variable {σ} {n : ℕ} {Q : Matrix (Fin (n + n)) (Fin (n + n)) E} {L : Submodule (𝓞 E) (Fin n → E)}
  [Submodule.IsLattice E L]

section Record

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end Record

end GlobalTheory.Doubling

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesCongruenceSubgroupSmoothCharacter
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem grp_theta_datum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (ψ : Fin n → kˣ →* ℂˣ), (∀ i, IsSmoothChar (ψ i)) → Ordered ψ → Datum (grp ψ) (theta ψ) ∧ IsOpen (grp ψ) := by
  intro k _ _ _ _ n ψ hs ho
  have hoc := _root_.GlobalTheory.PsType.grp_isOpen_isCompact k n ψ hs
  have hnear := _root_.GlobalTheory.PsType.theta_one_and_near k n ψ hs
  have hone : (1 : GL (Fin n) k) ∈ grp ψ := by
    refine ⟨(KO k (Fin n)).one_mem, fun i j hij => ?_⟩
    have h0 : (1 : GL (Fin n) k).val i j = 0 := by
      simp [Matrix.one_apply_ne (ne_of_lt hij)]
    rw [h0]
    exact (_root_.GlobalTheory.PsType.triv_ev_props k).2.2.1 _
  refine ⟨⟨hone, _root_.GlobalTheory.PsType.grp_mul_closed k n ψ ho, _root_.GlobalTheory.PsType.grp_inv_mem k n ψ ho, hoc.2, hnear.1,
    _root_.GlobalTheory.PsType.theta_mul k n ψ ho, ?_⟩, hoc.1⟩
  obtain ⟨U, hU, hUt⟩ := hnear.2
  exact ⟨U, hU, fun g hg _ => hUt g hg⟩

end GlobalTheory.PsType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankOneBaseWeightEqCmTheta
section
noncomputable section

namespace GlobalTheory.HalfOnRecord

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Pj.LPb Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Lev
  Formalism.IndefR.FWT GlobalTheory.IndefiniteRowSideFullHecke.TwistCoverDesign GlobalTheory.HalfCompare GlobalTheory.CoverHalf
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Level)
open Formalism.L2.Host (PiBar)

variable {D : D7}

def designLevel (P : PiBar D.host) : Level (hostOfRecord D) :=
  IndefiniteRowSideFullHecke.HalfLevelCoefficients.levelAt D (IndefiniteRowSideFullHecke.HalfLevelCoefficients.halfOf D P.pb) ((ParAtCompare.levelPb_iff D P.pb).1 (levelPb_exists D P.pb P.pb_over))

theorem designLevel_Mb (P : PiBar D.host) :
    (designLevel P).Mb = ∏ k, (P.pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) := rfl

section Rec

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

end Rec

end GlobalTheory.HalfOnRecord
end
end

