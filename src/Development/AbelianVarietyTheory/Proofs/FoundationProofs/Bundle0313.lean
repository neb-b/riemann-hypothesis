module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAntiJFrame
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryMemIntegralUnitaryDoubleCosetOfGLnDoubleC

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceLatticeLeThetaLatticeAtPlace
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
attribute [local instance 2000] Submodule.module

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Trace

variable {T : Full D} [inst : Algebra T.J.Q.c.F D.what₂.LL] {R : RealDat D A T.J.Q.c.F}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  (h : LawsP T.toTop) (fw : FWTie T.J R κ v₀) (ι : Fin D.R.m)
  (ℓ : G → (LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l))
  (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (ph : ℂ) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (p : ℕ)

def traceLat : Submodule (𝓞 D.what₂.LL) (Fin (R.nW ι) → D.what₂.LL) :=
  Submodule.span (𝓞 D.what₂.LL)
    ((fun f : U → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι) =>
        ∑ᶠ u : U, ((ψ u : D.what₂.LLˣ) : D.what₂.LL) • cuspTo h fw ι (f u)) ''
      {f | IsOrbitFamily (T.Q.Xo ((ι : ℕ) + 1)) T.Q.c (badN D) (wtA (κ ι)) (T.dδ ((ι : ℕ) + 1) (κ ι).n) (fun u : U => ℓ u)
        fun u => ((f u).1 : T.R ((ι : ℕ) + 1))})

def CompareAt (lam : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  localization₂ lam.asIdeal (traceLat h fw ι ℓ U ψ) ≤ localization₂ lam.asIdeal (thetaBase R ι U ψ ph v p)

def CompareOffOwn : Prop := ∀ lam, Formalism.EigenvalueLevelCeiling.plc lam ≠ p → CompareAt h fw ι ℓ U ψ ph v p lam

variable {h fw ι ℓ U ψ ph v p} {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D}
    {wL wF : WeightFamilies.Wt D ((ι : ℕ) + 1)} {nT : ℕ}
    {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
    {O : OnObj S P oc} {i : Bs.J}
    {z : (Fin (O.nZ i) → D.what₂.LL) ≃ₗ[D.what₂.LL]
      D.what₂.LL ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
    {act : P → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι) → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
    {inc : P →* G}
    {y : (Fin (O.nX v i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (srcDim A ι (R.mu v) U ψ) → D.what₂.LL)}

def comapEquiv {P G : Type} [Group P] [Group G] {inc : P →* G} (hi : Function.Injective inc) {U : Subgroup G}
    (hU : U ≤ inc.range) : U.comap inc ≃ U :=
  Equiv.ofBijective (fun u => ⟨inc u, u.2⟩) ⟨fun _ _ e => Subtype.ext (hi (congrArg Subtype.val e)), fun u => by
    obtain ⟨g, hg⟩ := hU u.2
    exact ⟨⟨g, show inc g ∈ U from hg ▸ u.2⟩, Subtype.ext hg⟩⟩

theorem isOrbitFamily_comp {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l}
    {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {bad : ℕ} {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {d : DeltaDat Xo c n} {I I' : Type}
    {m : I → (LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l)} {m' : I' → (LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l)}
    {f : I → Rul Xo c} (hf : IsOrbitFamily Xo c bad a d m f) (e : I' → I) (he : ∀ u, m' u = m (e u)) :
    IsOrbitFamily Xo c bad a d m' fun u => f (e u) := by
  obtain ⟨Λ, N, x₀, P, x, h1, h2, h3, h4, h5, h6, h7⟩ := hf
  exact ⟨Λ, N, x₀, P, fun u => x (e u), h1, h2, h3, h4, h5, h6, fun u => he u ▸ h7 (e u)⟩

theorem Th0_eq_comap (t : OnTie h fw hinj EX p ι wL wF nT O v i z act inc ℓ U ψ ph y) (hi : Function.Injective inc)
    (hU : U ≤ inc.range) :
    O.Th0 v i = (traceLat h fw ι ℓ U ψ).comap ((toForms h fw ι z).restrictScalars (𝓞 D.what₂.LL)) := by
  have hm : (O.Th0 v i).map ((toForms h fw ι z).restrictScalars (𝓞 D.what₂.LL)) = traceLat h fw ι ℓ U ψ := by
    rw [t.Th0_eq, t.U_eq]
    unfold thetaEig traceSpan traceLat
    rw [Submodule.map_span, Set.image_image]
    have key : ∀ f : U → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι),
        (toForms h fw ι z).restrictScalars (𝓞 D.what₂.LL)
          (∑ᶠ u : U.comap inc, O.ψ (u : P) • z.symm (1 ⊗ₜ[(recB h.toLawsCore).KO] f (comapEquiv hi hU u))) =
        ∑ᶠ u : U, ((ψ u : D.what₂.LLˣ) : D.what₂.LL) • cuspTo h fw ι (f u) := fun f => by
      rw [map_finsum _ (Set.toFinite _), ← finsum_comp_equiv (comapEquiv hi hU)]
      refine finsum_congr fun u => ?_
      rw [map_smul, LinearMap.restrictScalars_apply, toForms_tmul, one_smul, ← algebraMap_smul D.what₂.LL]
      exact congrArg (· • _) (t.ψ_eq u u.2)
    congr 1
    ext x
    constructor
    · rintro ⟨f, hf, rfl⟩
      refine ⟨fun u => f ((comapEquiv hi hU).symm u), isOrbitFamily_comp hf _ (fun u => ?_), ?_⟩
      · exact congrArg (fun a : U => ℓ a) ((comapEquiv hi hU).apply_symm_apply u).symm
      · refine (key _).symm.trans ?_
        simp only [Equiv.symm_apply_apply]
    · rintro ⟨f, hf, rfl⟩
      exact ⟨fun u => f (comapEquiv hi hU u), isOrbitFamily_comp hf _ fun u => rfl, key f⟩
  rw [← hm]
  exact (Submodule.comap_map_eq_of_injective (f := (toForms h fw ι z).restrictScalars (𝓞 D.what₂.LL))
    (toForms_bijective h fw ι z).1 _).symm

theorem trace_lattice_le_theta_lattice_at_place (t : OnTie h fw hinj EX p ι wL wF nT O v i z act inc ℓ U ψ ph y) (hi : Function.Injective inc)
    (hU : U ≤ inc.range) {n : ℕ} (hp : RunPin R ι n v p) (hA : CompareOffOwn h fw ι ℓ U ψ ph v p) :
    localization₂ v.asIdeal (O.Th0 v i) ≤ localization₂ v.asIdeal (O.ThJ v i) := by
  rw [Th0_eq_comap t hi hU, t.ThJ_eq]
  refine localization_comap_le v _ (hA v fun e => ?_)
  have h1 := hp.1
  split_ifs at h1 with h2
  · exact D.host.pde_ne (h2.symm.trans (e.trans h1))
  · exact h2 (e.trans h1)

end Trace

section Place

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type}
  [Group P] [Finite P] {c : OnConst}

def RankAtPlaces (O : OnObj S P c) : Prop :=
  AtPair S fun v => ∀ j, Formalism.EigenvalueLevelCeiling.IsLatIn (O.Zg j) ((O.Th0 v j).map ((O.e j).restrictScalars (𝓞 K))) ∧
    Formalism.EigenvalueLevelCeiling.IsLatIn (O.Zg j) (O.eJ v j) ∧ localization₂ v.asIdeal (O.Th0 v j) ≤ localization₂ v.asIdeal (O.ThJ v j)

def fillJ (O : OnObj S P c) : OnObj S P c := { O with ThJ := fun v j => O.ThJ v j ⊔ O.Th0 v j }

theorem leafRankJ_fillJ {O : OnObj S P c} (h : RankAtPlaces O) : LeafRankJ (fillJ O) := by
  have key : ∀ v j, Formalism.EigenvalueLevelCeiling.IsLatIn (O.Zg j) ((O.Th0 v j).map ((O.e j).restrictScalars (𝓞 K))) →
      Formalism.EigenvalueLevelCeiling.IsLatIn (O.Zg j) (O.eJ v j) → Formalism.EigenvalueLevelCeiling.IsLatIn (O.Zg j) ((fillJ O).eJ v j) := fun v j a b => by
    change Formalism.EigenvalueLevelCeiling.IsLatIn _ ((O.ThJ v j ⊔ O.Th0 v j).map ((O.e j).restrictScalars (𝓞 K)))
    rw [Submodule.map_sup]
    refine ⟨b.1.sup a.1, le_antisymm (Submodule.span_le.2 ?_) ?_⟩
    · change _ ≤ (O.Zg j).restrictScalars (𝓞 K)
      exact sup_le (fun x hx => b.2.le (Submodule.subset_span hx)) fun x hx => a.2.le (Submodule.subset_span hx)
    · exact b.2.ge.trans (Submodule.span_mono (show O.eJ v j ≤ _ from le_sup_left))
  exact fun w hw =>
    ⟨fun j => ⟨((h w hw).1 j).1, key _ j ((h w hw).1 j).1 ((h w hw).1 j).2.1, le_sup_right⟩,
      fun j => ⟨((h w hw).2 j).1, key _ j ((h w hw).2 j).1 ((h w hw).2 j).2.1, le_sup_right⟩⟩

theorem lix_fillJ {O : OnObj S P c} {v : HeightOneSpectrum (𝓞 K)} {j : Bs.J}
    (h : localization₂ v.asIdeal (O.Th0 v j) ≤ localization₂ v.asIdeal (O.ThJ v j)) (M : Submodule (𝓞 K) (Fin (O.nZ j) → K)) :
    Formalism.EigenvalueLevelCeiling.lix v M ((fillJ O).eJ v j) = Formalism.EigenvalueLevelCeiling.lix v M (O.eJ v j) := by
  have h1 : O.ThJ v j ⊔ O.Th0 v j ≤ localization₂ v.asIdeal (O.ThJ v j) :=
    sup_le (Formalism.HermitianLatticesTheory.locBasic_le_locS _ _) ((Formalism.HermitianLatticesTheory.locBasic_le_locS _ _).trans h)
  have h2 : (fillJ O).eJ v j ≤ localization₂ v.asIdeal (O.eJ v j) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨s, hs, hsx⟩ := h1 hx
    exact ⟨s, hs, _, hsx, map_smul ((O.e j).restrictScalars (𝓞 K)) s x⟩
  have h3 : localization₂ v.asIdeal ((fillJ O).eJ v j) = localization₂ v.asIdeal (O.eJ v j) :=
    le_antisymm ((Formalism.HermitianLatticesTheory.locBasic_locS_mono _ h2).trans (Formalism.HermitianLatticesTheory.locBasic_locS_idem _ _).le)
      (Formalism.HermitianLatticesTheory.locBasic_locS_mono _ (Submodule.map_mono le_sup_left))
  exact (Formalism.EigenvalueLevelCeiling.lix_locP v M _).trans ((congrArg _ h3).trans (Formalism.EigenvalueLevelCeiling.lix_locP v M _).symm)

theorem leafTW1_fillJ {O : OnObj S P c} (h : RankAtPlaces O) (h1 : LeafTW1 O) : LeafTW1 (fillJ O) :=
  ⟨fun w hw =>
    ⟨fun j => ⟨((h1.1 w hw).1 j).1, ((h1.1 w hw).1 j).2.trans_eq
        (congrArg (fun a : ℤ => (a : ℝ) + _) (lix_fillJ ((h w hw).1 j).2.2 _).symm)⟩,
      fun j => ⟨((h1.1 w hw).2 j).1, ((h1.1 w hw).2 j).2.trans_eq
        (congrArg (fun a : ℤ => (a : ℝ) + _) (lix_fillJ ((h w hw).2 j).2.2 _).symm)⟩⟩, h1.2⟩

theorem on_core_atPlaces (N : IndefNum Bs) (O : OnObj S P c) (CE : ℝ) (hRk : RankRows S)
    (hMk : LeafMackey O) (hSup : LeafSup O) (hProj : LeafProj O) (hC : TieCoord O)
    (hSp : LeafSpan O) (hS : LeafLemmaS O) (hT0 : LatticeIndexBoundAtPairs O) (hD : LeafData O) (hJ : RankAtPlaces O)
    (hI : LeafIdentity O) (h2 : LeafTW2 O) (h1 : LeafTW1 O)
    (hSh : LeafShareI O) (hIU : LeafIndexU O) (hBS : LeafBadShare O) (hUn : LeafUnip O)
    (hG : LeafDepthGood N O) (hR : LeafDepthRam N O) (h2p : LeafDepth2 N O) (hL : LeafDepthLevel N O)
    (hPg : LeafPage O) (hSz : LeafSizes O) (hX : LeafX O) (hBad : LeafBad O)
    (hJS : LeafJSum O) (hJE : LeafJExp N O) (hCE : c.CE ≤ CE) (tE1 : ErrorConstantMatchesDefinition N O CE) : ONwith S N O.errOn :=
  on_core N (fillJ O) CE hRk hMk hSup hProj hC hSp hS hT0 hD (leafRankJ_fillJ hJ) hI h2 (leafTW1_fillJ hJ h1) hSh hIU hBS hUn
    hG hR h2p hL hPg hSz hX hBad hJS hJE hCE tE1

end Place

section Row

variable {T : HeightOneSpectrum (𝓞 D.what₂.LL) → Full D} [inst : ∀ v, Algebra (T v).J.Q.c.F D.what₂.LL]
  {R : ∀ v, RealDat D A (T v).J.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ v (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), ((R v).MW i σ).Vec}
  {h : ∀ v, LawsP (T v).toTop} {fw : ∀ v, FWTie (T v).J (R v) κ (v₀ v)} {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D}
  {p : HeightOneSpectrum (𝓞 D.what₂.LL) → ℕ}
  {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
  {O : OnObj S P oc} {ι : Bs.J → Fin D.R.m} {wL wF : ∀ i, WeightFamilies.Wt D ((ι i : ℕ) + 1)} {nT : ℕ}
  {z : ∀ v i, (Fin (O.nZ i) → D.what₂.LL) ≃ₗ[D.what₂.LL]
    D.what₂.LL ⊗[(recB (h v).toLawsCore).KO] (recB (h v).toLawsCore).Cusp ((ι i : ℕ) + 1) (κ (ι i))}
  {act : ∀ v i, P → (recB (h v).toLawsCore).Cusp ((ι i : ℕ) + 1) (κ (ι i)) →
    (recB (h v).toLawsCore).Cusp ((ι i : ℕ) + 1) (κ (ι i))}
  {inc : P →* G}
  {ℓ : ∀ v i, G → (LaMod ((T v).Q.Dw ((ι i : ℕ) + 1)) (T v).Q.l ≃ₗ[𝓞 D.host.E] LaMod ((T v).Q.Dw ((ι i : ℕ) + 1)) (T v).Q.l)}
  {U : Subgroup G} {ψ : U →* D.what₂.LLˣ} {ph : HeightOneSpectrum (𝓞 D.what₂.LL) → Bs.J → ℂ}
  {y : ∀ v i, (Fin (O.nX v i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (srcDim A (ι i) ((R v).mu v) U ψ) → D.what₂.LL)}

end Row

end GlobalTheory.TraceClassRank
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryDoubleCosetOfGLintDoubleCoset
section
noncomputable section

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

namespace GlobalTheory.UnramDoubleCoset

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L]
  {ϖ : L} {σ : L →+* L} {q n : ℕ}

def intConj (hσ : ∀ x, Valued.v (σ x) = Valued.v x) : intL L →+* intL L :=
  (σ.comp (intL L).subtype).codRestrict (intL L) fun x => by
    show Valued.v (σ x) ≤ 1
    rw [hσ]; exact x.2


open scoped Valued in
theorem exists_dvd_norm_sub_X (hU : IsUnramInv ϖ σ q) (f : Polynomial (intL L)) (hf : f.Monic)
    (hfc : f.map (intConj hU.2.1) = f) (h0 : IsUnit (f.coeff 0)) :
    ∃ p : Polynomial (intL L), f ∣ p * p.map (intConj hU.2.1) - Polynomial.X := by
  haveI := P.fSatake_nontriv hU
  letI : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne _ (e := 2) (by norm_num)
  obtain ⟨hσσ, hσ, h3, h4, ⟨x, hx1, hx2⟩, hq, hcard⟩ := hU
  let A := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring
  haveI : IsDiscreteValuationRing A := (Valued.v : Valuation L _).valuationSubring_isDiscreteValuationRing
  haveI : Finite (A ⧸ IsLocalRing.maximalIdeal A) :=
    Nat.finite_of_card_ne_zero (ne_of_eq_of_ne hcard (pow_ne_zero _ (by omega)))
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal A) A := by
    refine NormIntegers.isAdicComplete_of_fg (C := L) ⟨?_, ?_, ?_⟩
      (IsNoetherian.noetherian _) (IsLocalRing.maximalIdeal.isMaximal _).ne_top
    · exact FaithfulSMul.algebraMap_injective _ _
    · intro x
      have : ‖(x : L)‖ ≤ 1 := Valued.toNormedField.norm_le_one_iff.2 x.2
      exact_mod_cast this
    · intro x hx
      have : ‖x‖ ≤ 1 := by exact_mod_cast hx
      exact ⟨⟨x, Valued.toNormedField.norm_le_one_iff.1 this⟩, rfl⟩
  let c : A →+* A := intConj hσ
  have hc : ∀ x, c (c x) = x := fun x => Subtype.ext (hσσ x)
  have hI : ∀ x ∈ IsLocalRing.maximalIdeal A, c x ∈ IsLocalRing.maximalIdeal A := by
    intro x hx hu
    exact hx (by simpa [hc] using hu.map c)
  have hω : ∃ ω, IsUnit (ω - c ω) := by
    refine ⟨⟨x, hx1⟩, ?_⟩
    rw [(Valuation.valuationSubring.integers _).isUnit_iff_valuation_eq_one]
    show Valued.v (x - σ x) = 1
    rw [Valuation.map_sub_swap, hx2]
  exact GlobalTheory.InertNorm.exists_dvd_mul_map_sub_X A _ c hc hI hω f hf hfc h0

theorem exists_antiJ_frame (hU : IsUnramInv ϖ σ q) (n : ℕ) :
    ∃ h ∈ GLint (Fin n) (intL L), cT σ h.1 * 1 * h.1 = antiJ L n := by
  let c := intConj hU.2.1
  have hc : ∀ x, c (c x) = x := fun x => Subtype.ext (hU.1 x)
  let ι := (intL L).subtype
  let B : Matrix (Fin n) (Fin n) (intL L) := fun i j => if i.val + j.val + 1 = n then 1 else 0
  have hBι : B.map ι = antiJ L n := by
    refine Matrix.ext fun i j => ?_
    show ι (if i.val + j.val + 1 = n then 1 else 0) = if i.val + j.val + 1 = n then 1 else 0
    rw [apply_ite ι, map_one, map_zero]
  have hB : cT c B = B := by
    refine Matrix.ext fun i j => ?_
    show c (if j.val + i.val + 1 = n then 1 else 0) = if i.val + j.val + 1 = n then 1 else 0
    rw [apply_ite c, map_one, map_zero, add_comm j.val]
  have hBB : B * B = 1 := Matrix.map_injective (f := ι) Subtype.val_injective (by
    show (B * B).map ι = (1 : Matrix _ _ _).map ι
    rw [Matrix.map_mul, hBι, GlobalTheory.UnitarySwap.antiJ_mul_self, Matrix.map_one _ (map_zero ι) (map_one ι)])
  obtain ⟨p, hp⟩ := GlobalTheory.UnitaryDoubleCoset.exists_poly_norm hc (exists_dvd_norm_sub_X hU) hB
    (IsUnit.of_mul_eq_one _ hBB)
  have h1 : (B * cT c (Polynomial.aeval B p)) * Polynomial.aeval B p = 1 := by rw [Matrix.mul_assoc, hp, hBB]
  refine ⟨bc ι ⟨Polynomial.aeval B p, _, mul_eq_one_comm.1 h1, h1⟩, ⟨_, rfl⟩, ?_⟩
  show cT σ ((Polynomial.aeval B p).map ι) * 1 * (Polynomial.aeval B p).map ι = _
  rw [Matrix.mul_one, GlobalTheory.UnitaryDoubleCoset.cT_map ι (c := c) (fun _ => rfl), ← Matrix.map_mul, hp, hBι]

theorem doubleCoset_one (hU : IsUnramInv ϖ σ q) :
    ∀ g ∈ UJ σ (1 : Matrix (Fin n) (Fin n) L), ∀ g' ∈ UJ σ (1 : Matrix (Fin n) (Fin n) L),
    ∀ h ∈ GLint (Fin n) (intL L), ∀ k ∈ GLint (Fin n) (intL L), g' = h * g * k →
      ∃ k₁ ∈ UJ σ (1 : Matrix (Fin n) (Fin n) L) ⊓ GLint (Fin n) (intL L),
      ∃ k₂ ∈ UJ σ (1 : Matrix (Fin n) (Fin n) L) ⊓ GLint (Fin n) (intL L), g' = k₁ * g * k₂ := by
  rintro g hg g' hg' _ ⟨h, rfl⟩ _ ⟨k, rfl⟩ e
  obtain ⟨k₁, hk₁, k₂, hk₂, ⟨M, hM⟩, e'⟩ :=
    GlobalTheory.UnitaryDoubleCoset.exists_unitary_factors (intL L).subtype (c := intConj hU.2.1) (σ := σ) (fun _ => rfl)
      (fun x => Subtype.ext (hU.1 x)) (exists_dvd_norm_sub_X hU) hg hg' h k e
  refine ⟨k₁, hk₁, k₂, ⟨hk₂, ?_⟩, e'⟩
  refine GlobalTheory.UnitarySwap.mem_GLint_of_unitary (J := 1) hU.2.1 (one_mem _) hk₂ fun i j => ?_
  rw [hM]
  exact (M i j).2


open GlobalTheory.InertDoubleCoset in
theorem doubleCoset_GU_of_GL : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ (g g' : GU σ n) (a b : GL (Fin n) L), a ∈ GLint (Fin n) (intL L) → b ∈ GLint (Fin n) (intL L) → (g' : GL (Fin n) L) = a * g * b → ∃ k₁ ∈ KU σ n, ∃ k₂ ∈ KU σ n, g' = k₁ * g * k₂ := by
  intro L _ _ _ ϖ σ q n hU g g' a b ha hb e
  obtain ⟨h, hh, eh⟩ := exists_antiJ_frame hU n
  obtain ⟨k₁, h₁, k₂, h₂, e'⟩ := doubleCoset_one hU _
    (conj_mem_UJ σ (inv_frame σ eh) g.2) _ (conj_mem_UJ σ (inv_frame σ eh) g'.2) (h * a * h⁻¹)
    (mul_mem (mul_mem hh ha) (inv_mem hh)) (h * b * h⁻¹) (mul_mem (mul_mem hh hb) (inv_mem hh)) (by rw [e]; group)
  have m : ∀ k ∈ UJ σ (1 : Matrix (Fin n) (Fin n) L) ⊓ GLint (Fin n) (intL L),
      ∃ k' ∈ KU σ n, (k' : GL (Fin n) L) = h⁻¹ * k * h := fun k hk =>
    ⟨⟨_, conj_mem_UJ σ eh hk.1⟩, ⟨conj_mem_UJ σ eh hk.1,
      mul_mem (s := GLint (Fin n) (intL L)) (mul_mem (inv_mem hh) hk.2) hh⟩, rfl⟩
  obtain ⟨l₁, m₁, e₁⟩ := m k₁ h₁
  obtain ⟨l₂, m₂, e₂⟩ := m k₂ h₂
  refine ⟨l₁, m₁, l₂, m₂, Subtype.ext ?_⟩
  simp only [Subgroup.coe_mul, e₁, e₂]
  calc (g' : GL (Fin n) L) = h⁻¹ * (h⁻¹⁻¹ * g' * h⁻¹) * h := by group
    _ = _ := by rw [e']; group

end GlobalTheory.UnramDoubleCoset

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitarySatakeTransformIsLaurentPolynomial
section
noncomputable section

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

namespace GlobalTheory.LFun.SatCoef

open GlobalTheory.InertThetaCompare

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n q : ℕ} {ϖ : L}


open Classical in
def cellSum (ϖ : L) (h : GU σ n → ℂ) (a : Fin (n / 2) → ℤ) : ℂ :=
  ∑ᶠ x : GU σ n ⧸ KU σ n, if Cell ϖ a x then h x.out else 0

theorem exists_of_cellSum {h : GU σ n → ℂ} {a : Fin (n / 2) → ℤ} (ha : cellSum ϖ h a ≠ 0) :
    ∃ x : GU σ n ⧸ KU σ n, h x.out ≠ 0 ∧ Cell ϖ a x := by
  classical
  by_contra hne
  push Not at hne
  refine ha (finsum_eq_zero_of_forall_eq_zero fun x => ?_)
  split_ifs with hx
  · by_contra h0
    exact hne x h0 hx
  · rfl

theorem finite_supp (hU : IsUnramInv ϖ σ q) {h : GU σ n → ℂ} (hh : h ∈ Hecke ℂ (KU σ n)) :
    {x : GU σ n ⧸ KU σ n | h x.out ≠ 0}.Finite :=
  P.finite_support_cosets (P.isCommensurated_integral_unitary_of_unramified hU n) hh.2

theorem finite_cellSum (hU : IsUnramInv ϖ σ q) {h : GU σ n → ℂ} (hh : h ∈ Hecke ℂ (KU σ n)) :
    {a | cellSum ϖ h a ≠ 0}.Finite := by
  refine ((finite_supp hU hh).biUnion (t := fun x => {a | Cell ϖ a x}) fun x _ => Set.Subsingleton.finite ?_).subset ?_
  · rintro a ⟨u, hu, k, hk, e⟩ a' ⟨u', hu', k', hk', e'⟩
    exact P.fSatake_cell_unique hU (Nat.mul_div_le n 2) hu hu' hk hk' (e.symm.trans e')
  · intro a ha
    obtain ⟨x, hx⟩ := exists_of_cellSum ha
    exact Set.mem_biUnion hx.1 hx.2

theorem cellSum_dosetInd (hU : IsUnramInv ϖ σ q) (t : GU σ n) (ε : Fin (n / 2) → ℤ)
    (ht : ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = tMat ϖ n (n / 2) ε) :
    cellSum ϖ (dosetInd ℂ (KU σ n) t) ε ≠ 0 := by
  classical
  have hf : {x : GU σ n ⧸ KU σ n | Cell ϖ ε x ∧ dosetInd ℂ (KU σ n) t x.out ≠ 0}.Finite :=
    (finite_supp hU (Final.DosetIndMem _ _ ℂ t)).subset fun x hx => hx.2
  have key : ∀ x : GU σ n ⧸ KU σ n, ∀ [Decidable (Cell ϖ ε x)],
      (if Cell ϖ ε x then dosetInd ℂ (KU σ n) t x.out else 0) = if x ∈ hf.toFinset then 1 else 0 := by
    intro x _
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    by_cases h1 : Cell ϖ ε x
    · by_cases h2 : dosetInd ℂ (KU σ n) t x.out = 0
      · simp [h1, h2]
      · rw [if_pos h1, if_pos ⟨h1, h2⟩]
        unfold dosetInd at h2 ⊢
        exact Set.indicator_of_mem (Set.mem_of_indicator_ne_zero h2) _
    · simp [h1]
  unfold cellSum
  rw [finsum_congr fun x => @key x _, finsum_eq_sum_of_support_subset (s := hf.toFinset) _ (fun x hx => by
    by_contra h
    exact hx (if_neg h)), Finset.sum_congr rfl fun x hx => if_pos hx]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, ne_eq, Nat.cast_eq_zero, Finset.card_eq_zero]
  refine Finset.ne_empty_of_mem (a := (QuotientGroup.mk t : GU σ n ⧸ KU σ n)) ?_
  rw [Set.Finite.mem_toFinset]
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (KU σ n) t
  refine ⟨⟨1, ⟨P.fSatake_borel_one, fun i => by simp⟩, k, k.2, ?_⟩, ?_⟩
  · rw [hk]
    simp only [Subgroup.coe_mul, Units.val_mul, ht, OneMemClass.coe_one, Units.val_one, Matrix.mul_one]
  · rw [hk]
    unfold dosetInd
    rw [Set.indicator_of_mem (DoubleCoset.mem_doubleCoset.2 ⟨1, one_mem _, k.1, k.2, by rw [one_mul]⟩ :
      t * k.1 ∈ DoubleCoset.doubleCoset t (KU σ n : Set (GU σ n)) (KU σ n : Set (GU σ n)))]
    exact one_ne_zero

theorem satU_laurent : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ h ∈ Hecke ℂ (KU σ n), ∃ s : (Fin (n / 2) → ℤ) →₀ ℂ, (∀ α : Fin (n / 2) → ℂ, SatU ϖ q h α = s.sum fun a c => c * ∏ i, α i ^ a i) ∧ (∀ κ, s κ ≠ 0 → ∃ g : GU σ n, h g ≠ 0 ∧ ∃ u : GU σ n, IsUnipU u ∧ ∃ k ∈ KU σ n, ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = tMat ϖ n (n / 2) κ * ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((k : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) ∧ ∀ (t : GU σ n) (ε : Fin (n / 2) → ℤ), ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = tMat ϖ n (n / 2) ε → h = dosetInd ℂ (KU σ n) t → s ε ≠ 0 := by
  intro L _ _ ϖ σ q n hU h hh
  have hq : (q : ℂ) ≠ 0 := by
    have := hU.2.2.2.2.2.1
    exact_mod_cast (by omega : q ≠ 0)
  let f : (Fin (n / 2) → ℤ) → ℂ := fun a =>
    (∏ i : Fin (n / 2), (q : ℂ) ^ (-(a i) * ((n : ℤ) - 1 - 2 * (i.val : ℤ)))) * cellSum ϖ h a
  have hf : (Function.support f).Finite := (finite_cellSum hU hh).subset fun a ha => right_ne_zero_of_mul ha
  refine ⟨Finsupp.ofSupportFinite f hf, fun α => ?_, fun κ hκ => ?_, fun t ε ht e => ?_⟩
  · have e : SatU ϖ q h α = ∑ᶠ a, f a * ∏ i, α i ^ a i := by
      unfold SatU
      refine finsum_congr fun a => ?_
      rw [Finset.prod_mul_distrib, mul_comm (∏ i, α i ^ a i), mul_right_comm]
      rfl
    rw [e, Finsupp.sum]
    exact finsum_eq_sum_of_support_subset _ fun a ha =>
      Finset.mem_coe.2 (Finsupp.mem_support_iff.2 (left_ne_zero_of_mul ha))
  · obtain ⟨x, h1, h2⟩ := exists_of_cellSum (right_ne_zero_of_mul (show f κ ≠ 0 from hκ))
    exact ⟨x.out, h1, h2⟩
  · subst e
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ hq) (cellSum_dosetInd hU t ε ht)

end GlobalTheory.LFun.SatCoef

end
end

