module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RationalRootsDef
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemSpanOfSemilinear
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0346
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0355
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0344
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0351
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import ReciprocityTheory.GaloisValuations.Global
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0353
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Formalism.LocalToGlobal.IndefiniteReal.SquareIntegrableTransfer
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0026
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0251
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateEvaluationMapSmoothAutomorphicValues
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0327
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0348
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FillPreservesIdempotent
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0313
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0352
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0365
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0350

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLayerParametersAdmissible
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top.LayOfCore

variable {K : Ctx} {X : Stages} {f : Fr X.B.toPre} {T : TwDat X.B}

theorem ties (c : V4.Core K X f T) : Formalism.BasicNotions.Ties X.toD7 :=
  ⟨c.real.cdScale, c.real.dsig_all, c.row.bu_def, twCoverPair_of_tie _ _ c.nch_tie, X.B.coeffGaloisSubfield_isGalois, c.row.ft_occ⟩

theorem dgam (c : V4.Core K X f T) : DGamDef X.toD7 := fun u μ =>
  ⟨fun u' μ' i hi x => by
    rw [c.col.one u μ, ← c.col.one u' μ']
    exact (X.toD7.chTw u' μ').dvd_DGam i hi x, c.col.one u μ⟩

noncomputable def lay (c : V4.Core K X f T) (hv : StandardLattice.VolumeEqMass₂ X.toD7) : Lay X.toD7 :=
  { c.O with
    ties := ties c
    rrDef := c.row.rrDef
    th_io := c.th_io
    vram := c.gy.vram
    fills_all := c.gy.fills
    idx := c.row.idx
    kap_def := c.row.kap_def
    lam_def := c.row.lam_def
    kapR_def := c.row.kapR_def
    piG_lev := c.col.piG_lev
    piT_lev := c.col.piT_lev
    seen := c.col.seen
    tauOf := c.col.tauOf
    dgam := dgam c
    nch_tie := c.nch_tie
    rationalRoots_def := c.row.rationalRoots_def
    duStar_def := (sizes_eq_count K X c.isOver hv c.dsig_eq).1
    Dstar_def := (sizes_eq_count K X c.isOver hv c.dsig_eq).2
    gauge_def := c.gauge_def }

theorem layObj_lay (c : V4.Core K X f T) (hv : StandardLattice.VolumeEqMass₂ X.toD7) : layObj (lay c hv) = c.O := rfl

theorem isOver (c : V4.Core K X f T) : Over X.toD7 K.P K.Lv := by
  obtain ⟨sp, hT, hY, hA, hV, hz, h, -⟩ := c.isOver
  exact ⟨sp, hT, hY, hA, hV, hz, X, h, rfl⟩

theorem untw (c : V4.Core K X f T) (w : X.toD7.what₂.places.Pl) (hw : X.toD7.what₂.muAt w = X.toD7.what₂.mu0) (j : ℕ)
    (h1 : 1 ≤ j) (h2 : j ≤ X.toD7.R.m) : X.toD7.what₂.Aj j w = 0 := by
  have a := c.row.untw w hw j h1 h2
  have b := c.row.untw (X.toD7.what₂.places.conj w) ((X.toD7.what₂.muAt_conj w).trans hw) j h1 h2
  unfold Rows.Data.Aj
  rw [hw, a.1, a.2, b.1]
  rfl

theorem fin (c : V4.Core K X f T) : {w | X.toD7.what₂.muAt w ≠ X.toD7.what₂.mu0}.Finite :=
  (TwFin.tw_fin X.B f T).2.2.2.subset fun w hw => c.mu.sub w (by_contra fun h => hw (c.mu.off w h))

theorem ledOK (c : V4.Core K X f T) (hv : StandardLattice.VolumeEqMass₂ X.toD7) : LedOK K.s K.C K.cD K.ch (lay c hv) K.a K.b := by
  intro L hs hW hV
  refine ⟨fun w hw j hj => ?_, fun I hI he hk hf => ⟨c.gy.led L hs hW hV I hI he hk hf, fun u w hg => ?_, fun u w hg _ =>
    NP_full X.toD7 L I c.O.Gy K.C.GK c.O.cmp c.gy.vram u w hg⟩⟩
  · refine c.fval L hs hW hV w (fun h => (TwFin.tw_fin X.B f T).2.1 w ?_) j hj
    rw [← c.mu.tw w, ← c.mu.on w h]
    exact (congrArg c.xi hw).trans c.mu.mu0
  · have hC : K.C.cX.Ce = 1 := by
      have := K.std.1
      unfold FC.Fixed at this
      tauto
    rw [(c.gatNum u w hg).2, he, hC, hs]

theorem tupUsed (c : V4.Core K X f T) : DQ.TupUsedAt X.toD7 := by
  intro μ
  have hμ : c.xi μ ∈ T.set f := c.mu.range ▸ Set.mem_range_self μ
  rcases hμ with (h | h | h) | ⟨w, h⟩
  · exact .inl (c.mu.inj (h.trans c.mu.mu0.symm))
  · exact .inr (.inl (c.mu.inj (h.trans c.mu.star.symm)))
  · exact .inr (.inr (.inl (c.mu.inj (h.trans c.mu.star'.symm))))
  · by_cases hw : w ∈ c.Wt
    · exact .inr (.inr (.inr ⟨w, (c.mu.inj (h.symm.trans (c.mu.tw w).symm)).trans (c.mu.on w hw).symm⟩))
    · unfold TwDat.xiTw at h
      rw [c.mu.supp w hw, mul_one] at h
      split_ifs at h
      · exact .inr (.inr (.inl (c.mu.inj (h.symm.trans c.mu.star'.symm))))
      · exact .inr (.inl (c.mu.inj (h.symm.trans c.mu.star.symm)))

theorem ev_imp {p q : Ctx → Prop} (hp : Ev p) (h : ∀ K, p K → q K) : Ev q := by
  obtain ⟨ε0, h0, H⟩ := hp
  refine ⟨ε0, h0, fun eps C8 a1 a2 a3 a4 => ?_⟩
  obtain ⟨K0, H⟩ := H eps C8 a1 a2 a3 a4
  refine ⟨K0, fun C b1 b2 b3 => ?_⟩
  obtain ⟨c1, H⟩ := H C b1 b2 b3
  refine ⟨c1, fun cD hcD => ?_⟩
  obtain ⟨c2, H⟩ := H cD hcD
  refine ⟨c2, fun ch hch => ?_⟩
  obtain ⟨x0, H⟩ := H ch hch
  exact ⟨x0, fun K d1 d2 d3 d4 d5 => h K (H K d1 d2 d3 d4 d5)⟩

theorem lay_of_core : Ev fun K => ∀ (X : Stages) (f : Fr X.B.toPre) (T : TwDat X.B) (c : V4.Core K X f T),
    StandardLattice.VolumeEqMass₂ X.toD7 → ∃ Y : Lay X.toD7, layObj Y = c.O ∧ Over X.toD7 K.P K.Lv ∧ RecOK K.s K.C K.cD X.toD7 ∧
      LedOK K.s K.C K.cD K.ch Y K.a K.b ∧ DQ.TupUsedAt X.toD7 :=
  ev_imp TamePow.tame_of_pow fun _ hK X _ _ c hv =>
    ⟨lay c hv, layObj_lay c hv, isOver c,
      ⟨c.del, c.etaF, untw c, fin c, (Full.dgam_pos_and_full X.toD7).1, (Full.dgam_pos_and_full X.toD7).2,
        hK X c.isOver c.chiT, c.col.mink, c.col.atT⟩, ledOK c hv, tupUsed c⟩

end GlobalTheory.Mem.Top.LayOfCore
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowValuationLtOfIntegralAlgClosurePlaceStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_valuation_lt_of_integral_algClosure_place : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A P → ∀ x c : Ω, IsIntegral ℤ x → IsIntegral ℤ c → c ≠ 0 → A.valuation x < 1 → ∃ k : ℕ, A.valuation x ^ k < A.valuation c := by
  first | exact @GlobalTheory.MaxIdealPow.exists_pow_lt_valuation | exact GlobalTheory.MaxIdealPow.exists_pow_lt_valuation | (intros; apply GlobalTheory.MaxIdealPow.exists_pow_lt_valuation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsResidueCharOfTameCharPrimeResidueField
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2

namespace GlobalTheory.TameTau

theorem tameChar_of_prime_residue : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (P : HeightOneSpectrum (𝓞 E)) (g : ℕ), g.Prime → normV P = g → ((g : ℕ) : 𝓞 E) ∈ P.asIdeal → ∀ {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ (χ : G E Ω →* Oˣ), Continuous (fun g => ((χ g : Oˣ) : O)) → (∀ A : ValuationSubring Ω, IsPlaceOver A P → ∀ σ ∈ Ine (F := E) A, χ σ ^ (g - 1) = 1) → ∃ τ : (ZMod g)ˣ →* Oˣ, ∀ (x : (ZMod g)ˣ) (u : 𝓞 E), (((x : ZMod g).val : 𝓞 E) - u) ∈ P.asIdeal → τ x = NX.tameVal χ P 1 u := by
  intro E Ω _ _ _ _ _ P g hg hN hgP O _ _ _ _ _ hadic χ hχc hχI
  have : NeZero g := ⟨hg.ne_zero⟩
  have : Fact (1 < g) := ⟨hg.one_lt⟩
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  set m := g - 1 with hm_def
  have hm0 : 0 < m := by have := hg.two_le; omega
  have hPtop : P.asIdeal ≠ ⊤ := P.isPrime.ne_top
  have hmP : ((m : ℕ) : 𝓞 E) ∉ P.asIdeal := by
    intro h
    apply hPtop
    rw [Ideal.eq_top_iff_one]
    have h1 : ((g : ℕ) : 𝓞 E) = (m : 𝓞 E) + 1 := by
      have : g = m + 1 := by have := hg.two_le; omega
      rw [this]; push_cast; ring
    have := P.asIdeal.sub_mem hgP h
    rwa [h1, add_sub_cancel_left] at this
  have hNm : normV P - 1 = m := by rw [hN]
  obtain ⟨ϖ, hϖ, hϖ2⟩ : ∃ ϖ : 𝓞 E, ϖ ∈ P.asIdeal ∧ ϖ ∉ P.asIdeal ^ 2 := by
    have hlt : P.asIdeal ^ (1 + 1) < P.asIdeal ^ 1 := Ideal.pow_succ_lt_pow P.ne_bot 1
    rw [pow_one] at hlt
    exact SetLike.exists_of_lt hlt
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap E Ω (ϖ : E)) hm0
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow hm0.ne', eq_comm, map_eq_zero_iff _ (algebraMap E Ω).injective] at hπ
    have hϖ0 : ϖ = 0 := by exact_mod_cast hπ
    exact hϖ2 (hϖ0 ▸ Ideal.zero_mem _)
  obtain ⟨A₀, hA₀⟩ := exists_isPlaceOver Ω P
  have hvm : ¬ A₀.valuation (m : Ω) < 1 := by
    intro h; apply hmP; rw [← hA₀]; simpa using h
  have hex : ∀ u : 𝓞 E, u ∉ P.asIdeal → ∃ σ : G E Ω, σ ∈ Ine (F := E) A₀ ∧ ∃ ζ : Ω, ζ ^ m = 1 ∧
      A₀.valuation (ζ - algebraMap E Ω (u : E)) < 1 ∧ σ π = ζ * π := by
    intro u hu
    obtain ⟨ζ, hζ, hζu⟩ := _root_.GlobalTheory.TameTau.exists_root_congr_unit A₀ P hA₀ u hu
    rw [hNm] at hζ
    obtain ⟨σ, hσ, hσπ⟩ := GlobalTheory.T.inertia_acts_on_tame_root A₀ P hA₀ m hm0 hmP ϖ hϖ hϖ2 π hπ ζ hζ
    exact ⟨σ, hσ, ζ, hζ, hζu, hσπ⟩
  have hrep : ∀ σ ∈ Ine (F := E) A₀, ∀ u : 𝓞 E, A₀.valuation (σ π / π - algebraMap E Ω (u : E)) < 1 →
      NX.TameRep P 1 σ u := by
    intro σ hσ u h
    refine ⟨A₀, hA₀, hσ, ϖ, π, hϖ, hϖ2, by rw [hNm]; exact hπ, ?_⟩
    rw [zpow_one]; exact h
  have hkey : ∀ (σ : G E Ω) (u : 𝓞 E), NX.TameRep P 1 σ u → NX.tameVal χ P 1 u = χ σ := by
    intro σ u h
    rw [NX.tameVal, dite_eq_left ⟨σ, h⟩]
    exact GlobalTheory.T.tameChar_eq_of_tameRep_congr P hadic χ hχc (by rw [hNm]; exact hm0) (by rw [hNm]; exact hmP)
      (by intro A hA σ' hσ'; rw [hNm]; exact hχI A hA σ' hσ') _ σ u u (⟨σ, h⟩ : ∃ σ, NX.TameRep P 1 σ u).choose_spec h (by simp)
  have hlt : ∀ a b : Ω, A₀.valuation a ≤ 1 → A₀.valuation b < 1 → A₀.valuation (a * b) < 1 := by
    intro a b ha hb
    rw [map_mul]
    calc A₀.valuation a * A₀.valuation b ≤ 1 * A₀.valuation b := by gcongr
      _ = A₀.valuation b := one_mul _
      _ < 1 := hb
  have hle : ∀ a b : Ω, A₀.valuation a ≤ 1 → A₀.valuation (a - b) < 1 → A₀.valuation b ≤ 1 := by
    intro a b ha hab
    have e : b = a - (a - b) := by ring
    rw [e]
    exact (Valuation.map_sub _ _ _).trans (max_le ha hab.le)
  have hP1 : ∀ w : 𝓞 E, w ∈ P.asIdeal → A₀.valuation (algebraMap E Ω (w : E)) < 1 := fun w hw => (hA₀ w).2 hw
  let U : (ZMod g)ˣ → 𝓞 E := fun x => (((x : ZMod g)).val : 𝓞 E)
  have hcong : ∀ x y : (ZMod g)ˣ, U x * U y - U (x * y) ∈ P.asIdeal := by
    intro x y
    simp only [U, Units.val_mul, ZMod.val_mul]
    have e : (((x : ZMod g).val * (y : ZMod g).val : ℕ) : 𝓞 E) =
        (g : 𝓞 E) * (((x : ZMod g).val * (y : ZMod g).val / g : ℕ) : 𝓞 E) +
          (((x : ZMod g).val * (y : ZMod g).val % g : ℕ) : 𝓞 E) := by
      exact_mod_cast (Nat.div_add_mod ((x : ZMod g).val * (y : ZMod g).val) g).symm
    rw [← Nat.cast_mul, e, add_sub_cancel_right]
    exact P.asIdeal.mul_mem_right _ hgP
  have hU1 : U 1 = 1 := by
    show (((1 : (ZMod g)ˣ) : ZMod g).val : 𝓞 E) = 1
    rw [Units.val_one, ZMod.val_one, Nat.cast_one]
  have hUP : ∀ x, U x ∉ P.asIdeal := by
    intro x hx
    have h := hcong x x⁻¹
    rw [mul_inv_cancel, hU1] at h
    apply hPtop
    rw [Ideal.eq_top_iff_one]
    have e : (1 : 𝓞 E) = U x * U x⁻¹ - (U x * U x⁻¹ - 1) := by ring
    rw [e]
    exact P.asIdeal.sub_mem (P.asIdeal.mul_mem_right _ hx) h
  choose σx hσx ζx hζx hζu hσπ using fun x => hex (U x) (hUP x)
  have hq : ∀ x, σx x π / π = ζx x := fun x => by rw [hσπ x, mul_div_cancel_right₀ _ hπ0]
  have hζ1 : ∀ x, A₀.valuation (ζx x) = 1 := fun x => valuation_eq_one_of_pow_eq_one A₀ hm0.ne' (hζx x)
  have hrepx : ∀ x, NX.TameRep P 1 (σx x) (U x) := fun x => hrep _ (hσx x) _ (by rw [hq]; exact hζu x)
  refine ⟨MonoidHom.mk' (fun x => χ (σx x)) ?_, ?_⟩
  · intro x y
    rw [← map_mul, ← hkey _ _ (hrepx (x * y))]
    refine hkey _ _ (hrep _ ((Ine (F := E) A₀).mul_mem (hσx x) (hσx y)) _ ?_)
    rw [GlobalTheory.TameTau.quot_mul (hσx x) m hvm hπ0 hπ, hq, hq]
    have e : ζx x * ζx y - algebraMap E Ω (U (x * y) : E) =
        ζx x * (ζx y - algebraMap E Ω (U y : E)) + algebraMap E Ω (U y : E) * (ζx x - algebraMap E Ω (U x : E)) +
          algebraMap E Ω ((U x * U y - U (x * y) : 𝓞 E) : E) := by
      push_cast; ring
    rw [e]
    refine Valuation.map_add_lt _ (Valuation.map_add_lt _ (hlt _ _ (hζ1 x).le (hζu y))
      (hlt _ _ (hle _ _ (hζ1 y).le (hζu y)) (hζu x))) (hP1 _ (hcong x y))
  · intro x u hxu
    show χ (σx x) = _
    refine (hkey _ _ (hrep _ (hσx x) _ ?_)).symm
    rw [hq]
    have e : ζx x - algebraMap E Ω (u : E) = (ζx x - algebraMap E Ω (U x : E)) +
        algebraMap E Ω ((U x - u : 𝓞 E) : E) := by
      push_cast; ring
    rw [e]
    exact Valuation.map_add_lt _ (hζu x) (hP1 _ hxu)

end GlobalTheory.TameTau
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowLevelTranslatedEvaluationOfConjRow
section
open Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section

namespace GlobalTheory.Mem.SRe

theorem exists_multR_eval_of_star_mem : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∀ (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (v₀ : (MP R).Vec), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (Formalism.MainNotions.S.uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → (∀ τ, c τ (v₀ τ : (MP R).H τ) = X.B.w (X.pl.symm τ)) → ∀ φ : L2X X, star φ ∈ HHX X → ∃ S ∈ MultR R F, φ =ᵐ[muX X] (fun x => ev (MP R) v₀ S ((iotaX X h).symm x * t)) := by
  intro hIC hCD hDU hFD D G' _ _ Pl0 T A Ks _ _ _ R F X h t hιE hgap hlev hinf hν0 hsee c v₀ hc hv₀ φ hφ
  obtain ⟨Φ, hΦ, hΦw⟩ := Formalism.L2.SG.EvalTOnto.rows_eq_hom X (fun v => Formalism.L2.SG.EvalTPh.phLoc_int_of_gap X hgap v) (star φ) hφ
  have hrep := _root_.GlobalTheory.ConjRowRepModels.exists_contRep_models hIC hCD hDU hFD D G' Pl0 T A Ks R F X h t hιE hgap hlev hinf hν0 hsee c hc Φ hΦ
  have hmm : IsMultMap R.θ (MP R) (JR R F) (chiR R F) (GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t) :=
    { aut := _root_.GlobalTheory.ConjEvalAut.conjMap_isAutFunSm_see hIC hCD hDU hFD D G' Pl0 T A Ks R F X h t hιE hgap hlev hinf hν0 hsee c hc Φ hΦ hrep
      cusp := _root_.GlobalTheory.ConjRowCuspGap.conjMap_isCuspFun hIC hCD hDU hFD D G' Pl0 T A Ks R F X h t hιE hgap hlev hinf hν0 hsee c hc Φ hΦ hrep
      lev := _root_.GlobalTheory.ConjRowLevelSee.conjMap_level_of_seeAt hIC hCD hDU hFD D G' Pl0 T A Ks R F X h t hιE hgap hlev hinf hν0 hsee c hc Φ hΦ hrep
      equiv := fun τ g hg v w hw => GlobalTheory.T.conjugated_intertwiner_equivariant_real_place hIC hCD hDU hFD D G' Pl0 T A Ks R F X h t hιE hgap hlev hinf hν0 hsee c hc Φ hΦ hrep τ g hg v w hw
      cont := fun τ v x => _root_.GlobalTheory.ConjRowCont.conjMap_sobCont_ofIdE hIC hCD hDU hFD D G' Pl0 T A Ks R F X h t hιE hgap hlev hinf hν0 hsee c hc Φ hΦ hrep τ v x }
  have hmem : GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t ∈ MultR R F := (Submodule.span_le (p := MultR R F)).1 le_rfl hmm
  refine ⟨GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t, hmem, ?_⟩
  · have hw : GlobalTheory.ConjRowMult.vecC X (MP R) c v₀ = X.B.w := GlobalTheory.ConjRowMult.vecC_eq X (MP R) c v₀ X.B.w hv₀
    obtain ⟨ψ, hψ⟩ := hrep v₀
    rw [hw, hΦw] at hψ
    have key : ∀ x, ev (MP R) v₀ (GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t) ((iotaX X h).symm x * t) = star (ψ x) := by
      intro x
      rw [ev_apply]
      refine (GlobalTheory.ConjRowMult.conjMap_apply X (MP R) c Φ h t v₀ _).trans ?_
      rw [hw, hΦw, GlobalTheory.ConjRowMult.contRepL_spec X hψ]
      simp only [mul_inv_cancel_right, ContinuousMulEquiv.apply_symm_apply]
    filter_upwards [hψ.2.2, Lp.coeFn_star φ] with x h1 h2
    rw [key x, ← h1, h2, Pi.star_apply, star_star]

end GlobalTheory.Mem.SRe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTypes
section
noncomputable section

namespace GlobalTheory.ParRay

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem exists_types : GlobalTheory.Published.RayClassFieldSt → GlobalTheory.Published.ChebotarevDegreeOne → ∀ (D : D7) (hE : IsEmpty D.nd.Loc)
    (jE : D.host.E →+* Qb) (Pl : PlSide D), (∀ k, IsRayPrime (KQbar D jE) (D.host.QS * D.host.q * D.host.d) (D.host.g k)) →
    ∃ X h1 h0, X.tg = D.ntypes.tg ∧ X.teichC = D.ntypes.teichC ∧ X.eSer = D.ntypes.eSer ∧ X.cenAmb = D.ntypes.cenAmb ∧
      X.cenMt = D.ntypes.cenMt ∧ Nonempty (ParSide (setTy D hE X h1 h0) jE) ∧
      (Nonempty (GrpSide D) → IotaOk (setTy D hE X h1 h0) ⟨Pl.ι, Pl.ι_w, Pl.plB, Pl.plB_eq, Pl.plκ⟩) := by
  intro hray _ D hE jE Pl hg
  obtain ⟨h, hf, hgal, hab, hunr, hsplit⟩ := GlobalTheory.T.rayClassFieldHostConductor_isRayClassField hray D jE
  letI := algK D jE h
  have := nfOf hf
  let X : NTypes D.naut :=
    { D.ntypes with
      Mray := MrayC D jE
      instMray := inferInstance
      nfMray := nfOf hf
      algKM := algK D jE h
      Mray_gal := hgal
      Mray_ab := hab
      Mray_unr := hunr
      g_Mray := fun k => hsplit _ (hg k)
      iota := fun k _ w =>
        haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
        redHom (Pl.plB w) (Pl.plκ w) (D.ntypes.teichC k)
      iota_inj := fun k _ w x y hx hy cx cy hxy =>
        haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
        redHom_inj (Pl.plB w) (Pl.plκ w) (D.ntypes.teichC k) (D.ntypes.teichC_inj k) x y hx hy cx cy hxy
      Par := ParC D
      labPar := fun k σ v => D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut σ.1 (D.naut.plGw k v))
      labPar_monic := fun k σ v => σ.2.2.2.2 k v
      locPar := fun σ w => isoLoc D.nd D.naut σ.1 w
      locPar_dim := fun σ w => (GlobalTheory.RowPar.lpDim_isoLoc D.naut σ.1 w).trans σ.2.2.2.1
      labPar_def := fun _ _ _ => rfl
      MtPar := fun _ _ _ => ⊥
      AmbPar := fun _ _ => ⊥ }
  refine ⟨X, D.nStage_trivialCharacter_compat, D.nStage_trivialCharacter_coeff_eq, rfl, rfl, rfl, rfl, rfl, ⟨?_⟩, fun _ => ?_⟩
  · exact
      { eM := RingEquiv.refl _
        eM_K := fun _ => rfl
        eP := Equiv.refl _
        locPar_def := fun _ _ => rfl }
  · intro lam k v x
    rfl

end GlobalTheory.ParRay

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FamRPlaces
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3

theorem famR_places : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG →
    (∀ t P, P ∈ (famR X I hX U Xg tr).A.ok t ↔
      Bridge.SplitOff (P.1 : Pl X.toD7.host.E) ((L.Pg : Set (Pl X.toD7.host.E)) ∪ (L.Q t : Set (Pl X.toD7.host.E)))) ∧
    (∀ PP, Bridge.SplitOff PP (L.Pg : Set (Pl X.toD7.host.E)) → ∃ P : PlS X.B px, (P.1 : Pl X.toD7.host.E) = PP) ∧
    Bridge.InertTie (famR X I hX U Xg tr) (fun Q : PlI X.B px => (Q.1 : Pl X.toD7.host.E)) (L.Pg : Set (Pl X.toD7.host.E)) L.Q ∧
    (∀ PP, Bridge.InertOff PP (L.Pg : Set (Pl X.toD7.host.E)) → ∃ Q : PlI X.B px, (Q.1 : Pl X.toD7.host.E) = PP) := by
  intro X px I hX U Xg tr L eG _ _ hL _
  have hS : ∀ t : TupU I U, ((∅ : Set (HeightOneSpectrum (𝓞 X.B.fields.E))) ∪
      ((∅ : Finset (HeightOneSpectrum (𝓞 X.B.fields.E))) : Set (HeightOneSpectrum (𝓞 X.B.fields.E))) ∪
      ((Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1 : Finset (HeightOneSpectrum (𝓞 X.B.fields.E))) :
        Set (HeightOneSpectrum (𝓞 X.B.fields.E)))) =
      (L.Pg : Set (Pl X.toD7.host.E)) ∪ (L.Q t : Set (Pl X.toD7.host.E)) := by
    intro t
    rw [hL.Pg, hL.Q t]
    have e : I.Q (ixOf I U t) = Formalism.L2.Col.QE I.sel (t.1 : Chr X.B.fields.F X.B.fields.E X.B.fields.K) := by
      show Formalism.L2.Col.QE I.sel (I.tup (ixOf I U t) : Chr X.B.fields.F X.B.fields.E X.B.fields.K) = _
      rw [tup_ixOf I t]
    rw [e]
    simp [Formalism.L2.Col.rowSG, Formalism.L2.Col.uSG]
    rfl
  have hS0 : ((∅ : Set (HeightOneSpectrum (𝓞 X.B.fields.E))) ∪
      ((∅ : Finset (HeightOneSpectrum (𝓞 X.B.fields.E))) : Set (HeightOneSpectrum (𝓞 X.B.fields.E))) ∪
      (((X.B.primes px).vGs : Finset (HeightOneSpectrum (𝓞 X.B.fields.E))) : Set (HeightOneSpectrum (𝓞 X.B.fields.E)))) =
      (L.Pg : Set (Pl X.toD7.host.E)) := by
    rw [hL.Pg]
    simp
    rfl
  refine ⟨fun t P => ?_, fun PP hPP => ?_, ⟨Subtype.val_injective, fun t Q => ?_⟩, fun PP hPP => ?_⟩
  · show P.1 ∈ Formalism.L2.DIV.offSet ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ∅ ↔ _
    unfold Formalism.L2.DIV.offSet Formalism.IndefR.Bridge.SplitOff
    rw [Set.mem_setOf_eq, hS t]
    exact Iff.rfl
  · obtain ⟨h1, h2, h3⟩ := hPP
    refine ⟨⟨PP, h1, ?_, fun Q hQ => h3 Q ?_⟩, rfl⟩
    · rw [hS0]; exact h2
    · rw [← hS0]; exact hQ
  · show Q.1 ∉ _ ↔ _
    unfold Formalism.IndefR.Bridge.InertOff
    rw [hS t]
    have hc : ∀ P : Pl X.toD7.host.E, Formalism.L2.Col.conjPrime₂ P = P →
        Formalism.HermitianLatticesTheory.conjIdeal (K := X.toD7.host.E) P.asIdeal = P.asIdeal := fun P hP => by
      rw [Formalism.L2.Col.conjIdeal_asIdeal, hP]
    exact ⟨fun h => ⟨hc Q.1 Q.2.1, h⟩, fun h => h.2⟩
  · obtain ⟨h1, h2⟩ := hPP
    have hc : Formalism.L2.Col.conjPrime₂ PP = PP := HeightOneSpectrum.ext (by rw [← Formalism.L2.Col.conjIdeal_asIdeal]; exact h1)
    have hin : ∃ x : 𝓞 X.toD7.host.E, Formalism.L2.Col.cO X.toD7.host.E x - x ∉ PP.asIdeal := by
      obtain ⟨θ, t, ht, hθ⟩ := X.toD7.sp.cm.cmUnram.2.2 PP.asIdeal PP.isMaximal
      have e : Formalism.L2.Col.cO X.toD7.host.E θ = t := RingOfIntegers.ext ht.symm
      refine ⟨θ, fun h => hθ ?_⟩
      rw [e] at h
      rw [← neg_sub]
      exact PP.asIdeal.neg_mem h
    refine ⟨⟨PP, hc, hin, ?_⟩, rfl⟩
    rw [hS0]; exact h2

end GlobalTheory.Mem.R3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTypesOfTypesTrueReal
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Host Formalism.IndefR Formalism.IndefR.Links NumberField IsDedekindDomain

namespace GlobalTheory.HeightCounting

theorem goodTypes_of_typesTrue_real : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → GlobalTheory.Mem.Top.TypesTrue D.ntypes R.C.P R.C.W → GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators.GoodTypes R :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hL h => GlobalTheory.LiftRows.Inh.goodTypes_of_typesTrue hL h

end GlobalTheory.HeightCounting
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IwasawaDecompositionFactStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawaDecomposition_fact : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (σ : G E Ω), σ ∈ Dec (F := E) A → ∀ t : Ω, A.valuation (σ t) = A.valuation t := by
  first | exact @GlobalTheory.Dec_valuation_apply_eq | exact GlobalTheory.Dec_valuation_apply_eq | (intros; apply GlobalTheory.Dec_valuation_apply_eq <;> assumption)
end

