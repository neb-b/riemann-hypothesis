module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0656
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0369
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0330
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridDepthPaysEveryLoss
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0467
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealVectorsAllPlacesOfLocalData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0268
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaLiftLastStepsCouplingCosetOrbitInvari
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0435
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsRealFnNeZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0180
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RepresentationAtEveryPlace

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodNonvanishingOfArchimedeanInputs
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PeriodNePf

section General

variable {D : D7} {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar}


open Classical in
theorem real_translate (hθ : IsInfFam θ) {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ} :
    ∀ a ∈ GinfC V, ∀ v : SmT M, ∃ v' : SmT M, ∀ T ∈ MultT θ M J χ, ∀ h, T v' h = T v (h * a) := by
  refine GlobalTheory.Core.Rk.TopOnto.real_induction hθ _ (fun v => ⟨v, fun T _ h => by rw [mul_one]⟩) (fun a b ha hb v => ?_)
    fun τ g hg v => ?_
  · obtain ⟨v₁, f1⟩ := hb v
    obtain ⟨v₂, f2⟩ := ha v₁
    exact ⟨v₂, fun T hT h => by rw [f2 T hT, f1 T hT, mul_assoc]⟩
  · induction v using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      let w : M.sm τ := ⟨M.rep τ g (v τ), GlobalTheory.Core.Rk.TopOnto.rep_mem_sm M τ hg _ (v τ).2⟩
      refine ⟨r • PiTensorProduct.tprod ℂ (Function.update v τ w), fun T hT h => ?_⟩
      rw [map_smul, map_smul, Pi.smul_apply, Pi.smul_apply,
        GlobalTheory.Core.Rk.TopOnto.multT_rel v (Function.update v τ w) (h * atTau θ V τ g) h 1 (fun m hm => by
          rw [one_mul]; exact congrFun (hm.equiv τ g hg v w rfl) h) hT, one_mul]
    | add a b ha hb =>
      obtain ⟨a', f1⟩ := ha
      obtain ⟨b', f2⟩ := hb
      exact ⟨a' + b', fun T hT h => by rw [map_add, map_add, Pi.add_apply, Pi.add_apply, f1 T hT, f2 T hT]⟩

end General

end GlobalTheory.PeriodNePf

namespace GlobalTheory.PeriodNePf

variable {D : D7}

theorem exists_kf {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G) (hM : M.IsRow)
    (hCR : GlobalTheory.Published.CuspRapidDecay) (hHC : GlobalTheory.Published.HarishChandraModules)
    (M₀ : DSModel (Yc D 0) (parB (Ptw D) 0)) (MP : DSModel (G.V (.core 0)) (Node.par D sc.cGap (.core 0)))
    {t : SmT M₀ →ₗ[ℂ] (GA D (Yc D 0) → ℂ)} (ht : t ∈ Rows L W.θ M₀)
    {y : SmT MP →ₗ[ℂ] (GA D (G.V (.core 0)) → ℂ)} (hy : y ∈ CoreForms G W.θ 0 MP) (v : SmT MP) (w' : SmT M₀)
    (h0 : per0 G M (y v) (t w') ≠ 0) (w : SmT M₀) (hw : w ≠ 0) :
    ∃ a ∈ KF MP, per0 G M (y a) (t w) ≠ 0 := by
  have hθ := W.θ_is
  obtain ⟨hμ, hfd⟩ := (hM.row 0 (Nat.zero_le _)).haar_fund
  let vY : GlobalTheory.Unf.Vol (Yc D 0) := ⟨M.ν (.grid 0 0), M.fd (.grid 0 0), hμ, hfd⟩
  have hyv : ∀ a, RapidDec (G.V (.core 0)) (y a) := fun a =>
    (GlobalTheory.ChainOnto.MultRapid.multT_apply_rapidDec hCR D _ _ MP W.θ hθ _ _ y hy a).2.2
  have htw : RapidDec (Yc D 0) (t w) :=
    (GlobalTheory.ChainOnto.MultRapid.multT_apply_rapidDec hCR D _ _ M₀ W.θ hθ _ _ t ht w).2.2
  have hF : GlobalTheory.Unf.IsContAut (Yc D 0) (fun g => y v (stabilizerEmbedding G.sp.dec0 g)) :=
    ⟨fun γ hγ g => by
      simp only [GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul]
      exact (hyv v).1 _ (GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_rational _ γ hγ) _,
      (hyv v).2.1.comp (GlobalTheory.UnitaryEmbeddingProperties.continuous_unitaryEmbedding _)⟩
  have hB : ∃ C, ∀ g, ‖y v (stabilizerEmbedding G.sp.dec0 g)‖ ≤ C := by
    obtain ⟨C, hC⟩ := (hyv v).2.2 0
    exact ⟨C, fun g => by simpa using hC (stabilizerEmbedding G.sp.dec0 g)⟩
  obtain ⟨h, hh, hne⟩ : ∃ h ∈ GinfC (Yc D 0),
      ∫ g in vY.𝓕, y v (stabilizerEmbedding G.sp.dec0 g) * t w (g * h) ∂vY.μ ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact h0 (_root_.GlobalTheory.TransOrth.integral_eq_zero_of_translates hCR GlobalTheory.Mem.VolFin.finVol D W.θ hθ (Yc D 0) _ M₀ _ _ t ht vY _ hF hB w hw hn w')
  have e1 := GlobalTheory.QPl.LastOrb.setIntegral_mul_right vY
    (fun g => y v (stabilizerEmbedding G.sp.dec0 (g * h⁻¹)) * t w g) (fun γ hγ g => by
      simp only [mul_assoc, GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul]
      rw [(hyv v).1 _ (GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_rational _ γ hγ), htw.1 γ hγ g]) h
  simp only [mul_inv_cancel_right] at e1
  have hinf : stabilizerEmbedding G.sp.dec0 h⁻¹ ∈ GinfC (G.V (.core 0)) := GlobalTheory.RealType.Emb_mem_inf G.sp.dec0 (inv_mem hh)
  obtain ⟨v', hv'⟩ := real_translate hθ (M := MP) (J := (lev G (.core 0) : Set _)) (χ := 1) _ hinf v
  have hp : per0 G M (y v') (t w) ≠ 0 := by
    unfold per0
    simp only [hv' y hy]
    rw [e1] at hne
    simp only [GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul] at hne
    exact hne
  by_contra hn
  push_neg at hn
  have key := _root_.GlobalTheory.SepPer.KFinPer.per_eq_zero_of_kF hCR hHC D W.θ hθ (G.V (.core 0)) _ MP _ _ y hy (GA D (Yc D 0)) (vY.μ.restrict vY.𝓕)
    (stabilizerEmbedding G.sp.dec0) (t w) (GlobalTheory.UnitaryEmbeddingProperties.continuous_unitaryEmbedding _).measurable
    (htw.integrableOn_fundamentalDomain hμ hfd) (fun a ha => hn a ha) v'
  exact hp key

end GlobalTheory.PeriodNePf

namespace GlobalTheory.PeriodNePf

end GlobalTheory.PeriodNePf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowPeriodSubgroupFinitePointsSemidirect
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.CellMass

noncomputable section

namespace GlobalTheory.RowGrpSemi

theorem finite_split {X Y : Type} [Group X] [TopologicalSpace X] [Group Y] [TopologicalSpace Y]
    (Xf : Subgroup X) (Yf : Subgroup Y) (N R K : Subgroup X) (s : Y →* X) (p : R → Y)
    (hR : R = N ⊔ s.range) (hconj : ∀ n ∈ N, ∀ h, s h * n * (s h)⁻¹ ∈ N) (hs : Continuous s) (hp : Continuous p)
    (hpn : ∀ n ∈ N, ∀ h (hm : n * s h ∈ R), p ⟨n * s h, hm⟩ = h) (hsf : ∀ y ∈ Yf, s y ∈ Xf)
    (hkey : ∀ n ∈ N, ∀ h, n * s h ∈ Xf → h ∈ Yf) (hK : K ≤ Xf) :
    ∃ (π : R.subgroupOf Xf →* Yf) (σ : Yf →* R.subgroupOf Xf),
      Continuous π ∧ Continuous σ ∧ (∀ y, π (σ y) = y) ∧ (∀ r, π r = 1 ↔ r.1 ∈ N.subgroupOf Xf) ∧
      ∀ b : Xf, {g : Yf | ∃ n ∈ N, (b.1)⁻¹ * (n * s g.1) * b.1 ∈ K} = π '' {r | b⁻¹ * r.1 * b ∈ K.subgroupOf Xf} := by

  have hnorm : s.range ≤ Subgroup.normalizer (N : Set X) := by
    rintro _ ⟨y, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨fun hn => hconj n hn y, fun hn => ?_⟩
    have := hconj _ hn y⁻¹
    have e : s y⁻¹ * (s y * n * (s y)⁻¹) * (s y⁻¹)⁻¹ = n := by rw [map_inv]; group
    rwa [e] at this
  have hdec : ∀ x ∈ R, ∃ n ∈ N, ∃ h, x = n * s h := by
    intro x hx
    rw [hR, ← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left N s.range hnorm] at hx
    obtain ⟨n, hn, _, ⟨h, rfl⟩, e⟩ := hx
    exact ⟨n, hn, h, e.symm⟩
  have hmemR : ∀ n ∈ N, ∀ h, n * s h ∈ R := fun n hn h => by
    rw [hR]; exact mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right ⟨h, rfl⟩)
  have hpeq : ∀ x y (hx : x ∈ R) (hy : y ∈ R), x = y → p ⟨x, hx⟩ = p ⟨y, hy⟩ := by
    rintro x _ hx hy rfl; rfl
  have hval : ∀ x (hx : x ∈ R), ∃ n ∈ N, x = n * s (p ⟨x, hx⟩) := by
    intro x hx
    obtain ⟨n, hn, h, rfl⟩ := hdec x hx
    exact ⟨n, hn, by rw [hpn n hn h hx]⟩
  have hpmul : ∀ x y (hx : x ∈ R) (hy : y ∈ R) (hxy : x * y ∈ R), p ⟨x * y, hxy⟩ = p ⟨x, hx⟩ * p ⟨y, hy⟩ := by
    intro x y hx hy hxy
    obtain ⟨n, hn, h, rfl⟩ := hdec x hx
    obtain ⟨n', hn', h', rfl⟩ := hdec y hy
    have e : n * s h * (n' * s h') = (n * (s h * n' * (s h)⁻¹)) * s (h * h') := by rw [map_mul]; group
    rw [hpeq _ _ hxy (hmemR _ (mul_mem hn (hconj n' hn' h)) _) e, hpn _ (mul_mem hn (hconj n' hn' h)),
      hpn n hn h, hpn n' hn' h']
  have hp1 : ∀ (h1 : (1 : X) ∈ R), p ⟨1, h1⟩ = 1 := by
    intro h1
    rw [hpeq 1 (1 * s 1) h1 (hmemR 1 N.one_mem 1) (by rw [map_one, one_mul]), hpn 1 N.one_mem 1]
  have hfin : ∀ x (hx : x ∈ R), x ∈ Xf → p ⟨x, hx⟩ ∈ Yf := by
    intro x hx hxf
    obtain ⟨n, hn, e⟩ := hval x hx
    exact hkey n hn _ (e ▸ hxf)
  have hRf : ∀ r : R.subgroupOf Xf, r.1.1 ∈ R := fun r => Subgroup.mem_subgroupOf.1 r.2
  let π : R.subgroupOf Xf →* Yf :=
    { toFun := fun r => ⟨p ⟨r.1.1, hRf r⟩, hfin _ _ r.1.2⟩
      map_one' := Subtype.ext (hp1 _)
      map_mul' := fun r r' => Subtype.ext (hpmul _ _ (hRf r) (hRf r') (hRf (r * r'))) }
  have hsR : ∀ y, s y ∈ R := fun y => by rw [hR]; exact Subgroup.mem_sup_right ⟨y, rfl⟩
  let σ : Yf →* R.subgroupOf Xf :=
    { toFun := fun y => ⟨⟨s y.1, hsf _ y.2⟩, Subgroup.mem_subgroupOf.2 (hsR _)⟩
      map_one' := Subtype.ext (Subtype.ext (map_one s))
      map_mul' := fun y y' => Subtype.ext (Subtype.ext (map_mul s _ _)) }
  have hπ : ∀ r, (π r).1 = p ⟨r.1.1, hRf r⟩ := fun r => rfl
  refine ⟨π, σ, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hp.comp ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)).subtype_mk _
  · exact ((hs.comp continuous_subtype_val).subtype_mk _).subtype_mk _
  · intro y
    apply Subtype.ext
    rw [hπ]
    exact (hpeq _ (1 * s y.1) _ (hmemR 1 N.one_mem _) (one_mul _).symm).trans (hpn 1 N.one_mem _ _)
  · intro r
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro h1
      have h1' : p ⟨r.1.1, hRf r⟩ = 1 := by rw [← hπ, h1]; rfl
      obtain ⟨n, hn, e⟩ := hval _ (hRf r)
      rw [h1', map_one, mul_one] at e
      exact e ▸ hn
    · intro hn
      apply Subtype.ext
      rw [hπ]
      exact (hpeq _ (r.1.1 * s 1) _ (hmemR _ hn 1) (by rw [map_one, mul_one])).trans (hpn _ hn 1 _)
  · intro b
    ext g
    constructor
    · rintro ⟨n, hn, hk⟩
      have hxf : n * s g.1 ∈ Xf := by
        have e : n * s g.1 = b.1 * ((b.1)⁻¹ * (n * s g.1) * b.1) * (b.1)⁻¹ := by group
        rw [e]
        exact mul_mem (mul_mem b.2 (hK hk)) (inv_mem b.2)
      refine ⟨⟨⟨n * s g.1, hxf⟩, Subgroup.mem_subgroupOf.2 (hmemR n hn _)⟩, ?_, ?_⟩
      · show ((b⁻¹ * ⟨n * s g.1, hxf⟩ * b : Xf) : X) ∈ K
        exact hk
      · apply Subtype.ext
        rw [hπ]
        exact hpn n hn _ _
    · rintro ⟨r, hr, rfl⟩
      obtain ⟨n, hn, e⟩ := hval _ (hRf r)
      refine ⟨n, hn, ?_⟩
      rw [hπ, ← e]
      exact hr

end GlobalTheory.RowGrpSemi

namespace GlobalTheory.RowGrpSemi

open GlobalTheory.Core.Mi

theorem key_jac {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {n : GA D S} (hn : n ∈ flagN d) (h : GA D S₀)
    (hf : n * d.emb0 h ∈ GfC S) : h ∈ GfC S₀ := by
  rw [CenAct.mem_GfC_iff] at hf ⊢
  have := GlobalTheory.LevNorm.finf_sand d.p0 _ d.j0 hf d.p0_j0
  rwa [GlobalTheory.JacProj.witt_anisotropic_block_flag_mul_embedded d hn h] at this

theorem jac_case {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (N R K : Subgroup (GA D S)) (s : GA D S₀ →* GA D S)
    (hN : N = flagN d) (hs : s = d.emb0) (hR : R = N ⊔ s.range) (hK : K ≤ GfC S) :
    ∃ (π : R.subgroupOf (GfC S) →* GfC S₀) (σ : GfC S₀ →* R.subgroupOf (GfC S)),
      Continuous π ∧ Continuous σ ∧ (∀ y, π (σ y) = y) ∧ (∀ r, π r = 1 ↔ r.1 ∈ N.subgroupOf (GfC S)) ∧
      ∀ b : GfC S, {g : GfC S₀ | ∃ n ∈ N, (b.1)⁻¹ * (n * s g.1) * b.1 ∈ K} =
        π '' {r | b⁻¹ * r.1 * b ∈ K.subgroupOf (GfC S)} := by
  subst hN hs hR
  exact finite_split (GfC S) (GfC S₀) (flagN d) _ K d.emb0 (GlobalTheory.JacProj.proj d) rfl
    (fun n hn h => GlobalTheory.MixPer.witt_anisotropic_group_normalizes_flag_unipotent D S S₀ ρ d n hn h) d.continuous_embed (GlobalTheory.JacProj.continuous_proj d)
    (fun n hn h _ => GlobalTheory.JacProj.proj_mul d h ⟨n, hn⟩) (fun y hy => CenAct.witt_embedding_mem_finite_unitary_points d hy)
    (fun n hn h hf => key_jac d hn h hf) hK

theorem bes_case {D : D7} {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) (N R K : Subgroup (GA D S))
    (s : GA D A →* GA D S) (hN : N = flagN d) (hs : s = embA d o) (hR : R = N ⊔ s.range) (hK : K ≤ GfC S) :
    ∃ (π : R.subgroupOf (GfC S) →* GfC A) (σ : GfC A →* R.subgroupOf (GfC S)),
      Continuous π ∧ Continuous σ ∧ (∀ y, π (σ y) = y) ∧ (∀ r, π r = 1 ↔ r.1 ∈ N.subgroupOf (GfC S)) ∧
      ∀ b : GfC S, {g : GfC A | ∃ n ∈ N, (b.1)⁻¹ * (n * s g.1) * b.1 ∈ K} =
        π '' {r | b⁻¹ * r.1 * b ∈ K.subgroupOf (GfC S)} := by
  subst hN hs hR
  obtain ⟨p, hp, hpn⟩ := GlobalTheory.BesProj.exists_continuous_proj D S S₀ A L ρ d o
  refine finite_split (GfC S) (GfC A) (flagN d) _ K (embA d o) p rfl (fun n hn h => ?_)
    (d.continuous_embed.comp (o.continuous_emb.comp (continuous_id.prodMk continuous_const))) hp (fun n hn h _ => hpn h ⟨n, hn⟩) (fun y hy => CenAct.embA_mem_GfC d o hy)
    (fun n hn h hf => ?_) hK
  · rw [embA_apply]
    exact GlobalTheory.MixPer.witt_anisotropic_group_normalizes_flag_unipotent D S S₀ ρ d n hn _
  · rw [embA_apply] at hf
    have h0 := key_jac d hn _ hf
    have h1 : embA d o h ∈ GfC S := by rw [embA_apply]; exact CenAct.witt_embedding_mem_finite_unitary_points d h0
    exact GlobalTheory.LevNorm.mem_GfC_of_embA d o h1

end GlobalTheory.RowGrpSemi

namespace GlobalTheory.CellMass

theorem rowGrp_finite_semidirect : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R), ∀ j ∈ idx D,
    IsClosed (((rowGrp ch.G j).subgroupOf (GfC _) : Subgroup (GfC (ch.G.V (.grid D.R.m j)))) : Set (GfC (ch.G.V (.grid D.R.m j)))) ∧
    IsClosed (((rowN ch.G j).subgroupOf (GfC _) : Subgroup (GfC (ch.G.V (.grid D.R.m j)))) : Set (GfC (ch.G.V (.grid D.R.m j)))) ∧
    (rowN ch.G j).subgroupOf (GfC _) ≤ (rowGrp ch.G j).subgroupOf (GfC (ch.G.V (.grid D.R.m j))) ∧
    IsOpen (((latGrp ch.G j).subgroupOf (GfC _) : Subgroup (GfC (ch.G.V (.grid D.R.m j)))) : Set (GfC (ch.G.V (.grid D.R.m j)))) ∧
    IsCompact (((latGrp ch.G j).subgroupOf (GfC _) : Subgroup (GfC (ch.G.V (.grid D.R.m j)))) : Set (GfC (ch.G.V (.grid D.R.m j)))) ∧
    ∃ (π : (rowGrp ch.G j).subgroupOf (GfC (ch.G.V (.grid D.R.m j))) →* GfC (ch.G.V (.top j)))
      (σ : GfC (ch.G.V (.top j)) →* (rowGrp ch.G j).subgroupOf (GfC (ch.G.V (.grid D.R.m j)))),
      Continuous π ∧ Continuous σ ∧ (∀ y, π (σ y) = y) ∧ (∀ r, π r = 1 ↔ r.1 ∈ (rowN ch.G j).subgroupOf (GfC _)) ∧
      ∀ b : GfC (ch.G.V (.grid D.R.m j)), prSet ch.G j b = π '' {r | b⁻¹ * r.1 * b ∈ (latGrp ch.G j).subgroupOf (GfC _)} := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch j hj
  have hj' := List.mem_range'_1.1 hj
  have sp := GlobalTheory.RowGrpSplit.grpAt_all ch j hj
  have hNfl : ∃ (S₀ : HSp D) (ρ : ℕ) (d : HypDec (ch.G.V (.grid D.R.m j)) S₀ ρ), rowN ch.G j = flagN d := by
    by_cases h1 : j + 2 * ((D.R.m - 1 - j) / 2) + 1 = D.R.m
    · exact ⟨_, _, _, by unfold rowN; rw [dite_eq_left h1]⟩
    · have h2 : j + 2 * ((D.R.m - 2 - j) / 2) + 2 = D.R.m := by omega
      exact ⟨_, _, _, by unfold rowN; rw [dite_eq_right h1, dite_eq_left h2]⟩
  have hNc : IsClosed ((rowN ch.G j : Subgroup (GA D (ch.G.V (.grid D.R.m j)))) : Set (GA D (ch.G.V (.grid D.R.m j)))) := by
    obtain ⟨S₀, ρ, d, e⟩ := hNfl
    rw [e]
    exact GlobalTheory.Mem.TrueRecord.isClosed_NFlag _ (isIsoSub_e d)
  refine ⟨?_, ?_, ?_, sp.opn, ?_, ?_⟩
  · rw [Subgroup.coe_subgroupOf]
    exact sp.clR.preimage continuous_subtype_val
  · rw [Subgroup.coe_subgroupOf]
    exact hNc.preimage continuous_subtype_val
  · intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    rw [rowGrp_eq]
    exact Subgroup.mem_sup_left hx
  · rw [Subgroup.coe_subgroupOf]
    exact sp.clB.isClosedEmbedding_subtypeVal.isCompact_preimage sp.cpt
  · by_cases h1 : j + 2 * ((D.R.m - 1 - j) / 2) + 1 = D.R.m
    · exact GlobalTheory.RowGrpSemi.jac_case (rowJac ch.G j (by omega) ((D.R.m - 1 - j) / 2) (by omega)) _ _ _ _
        (by unfold rowN; rw [dite_eq_left h1]) (by unfold rowEmb; rw [dite_eq_left h1]) (rowGrp_eq ch.G j) sp.le
    · have h2 : j + 2 * ((D.R.m - 2 - j) / 2) + 2 = D.R.m := by omega
      exact GlobalTheory.RowGrpSemi.bes_case (besDecAt ch.G j _ h2) (GlobalTheory.OrthSumExists.orthDecHsum D _ _) _ _ _ _
        (by unfold rowN; rw [dite_eq_right h1, dite_eq_left h2]) (by unfold rowEmb; rw [dite_eq_right h1, dite_eq_left h2]) (rowGrp_eq ch.G j) sp.le

end GlobalTheory.CellMass
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestMemFourierJacobiGroupOfSumFrameSymmetric
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open GlobalTheory.RootEx GlobalTheory.RowRep
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RowRepLoc
open GlobalTheory.LocGrp GlobalTheory.LocMod

private lemma lev_le_of_sum_elim_le {σ p' : ℕ} (hp : p' = σ ∨ p' = σ + 1) {n : Type} (r s : n ⊕ Fin (2 * σ))
    (h : (Sum.elim (fun _ => σ + 1) (fun j : Fin (2 * σ) => if j.val < σ then j.val + 1 else j.val + 2) : n ⊕ Fin (2 * σ) → ℕ) s ≤
      (Sum.elim (fun _ => σ + 1) (fun j : Fin (2 * σ) => if j.val < σ then j.val + 1 else j.val + 2) : n ⊕ Fin (2 * σ) → ℕ) r) :
    GlobalTheory.RootEx.lev p' s ≤ GlobalTheory.RootEx.lev p' r := by

  rcases hp with rfl | rfl <;> rcases r with r | r <;> rcases s with s | s <;>
    simp only [Sum.elim_inl, Sum.elim_inr, GlobalTheory.RootEx.lev] at h ⊢ <;> (try split_ifs at h) <;> omega

private lemma mul_apply_eq_of_mul_eq_of_col_eq {K : Type} [Field K] {m n n' : Type} [Fintype m] (M : Matrix m m K) (X : Matrix m n K)
    (Y : Matrix m n' K) (hX : M * X = X) (i : n) (j : n') (hc : ∀ t, X t i = Y t j) (r : m) : (M * Y) r j = Y r j := by

  have h := congrFun (congrFun hX r) i
  simp only [Matrix.mul_apply, hc] at h ⊢
  exact h

theorem mem_jac {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
    {A B : HSp D} {σ : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B (2 * σ) ε)
    {b b' : Matrix (Fin A.rank) (Fin A.rank) k} (hb : b * b' = 1) (hb' : b' * b = 1) {u : Fin (2 * σ) → k}
    {Γ : Matrix (Fin A.rank ⊕ Fin (2 * σ)) (Fin B.rank) k} (h1 : Γ * sumCols d p.π b u = 1) (h2 : sumCols d p.π b u * Γ = 1)
    {g : GA D B} (hg : SuppAt p.e B g) {x : GL (Fin A.rank ⊕ Fin (2 * σ)) k}
    (e : x.val = Γ * ((mt B g).map p.π * sumCols d p.π b u)) (hx : x ∈ symR k (Fin A.rank) (2 * σ)) :
    g ∈ jacGrp (jacDec d rfl) := by
  classical
  have hS : ∀ r (j : Fin (2 * σ)), sumCols d p.π b u r (Sum.inr j) = p.π (incA D (d.a r j)) * u j := by
    intro r j
    simp only [sumCols, Matrix.fromCols_apply_inr, Matrix.mul_diagonal, Matrix.map_apply, RingHom.comp_apply]
  let F : Frame k B.rank (Fin A.rank ⊕ Fin (2 * σ)) := ⟨sumCols d p.π b u, Γ, h2, h1⟩
  let FA : Frame k A.rank (Fin A.rank) := ⟨b, b', hb, hb'⟩
  obtain ⟨φ, hφ⟩ := exists_hom p F
  have hgx : p.IsLoc F g x := by
    refine ⟨hg, ?_⟩
    show (mt B g).map p.π = sumCols d p.π b u * x.val * Γ
    rw [e]
    simp only [Matrix.mul_assoc]
    rw [h2, Matrix.mul_one, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  rw [isLoc_unique p hgx (hφ x)]

  have hfix : ∀ g₀ : GA D A, (mt B ((jacDec d rfl).emb0 g₀)).map p.π * d.a.map (p.π.comp (incA D)) =
      d.a.map (p.π.comp (incA D)) := by
    intro g₀
    have hX := map_fix p (HypDec.wittDecomp_anisotropicEmbedding_inclX (d := jacDec d rfl) (g := g₀))
    have hY := map_fix p (HypDec.wittDecomp_anisotropicEmbedding_inclY (d := jacDec d rfl) (g := g₀))
    ext r j
    by_cases hj : j.val < σ
    · exact mul_apply_eq_of_mul_eq_of_col_eq _ _ _ hX ⟨j.val, hj⟩ j (fun t => rfl) r
    · refine mul_apply_eq_of_mul_eq_of_col_eq _ _ _ hY ⟨2 * σ - 1 - j.val, by omega⟩ j (fun t => ?_) r
      show p.π (incA D ((jacDec d rfl).e' t ⟨2 * σ - 1 - j.val, by omega⟩)) = p.π (incA D (d.a t j))
      dsimp only [jacDec, Matrix.submatrix_apply, id]
      congr 3
      apply Fin.ext
      simp
      omega
  have hN : ∀ p', (p' = σ ∨ p' = σ + 1) → GlobalTheory.RootEx.N k (Fin A.rank) (2 * σ) p' ≤ (jacGrp (jacDec d rfl)).comap φ := by
    intro p' hp'
    unfold GlobalTheory.RootEx.N
    rw [Subgroup.closure_le]
    intro q hq
    show φ q ∈ flagN (jacDec d rfl) ⊔ (jacDec d rfl).emb0.range
    refine Subgroup.mem_sup_left (flag_of_strict p (jacDec d rfl) FA F
      (Sum.elim (fun a => Sum.inl a) (Sum.elim (fun i : Fin σ => Sum.inr ⟨i.val, by omega⟩)
        (fun i : Fin σ => Sum.inr ⟨2 * σ - 1 - i.val, by omega⟩))) ?_
      (Sum.elim (fun _ => (1 : k)) (Sum.elim (fun i : Fin σ => u ⟨i.val, by omega⟩)
        (fun i : Fin σ => u ⟨2 * σ - 1 - i.val, by omega⟩))) ?_
      (Sum.elim (fun _ => σ + 1) (fun j : Fin (2 * σ) => if j.val < σ then j.val + 1 else j.val + 2)) ?_ (hφ q) ?_)
    · rintro (a | j)
      · exact ⟨Sum.inl a, rfl⟩
      · by_cases hj : j.val < σ
        · exact ⟨Sum.inr (Sum.inl ⟨j.val, hj⟩), rfl⟩
        · refine ⟨Sum.inr (Sum.inr ⟨2 * σ - 1 - j.val, by omega⟩), congrArg Sum.inr (Fin.ext ?_)⟩
          show 2 * σ - 1 - (2 * σ - 1 - j.val) = j.val
          omega
    · rintro r (a | i | i)
      · show sumCols d p.π b u r (Sum.inl a) = 1 * ((jacDec d rfl).j0.map p.π * b) r a
        rw [one_mul]
        rfl
      · show sumCols d p.π b u r (Sum.inr ⟨i.val, _⟩) = u ⟨i.val, _⟩ * ((jacDec d rfl).jX.map p.π) r i
        rw [hS, mul_comm]
        rfl
      · show sumCols d p.π b u r (Sum.inr ⟨2 * σ - 1 - i.val, _⟩) = u ⟨2 * σ - 1 - i.val, _⟩ * ((jacDec d rfl).jY.map p.π) r i
        rw [hS, mul_comm]
        show u ⟨2 * σ - 1 - i.val, _⟩ * p.π (incA D (d.a r ⟨2 * σ - 1 - i.val, _⟩)) =
          u ⟨2 * σ - 1 - i.val, _⟩ * p.π (incA D ((jacDec d rfl).e' r i))
        dsimp only [jacDec, Matrix.submatrix_apply, id]
        congr 4
        apply Fin.ext
        simp
        omega
    · rintro (a | i | i)
      · rfl
      · show (if i.val < σ then i.val + 1 else i.val + 2) = i.val + 1
        rw [if_pos i.isLt]
      · show (if 2 * σ - 1 - i.val < σ then 2 * σ - 1 - i.val + 1 else 2 * σ - 1 - i.val + 2) = 2 * σ - i.val + 1
        have := i.isLt
        rw [if_neg (by omega)]
        omega
    · intro r s hrs
      have hq' : GlobalTheory.RootEx.InN p' q := hq
      rw [Matrix.sub_apply, hq' r s (lev_le_of_sum_elim_le hp' r s hrs), sub_self]
  have hR : symR k (Fin A.rank) (2 * σ) ≤ (jacGrp (jacDec d rfl)).comap φ := by
    unfold symR symN
    rw [show (2 * σ + 1) / 2 = σ by omega, show 2 * σ / 2 + 1 = σ + 1 by omega]
    refine sup_le ?_ (sup_le (hN σ (Or.inl rfl)) (hN (σ + 1) (Or.inr rfl)))
    rintro _ ⟨g₀, rfl⟩
    obtain ⟨ψ, hψ⟩ := exists_hom p FA
    have hloc : p.IsLoc F ((jacDec d rfl).emb0 (ψ g₀)) (embX (2 * σ) g₀) := by
      refine ⟨suppAt_wittLeviEmbedding _ (hψ g₀).1, ?_⟩
      refine eq_embX F _ g₀ ((frameMat B A d.ι).map (p.π.comp (incA D)) * b) (fun r a => rfl) ?_ ?_
      · exact intertwine p (HypDec.wittDecomp_anisotropicEmbedding_inclAnisotropic (d := jacDec d rfl) (g := ψ g₀)) (hψ g₀)
      · intro j
        refine fix_col (hfix (ψ g₀)) (u j) j (fun r => ?_)
        show sumCols d p.π b u r (Sum.inr j) = u j * (d.a.map (p.π.comp (incA D))) r j
        rw [hS, mul_comm]
        rfl
    show φ (embX (2 * σ) g₀) ∈ flagN (jacDec d rfl) ⊔ (jacDec d rfl).emb0.range
    rw [isLoc_unique p (hφ _) hloc]
    exact Subgroup.mem_sup_right ⟨_, rfl⟩
  exact hR hx

end GlobalTheory.RowRepLoc

theorem GlobalTheory.RowRepLoc.mem_jacGrp_of_symR : ∀ {D : D7} {A B : HSp D} {c σ : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (h : c = 2 * σ), 1 ≤ σ → ∀ (w : Pl D.host.E) (β : GL (Fin A.rank) (Lev.EAf D)) (β' : GL (Fin B.rank) (Lev.EAf D)) (u : Fin c → Kw w), IsSumFrame d w β β' u → (∀ p, u p ≠ 0) → ∀ {a b : ℕ} (_ : a = A.rank) (hb : b = B.rank) (hab : a + c = b) (q : GlobalTheory.FinPl.SplitPt D (Kw w)), (∀ x, q.pr x = GlobalTheory.RowRep.piAt w x) → ∀ g : GA D B, SuppAt q.e B g → frameGL hab (inBasis hb β' w (Lev.finE B g)) ∈ symR (Kw w) (Fin a) c → g ∈ jacGrp (jacDec d h) := by
  intro D A B c σ ε d h _ w β β' u hF _ a b ha hb hab q hq g hg hx
  subst h ha hb
  obtain ⟨Γ, hΓ1, hΓ2, hΓ⟩ := frame_val d w hF
  have hπ : (GlobalTheory.LocMod.Place.ofSplitPt q).π = piAt w := RingHom.ext hq
  refine GlobalTheory.RowRepLoc.mem_jac (GlobalTheory.LocMod.Place.ofSplitPt q) d (b' := (GlobalTheory.StdFrames.loc w β)⁻¹.val)
    (Units.mul_inv _) (Units.inv_mul _) (u := u) (Γ := Γ) ?_ ?_ hg (x := frameGL hab (inBasis rfl β' w (Lev.finE B g))) ?_ hx
  · rw [hπ]; exact hΓ1
  · rw [hπ]; exact hΓ2
  · rw [hπ]; exact hΓ g

end
end

