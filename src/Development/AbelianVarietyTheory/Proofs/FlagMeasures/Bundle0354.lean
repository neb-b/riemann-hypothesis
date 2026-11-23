module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCompactKH
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsHaarProbabilityMaxCompactHermitian
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0348
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsBesPosOfBesselTied
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselCharacterGenericCharacterLaws
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0181
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CuspidalSubspaceClosedRightTranslationStable
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0301
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.RealPlaceAnalysis.FinalF
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0302
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantOrthogonalInf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EventuallyUJ
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0202
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HighestWeightGapBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HighestWeightEventuallyZero
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeAnalytic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0351

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DsigWSubAvg
section
open MeasureTheory Matrix Filter Topology

noncomputable section

namespace GlobalTheory.KFinAvg

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}

theorem dsigW_sub_avg {μ : Measure (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)}
    {φ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ} {v : H}
    (hU : Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH (PI.UpqRep.Hpk k r)) σ) (hv : Formalism.MainNotions.S.IsSmoothVec (k := k) (r := r) σ v)
    (hD' : ∀ (D : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))
      (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ),
      (∀ Y ∈ D, Formalism.MainNotions.S.InLieHpk k r Y) → Formalism.MainNotions.S.InLieHpk k r X →
      HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (∫ g, φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ D (σ g v) ∂μ))
        (∫ g, φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ (X :: D) (σ g v) ∂μ) 0) :
    ∀ D : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), (∀ Y ∈ D, Formalism.MainNotions.S.InLieHpk k r Y) →
      Formalism.MainNotions.S.dsigW (k := k) (r := r) σ D (v - ∫ g, φ g • σ g v ∂μ) =
        Formalism.MainNotions.S.dsigW (k := k) (r := r) σ D v - ∫ g, φ g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ D (σ g v) ∂μ := by
  intro D
  induction D with
  | nil => intro _; rfl
  | cons X D ih =>
    intro hD
    have hX : Formalism.MainNotions.S.InLieHpk k r X := hD X List.mem_cons_self
    have hD1 : ∀ Y ∈ D, Formalism.MainNotions.S.InLieHpk k r Y := fun Y hY => hD Y (List.mem_cons_of_mem _ hY)
    show deriv (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) (Formalism.MainNotions.S.dsigW (k := k) (r := r) σ D _)) 0 = _
    rw [ih hD1]
    simp only [map_sub]
    exact ((Formalism.MainNotions.LowestKTypeMultiplicity.dsigW_hasDeriv hU hv D hD1 hX).sub (hD' D X hD1 hX)).deriv

theorem kDense : Formalism.MainNotions.S.Pv.AmpDD.KDense := by
  intro k r ε lam H _ _ _ σ _ hDS v hv Ws hWs e he
  obtain ⟨-, hU, -⟩ := GlobalTheory.BesselMapOne.rep_of_isDSHpk hDS
  obtain ⟨μ, hμ⟩ := _root_.GlobalTheory.KFinAvg.exists_isHaarKH k r
  have hv' : Formalism.MainNotions.S.IsSmoothVec (k := k) (r := r) σ v := hv
  obtain ⟨hpc, hp1, hp01, hpδ⟩ := _root_.GlobalTheory.KFinAvg.peak_properties (2 * r + k + 1) (Nat.succ_pos _)
  have hKc : IsCompact (GlobalTheory.ThA.KH k r) := isCompact_KH k r
  have hK1 : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ GlobalTheory.ThA.KH k r :=
    ⟨by show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ᴴ * _ * 1 = _; simp,
      one_mem _⟩
  have hpK : ∀ x ∈ GlobalTheory.ThA.KH k r, 0 ≤ peak (2 * r + k + 1) x ∧ peak (2 * r + k + 1) x ≤ 1 :=
    fun x hx => hp01 x hx.2
  have hpU : ∀ U ∈ 𝓝 (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), ∃ δ < 1,
      ∀ x ∈ GlobalTheory.ThA.KH k r, x ∉ U → peak (2 * r + k + 1) x ≤ δ := fun U hU' => by
    obtain ⟨δ, hδ, h⟩ := hpδ U hU'
    exact ⟨δ, hδ, fun x hx hxU => h x hx.2 hxU⟩
  have hσ1 : σ 1 = 1 := hU.1.1
  have hconv : ∀ w ∈ Ws, Tendsto (fun m : ℕ => ∫ g, peakN μ m g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w (σ g v) ∂μ)
      atTop (𝓝 (Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w v)) := by
    intro w hw
    have hc := (Formalism.MainNotions.LowestKTypeMultiplicity.orbit_cont hU hv' w (hWs w hw)).mono
      (Set.inter_subset_left : GlobalTheory.ThA.KH k r ⊆ _)
    have := _root_.GlobalTheory.tendsto_integral_normalised_pow_peak _ μ hμ.1 _ 1 _ hKc hμ.2.1 hK1 hμ.2.2.2 hpc hp1 hpK hpU H _ hc
    rw [hσ1, one_apply_eq_self] at this
    exact this
  set L := Ws.length
  have hε : 0 < e / (L + 1) := by positivity
  have hev : ∀ᶠ m : ℕ in atTop, ∀ w ∈ {w | w ∈ Ws},
      dist (∫ g, peakN μ m g • Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w (σ g v) ∂μ)
        (Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w v) < e / (L + 1) :=
    (Filter.eventually_all_finite Ws.finite_toSet).2 fun w hw => Metric.tendsto_nhds.1 (hconv w hw) _ hε
  obtain ⟨m, hm⟩ := hev.exists
  obtain ⟨N, b, c, hbc, hpoly, htr⟩ := _root_.GlobalTheory.KFinAvg.peak_pow_polynomial (2 * r + k + 1) m
  set Z : ℝ := ∫ h, peak (2 * r + k + 1) h ^ m ∂μ
  have e1 : ∀ g, peakN μ m g = ∑ j, (c j / (Z : ℂ)) * b j g := fun g => by
    show ((peak (2 * r + k + 1) g ^ m / Z : ℝ) : ℂ) = _
    rw [Complex.ofReal_div, hpoly g, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  refine ⟨∫ g, peakN μ m g • σ g v ∂μ, ?_, ?_⟩
  · have := GlobalTheory.T.integral_translate_family_isKFinite_hermitian k r H σ μ hU hμ N b hbc htr (fun j => c j / (Z : ℂ)) v
    simpa only [← e1] using this
  · have hD' := fun D X hD hX => GlobalTheory.T.hasDerivAt_derived_action_max_compact_average k r H σ μ (peakN μ m) v D X hU hμ
      (by rw [show peakN μ m = fun g => ∑ j, (c j / (Z : ℂ)) * b j g from funext e1]
          exact continuous_finsetSum _ fun j _ => continuous_const.mul (hbc j)) hv' hD hX
    have hterm : ∀ w ∈ Ws, ‖PI.UpqRep.dsigW (k := k) (r := r) σ w (v - ∫ g, peakN μ m g • σ g v ∂μ)‖ ≤ e / (L + 1) := by
      intro w hw
      rw [Formalism.MainNotions.BridgeCS3d.dsigW_eq, dsigW_sub_avg hU hv' hD' w (hWs w hw), norm_sub_rev, ← dist_eq_norm]
      exact (hm w hw).le
    calc (Ws.map fun w => ‖PI.UpqRep.dsigW (k := k) (r := r) σ w (v - ∫ g, peakN μ m g • σ g v ∂μ)‖).sum
        ≤ (Ws.map fun _ => e / (L + 1)).sum := List.sum_le_sum (fun w hw => hterm w hw)
      _ = L * (e / (L + 1)) := by simp [L, List.map_const', List.sum_replicate, nsmul_eq_mul]
      _ < e := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith

end GlobalTheory.KFinAvg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAllTiedPerTied
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField
open scoped TensorProduct

namespace GlobalTheory.Per.Inhab

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Iterated

variable {G N : Type} [MeasurableSpace G] [MeasurableSpace N] {μ : Measure G} {𝓕 : Set G} {ν : Measure N} {𝓝 : Set N}
  {P P' R : G → N → ℂ}

theorem iterated_add (h : (∀ g, IntegrableOn (P g) 𝓝 ν) ∧ IntegrableOn (fun g => ∫ n in 𝓝, P g n ∂ν) 𝓕 μ)
    (h' : (∀ g, IntegrableOn (P' g) 𝓝 ν) ∧ IntegrableOn (fun g => ∫ n in 𝓝, P' g n ∂ν) 𝓕 μ)
    (hR : ∀ g n, R g n = P g n + P' g n) :
    ∫ g in 𝓕, ∫ n in 𝓝, R g n ∂ν ∂μ = ∫ g in 𝓕, ∫ n in 𝓝, P g n ∂ν ∂μ + ∫ g in 𝓕, ∫ n in 𝓝, P' g n ∂ν ∂μ := by
  rw [← integral_add h.2 h'.2]
  congr 1
  funext g
  rw [← integral_add (h.1 g) (h'.1 g)]
  simp only [hR]

end Iterated

variable {D : D7}

theorem flag_topology (B : HSp D) {ρ : ℕ} {e : Matrix (Fin B.rank) (Fin ρ) D.host.E} (he : IsIsoSub B e) :
    LocallyCompactSpace (NFlag B e) ∧ SecondCountableTopology (NFlag B e) ∧ BorelSpace (NFlag B e) ∧
      Countable (NFlagQ B e) := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  obtain ⟨K, hK, h⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D B ρ e he).1
  haveI : DiscreteTopology (GQ B ⊓ NFlag B e : Subgroup (GA D B)) :=
    DiscreteTopology.of_subset (s := (GQ B : Set (GA D B))) i6 (fun x hx => hx.1)
  have h1 : IsClosed ((GQ B ⊓ NFlag B e : Subgroup (GA D B)) : Set (GA D B)) := Subgroup.isClosed_of_discrete
  have h2 : IsClosed (NFlag B e : Set (GA D B)) := by
    convert h1.mul_right_of_isCompact (hK.image continuous_subtype_val) using 1
    ext x
    constructor
    · intro hx
      obtain ⟨γ, hγ, k, hk, e⟩ := h ⟨x, hx⟩
      exact ⟨γ, ⟨hγ, γ.2⟩, k, ⟨k, hk, rfl⟩, (congrArg Subtype.val e).symm⟩
    · rintro ⟨γ, hγ, _, ⟨k, -, rfl⟩, rfl⟩
      exact mul_mem hγ.2 k.2
  refine ⟨h2.locallyCompactSpace,
    (inferInstance : SecondCountableTopology (NFlag B e : Set (GA D B))), inferInstance, ?_⟩
  exact Function.Injective.countable (f := fun γ : NFlagQ B e => (⟨γ.1.1, γ.2⟩ : GQ B))
    fun a b h => Subtype.ext (Subtype.ext (congrArg (fun x : GQ B => (x : GA D B)) h))

section Invariant

variable {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} {ρ : ℕ} {e : Matrix (Fin B.rank) (Fin ρ) D.host.E}

structure IsRatInv (ι : A.V →ₗ[D.host.E] B.V) (e : Matrix (Fin B.rank) (Fin ρ) D.host.E)
    (Q : GA D A → GA D B → ℂ) : Prop where
  norm : ∀ δ γ, EmbRel B A ι δ γ → ∀ n ∈ NFlag B e, δ * n * δ⁻¹ ∈ NFlag B e
  left : ∀ g, ∀ n ∈ NFlag B e, ∀ γ ∈ NFlag B e, γ ∈ GQ B → Q g (γ * n) = Q g n
  conj : ∀ g, ∀ n ∈ NFlag B e, ∀ γ ∈ GQ A, ∀ δ, EmbRel B A ι δ γ → Q (γ * g) (δ * n * δ⁻¹) = Q g n

variable {Q : GA D A → GA D B → ℂ}

end Invariant

section Integrands

variable {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} {s : GA D A → GA D B} {φ : GA D A → ℂ} {F : GA D B → ℂ}

theorem conj_arg (hι : HSpace.IsIsomEmb A B ι) (hs : ∀ h, EmbRel B A ι (s h) h) (hF : IsAutFun B F) {γ δ}
    (hγ : γ ∈ GQ A) (hδ : EmbRel B A ι δ γ) (g n y) : F (δ * n * δ⁻¹ * s (γ * g) * y) = F (n * s g * y) := by
  obtain ⟨s₀, -, hrel, hq⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D B A ι hι
  obtain rfl : s = s₀ := funext fun h => (hrel h _).1 (hs h)
  rw [(hrel _ _).1 hδ, ← hF.left _ (hq γ hγ) (n * s₀ g * y)]
  simp only [map_mul, mul_assoc, inv_mul_cancel_left]

theorem emb_continuous (hι : HSpace.IsIsomEmb A B ι) (hs : ∀ h, EmbRel B A ι (s h) h) : Continuous s := by
  obtain ⟨s₀, hc, hrel, -⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D B A ι hι
  obtain rfl : s = s₀ := funext fun h => (hrel h _).1 (hs h)
  exact hc

theorem bes_inv {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (hι : HSpace.IsIsomEmb A B ι) (d : BesDat A B ι)
    (hs : ∀ h, EmbRel B A ι (s h) h) (hφ : IsAutFun A φ) (hF : IsAutFun B F) :
    IsRatInv ι d.e fun h n => star (φ h) * F (n * s h * (d.y : GA D B)) * star (besChar ψ d n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro δ γ h n hn
    exact (BesselChar.besChar_conj ψ d δ γ h n hn).1
  · intro g n hn γ hγ hq
    rw [BesselChar.besChar_mul ψ d γ n hγ hn, BesselChar.besChar_rat ψ hψ.1 d γ hγ hq, one_mul, mul_assoc γ, mul_assoc γ,
      hF.left γ hq]
  · intro g n hn γ hγ δ hδ
    rw [(BesselChar.besChar_conj ψ d δ γ hδ n hn).2, conj_arg hι hs hF hγ hδ, hφ.left γ hγ]

end Integrands

section Periods

variable {X : ThetaX D} {T : ThetaTied D X} (Wl : WeilTied D X T) {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

structure IsGood (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) : Prop where
  sigOK : A.SigOK
  aniso : IsAniso A
  rank : 1 < A.rank
  isom : HSpace.IsIsomEmb A B ι

structure Frame (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) {ρ : ℕ} (e : Matrix (Fin B.rank) (Fin ρ) D.host.E) where
  μ : Measure (GA D A)
  𝓕 : Set (GA D A)
  ν : Measure (NFlag B e)
  𝓝 : Set (NFlag B e)
  s : GA D A → GA D B
  vol : IsVolPair D A μ 𝓕
  unit : IsUnitN B e ν 𝓝
  emb : ∀ h, EmbRel B A ι (s h) h


section

variable {ρ : ℕ} {e : Matrix (Fin B.rank) (Fin ρ) D.host.E} {f f' f'' : Frame A B ι e → ℂ}

end

variable (hg : IsGood A B ι)

include hg

omit hg

end Periods

section Record

variable {X : ThetaX D} {T : ThetaTied D X}

variable (Wl : WeilTied D X T) {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

end Record

end GlobalTheory.Per.Inhab

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalCuspidalIsometricIntertwiners
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.Dec.CuspFrameOneType

theorem one_mem_Kg (I : AutInst) (g : ℕ) : (1 : I.Gf) ∈ I.Kg g := by
  refine ⟨(Formalism.UG.stabGL I.Lf).one_mem, fun y _ => ⟨0, I.Lf.zero_mem, ?_⟩⟩
  have : I.fmat 1 = 1 := rfl
  simp [this]

theorem re_fixed (B : RowsAut) : ∀ k ∈ B.I.Kg B.g, (B.R (1, k)).comp B.Re = B.Re := by
  intro k hk
  obtain ⟨hT2, -, hsc, -⟩ := GlobalTheory.CongTop.adelic_topology B.I
  obtain ⟨R1, Rm, Rn, -⟩ := GlobalTheory.RightRegFund.rightReg_unitary_continuous B
  obtain ⟨-, -, -, -, -, hinv, -⟩ := B.e_adm
  obtain ⟨-, hT⟩ := B.Re_spec
  have p1 : (fun g : B.I.Gf => B.R (1, g)) 1 = 1 := R1
  have pm : ∀ a b : B.I.Gf, B.R (1, a * b) = B.R (1, a) * B.R (1, b) := by
    intro a b; rw [← Rm]; simp
  have pn : ∀ (g : B.I.Gf) v, ‖B.R (1, g) v‖ = ‖v‖ := fun g v => Rn _ v
  exact GlobalTheory.IdemProj.op_fixed B.μf (fun g => B.R (1, g)) p1 pm pn B.e B.Re hT k
    (fun x => by simpa using hinv x k hk 1 (one_mem_Kg B.I B.g))

theorem integrable_ph (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ) (hd : IsDSData B d)
    (hl : LocDec B h) (hb : HBig B 40 h) : Integrable (ph B d) (muInf B.I) := by
  obtain ⟨hc, hm, hi⟩ := GlobalTheory.Dec.PhMajProof.phMaj B d h hd hl
  have h0 := hi 0 le_rfl (fun v => by
    rcases Nat.eq_zero_or_pos (rkR (B.I.ε v)) with hq | hq
    · exact Or.inl hq
    · right
      have hle : rkR (B.I.ε v) ≤ B.I.n := by
        unfold rkR
        refine (min_le_left _ _).trans ((Finset.card_filter_le _ _).trans (by simp))
      have h1 : (0 : ℝ) < rkR (B.I.ε v) := by exact_mod_cast hq
      have h2 : ((rkR (B.I.ε v) : ℕ) : ℝ) ≤ B.I.n := by exact_mod_cast hle
      have h3 := Real.sqrt_pos.2 h1
      have h4 := hb v
      have h5 : (0 : ℝ) < B.I.n := h1.trans_le h2
      have h6 : (B.I.n : ℝ) * rkR (B.I.ε v) ≤ (B.I.n : ℝ) ^ 2 := by nlinarith
      have h7 : 0 < (B.I.n : ℝ) ^ 2 * Real.sqrt (rkR (B.I.ε v)) := by positivity
      nlinarith [mul_le_mul_of_nonneg_right h6 h3.le])
  simp only [zero_mul, Real.exp_zero, mul_one] at h0
  exact h0.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall hm)

theorem cuspidal_frame : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v)) (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) → 1 ≤ B.g → (∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) → LocDec B h → HBig B 40 h → FiniteDimensional ℂ (B.I.eHom B.σs B.μf B.fund B.R B.Re) → ∃ Rφ : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund, B.I.IsRConv B.μf B.fund B.R (phe B d) Rφ ∧ ∃ T : Fin B.D → (B.Hs →L[ℂ] B.I.L2 B.μf B.fund), GlobalTheory.IndefiniteRowSideFullHecke.CuspidalFrames.IsCuspidalFrame B Rφ T := by
  intro B d h hd hS _ hgap hl hb hfin
  obtain ⟨-, hcomm, ⟨Rφ, hR⟩, hP⟩ := GlobalTheory.GlobProj.globalProj_holds B d hd (integrable_ph B d h hd hl hb)
  obtain ⟨hproj, hfix, hex, -, -⟩ := hP Rφ hR
  obtain ⟨hU, hirr, -, hw, -⟩ := GlobalTheory.Dec.tensorRep B d hd
  have hle : B.I.eHom B.σs B.μf B.fund B.R B.Re ≤ B.I.HomS B.σs B.μf B.fund B.R := by
    rintro _ ⟨A, hA, rfl⟩ g
    show (B.Re.comp A).comp (B.σs g) = (B.R (g, 1)).comp (B.Re.comp A)
    rw [ContinuousLinearMap.comp_assoc, hA g, ← ContinuousLinearMap.comp_assoc, hcomm g,
      ContinuousLinearMap.comp_assoc]
  obtain ⟨T, hT, hn, ho, hsp⟩ := GlobalTheory.IntertwinerFrame.exists_orthonormal_frame B d hd hfin hle
  obtain ⟨S, hSm, hScl, hSst, -⟩ := GlobalTheory.CuspSubspace.cuspidal_closed_stable B
  refine ⟨Rφ, hR, T, hT, fun i => hle (hT i), hn, ho, hsp, fun i u => ?_, fun i u k hk => ?_, ?_, ?_⟩
  · have hw' : T i (B.tens B.w) ∈ S := by
      rw [hSm, ← hfix _ (hT i)]
      exact (_root_.GlobalTheory.Dec.range_cuspidal_of_lowKType B d h hd hS hgap hl hb hfin Rφ hR _).2
    have hcl : IsClosed ((S.comap (T i : B.Hs →ₗ[ℂ] B.I.L2 B.μf B.fund) : Submodule ℂ B.Hs) : Set B.Hs) :=
      hScl.preimage (T i).continuous
    rcases hirr _ hcl (fun g v hv => by
      have e := congrArg (fun A : B.Hs →L[ℂ] B.I.L2 B.μf B.fund => A v) (hle (hT i) g)
      simp only [ContinuousLinearMap.comp_apply] at e
      show T i (B.σs g v) ∈ S
      rw [e]
      exact hSst _ _ hv) with h0 | h0
    · have : B.tens B.w ∈ S.comap (T i : B.Hs →ₗ[ℂ] B.I.L2 B.μf B.fund) := hw'
      rw [h0, Submodule.mem_bot] at this
      rw [this] at hw
      simp at hw
    · have : u ∈ S.comap (T i : B.Hs →ₗ[ℂ] B.I.L2 B.μf B.fund) := by rw [h0]; trivial
      exact (hSm _).1 this
  · obtain ⟨A, -, hA⟩ := hT i
    rw [← hA]
    exact congrArg (fun C : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund => C (A u)) (re_fixed B k hk)
  · exact ⟨fun i => by rw [hn, hw], fun i j hij => ho i j hij _ _⟩
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨_, hfix _ (hT i)⟩
    · rintro _ ⟨z, rfl⟩
      have hz : Rφ (Rφ z) = Rφ z :=
        congrArg (fun C : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund => C z) hproj.1
      obtain ⟨A, ⟨hA, hAw⟩, -⟩ := hex _ hz
      rw [← hsp] at hA
      have := Submodule.mem_map_of_mem
        (f := (ContinuousLinearMap.apply ℂ (B.I.L2 B.μf B.fund) (B.tens B.w)).toLinearMap) hA
      rw [Submodule.map_span, ← Set.range_comp] at this
      show Rφ z ∈ _
      rw [← hAw]
      exact this

end GlobalTheory.Dec.CuspFrameOneType
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeCompressionFormulaOfStrictLowestKType
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.Jet.FormGapFree

open GlobalTheory.Jet.FormGap GlobalTheory.Dec.FormF GlobalTheory.Dec.PsiEig Filter Topology

theorem formulaGap : FormulaGap := by
  intro n ε lam H _ _ σ hlam hσ h hgap hh w hw X hX u hu v hv
  haveI := hσ.1
  have hU := hσ.2.2.1
  obtain ⟨g₀, hg1, hg2⟩ := exists_gap hlam hgap hh
  have hS := GlobalTheory.Jet.MultGap.isKTypeOf_lowKSub n ε lam H σ hlam hσ fun a b hab => by
    rcases lt_trichotomy a b with hlt | heq | hlt
    · exact (hg2.trans_le (hg1 a b hlt hab)).trans_le (le_abs_self _)
    · exact absurd (congrArg ε heq) hab
    · rw [abs_sub_comm]
      exact (hg2.trans_le (hg1 b a hlt hab.symm)).trans_le (le_abs_self _)
  obtain ⟨V, E, hD, hSV⟩ := GlobalTheory.DerEx.exists_isDer_lowKSub n ε lam H σ hU hS
  have han := GlobalTheory.Jet.Anal.lowK_analytic n ε H σ V E lam hU hD hS hSV u hu X hX.1
  obtain ⟨hw1, hwS, hwt⟩ := hw
  generalize lowKSub ε lam σ = S at *
  haveI := hS.1
  haveI := FiniteDimensional.complete ℂ S
  obtain ⟨τ, hτ, hτσ⟩ := TauExt.tauExists n ε _ H σ S ⟨w, hwS⟩ (URep_K hU) hS hw1 hwt
  have hw0 : (⟨w, hSV hwS⟩ : V) ≠ 0 := fun h0 => by
    have : w = 0 := congrArg Subtype.val h0
    simp [this] at hw1
  obtain ⟨hK, hsp, hfd⟩ := (KType.kType_iff n ε H σ V E hU hD).2 _ S ⟨w, hSV hwS⟩ hS hSV hwS hw0 hwt
  have hA : ∀ x y : S, LocAn ε (fun z => ⟪y, Psi ε lam τ ⟨w, hwS⟩ (z.map star) x⟫_ℂ) := fun x y =>
    locAn_conj (f := fun z => ⟪y, Psi ε lam τ ⟨w, hwS⟩ z x⟫_ℂ) fun g hg => psiAnalytic n ε lam S τ _ hlam hτ y x g hg
  have hsm : ∀ (x : V) (y : H), SmoothOnG ε (fun z => ⟪y, diffOp ε lam σ τ ⟨w, hwS⟩ z x⟫_ℂ) := fun x y => by
    rw [inner_diffOp]
    exact Line.smooth_comb _ (hD.2.2.2 x _) (hA _ _).smooth
  have hjet := GlobalTheory.Jet.Germ.germ_jet_zero n ε H σ V E lam g₀ ⟨w, hSV hwS⟩ hU hD hK hfd hg1 hg2
    (fun z => (diffOp ε lam σ τ ⟨w, hwS⟩ z : H →ₗ[ℂ] H)) ?_ ?_ ?_ ?_
  · rw [hsp] at hjet
    have h0 := Line.vanish_of_zero_jet n ε _ X (hsm ⟨u, hSV hu⟩ v) hX.1 (fun l => hjet l u hu v) (by
      intro t ht
      have e := inner_diffOp (ε := ε) (σ := σ) lam τ ⟨w, hwS⟩ u v
      simp only [congrFun e]
      exact (((innerSL ℂ (S.starProjection v)).restrictScalars ℝ).analyticAt _ |>.comp (han t ht)).add
        (analyticAt_const.mul (locAn_line (hA _ _) hX.1 t ht)))
    have hp := exp_posDef (P_star hX)
    have h1 := (psiPolar n ε lam S τ _ hlam hτ).1 1 (one_K ε) _ (P_star hX)
    rw [one_mul, hτ.2.1.1, ← exp_star] at h1
    rw [← exp_star] at hp
    have h2 := ps_entry (lam := lam) hτ hτσ (z := NormedSpace.exp X) (fun k hk => (phiPos n lam _ (by
      rw [K_inv hk]
      exact hp.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit (K_KC hk).1))).1) u v
    rw [congrFun (inner_diffOp lam τ ⟨w, hwS⟩ u v), h1, Submodule.starProjection_eq_self_iff.2 hv, neg_one_mul,
      add_neg_eq_zero] at h0
    refine h0.trans (h2.trans ?_)
    congr 2
    funext k
    have hk : toMK k ∈ Kset ε := k.2
    have hpos : ((toMK k)⁻¹ * NormedSpace.exp X * toMK k).PosDef := by
      rw [K_inv hk]
      exact (exp_posDef hX).conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit (K_KC hk).1)
    rw [Phi_star, (phiPos n lam _ hpos).2.1.le.isSelfAdjoint.star_eq]
  · rw [hsp]
    exact fun g hg x _ => ⟨S.sub_mem (S.starProjection_apply_mem _) (Subtype.prop _),
      fun k₁ h₁ k₂ h₂ => diffOp_equiv hlam hU hS.2.1 hτ hτσ hg h₁ h₂ x⟩
  · rw [hsp]
    exact fun x hx y => hsm ⟨x, hSV hx⟩ y
  · intro G hG y
    filter_upwards [psi_near_one hlam hτ hτσ, GlobalTheory.Jet.SchmidIntegral.eab_integral_eq_zero n ε H σ V E lam _ hU hD hK hfd G hG y] with g h1 h2
    have h3 : ∀ a b, Eab ε a b (fun z => ⟪y, diffOp ε lam σ τ ⟨w, hwS⟩ z (at1 G a b : V)⟫_ℂ) (umat g) =
        ⟪S.starProjection y, σ (umat g) (E a b (at1 G a b) : V)⟫_ℂ + (-1) * ((Module.finrank ℂ S : ℂ) *
          Eab ε a b (fun z => ∫ k : KG ε, Phi lam (((toMK k)⁻¹ * z * toMK k).map star) *
            (⟪y, σ (toMK k) w⟫_ℂ * ⟪σ (toMK k) w, (at1 G a b : V)⟫_ℂ) ∂(muK ε)) (umat g)) := fun a b => by
      rw [inner_diffOp, ← h1 a b (at1 G a b : V) y]
      refine (Line.word_comb (-1) (hD.2.2.2 _ _) (hA _ _).smooth [(a, b)] _ g.2).trans ?_
      rw [(Coef.coef_flow n ε H σ V E hU hD).1 _ _ _ _ g.2]
      rfl
    have h4 := congrArg (fun x : V => ⟪S.starProjection y, σ (umat g) x⟫_ℂ)
      (GlobalTheory.Jet.Schmid.mul_vminus_eq_zero n ε H σ V E lam _ hlam hσ hD hK hfd G hG)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Submodule.coe_sum, map_sum, inner_sum, Submodule.coe_zero, map_zero, inner_zero_right] at h4
    simp only [ContinuousLinearMap.coe_coe, h3, Finset.sum_add_distrib, ← Finset.mul_sum, h2, h4]
    simp
  · rw [hsp]
    intro x hx
    change diffOp ε lam σ τ ⟨w, hwS⟩ 1 x = 0
    rw [diffOp_apply, map_star_one, (psiPolar n ε lam S τ _ hlam hτ).2.1, hU.1.1]
    exact sub_self _

end GlobalTheory.Jet.FormGapFree
end
end

