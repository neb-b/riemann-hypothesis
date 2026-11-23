module

public import Mathlib
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0078
public import Formalism.LocalRingCardinality.Bundle0004
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
public import Formalism.GradedWeylDivisibility.FinalD
public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TransportedLatticeLocalizationFreeLeCoefficientS
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0071
public import Formalism.LocalToGlobal.InertKernelTheory.DefsBeCob
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.Bundle0004
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.ChordEquation
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalC
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KurComplete
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemClosureRootsOfUnity

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDatumPeriodIdealFgAndSelfDual
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

noncomputable section

namespace GlobalTheory.TieLat

section Gen

variable {E E' : Type} [Field E] [NumberField E] [StarRing E] [Field E'] [NumberField E'] [StarRing E']

def cw (i : E ≃+* E') {n : ℕ} (x : Sp E n) : Fin n → E' := fun k => i (x k)

def cwInv (i : E ≃+* E') {n : ℕ} (y : Fin n → E') : Sp E n := fun k => i.symm (y k)

theorem cw_cwInv (i : E ≃+* E') {n : ℕ} (y : Fin n → E') : cw i (cwInv i y) = y := by
  funext k; simp [cw, cwInv]

theorem cwInv_cw (i : E ≃+* E') {n : ℕ} (x : Sp E n) : cwInv i (cw i x) = x := by
  funext k; simp [cw, cwInv]

theorem coe_iO_symm (i : E ≃+* E') (r : 𝓞 E') :
    (((RingOfIntegers.mapRingEquiv i).symm r : 𝓞 E) : E) = i.symm (r : E') := rfl

theorem cwInv_smul (i : E ≃+* E') {n : ℕ} (r : 𝓞 E') (y : Fin n → E') :
    cwInv i (r • y) = (RingOfIntegers.mapRingEquiv i).symm r • cwInv i y := by
  funext k
  simp only [cwInv, Pi.smul_apply]
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  rfl

theorem mem_span_cw (i : E ≃+* E') {n : ℕ} (N : Submodule (𝓞 E) (Sp E n)) (y : Fin n → E') :
    y ∈ Submodule.span (𝓞 E') ((fun (x : Sp E n) (k : Fin n) => i (x k)) '' (N : Set (Sp E n))) ↔ cwInv i y ∈ N := by
  constructor
  · intro h
    induction h using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      have : cwInv i (fun k => i (x k)) = x := cwInv_cw i x
      rw [this]; exact hx
    | zero =>
      have : cwInv i (0 : Fin n → E') = 0 := by funext k; simp [cwInv]
      rw [this]; exact N.zero_mem
    | add a b _ _ ha hb =>
      have : cwInv i (a + b) = cwInv i a + cwInv i b := by funext k; simp [cwInv]
      rw [this]; exact N.add_mem ha hb
    | smul r a _ ha =>
      rw [cwInv_smul]; exact N.smul_mem _ ha
  · intro h
    exact Submodule.subset_span ⟨cwInv i y, h, cw_cwInv i y⟩

theorem isSdLat_of_transport (i : E ≃+* E') (hst : ∀ x, i (star x) = star (i x)) {n : ℕ} (N : Submodule (𝓞 E) (Sp E n))
    (h : IsSDLat E' n (Submodule.span (𝓞 E') ((fun (x : Sp E n) (k : Fin n) => i (x k)) '' (N : Set (Sp E n))))) :
    IsSdLat N := by
  set L := Submodule.span (𝓞 E') ((fun (x : Sp E n) (k : Fin n) => i (x k)) '' (N : Set (Sp E n))) with hL
  have hmem : ∀ y, y ∈ L ↔ cwInv i y ∈ N := mem_span_cw i N
  have hmem' : ∀ x, cw i x ∈ L ↔ x ∈ N := fun x => by rw [hmem, cwInv_cw]
  obtain ⟨hfg, hspan, hdual⟩ := h
  refine ⟨⟨?_, ?_⟩, ?_⟩
  ·
    obtain ⟨S, hS⟩ := hfg
    refine ⟨S.image (cwInv i), ?_⟩
    apply le_antisymm
    · rw [Submodule.span_le]
      intro x hx
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
      obtain ⟨s, hs, rfl⟩ := hx
      have : s ∈ L := hS ▸ Submodule.subset_span hs
      exact (hmem s).1 this
    · intro x hx
      have hy : cw i x ∈ Submodule.span (𝓞 E') (S : Set (Fin n → E')) := hS ▸ (hmem' x).2 hx
      have key : ∀ y ∈ Submodule.span (𝓞 E') (S : Set (Fin n → E')),
          cwInv i y ∈ Submodule.span (𝓞 E) ((S.image (cwInv i) : Finset (Sp E n)) : Set (Sp E n)) := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hy => exact Submodule.subset_span (by simpa using ⟨y, hy, rfl⟩)
        | zero =>
          have : cwInv i (0 : Fin n → E') = 0 := by funext k; simp [cwInv]
          rw [this]; exact Submodule.zero_mem _
        | add a b _ _ ha hb =>
          have : cwInv i (a + b) = cwInv i a + cwInv i b := by funext k; simp [cwInv]
          rw [this]; exact Submodule.add_mem _ ha hb
        | smul r a _ ha =>
          rw [cwInv_smul]; exact Submodule.smul_mem _ _ ha
      have := key _ hy
      rwa [cwInv_cw] at this
  ·
    intro s hs hli
    exact (LinearIndependent.iff_fractionRing (𝓞 E) E).mp hli
  ·
    have hform : ∀ x y : Sp E n, stdH E' n (cw i x) (cw i y) = i (hStd E n x y) := by
      intro x y
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [stdH, cw, hStd, LinearMap.mk₂'ₛₗ_apply, map_sum, map_mul, hst]
    have hrange : ∀ w : E, i w ∈ (algebraMap (𝓞 E') E').range ↔ w ∈ (1 : Submodule (𝓞 E) E) := by
      intro w
      rw [Submodule.mem_one]
      constructor
      · rintro ⟨r, hr⟩
        refine ⟨(RingOfIntegers.mapRingEquiv i).symm r, ?_⟩
        have : i.symm (r : E') = w := by
          have h2 : (r : E') = i w := hr
          rw [h2]; simp
        exact this
      · rintro ⟨r, rfl⟩
        exact ⟨RingOfIntegers.mapRingEquiv i r, rfl⟩
    unfold IsUnimodular dual Formalism.E.hdual
    ext y
    simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars]
    rw [← hmem' y, hdual (cw i y)]
    constructor
    · intro hy x' hx'
      have h1 := hy (cwInv i x') ((hmem x').1 hx')
      rw [← cw_cwInv i x', hform]
      exact (hrange _).2 h1
    · intro hy x hx
      have h1 := hy (cw i x) ((hmem' x).2 hx)
      rw [hform] at h1
      exact (hrange _).1 h1

theorem span_fg_of_denom (a : 𝓞 E) (ha : a ≠ 0) (A : Set E) (hA : ∀ r ∈ A, IsIntegral ℤ ((a : E) * r)) :
    (Submodule.span (𝓞 E) A).FG := by
  have ha' : (a : E) ≠ 0 := by simpa using ha
  have hfg : (Submodule.span (𝓞 E) {(a : E)⁻¹}).FG := ⟨{(a : E)⁻¹}, by simp⟩
  have hN : IsNoetherian (𝓞 E) (Submodule.span (𝓞 E) {(a : E)⁻¹}) := by
    haveI : Module.Finite (𝓞 E) (Submodule.span (𝓞 E) {(a : E)⁻¹}) := Module.Finite.iff_fg.2 hfg
    infer_instance
  refine isNoetherian_submodule.1 hN _ ?_
  rw [Submodule.span_le]
  intro r hr
  rw [SetLike.mem_coe, Submodule.mem_span_singleton]
  obtain ⟨z, hz⟩ : ∃ z : 𝓞 E, (z : E) = (a : E) * r := ⟨⟨_, hA r hr⟩, rfl⟩
  refine ⟨z, ?_⟩
  rw [Algebra.smul_def]
  change (z : E) * (a : E)⁻¹ = r
  rw [hz]
  field_simp

end Gen

section Comparison₂

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}

theorem tie_sd {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) (u μ i c) : IsSdLat ((t.rd u μ).N i c) := by
  letI := D.host.cmStar
  have h : IsSDLat D.host.E _ (t.seam.lat ((t.rd u μ).N i c)) := t.O_lat u μ i c ▸ ((t.O u μ).lat i c).2
  exact isSdLat_of_transport t.seam.iE (fun x => by rw [t.seam_ok.2 x]; exact (Examples₂.star_eq_conj _ _).symm) _ h

theorem tie_AA_fg {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) : t.amb.AA.FG := by
  obtain ⟨b, hb, hfr⟩ := D.host.AA0.isFractional
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha : (RingOfIntegers.mapRingEquiv t.seam.iE).symm b ≠ 0 := by simpa using hb0
  refine span_fg_of_denom _ ha _ ?_
  rintro r ⟨c, hc, s, hs, rfl⟩
  obtain ⟨w, hw⟩ := hfr s hs
  have hw' : (w : D.host.E) = (b : D.host.E) * s := by
    rw [← Algebra.smul_def]; exact hw
  rw [coe_iO_symm, ← map_mul]
  have hcI : IsIntegral ℤ ((((c : 𝓞 D.host.K) : D.host.K) : D.host.E)) :=
    (NumberField.RingOfIntegers.isIntegral_coe c).map ((IntermediateField.val D.host.K).restrictScalars ℤ)
  have e : (b : D.host.E) * ((((c : 𝓞 D.host.K) : D.host.K) : D.host.E) * s) = (((c : 𝓞 D.host.K) : D.host.K) : D.host.E) * w := by
    rw [hw']; ring
  rw [e]
  exact (hcI.mul (NumberField.RingOfIntegers.isIntegral_coe w)).map (t.seam.iE.symm : D.host.E →+* t.X.E).toIntAlgHom

end Comparison₂

end GlobalTheory.TieLat

theorem GlobalTheory.TieLat.tie_AA_fg_and_sd : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.amb.AA.FG ∧ ∀ u μ i c, IsSdLat ((t.rd u μ).N i c) :=
  fun _ _ _ _ _ _ _ _ _ t => ⟨GlobalTheory.TieLat.tie_AA_fg t, fun u μ i c => GlobalTheory.TieLat.tie_sd t u μ i c⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NatCastMemOfPrimeDvdAbsNorm
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

namespace GlobalTheory.KerTie

theorem natCast_mem_of_prime_dvd_absNorm {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) {q : ℕ}
    (hq : q.Prime) (h : q ∣ Ideal.absNorm P.asIdeal) : (q : 𝓞 E) ∈ P.asIdeal := by
  have : Fact q.Prime := ⟨hq⟩
  have := P.isPrime
  have : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot P.asIdeal P.ne_bot
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := 𝓞 E ⧸ P.asIdeal) q h
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [addOrderOf_zero] at hx
    exact hq.one_lt.ne hx
  have h1 : q • x = 0 := by rw [← hx]; exact addOrderOf_nsmul_eq_zero x
  rw [nsmul_eq_mul] at h1
  have h2 : ((q : ℕ) : 𝓞 E ⧸ P.asIdeal) = 0 := (mul_eq_zero.1 h1).resolve_right hx0
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact h2

theorem sNum_qOf_rowSG :
    ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC)
      (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex),
      ∀ u μ (P : rowSG t.Pr t.sel (t.tup μ)), SNum (t.O u μ).S (qOf P.1) := by
  intro D L hT Gi Gl K Y cX ex t u μ P
  refine ⟨Nat.pos_of_ne_zero ?_, fun q hq hP => ?_⟩
  · simpa [Formalism.L2.Col.qOf, Ideal.absNorm_eq_zero_iff] using P.1.ne_bot
  rw [t.O_S]
  refine Finset.mem_insert_of_mem ?_
  rcases Finset.mem_union.1 P.2 with hG | hQ
  · refine Finset.mem_union_left _ ?_
    rcases Finset.mem_union.1 hG with h0 | h0
    · have e : Formalism.L2.Col.qOf P.1 = t.Pr.g 0 := t.pr_ok.vG_norm 0 P.1 h0
      rw [e] at hP
      rw [(Nat.prime_dvd_prime_iff_eq hq (t.pr_ok.g_prime 0)).1 hP, t.g_rec]
      simp
    · have e : Formalism.L2.Col.qOf P.1 = t.Pr.g 1 := t.pr_ok.vG_norm 1 P.1 h0
      rw [e] at hP
      rw [(Nat.prime_dvd_prime_iff_eq hq (t.pr_ok.g_prime 1)).1 hP, t.g_rec]
      simp
  · exact Finset.mem_union_right _
      ((t.Q_rec μ q).2 ⟨hq, P.1, hQ, natCast_mem_of_prime_dvd_absNorm P.1 hq hP⟩)

end GlobalTheory.KerTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormTauEmbPosPlConjEq
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical

namespace GlobalTheory.KerStd

open GlobalTheory.InertCompare GlobalTheory.Proof.IdempotentLatticeSequence

section General

variable {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime]

theorem SamePrime.lt_one_imp {ρ ρ' : E →+* ℂ_[l]} (h : SamePrime ρ ρ') (x : E) (hx : ‖ρ x‖ < 1) : ‖ρ' x‖ < 1 := by
  have hone : ∀ (σ : E →+* ℂ_[l]) (a : 𝓞 E), ¬ ‖σ (a : E)‖ < 1 → ‖σ (a : E)‖ = 1 := fun σ a ha =>
    le_antisymm (norm_int_le σ a) (not_lt.1 ha)
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 E) :=
    ⟨primeOf ρ, primeOf_isPrime ρ, fun hb => by
      have := natCast_mem_primeOf ρ
      rw [hb, Ideal.mem_bot] at this
      exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast this)⟩
  obtain ⟨n, d, e | e⟩ := v.exists_primeCompl_mul_eq_or_mul_eq (K := E) x
  · have hd : ¬ ‖ρ ((d : 𝓞 E) : E)‖ < 1 := d.2
    have hd' : ¬ ‖ρ' ((d : 𝓞 E) : E)‖ < 1 := fun c => hd ((h _).2 c)
    have e' : x * ((d : 𝓞 E) : E) = (n : E) := e
    have hn : ‖ρ (n : E)‖ < 1 := by
      rw [← e', map_mul, norm_mul, hone ρ _ hd, mul_one]
      exact hx
    have hn' := (h n).1 hn
    rwa [← e', map_mul, norm_mul, hone ρ' _ hd', mul_one] at hn'
  · exfalso
    have hd : ¬ ‖ρ ((d : 𝓞 E) : E)‖ < 1 := d.2
    have e' : x * (n : E) = ((d : 𝓞 E) : E) := e
    apply hd
    rw [← e', map_mul, norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (norm_int_le ρ n)) hx

theorem SamePrime.norm_eq {ρ ρ' : E →+* ℂ_[l]} (h : SamePrime ρ ρ') (x : E) : ‖ρ x‖ = ‖ρ' x‖ := by
  let u : AbsoluteValue E ℝ := (NormedField.toAbsoluteValue ℂ_[l]).comp ρ.injective
  let w : AbsoluteValue E ℝ := (NormedField.toAbsoluteValue ℂ_[l]).comp ρ'.injective
  have hu (x) : u x = ‖ρ x‖ := rfl
  have hw (x) : w x = ‖ρ' x‖ := rfl
  have he : u.IsEquiv w := AbsoluteValue.isEquiv_iff_lt_one_iff.2 fun a =>
    ⟨SamePrime.lt_one_imp h a, SamePrime.lt_one_imp (fun b => (h b).symm) a⟩
  obtain ⟨c, hc, hce⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.1 he
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hn (σ : E →+* ℂ_[l]) : ‖σ (l : E)‖ = (l : ℝ)⁻¹ := by
    rw [map_natCast, ← Padic.norm_p, ← PadicComplex.norm_extends']
    simp
  have h1 : c = 1 := by
    have h2 := congrFun hce (l : E)
    simp only [hu, hw, hn] at h2
    have h3 : ((l : ℝ)⁻¹) ^ c = ((l : ℝ)⁻¹) ^ (1 : ℝ) := by rw [h2, Real.rpow_one]
    exact (Real.rpow_right_inj (by positivity) (by
      exact (inv_lt_one₀ (by positivity)).2 hl |>.ne)).1 h3
  have h4 := congrFun hce x
  simp only [hu, hw, h1, Real.rpow_one] at h4
  exact h4

end General

theorem norm_tauEmb_posPl_conj_eq : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), (IsResidueClassZero D p ∨ IsSg D p) → ∀ (z : Bool × HH D) (y : D.host.E), ‖tauEmb D lam (tauPl D (posPl D p z 1)) (D.host.conj y)‖ = ‖tauEmb D lam (tauPl D z) y‖ := by
  intro D p _ lam h z y
  have hcc : D.host.conj (D.host.conj y) = y := D.host.φ₀.injective (by
    rw [D.host.toHostAx.conjE_apply, D.host.toHostAx.conjE_apply, Complex.conj_conj])
  have h1 := SamePrime.norm_eq (samePrime_step D p lam h z) (D.host.conj y)
  have h2 : rhoC D lam (tauPl D z) (D.host.conj y) = rhoH D lam (tauPl D z) y := by
    change rhoH D lam (tauPl D z) (D.host.conj (D.host.conj y)) = _
    rw [hcc]
  rw [h2] at h1
  rw [← coe_rhoH, ← coe_rhoH]
  exact h1

end GlobalTheory.KerStd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodBoundIff
section
noncomputable section

namespace GlobalTheory.ExpAtTypePrimes

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G NumberField IsDedekindDomain

theorem col_smul {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} (C : ColumnChain R ι hc) (a : ℂ)
    (φ : C.cls 0 → C.Y 0 → ℂ) : C.col (a • φ) = a • C.col φ := by
  unfold ColumnChain.col
  generalize R.m = n
  induction n with
  | zero => rfl
  | succ n ih =>
    funext j
    simp only [Formalism.ThetaLiftIndependence.chainOpM, Formalism.ThetaLiftIndependence.kerOpM, ih, Pi.smul_apply, map_smul, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

theorem perCol_smul (D : D7) (u : D.what₂.Word) (μ : D.what₂.Tup) (a : ℂ) (φ : D.what₂.Mu u) (F : D.what₂.Amb μ) :
    D.what₂.perCol u μ (a • φ) F = a * D.what₂.perCol u μ φ F := by
  by_cases hμ : μ = D.what₂.mu0
  · subst hμ
    simp only [D.perCol_base_eq_PtilCol, PeriodMap.PtilCol, PeriodMap.Ptil, map_smul, Submodule.coe_smul, col_smul,
      LinearMap.smul_apply, smul_eq_mul]
  · simp only [D.perCol_tie u μ hμ, PeriodMap.PtilCol, PeriodMap.Ptil, map_smul, Submodule.coe_smul, col_smul,
      LinearMap.smul_apply, smul_eq_mul]

end GlobalTheory.ExpAtTypePrimes

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanMapNabKDelK
section
open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp

namespace GlobalTheory.ValCmp

theorem use₂ {Kf K ι : Type} [Field Kf] [Field K] [Fintype ι] {n : ℕ} (eK : K →+* Kf) (lam : ι → DomWeight n)
    (B : ι → GL (Fin n) K) (F : Pol K ι n) :
    MvPolynomial.map eK (actP lam B F) = actP lam (fun τ => Formalism.UG.bc eK (B τ)) (MvPolynomial.map eK F) := by
  have h1 : (MvPolynomial.map eK).comp (trAct B).toRingHom =
      (trAct (fun τ => Formalism.UG.bc eK (B τ))).toRingHom.comp (MvPolynomial.map eK) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [trAct]
    · intro v
      simp [trAct, blockAct_X, bc_coe]
  have h2 : MvPolynomial.map eK (trAct B F) = trAct (fun τ => Formalism.UG.bc eK (B τ)) (MvPolynomial.map eK F) :=
    congrArg (fun φ : Pol K ι n →+* Pol Kf ι n => φ F) h1
  have h3 : eK (detTwK lam B) = detTwK lam (fun τ => Formalism.UG.bc eK (B τ)) := by
    rw [detTw_eq, detTw_eq, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_zpow₀, bc_coe, RingHom.map_det]
    rfl
  simp only [actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, smul_eq_C_mul, map_mul, map_C, h2, h3]

end GlobalTheory.ValCmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedWeierstrassCurveTransformCoefficientsW
section
noncomputable section

namespace GlobalTheory.CoefWfUnram

open Formalism.MainNotions.GL3Theta

variable {p : ℕ} [Fact p.Prime]

theorem inWf_of_kur {x : ℂ_[p]} (hx : x ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) : InWf x := by
  first
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact @_root_.GlobalTheory.WittRootsOfUnity.inWf_of_mem_Kur
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact _root_.GlobalTheory.WittRootsOfUnity.inWf_of_mem_Kur
  | exact @_root_.GlobalTheory.WittRootsOfUnity.inWf_of_mem_Kur
  | exact _root_.GlobalTheory.WittRootsOfUnity.inWf_of_mem_Kur
  | (apply _root_.GlobalTheory.WittRootsOfUnity.inWf_of_mem_Kur <;> assumption)
  | (intros; apply _root_.GlobalTheory.WittRootsOfUnity.inWf_of_mem_Kur <;> assumption)
  | (intros; apply @_root_.GlobalTheory.WittRootsOfUnity.inWf_of_mem_Kur <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.WittRootsOfUnity.inWf_of_mem_Kur ..)

theorem coefWf_phW_of_kur (W : WeierstrassCurve ℂ_[p]) (h1 : W.a₁ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p)
    (h2 : W.a₂ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) (h3 : W.a₃ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) (h4 : W.a₄ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p)
    (h6 : W.a₆ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) {s2 : ℂ_[p]} (hs : s2 ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) :
    CoefWf (Formalism.L2.Th1.B.phW W s2 : MvPowerSeries Unit ℂ_[p]) := by
  let K := Formalism.L2.Th1.CM.MaximalUnramifiedExtension p
  let W' : WeierstrassCurve K := ⟨⟨W.a₁, h1⟩, ⟨W.a₂, h2⟩, ⟨W.a₃, h3⟩, ⟨W.a₄, h4⟩, ⟨W.a₆, h6⟩⟩
  have hWW : W'.map K.subtype = W := rfl
  obtain ⟨hl, -, hwp, -, -⟩ := Formalism.L2.Th1.A.zMap K ℂ_[p] K.subtype W'
  obtain ⟨h0, h1', -, -⟩ := Formalism.L2.Th1.A.logSpec K W'
  have hB := (Formalism.L2.Th1.B.baseChange K ℂ_[p] K.subtype ⟨s2, hs⟩ 0 0 (Formalism.L2.Th1.A.wpReg W') 0
    (Formalism.L2.Th1.A.logSer W') 0 h0 h1' (by simp)).2.2.2.2.1
  have e : Formalism.L2.Th1.B.phW W s2 =
      PowerSeries.map K.subtype (Formalism.L2.Th1.B.phO ⟨s2, hs⟩ (Formalism.L2.Th1.A.wpReg W') (Formalism.L2.Th1.A.logSer W')) := by
    rw [hB, hl, hwp, hWW]
    rfl
  intro n
  rw [e]
  refine inWf_of_kur ?_
  rw [show MvPowerSeries.coeff n (PowerSeries.map K.subtype
      (Formalism.L2.Th1.B.phO ⟨s2, hs⟩ (Formalism.L2.Th1.A.wpReg W') (Formalism.L2.Th1.A.logSer W')) : MvPowerSeries Unit ℂ_[p]) =
      K.subtype (MvPowerSeries.coeff n (Formalism.L2.Th1.B.phO ⟨s2, hs⟩ (Formalism.L2.Th1.A.wpReg W')
        (Formalism.L2.Th1.A.logSer W') : MvPowerSeries Unit K)) from MvPowerSeries.coeff_map _ _ _]
  exact (MvPowerSeries.coeff n _ : K).2

theorem coefWf_phW : ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]), W.a₁ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → W.a₂ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → W.a₃ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → W.a₄ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → W.a₆ ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → ∀ s2 : ℂ_[p], s2 ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p → Formalism.MainNotions.GL3Theta.CoefWf (Formalism.L2.Th1.B.phW W s2 : MvPowerSeries Unit ℂ_[p]) :=
  fun _ _ W h1 h2 h3 h4 h6 _ hs => coefWf_phW_of_kur W h1 h2 h3 h4 h6 hs

end GlobalTheory.CoefWfUnram
end
end

