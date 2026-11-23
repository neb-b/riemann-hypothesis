module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0147
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwoMulRankWLt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def realLev (R : RealDat D A Ks) (i : Fin D.R.m) : Set (GA D (Wc D i)) :=
  {h | ∃ u ∈ GinfC (Wc D i), ∃ k ∈ levW R i, h = u * k}

def lowCoefSq (R : RealDat D A Ks) (i : Fin D.R.m) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (h : GA D (Wc D i)) : ℝ :=
  ‖∏ ρ, ⟪((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ),
    (R.MW i (sg0 D A)).rep ρ (infMat D.sp.cm.sig (Wc D i).gram (R.θ ρ) h)
      ((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ)⟫_ℂ‖ ^ 2


variable (A) in
def dimProd (i : Fin D.R.m) : ℂ :=
  ∏ ρ, ((dimK _ _ (kapAt (Wc D i) (sg0 D A) ρ) : ℚ) : ℂ)

def rallisF (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (μ : Measure (WO (Vc D i) (Wc D i)))
    (𝓕 : Set (WO (Vc D i) (Wc D i))) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (f : WO (Vc D i) (Wc D i) → ℂ)
    (x y : (R.HW i (sg0 D A)).H) (g : GA D (Wc D i)) : ℂ :=
  thetaIP μ 𝓕 (R.ωP i t (1, g) f) f *
    ∫ z in R.fdW i, star (val R i v x z) * val R i v y (z * g) ∂(R.νW i)

theorem two_mul_rank_W_lt (D : D7) (i : Fin D.R.m) : 2 * (Wc D i).rank < (Vc D i).rank := by
  have h1 := i.2
  rw [D.sp.W_rank _ (by omega) (by omega), D.sp.V_rank _ (by omega) (by omega)]
  have := (D.R.rank_add_five_le : D.R.r + 5 ≤ D.R.t)
  unfold Ranks.nV
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  omega

end GlobalTheory.RawLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnderEqOfConj
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift.Small

theorem exists_under (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    ∃ P : HeightOneSpectrum (𝓞 D.host.E), P.under (𝓞 D.host.F) = v := by
  obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 D.host.E) v.asIdeal
    (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (FaithfulSMul.algebraMap_injective (𝓞 D.host.F) (𝓞 D.host.E))]
      exact bot_le)
  refine ⟨⟨Q, hQ, fun h => v.ne_bot ?_⟩, HeightOneSpectrum.ext hQv⟩
  rw [← hQv, h]
  exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)

theorem under_eq_of_conj {D : D7} {P P' : HeightOneSpectrum (𝓞 D.host.E)} (h : Formalism.IndefR.Lev.IsConjPl P P') :
    P.under (𝓞 D.host.F) = P'.under (𝓞 D.host.F) := by
  refine HeightOneSpectrum.ext ((P.under (𝓞 D.host.F)).isMaximal.eq_of_le (P'.under (𝓞 D.host.F)).isPrime.ne_top
    fun a ha => ?_)
  obtain ⟨c', h1, h2⟩ := h (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) ha
  have hfix : star (algebraMap D.host.F D.host.E (a : D.host.F)) = algebraMap D.host.F D.host.E (a : D.host.F) :=
    (D.sp.cm.fixed _).2 ⟨_, rfl⟩
  have e : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a = c' := RingOfIntegers.ext (h2.trans hfix).symm
  change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a ∈ P'.asIdeal
  rwa [e]

end GlobalTheory.RawLift.Small

namespace GlobalTheory.RawLift.Small

theorem norm_eq_rpow {z : ℂ} {L n : ℕ} (h : ‖z‖ ^ 2 * (L : ℝ) ^ n = 1) : ‖z‖ = (L : ℝ) ^ (-(n : ℝ) / 2) := by
  have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have hLn : (L : ℝ) ^ n ≠ 0 := fun h0 => by rw [h0, mul_zero] at h; exact zero_ne_one h
  have h1 : ((L : ℝ) ^ (-(n : ℝ) / 2)) ^ 2 = ((L : ℝ) ^ n)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL, show -(n : ℝ) / 2 * ((2 : ℕ) : ℝ) = -(n : ℝ) by push_cast; ring,
      Real.rpow_neg hL, Real.rpow_natCast]
  have h2 : ‖z‖ ^ 2 = ((L : ℝ) ^ n)⁻¹ := eq_inv_of_mul_eq_one_left h
  exact (pow_left_inj₀ (norm_nonneg z) (Real.rpow_nonneg hL _) two_ne_zero).1 (h2.trans h1.symm)

theorem locSmall : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i t, BadSupp R i t → GoodMod R i t → IndexSum (Wc D i) (Vc D i).rank → LocSmall R i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL _ i t hB hG hI μ 𝓕 hμ
  obtain ⟨s, hs, hs1, hsC⟩ := hI
  refine ⟨fun v => max (s v) 0, ?_, fun v => max_lt (hs1 v) one_pos, ?_⟩
  · exact Summable.of_nonneg_of_le (fun v => le_max_right _ _) (fun v => max_le (le_abs_self _) (abs_nonneg _)) hs.abs
  intro v f hf C hC hCd
  by_cases hbad : ∃ P, (P ∈ R.Pg ∨ P ∈ R.Q t) ∧ ∃ e f', IsPrimeIdem P e f' ∧ f' = f
  · obtain ⟨P, hP, e, f', hPI, rfl⟩ := hbad
    rw [Finset.sum_eq_zero fun g hg => by rw [hB μ 𝓕 hμ P hP e f' hPI g (hC g hg).1 (hC g hg).2, norm_zero]]
    exact le_max_right _ _
  push_neg at hbad
  obtain ⟨ε, hε, hfε⟩ := hf
  have hI0 := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents (Wc D i)
  obtain ⟨P, hPv⟩ := exists_under D v
  obtain ⟨e, fP, hPI⟩ := hI0.2.1 P
  have hfP : fP = f := by
    rw [GlobalTheory.AdelicU.Supp.eq_placeIdem_of_isPrimeIdem hPI hPv, hfε, GlobalTheory.AdelicU.Supp.isPlaceIdem_iff.1 hε]
  subst hfP
  obtain ⟨c, hβ⟩ := hL.lev.βW i
  have hN : ((1 ^ c : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    rw [one_pow, Nat.cast_one]
    exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  have hoff : ∀ PP, PP ∈ (R.datWp i R.triv).Pg ∨ PP ∈ (R.datWp i R.triv).Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P := by
    intro PP hPP
    have hPP' : PP ∈ R.Pg := hPP.elim id fun h => absurd h (Finset.notMem_empty _)
    obtain ⟨e', f', h'⟩ := hI0.2.1 PP
    have hne := hbad PP (Or.inl hPP') e' f' h'
    refine ⟨fun h => hne ?_, fun h => hne ?_⟩
    · subst h
      exact ((hI0.2.2.1 PP e fP hPI).2.2.2.1 e' f' h').2
    · rw [GlobalTheory.AdelicU.Supp.eq_placeIdem_of_isPrimeIdem h' ((under_eq_of_conj h).trans hPv),
        GlobalTheory.AdelicU.Supp.eq_placeIdem_of_isPrimeIdem hPI hPv]
  obtain ⟨hJ, -, -⟩ := (GlobalTheory.LevSplit.lev_split (Wc D i) (R.βW i) (R.ΛW i) (1 ^ c) (R.datWp i R.triv) hβ).2 P e fP hPI hN hoff
  have hPI' := hI0.2.2.1 P e fP hPI
  obtain ⟨L, hL'⟩ := (hI0.1 fP hPI'.1 hPI'.2.1).1
  have hsupp : ∀ g ∈ C, ∀ g' ∈ C, SuppF (Wc D i) fP (g⁻¹ * g') := fun g hg g' hg' =>
    (hL' _).1 (L.mul_mem (L.inv_mem ((hL' g).2 (hC g hg).1)) ((hL' g').2 (hC g' hg').1))
  calc ∑ g ∈ C, ‖coef R i t μ 𝓕 g‖ = ∑ g ∈ C, (latIndex (Wc D i) g : ℝ) ^ (-((Vc D i).rank : ℝ) / 2) :=
        Finset.sum_congr rfl fun g hg => norm_eq_rpow (hG μ 𝓕 hμ v fP ⟨ε, hε, hfε⟩ hbad g (hC g hg).1)
    _ ≤ s v := hsC v fP ⟨ε, hε, hfε⟩ C (fun g hg => ⟨(hC g hg).1, fun hk => (hC g hg).2 ((hJ g (hC g hg).1).2 hk)⟩)
        fun g hg g' hg' hk => hCd g hg g' hg' ((hJ _ (hsupp g hg g' hg')).2 hk)
    _ ≤ max (s v) 0 := le_max_left _ _

end GlobalTheory.RawLift.Small

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitarisableSegmentTwistPrecedesAddOneLe
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix

namespace GlobalTheory.LocGL.UnitaryOrder

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem hasCentralChar_nu (x : IrrGL (k := k)) {ω : kˣ →* ℂˣ} (h : HasCentralChar x.rep ω) (s : ℂ) :
    HasCentralChar (x.nu s).rep (ω * absPow k s ^ x.1) := by
  have h1 := hasCentralChar_twist h (absPow k s)
  rw [Fintype.card_fin] at h1
  exact hasCentralChar_of_equiv (x.twEquiv _ _) h1

theorem norm_eq_one_of_isUnitarisable {G X : Type} [Group G] [AddCommGroup X] [Module ℂ X] [Nontrivial X]
    {ρ : Representation ℂ G X} (hU : IsUnitarisable ρ) {g : G} {c : ℂ} (hc : ∀ v, ρ g v = c • v) : ‖c‖ = 1 := by
  obtain ⟨B, -, hp, hi⟩ := hU
  obtain ⟨v, hv⟩ := exists_ne (0 : X)
  have h := hi g v v
  have h0 : B v v ≠ 0 := fun e => by simpa [e] using hp v hv
  rw [hc, B.map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    Complex.mul_conj, mul_eq_right₀ h0] at h
  have h2 : ‖c‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq]; exact_mod_cast h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2

theorem log_norm_mul_absPow (ω : kˣ →* ℂˣ) (t : ℝ) (d : ℕ) (z : kˣ) :
    Real.log ‖(((ω * absPow k (t : ℂ) ^ d) z : ℂˣ) : ℂ)‖ =
      Real.log ‖(ω z : ℂ)‖ + d * t * Real.log (nabs k z) := by
  have hz := nabs_pos' k z
  have hω : ‖(ω z : ℂ)‖ ≠ 0 := norm_ne_zero_iff.2 (ω z).ne_zero
  rw [MonoidHom.mul_apply, MonoidHom.pow_apply, Units.val_mul, Units.val_pow_eq_pow_val, val_absPow_ofReal,
    norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hz.le _),
    Real.log_mul hω (pow_ne_zero _ (Real.rpow_pos_of_pos hz _).ne'), Real.log_pow, Real.log_rpow hz]
  ring

theorem sum_range_mul_two (l : ℕ) : (∑ i ∈ Finset.range l, (i : ℝ)) * 2 = l * ((l : ℝ) - 1) := by
  induction l with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, add_mul, ih]; push_cast; ring

theorem log_norm_centralChar {δ : IrrGL (k := k)} {Δ : Segment k} (hL : IsLSeg Δ δ.rep) (hU : IsUnitarisable δ.rep)
    {ω : kˣ →* ℂˣ} (hω : HasCentralChar Δ.first.rep ω) (z : kˣ) :
    Real.log ‖(ω z : ℂ)‖ = -((Δ.d : ℝ) * ((Δ.len : ℝ) - 1) / 2) * Real.log (nabs k z) := by
  obtain ⟨hd, hi, f, hf, -⟩ := hL
  have hterm : ∀ a : Fin Δ.len,
      HasCentralChar (Δ.term a).rep (ω * absPow k (((a : ℕ) : ℝ) : ℂ) ^ Δ.d) := fun a => by
    have h := hasCentralChar_nu Δ.first hω ((a : ℕ) : ℂ)
    rw [Complex.ofReal_natCast]
    exact h
  have hsc : ∀ v, δ.rep (GeneralLinearGroup.scalar (Fin δ.1) z) v =
      (∏ a : Fin Δ.len, (((ω * absPow k (((a : ℕ) : ℝ) : ℂ) ^ Δ.d) z : ℂˣ) : ℂ)) • v := by
    intro v
    obtain ⟨w, rfl⟩ := hf v
    have h1 := GlobalTheory.BoundaryMaps.multiProd_scalar (stdBlocks (fun a => (Δ.term a).1) hd)
      (fun a => (Δ.term a).rep) _ hterm z w
    rw [← f.isIntertwining]
    exact (congrArg f h1).trans (map_smul f _ _)
  haveI := Model.nontrivial_of_isIrreducible hi
  have hc := congrArg Real.log (norm_eq_one_of_isUnitarisable hU hsc)
  rw [norm_prod, Real.log_one, Real.log_prod fun a _ => norm_ne_zero_iff.2 (Units.ne_zero _)] at hc
  simp only [log_norm_mul_absPow] at hc
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.sum_mul, ← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun i => (i : ℝ)) Δ.len] at hc
  have hS := sum_range_mul_two Δ.len
  have hl : (Δ.len : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Δ.len_pos.ne'
  apply mul_left_cancel₀ hl
  linear_combination hc - ((Δ.d : ℝ) * Real.log (nabs k z) / 2) * hS

theorem add_one_le_of_precedes (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (δ δ' : IrrGL (k := k)) (Δ Δ' : Segment k) (hL : IsLSeg Δ δ.rep) (hU : IsUnitarisable δ.rep) (hL' : IsLSeg Δ' δ'.rep)
    (hU' : IsUnitarisable δ'.rep) (x y : ℝ) (hP : (Δ.nu x).Precedes (Δ'.nu y)) : x + 1 ≤ y := by
  obtain ⟨⟨-, -, hnsub⟩, j, hj, hfirst⟩ := hP
  have hf : Δ'.first.nu (y : ℂ) = (Δ.first.nu (x : ℂ)).nu (j : ℂ) := hfirst
  have hρ' : Δ'.first = Δ.first.nu (((x + j - y : ℝ)) : ℂ) := by
    have h1 := congrArg (fun r => r.nu (-(y : ℂ))) hf
    simp only [IrrGL.nu_nu, add_neg_cancel, IrrGL.nu_zero] at h1
    rw [h1]
    congr 1
    push_cast
    ring
  have hd : Δ'.d = Δ.d := congrArg Sigma.fst hρ'
  obtain ⟨ω, -, hω⟩ := exists_smooth_hasCentralChar Δ.first.2.rep.smooth Δ.first.2.rep.irr
  have hω' : HasCentralChar Δ'.first.rep (ω * absPow k (((x + j - y : ℝ)) : ℂ) ^ Δ.first.1) := by
    rw [hρ']
    exact hasCentralChar_nu _ hω _
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer k
  have hne : nabs k ϖ ≠ 1 := fun e => uniformizer_lt_one.ne (hϖ ▸ (nabs_eq_one_iff ϖ).1 e)
  have hL0 : Real.log (nabs k ϖ) ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (nabs_pos' k ϖ) hne
  have hA := log_norm_centralChar hL hU hω ϖ
  have hA' := log_norm_centralChar hL' hU' hω' ϖ
  rw [log_norm_mul_absPow, hd] at hA'
  have hdL : (Δ.d : ℝ) * Real.log (nabs k ϖ) ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.2 Δ.d_pos.ne') hL0
  have ht : x + j - y = ((Δ.len : ℝ) - Δ'.len) / 2 := by
    apply mul_left_cancel₀ hdL
    have e1 : (Δ.first.1 : ℝ) = Δ.d := rfl
    rw [e1] at hA'
    linear_combination hA' - hA
  have hlen : Δ.len < j + Δ'.len := by
    by_contra hcon
    push_neg at hcon
    apply hnsub
    intro w hw
    obtain ⟨a, ha, rfl⟩ := Segment.mem_carrier.1 hw
    refine Segment.mem_carrier.2 ⟨j + a, ?_, ?_⟩
    · have ha' : a < Δ'.len := ha
      show j + a < Δ.len
      omega
    · rw [hfirst, IrrGL.nu_nu]
      push_cast
      rfl
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hl1 : (Δ.len : ℝ) + 1 ≤ j + Δ'.len := by exact_mod_cast hlen
  linarith

end GlobalTheory.LocGL.UnitaryOrder
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UpperMatrixUnitKillsUnipotentInvariantOnLevi
section
open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

noncomputable section

namespace GlobalTheory.UnipKill

open Matrix

section General

variable {R S : Type} [CommRing R] [CommRing S] {α : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] {N : ℕ}

theorem cornerGL_mem_unipRad (s : R →ₙ+* S) (e : (Σ a, m a) ≃ Fin N) {g : GL (Fin N) R}
    (hg : g ∈ unipRad R e) : cornerGL N s g ∈ unipRad S e := by
  rw [mem_unipRad] at hg ⊢
  have hval : ∀ i j, ((cornerGL N s g : GL (Fin N) S) : Matrix (Fin N) (Fin N) S) i j =
      (1 : Matrix (Fin N) (Fin N) S) i j - s ((1 : Matrix (Fin N) (Fin N) R) i j) +
        s ((g : Matrix (Fin N) (Fin N) R) i j) := fun i j => rfl
  refine ⟨mem_parab.2 fun i j hij => ?_, fun a i j => ?_⟩
  · have hne : i ≠ j := by rintro rfl; exact lt_irrefl _ hij
    rw [hval, mem_parab.1 hg.1 i j hij]
    simp [Matrix.one_apply_ne hne]
  · rw [hval, hg.2 a i j]
    by_cases hij : i = j
    · subst hij; simp
    · have hne : e ⟨a, i⟩ ≠ e ⟨a, j⟩ := fun h => hij (by simpa using e.injective h)
      simp [Matrix.one_apply_ne hne, Matrix.one_apply_ne hij]


omit [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] in
def tv {p q : Fin N} (hpq : p ≠ q) (c : R) : GL (Fin N) R :=
  ⟨transvection p q c, transvection p q (-c),
    (transvection_mul_transvection_same p q hpq c (-c)).trans (by rw [add_neg_cancel, transvection_zero]),
    (transvection_mul_transvection_same p q hpq (-c) c).trans (by rw [neg_add_cancel, transvection_zero])⟩


omit [Fintype α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] in
theorem ne_of_blk_lt (e : (Σ a, m a) ≃ Fin N) {p q : Fin N} (hpq : blk e p < blk e q) : p ≠ q := by
  rintro rfl; exact lt_irrefl _ hpq

theorem tv_mem_unipRad (e : (Σ a, m a) ≃ Fin N) {p q : Fin N} (hpq : blk e p < blk e q) (c : R) :
    tv (ne_of_blk_lt e hpq) c ∈ unipRad R e := by
  rw [mem_unipRad]
  refine ⟨mem_parab.2 fun i j hij => ?_, fun a i j => ?_⟩
  · have hne : i ≠ j := by rintro rfl; exact lt_irrefl _ hij
    change (transvection p q c) i j = 0
    rw [transvection, Matrix.add_apply, Matrix.one_apply_ne hne, Matrix.single_apply]
    rw [if_neg, zero_add]
    rintro ⟨rfl, rfl⟩
    exact lt_asymm hpq hij
  · change (transvection p q c) (e ⟨a, i⟩) (e ⟨a, j⟩) = _
    rw [transvection, Matrix.add_apply, Matrix.single_apply, if_neg, add_zero]
    · by_cases hij : i = j
      · subst hij; simp
      · have hne : e ⟨a, i⟩ ≠ e ⟨a, j⟩ := fun h => hij (by simpa using e.injective h)
        rw [Matrix.one_apply_ne hne, Matrix.one_apply_ne hij]
    · rintro ⟨h1, h2⟩
      have h1' : blk e p = a := by rw [h1]; simp
      have h2' : blk e q = a := by rw [h2]; simp
      rw [h1', h2'] at hpq
      exact lt_irrefl _ hpq

end General

section Adelic

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}

theorem toL_tv {p q : Fin N} (hpq : p ≠ q) (x : Cinf E) (t : ℝ) :
    toL ((tv hpq (t • x) : GL (Fin N) (Cinf E)) : Matrix (Fin N) (Fin N) (Cinf E)) =
      oneL E N + t • toL (Matrix.single p q x) := by
  funext i j
  change (transvection p q (t • x)) i j = (1 : Matrix (Fin N) (Fin N) (Cinf E)) i j + t • (Matrix.single p q x) i j
  rw [transvection, Matrix.add_apply, Matrix.single_apply, Matrix.single_apply]
  split_ifs <;> simp

theorem lieD_single_leviEmb {c : ℕ} {n : Fin c → ℕ} (h : ∑ i, n i = N) (ψ : Sm E N)
    (hψ : ∀ u ∈ unipRad (Ad E) (stdBlocks n h), ∀ g, ψ.1 (u * g) = ψ.1 g) {p q : Fin N}
    (hpq : blk (stdBlocks n h) p < blk (stdBlocks n h) q) (x : Cinf E) (m : Levi (Ad E) fun i => Fin (n i)) :
    lieD (toL (Matrix.single p q x)) ψ.1 (leviEmb (Ad E) (stdBlocks n h) m) = 0 := by
  set e := stdBlocks n h
  set g := leviEmb (Ad E) e m
  have hne := ne_of_blk_lt e hpq
  let u : ℝ → GL (Fin N) (Cinf E) := fun t => tv hne (t • x)
  have hu0 : u 0 = 1 := Units.ext (by
    show transvection p q ((0 : ℝ) • x) = 1
    rw [zero_smul, transvection_zero])
  have hline : HasDerivAt (fun t => toL (u t).val) (toL (Matrix.single p q x)) 0 := by
    have : (fun t => toL (u t).val) = fun t : ℝ => oneL E N + t • toL (Matrix.single p q x) :=
      funext fun t => toL_tv hne x t
    rw [this]
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (toL (Matrix.single p q x))).const_add (oneL E N)
  have hc := hasDerivAt_curve ψ g u (toL (Matrix.single p q x)) hu0 hline
  have hconst : (fun t => ψ.1 (g * infGL E N (u t))) = fun _ => ψ.1 g := by
    funext t
    have hv : infGL E N (u t) ∈ unipRad (Ad E) e := cornerGL_mem_unipRad (sInf E) e (tv_mem_unipRad e hpq _)
    have hw : g * infGL E N (u t) * g⁻¹ ∈ unipRad (Ad E) e :=
      (Subgroup.mem_normalizer_iff.1 (leviEmb_mem_normalizer (Ad E) e m) _).1 hv
    rw [← hψ _ hw g, inv_mul_cancel_right]
  rw [hconst] at hc
  exact hc.unique (hasDerivAt_const 0 _)

end Adelic


open Complex in
theorem eop_leviEmb_eq_zero (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {c N : ℕ} (n : Fin c → ℕ)
    (h : ∑ i, n i = N) (ψ : Sm E N) (hψ : ∀ u ∈ unipRad (Ad E) (stdBlocks n h), ∀ g, ψ.1 (u * g) = ψ.1 g)
    (τ : E →+* ℂ) (p q : Fin N) (hpq : blk (stdBlocks n h) p < blk (stdBlocks n h) q) (m) :
    (Eop τ p q ψ).1 (leviEmb (Ad E) (stdBlocks n h) m) = 0 := by
  have key := fun x => lieD_single_leviEmb h ψ hψ hpq x m
  change ((1 / 2 : ℂ) • (lieS E N p q (atEmb τ 1) - Complex.I • lieS E N p q (atEmb τ Complex.I)) ψ).1 _ = 0
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, Submodule.coe_smul, Submodule.coe_sub, Pi.smul_apply,
    Pi.sub_apply, lieS_apply, CuspRep.lie_apply, key, smul_zero, sub_zero]

end GlobalTheory.UnipKill
end
end

