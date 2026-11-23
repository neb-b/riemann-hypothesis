module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0259
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0253
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0252
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeAlgebraMapOC

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamPeriodRingFieldTPowFiltrationUnits
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.BdRTied

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

def tu : P.R.BdRˣ := Units.map (P.ιB : P.R.B →* P.R.BdR) (isUnit_tB P).unit

theorem tu_val : (tu P : P.R.BdR) = P.ιB P.tB := by
  simp [tu]

theorem tz_eq (a : ℤ) : tz P a = ((tu P ^ a : P.R.BdRˣ) : P.R.BdR) := by
  rw [tz, tu, ← map_zpow]
  rfl

theorem fil_anti_le {a b : ℤ} (h : a ≤ b) (x : P.R.BdR) (hx : x ∈ Fil P b) : x ∈ Fil P a := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, b = a + n := ⟨(b - a).toNat, by omega⟩
  subst b
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    change x ∈ (P.PD (botExt l)).Fil (a + ↑(n + 1)) at hx
    exact ih (by omega) ((P.PD (botExt l)).Fil_anti (a + n) (by simpa [add_assoc] using hx))

theorem ι_injective : Function.Injective P.ιB := fun a b h =>
  (P.PD (botExt l)).ι_inj (by rw [P.PD_ι, P.PD_ι]; exact h)

theorem fil_mul (a b : ℤ) (x y : P.R.BdR) (hx : x ∈ Fil P a) (hy : y ∈ Fil P b) : x * y ∈ Fil P (a + b) :=
  (P.PD (botExt l)).Fil_mul a b x y hx hy

theorem fil_act (a : ℤ) (g : GQ l) (x : P.R.BdR) (hx : x ∈ Fil P a) : P.actQdR g x ∈ Fil P a := by
  have h := (P.PD (botExt l)).Fil_G ⟨g, mem_GK_botExt g⟩ a x hx
  rwa [P.PD_actdR] at h

theorem actQ_tpow (g : GQ l) (a : ℤ) : P.actQ g (((isUnit_tB P).unit ^ a : P.R.Bˣ) : P.R.B) =
    algebraMap ℚ_[l] P.R.B ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l]) * (((isUnit_tB P).unit ^ a : P.R.Bˣ) : P.R.B) := by
  have h : Units.map (P.actQ g : P.R.B →* P.R.B) (isUnit_tB P).unit =
      Units.map (algebraMap ℚ_[l] P.R.B : ℚ_[l] →* P.R.B) (P.χQ g) * (isUnit_tB P).unit := by
    apply Units.ext
    simpa [Algebra.smul_def] using localPrime_galoisAction_periodT P g
  have h2 := congrArg (fun u : P.R.Bˣ => ((u ^ a : P.R.Bˣ) : P.R.B)) h
  simp only [mul_zpow, ← map_zpow, Units.val_mul, Units.coe_map] at h2
  rw [← map_zpow P.χQ]
  exact h2

theorem act_tz (g : GQ l) (a : ℤ) : P.actQdR g (tz P a) =
    algebraMap ℚ_[l] P.R.BdR ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l]) * tz P a := by
  have hι : ∀ b : P.R.B, P.actQdR g (P.ιB b) = P.ιB (P.actQ g b) := fun b => by
    have h := (P.PD (botExt l)).ι_comm ⟨g, mem_GK_botExt g⟩ b
    rw [P.PD_actB, P.PD_actdR, P.PD_ι, P.PD_ι] at h
    exact h.symm
  rw [tz, hι, actQ_tpow, map_mul, AlgHom.commutes]

variable {AI : LocAinf l P}

theorem fil_step (T : LocTied l P AI) (a : ℤ) (x : P.R.BdR) : x ∈ Fil P a ↔ P.ιB P.tB * x ∈ Fil P (a + 1) := by
  have h := ((GlobalTheory.MemLoc.TiedUnif.tied_uniformiser l P AI T).2.2 (botExt l) a (P.ιB P.tB * x))
  change x ∈ (P.PD (botExt l)).Fil a ↔ P.ιB P.tB * x ∈ (P.PD (botExt l)).Fil (a + 1)
  rw [h]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, e⟩
    have hu : IsUnit (P.ιB P.tB) := tu_val P ▸ (tu P).isUnit
    rwa [hu.mul_left_cancel e]

theorem fil_tz (T : LocTied l P AI) (b : ℤ) : ∀ (a : ℤ) (x : P.R.BdR), x ∈ Fil P a ↔ tz P b * x ∈ Fil P (a + b) := by
  induction b using Int.induction_on with
  | zero => intro a x; simp [tz_eq]
  | succ b ih =>
    intro a x
    rw [ih a x, fil_step P T (a + b), tz_eq, tz_eq, zpow_add_one, Units.val_mul, tu_val, ← add_assoc]
    ring_nf
  | pred b ih =>
    intro a x
    rw [ih a x, fil_step P T (a + (-(b : ℤ) - 1)), tz_eq, tz_eq, ← tu_val, ← mul_assoc, ← Units.val_mul,
      ← zpow_one_add]
    ring_nf

theorem isField (T : LocTied l P AI) : IsField P.R.BdR := by
  obtain ⟨-, -, hF, -⟩ := GlobalTheory.MemLoc.BdRField.bdR_isField l
  exact MulEquiv.isField hF T.eD.toMulEquiv

theorem unit_of_fil (T : LocTied l P AI) (x : P.R.BdR) (h0 : x ∈ Fil P 0) (h1 : x ∉ Fil P 1) :
    ∃ y ∈ Fil P 0, x * y = 1 := by
  obtain ⟨C, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  have he : GlobalTheory.MemLoc.IsEps AI.ε := hC.ε ▸ GlobalTheory.MemLoc.core_isEps l C
  obtain ⟨-, hker, hunit, -, -⟩ := GlobalTheory.MemLoc.thetaD_props l
  have h0' : T.eD x ∈ Formalism.Per.FilD l 0 := (T.fil (botExt l) 0 x).1 h0
  obtain ⟨w, hw⟩ := (GlobalTheory.MemLoc.TiedUnif.mem_FilD_iff he 0 (T.eD x)).1 h0'
  rw [zpow_zero, Units.val_one, one_mul] at hw
  have hθ : Formalism.Per.θD l w ≠ 0 := by
    intro hz
    apply h1
    change x ∈ (P.PD (botExt l)).Fil 1
    rw [T.fil, hw]
    have := GlobalTheory.MemLoc.TiedUnif.alg_mem_FilD 1 ((hker w).1 hz)
    simpa using this
  obtain ⟨w', hw'⟩ := (hunit w hθ).exists_right_inv
  refine ⟨T.eD.symm (algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) w'), ?_, T.eD.injective ?_⟩
  · change _ ∈ (P.PD (botExt l)).Fil 0
    rw [T.fil, RingEquiv.apply_symm_apply]
    exact GlobalTheory.MemLoc.TiedUnif.alg_mem_FilD_zero w'
  · rw [map_mul, RingEquiv.apply_symm_apply, hw, ← map_mul, hw', map_one, map_one]

theorem exact_deg (x : P.R.BdR) (hx : x ≠ 0) : ∃ a : ℤ, x ∈ Fil P a ∧ x ∉ Fil P (a + 1) := by
  classical
  obtain ⟨a₀, ha₀⟩ := (P.PD (botExt l)).Fil_exh x
  have hc : ∃ c, x ∉ Fil P c := by
    by_contra h
    push_neg at h
    exact hx ((P.PD (botExt l)).Fil_sep x h)
  obtain ⟨c, hc⟩ := hc
  have hbd : ∀ z : ℤ, x ∈ Fil P z → z ≤ c := fun z hz => by
    by_contra hlt
    exact hc (fil_anti_le P (le_of_lt (not_le.1 hlt)) x hz)
  obtain ⟨a, ha, hmax⟩ := Int.exists_greatest_of_bdd ⟨c, hbd⟩ ⟨a₀, ha₀⟩
  exact ⟨a, ha, fun h => by have := hmax _ h; omega⟩

end GlobalTheory.PMon.BdRTied

namespace GlobalTheory.PMon

theorem bdR_tied : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI),
    IsField P.R.BdR ∧ Function.Injective P.ιB ∧
    (∀ (a b : ℤ) (x : P.R.BdR), x ∈ Fil P a ↔ tz P b * x ∈ Fil P (a + b)) ∧
    (∀ x ∈ Fil P 0, x ∉ Fil P 1 → ∃ y ∈ Fil P 0, x * y = 1) ∧
    (∀ x : P.R.BdR, x ≠ 0 → ∃ a : ℤ, x ∈ Fil P a ∧ x ∉ Fil P (a + 1)) ∧
    (∀ (a b : ℤ) (x y : P.R.BdR), x ∈ Fil P a → y ∈ Fil P b → x * y ∈ Fil P (a + b)) ∧
    (∀ (a : ℤ) (g : GQ l) (x : P.R.BdR), x ∈ Fil P a → P.actQdR g x ∈ Fil P a) ∧
    (∀ (a : ℤ) (g : GQ l), P.actQdR g (tz P a) = algebraMap ℚ_[l] P.R.BdR ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l]) * tz P a) ∧
    (∀ a b : ℤ, tz P (a + b) = tz P a * tz P b) ∧ tz P 0 = 1 ∧ tz P 1 = P.ιB P.tB := by
  intro l _ P AI T
  refine ⟨BdRTied.isField P T, BdRTied.ι_injective P, fun a b x => BdRTied.fil_tz P T b a x,
    fun x h0 h1 => BdRTied.unit_of_fil P T x h0 h1, BdRTied.exact_deg P, BdRTied.fil_mul P,
    BdRTied.fil_act P, fun a g => BdRTied.act_tz P g a, fun a b => ?_, ?_, ?_⟩
  · rw [BdRTied.tz_eq, BdRTied.tz_eq, BdRTied.tz_eq, zpow_add, Units.val_mul]
  · rw [BdRTied.tz_eq, zpow_zero, Units.val_one]
  · rw [BdRTied.tz_eq, zpow_one, BdRTied.tu_val]

end GlobalTheory.PMon
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EmbWInjective
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct

namespace GlobalTheory.PrismS

variable {l : ℕ} [Fact l.Prime]

abbrev unr (K : FinExt l) : FinExt l :=
  ⟨K0 K, by
    have := K.2
    exact FiniteDimensional.of_injective
      (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective (inf_le_left : K0 K ≤ K.1))⟩

abbrev WK (K : FinExt l) : Type := ↥(OL (unr K))

def embW {K LL : FinExt l} (e : ↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1) : WK K →ₐ[ℤ_[l]] ↥(OL LL) :=
  (e.restrictScalars ℤ_[l]).mapIntegralClosure

theorem embW_injective {K LL : FinExt l} (e : ↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1) : Function.Injective (embW e) :=
  fun _ _ h => Subtype.ext (e.toRingHom.injective (congrArg Subtype.val h))

def letEmb {K LL : FinExt l} {n : ℕ} (emb : ZMod n → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1)) :
    PowerSeries (WK K) →+* LetA ↥(OL LL) n :=
  RingHom.pi fun i => PowerSeries.map (embW (emb i)).toRingHom

theorem letEmb_apply {K LL : FinExt l} {n : ℕ} (emb : ZMod n → (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1))
    (x : PowerSeries (WK K)) (i : ZMod n) :
    letEmb emb x i = PowerSeries.map (embW (emb i)).toRingHom x := rfl

end GlobalTheory.PrismS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfPowEqOneOfValLt
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.TameCharDet

open scoped Pointwise

theorem eq_of_pow_eq_one_of_val_lt {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (n : ℕ)
    (hn : ¬ A.valuation (n : Ω) < 1) {ξ ξ' : Ω} (h : ξ ^ n = 1) (h' : ξ' ^ n = 1)
    (hlt : A.valuation (ξ - ξ') < 1) : ξ = ξ' := by
  first
  | exact @_root_.GlobalTheory.RootValuationOne.main
  | exact _root_.GlobalTheory.RootValuationOne.main
  | (apply _root_.GlobalTheory.RootValuationOne.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.RootValuationOne.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RootValuationOne.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RootValuationOne.main ..)

theorem eq_of_tameChar : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), Formalism.ConjugateSelfDual.IsPlaceOver A v → ∀ γ : Formalism.ConjugateSelfDual.G E Ω, TameGenAt A γ → ∀ (K : Type) [Field K] [TopologicalSpace K] [T2Space K] (r : Formalism.ConjugateSelfDual.G E Ω →* Kˣ), Continuous r → ∀ n : ℕ, 0 < n → ((n : ℕ) : 𝓞 E) ∉ v.asIdeal → (∀ σ ∈ Ine (F := E) A, r σ ^ n = 1) → ∀ (π : Ω) (e : E), π ≠ 0 → π ^ n = algebraMap E Ω e → orderOf (γ π / π) = n → ∀ σ ∈ Ine (F := E) A, A.valuation (σ π / π - γ π / π) < 1 → r σ = r γ := by
  intro E Ω _ _ _ _ _ v A hA γ hγ K _ _ _ r hr n hn hnv hI π e hπ he hord σ hσ hσv
  have hn0 : n ≠ 0 := hn.ne'
  have hnA : ¬ A.valuation (n : Ω) < 1 := by
    intro h
    apply hnv
    rw [← hA]
    simpa using h
  set ζ := γ π / π with hζ
  have hζn : ζ ^ n = 1 := by rw [← hord]; exact pow_orderOf_eq_one ζ
  have hγn : r γ ^ n = 1 := hI γ hγ.1
  have hred : ∀ {M : Type} [Monoid M] (x : M), x ^ n = 1 → ∀ a : ℕ, x ^ a = x ^ (a % n) := by
    intro M _ x hx a
    conv_lhs => rw [← Nat.div_add_mod a n, pow_add, pow_mul, hx, one_pow, one_mul]
  have hvζ : A.valuation ζ = 1 := by
    have hp : A.valuation ζ ^ n = 1 := by rw [← map_pow, hζn, map_one]
    rcases lt_trichotomy (A.valuation ζ) 1 with hl | he | hg
    · exact absurd hp (pow_lt_one₀ zero_le' hl hn0).ne
    · exact he
    · exact absurd hp (one_lt_pow₀ hg hn0).ne'

  have hfixζ : ∀ τ ∈ Ine (F := E) A, τ ζ = ζ := by
    intro τ hτ
    refine eq_of_pow_eq_one_of_val_lt A n hnA ?_ hζn (hτ.2 ζ hvζ.le)
    rw [← map_pow, hζn, map_one]

  have hfixπ : ∀ τ : Formalism.ConjugateSelfDual.G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) → τ π = π := by
    intro τ hτ
    have h1 : (τ π / π) ^ n = 1 := by
      rw [div_pow, ← map_pow, he, AlgEquiv.commutes, div_self]
      rw [← he]; exact pow_ne_zero _ hπ
    have h2 := eq_of_pow_eq_one_of_val_lt A n hnA h1 (one_pow n) (hτ π hπ)
    rwa [div_eq_one_iff_eq hπ] at h2

  have hw : ∀ τ : Formalism.ConjugateSelfDual.G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) → r τ = 1 := by
    intro τ hτ
    by_contra hne
    have hd : orderOf (r τ) ∣ n := orderOf_dvd_of_pow_eq_one (hI τ (GlobalTheory.TameGenPowers.wild_mem_Ine hτ))
    have hne1 : orderOf (r τ) ≠ 1 := by rwa [Ne, orderOf_eq_one_iff]
    obtain ⟨l, hl, k, hk⟩ := Nat.exists_prime_and_dvd hne1
    have hlv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal := by
      intro h
      apply hnv
      obtain ⟨c, hc⟩ := hd
      rw [hc, hk]
      push_cast
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ h)
    have h1 : r (τ ^ k) = 1 := by
      refine GlobalTheory.TameGenPowers.eq_one_of_wild_prime E Ω v A hA K r hr l hl hlv _
        (GlobalTheory.WildInertiaChar.wild_pow A τ hτ k) ?_
      rw [map_pow, ← pow_mul, mul_comm, ← hk, pow_orderOf_eq_one]
    rw [map_pow] at h1
    have h2 := orderOf_dvd_of_pow_eq_one h1
    have ho : orderOf (r τ) ≠ 0 := fun h => hn0 (by simpa [h] using hd)
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact ho (by simpa using hk)
    have h3 := Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) h2
    rw [hk] at h3
    have := hl.two_le
    have := Nat.pos_of_ne_zero hk0
    nlinarith

  have hint : IsIntegral E π := Algebra.IsIntegral.isIntegral π
  haveI : FiniteDimensional E (IntermediateField.adjoin E {π}) :=
    IntermediateField.adjoin.finiteDimensional hint
  have hHo : IsOpen ((IntermediateField.adjoin E {π}).fixingSubgroup : Set (Formalism.ConjugateSelfDual.G E Ω)) :=
    IntermediateField.fixingSubgroup_isOpen _
  have hfixH : ∀ τ g : Formalism.ConjugateSelfDual.G E Ω, g ∈ (IntermediateField.adjoin E {π}).fixingSubgroup →
      (τ * g) π = τ π := by
    intro τ g hg
    rw [AlgEquiv.mul_apply, (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg π
      (IntermediateField.mem_adjoin_simple_self E π)]
  have hopen : ∀ U : Set (Formalism.ConjugateSelfDual.G E Ω), (∀ τ ∈ U, ∀ g ∈ (IntermediateField.adjoin E {π}).fixingSubgroup,
      τ * g ∈ U) → IsOpen U := by
    intro U hU
    rw [isOpen_iff_mem_nhds]
    intro τ hτ
    rw [← map_mul_left_nhds_one τ]
    exact Filter.mem_map.2 (Filter.mem_of_superset (hHo.mem_nhds (one_mem _)) fun g hg => hU τ hτ g hg)
  have hloc : ∀ c : Ω, IsClosed {τ : Formalism.ConjugateSelfDual.G E Ω | τ π = c} := by
    intro c
    rw [← isOpen_compl_iff]
    refine hopen _ fun τ hτ g hg => ?_
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hτ ⊢
    rwa [hfixH τ g hg]
  let T : Set (Formalism.ConjugateSelfDual.G E Ω) := ⋃ a ∈ Finset.range n, {τ | r τ = r γ ^ a ∧ τ π = ζ ^ a * π}
  have hTc : IsClosed T := by
    refine isClosed_biUnion_finset fun a _ => ?_
    exact (isClosed_singleton.preimage hr).inter (hloc _)

  let P : Formalism.ConjugateSelfDual.G E Ω → Prop := fun τ =>
    τ ∈ Ine (F := E) A ∧ ∃ a : ℕ, r τ = r γ ^ a ∧ τ π = ζ ^ a * π
  have hP : ∀ τ ∈ Subgroup.closure (insert γ
      {σ : Formalism.ConjugateSelfDual.G E Ω | ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1}), P τ := by
    intro τ hτ
    induction hτ using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · exact ⟨hγ.1, 1, (pow_one _).symm, by rw [pow_one, hζ, div_mul_cancel₀ _ hπ]⟩
      · exact ⟨GlobalTheory.TameGenPowers.wild_mem_Ine hx, 0, by rw [hw x hx, pow_zero],
          by rw [hfixπ x hx, pow_zero, one_mul]⟩
    | one => exact ⟨one_mem _, 0, by rw [map_one, pow_zero], by rw [pow_zero, one_mul]; rfl⟩
    | mul x y _ _ ihx ihy =>
      obtain ⟨hxI, a, ha, haπ⟩ := ihx
      obtain ⟨hyI, b, hb, hbπ⟩ := ihy
      refine ⟨mul_mem hxI hyI, a + b, by rw [map_mul, ha, hb, pow_add], ?_⟩
      rw [AlgEquiv.mul_apply, hbπ, map_mul, map_pow, hfixζ x hxI, haπ, pow_add]
      ring
    | inv x _ ihx =>
      obtain ⟨hxI, a, ha, haπ⟩ := ihx
      have hiI : x⁻¹ ∈ Ine (F := E) A := inv_mem hxI
      have hex : a * (n - 1) + a = a * n := by
        rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hn]
      refine ⟨hiI, a * (n - 1), ?_, ?_⟩
      · rw [map_inv, ha]
        symm
        refine eq_inv_of_mul_eq_one_left ?_
        rw [← pow_add, hex, pow_mul', hγn, one_pow]
      · have hxx : (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) (x π) = π := by
          rw [← AlgEquiv.mul_apply, inv_mul_cancel]; rfl
        have h1 : π = ζ ^ a * (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π := by
          have h2 := congrArg (fun y => (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) y) haπ
          rw [hxx, map_mul, map_pow, hfixζ _ hiI] at h2
          exact h2
        calc (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π = ζ ^ (a * (n - 1) + a) * (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π := by
              rw [hex, pow_mul', hζn, one_pow, one_mul]
          _ = ζ ^ (a * (n - 1)) * (ζ ^ a * (x⁻¹ : Formalism.ConjugateSelfDual.G E Ω) π) := by ring
          _ = ζ ^ (a * (n - 1)) * π := by rw [← h1]
  have hST : ((Subgroup.closure (insert γ
      {σ : Formalism.ConjugateSelfDual.G E Ω | ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1}) : Subgroup (Formalism.ConjugateSelfDual.G E Ω)) :
        Set (Formalism.ConjugateSelfDual.G E Ω)) ⊆ T := by
    intro τ hτ
    obtain ⟨-, a, ha, haπ⟩ := hP τ hτ
    refine Set.mem_biUnion (x := a % n) (Finset.mem_coe.2 (Finset.mem_range.2 (Nat.mod_lt _ hn))) ?_
    exact ⟨by rw [ha, hred _ hγn a], by rw [haπ, hred _ hζn a]⟩
  have hσT : σ ∈ T := closure_minimal hST hTc (hγ.2 hσ)
  obtain ⟨a, ha, haπ⟩ : ∃ a : ℕ, r σ = r γ ^ a ∧ σ π = ζ ^ a * π := by
    simp only [T, Set.mem_iUnion] at hσT
    obtain ⟨a, -, h⟩ := hσT
    exact ⟨a, h⟩
  have hq : σ π / π = ζ ^ a := by rw [haπ, mul_div_assoc, div_self hπ, mul_one]
  rw [hq] at hσv
  have hζa : ζ ^ a = ζ := by
    refine eq_of_pow_eq_one_of_val_lt A n hnA ?_ hζn hσv
    rw [← pow_mul, mul_comm, pow_mul, hζn, one_pow]
  have hmod : a ≡ 1 [MOD n] := by
    rcases Nat.eq_zero_or_pos a with rfl | ha0
    · have h1 : orderOf ζ = 1 := orderOf_eq_one_iff.2 (by rw [← hζa, pow_zero])
      rw [← hord, h1]; exact Nat.modEq_one
    · have hζ0 : ζ ≠ 0 := by
        intro h; rw [h, zero_pow hn0] at hζn; exact zero_ne_one hζn
      have h1 : ζ ^ (a - 1) = 1 := by
        have h3 : ζ ^ (a - 1) * ζ = 1 * ζ := by
          rw [← pow_succ, Nat.sub_add_cancel ha0, hζa, one_mul]
        exact mul_right_cancel₀ hζ0 h3
      have h2 := orderOf_dvd_of_pow_eq_one h1
      rw [hord] at h2
      exact ((Nat.modEq_iff_dvd' ha0).2 h2).symm
  rw [ha]
  conv_rhs => rw [← pow_one (r γ)]
  exact (pow_eq_pow_iff_modEq).2 (hmod.of_dvd (orderOf_dvd_of_pow_eq_one hγn))

end GlobalTheory.TameCharDet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfTmulOne
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.Pass.RankDeRham

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)


include PD in
theorem one_ne_zero_BdR : (1 : BdR) ≠ 0 := by
  intro h
  apply PD.not_mem_filtration_two
  have : PD.ι PD.t = 0 := by rw [← mul_one (PD.ι PD.t), h, mul_zero]
  rw [this]
  exact Submodule.zero_mem _


include PD in
theorem eq_zero_of_tmul_one (v : V) (hv : v ⊗ₜ[Qp] (1 : BdR) = 0) : v = 0 := by
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one Qp (one_ne_zero_BdR PD)
  have h := congrArg (fun x => TensorProduct.rid Qp V (LinearMap.lTensor V f x)) hv
  simpa [hf] using h

theorem finrank_H0V_le [FiniteDimensional LL ↥(DdR PD ρ)] :
    finrank LL ↥(H0V ρ) ≤ finrank LL ↥(DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) 0) := by
  haveI : FiniteDimensional LL ↥(DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) 0) :=
    Submodule.finiteDimensional_of_le inf_le_left
  let j : V →ₗ[LL] V ⊗[Qp] BdR := (AlgebraTensorModule.mk Qp LL V BdR).flip 1
  have hj : ∀ v, j v = v ⊗ₜ[Qp] (1 : BdR) := fun v => rfl
  have hm : ∀ v ∈ H0V ρ, j v ∈ DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) 0 := by
    intro v hv
    refine ⟨?_, ?_⟩
    · simp only [H0V, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero] at hv
      have : j v ∈ DdR PD ρ := by
        simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
          LinearMap.id_apply, sub_eq_zero]
        intro g
        rw [hj]
        simp [actVdR, hv g]
      exact this
    · exact ⟨v ⊗ₜ[Qp] ⟨1, PD.one_mem⟩, by simp [hj]⟩
  refine LinearMap.finrank_le_finrank_of_injective (f := j.restrict hm) ?_
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro v hv
  have h0 : j v.1 = 0 := congrArg Subtype.val (LinearMap.mem_ker.1 hv)
  have := eq_zero_of_tmul_one PD v.1 (by rw [← hj]; exact h0)
  exact (Submodule.mem_bot _).2 (Subtype.ext this)

theorem h0_add_le [FiniteDimensional LL V] (hK : finrank Qp K = 1) (h : IsDR PD ρ) :
    (finrank LL ↥(H0V ρ) : ℤ) + ((finrank LL ↥(DdR PD ρ) : ℤ) -
      finrank LL ↥(DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) 0)) ≤ finrank LL V := by
  have h' : finrank LL ↥(DdR PD ρ) = finrank LL V := by rw [h, hK, one_mul]
  rcases Nat.eq_zero_or_pos (finrank LL V) with h0 | h0
  · have := Submodule.finrank_le (H0V ρ)
    omega
  · haveI : FiniteDimensional LL ↥(DdR PD ρ) := Module.finite_of_finrank_pos (by omega)
    have := finrank_H0V_le PD ρ
    omega

end General

set_option synthInstance.maxHeartbeats 400000 in
theorem finrank_H1f_le : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l), finrank ℚ_[l] ↥K.1 = 1 → LocalSituation.bkAll (P.PD K) → ∀ A : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL), IsDR (P.PD K) A.ρ → finrank ↥LL.1 (FiniteCohomology (P.PD K) A.ρ) ≤ finrank ↥LL.1 A.V := by
  intro l _ P K LL hK hBK A hA
  have hd := hBK.2.1 _ _ (goodO_ringOfIntegers l LL) A hA
  have h := h0_add_le (P.PD K) A.ρ hK hA
  rw [← hd] at h
  exact_mod_cast h

end GlobalTheory.Pass.RankDeRham
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimeEqMulPrimitiveRootSubOnePowStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_eq_mul_primitiveRoot_sub_one_pow' : ∀ (l : ℕ) [Fact l.Prime] (H : ℕ) (ζ : PadicComplex l), IsPrimitiveRoot ζ (l ^ (1 + n0 l H)) → ∃ u : PadicComplex l, ‖u‖ ≤ 1 ∧ (l : PadicComplex l) = u * (ζ - 1) ^ H := by
  first | exact @GlobalTheory.Cyc.Decomp.exists_prime_eq_mul_primitiveRoot_sub_one_pow | exact GlobalTheory.Cyc.Decomp.exists_prime_eq_mul_primitiveRoot_sub_one_pow | (intros; apply GlobalTheory.Cyc.Decomp.exists_prime_eq_mul_primitiveRoot_sub_one_pow <;> assumption)
end

