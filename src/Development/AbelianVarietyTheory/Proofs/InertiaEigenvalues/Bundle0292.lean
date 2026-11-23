module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverEta
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWittTiltTensor
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0282
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0267
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0223
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0269
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffEmbeddingIntegersResCharUnit
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

namespace GlobalTheory.NLocPlace

theorem vAdd_int (D : D7) (w : D.what₂.places.Pl) (a : 𝓞 D.what₂.LL) (ha : (a : D.what₂.LL) ≠ 0) :
    0 ≤ vAdd (D.plEq w) (a : D.what₂.LL) ∧ (a ∈ (D.plEq w).asIdeal ↔ 0 < vAdd (D.plEq w) (a : D.what₂.LL)) := by
  have hv0 : (D.plEq w).valuation D.what₂.LL (a : D.what₂.LL) ≠ 0 := (Valuation.ne_zero_iff _).2 ha
  have hle : (D.plEq w).valuation D.what₂.LL (algebraMap (𝓞 D.what₂.LL) D.what₂.LL a) ≤ 1 :=
    (D.plEq w).valuation_le_one a
  have hmem := (D.plEq w).valuation_lt_one_iff_mem (K := D.what₂.LL) a
  change (D.plEq w).valuation D.what₂.LL (a : D.what₂.LL) ≤ 1 at hle
  change (D.plEq w).valuation D.what₂.LL (a : D.what₂.LL) < 1 ↔ _ at hmem
  unfold vAdd
  rw [← WithZero.exp_log hv0, ← WithZero.exp_zero, WithZero.exp_le_exp] at hle
  rw [← WithZero.exp_log hv0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hmem
  refine ⟨by omega, ?_⟩
  rw [← hmem]
  omega

end GlobalTheory.NLocPlace

namespace GlobalTheory.NLocPlace

theorem ec_int_resChar_unit : ∀ (D : D7) (M : MtFam D) (B : NLocBase D M) (j : ℕ) (w : D.what₂.places.Pl),
    (∀ a : 𝓞 D.what₂.LL, B.ec j w (a : D.what₂.LL) ∈ (algebraMap (B.Oc j w) (FractionRing (B.Oc j w))).range) ∧
    ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal ∧
    ∀ (a : 𝓞 D.what₂.LL) (z : B.Oc j w), algebraMap (B.Oc j w) (FractionRing (B.Oc j w)) z = B.ec j w (a : D.what₂.LL) →
      (a ∈ (D.plEq w).asIdeal ↔ ¬ IsUnit z) := by
  intro D M B j w
  have hinj : Function.Injective (algebraMap (B.Oc j w) (FractionRing (B.Oc j w))) :=
    IsFractionRing.injective _ _

  have hval : ∀ x : D.what₂.LL, x ≠ 0 → D.what₂.places.val w x = ((vAdd (D.plEq w) x : ℤ) : WithTop ℤ) :=
    fun x hx => D.val_eq w x hx

  have hsum : ∀ x : D.what₂.LL, x ≠ 0 → vAdd (D.plEq w) x + vAdd (D.plEq w) x⁻¹ = 0 := by
    intro x hx
    have h1 : D.what₂.places.val w (x * x⁻¹) = 0 := by rw [mul_inv_cancel₀ hx, AddValuation.map_one]
    rw [AddValuation.map_mul, hval x hx, hval x⁻¹ (inv_ne_zero hx), ← WithTop.coe_add] at h1
    exact_mod_cast h1
  refine ⟨?_, ?_, ?_⟩
  · intro a
    apply (B.ec_w j w _).1
    by_cases ha : (a : D.what₂.LL) = 0
    · rw [ha, AddValuation.map_zero]; exact le_top
    · rw [hval _ ha]
      exact_mod_cast (vAdd_int D w a ha).1
  · have hp0 : (((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) : D.what₂.LL) ≠ 0 := by
      push_cast; exact Nat.cast_ne_zero.2 (D.what₂.places.resChar_prime w).ne_zero
    rw [(vAdd_int D w _ hp0).2]
    have h1 := D.what₂.places.val_resChar w
    have hc : (((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) : D.what₂.LL) = ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) := by
      push_cast; rfl
    rw [← hc, hval _ hp0] at h1
    have h2 : vAdd (D.plEq w) (((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) : D.what₂.LL) = (D.what₂.places.ramIdx w : ℤ) :=
      WithTop.coe_injective h1
    rw [h2]
    exact_mod_cast D.what₂.places.ramIdx_pos w
  · intro a z hz
    by_cases ha : (a : D.what₂.LL) = 0
    · have ha' : a = 0 := by exact_mod_cast ha
      have hz0 : z = 0 := hinj (by rw [hz, ha, map_zero, map_zero])
      subst ha' hz0
      simp
    · have hec : B.ec j w (a : D.what₂.LL) ≠ 0 := by
        rw [map_ne_zero]; exact ha
      obtain ⟨hnn, hiff⟩ := vAdd_int D w a ha
      have hs := hsum _ ha
      rw [hiff]
      constructor
      · rintro hpos ⟨u, hu⟩
        have h1 : algebraMap (B.Oc j w) (FractionRing (B.Oc j w)) (↑u⁻¹ : B.Oc j w) = B.ec j w (a : D.what₂.LL)⁻¹ := by
          rw [map_inv₀, ← hz, ← hu]
          apply eq_inv_of_mul_eq_one_right
          rw [← map_mul, Units.mul_inv, map_one]
        have h2 := (B.ec_w j w (a : D.what₂.LL)⁻¹).2 ⟨_, h1⟩
        rw [hval _ (inv_ne_zero ha)] at h2
        have h3 : (0 : ℤ) ≤ vAdd (D.plEq w) (a : D.what₂.LL)⁻¹ := by exact_mod_cast h2
        omega
      · intro hnu
        by_contra hle
        have h0 : vAdd (D.plEq w) (a : D.what₂.LL)⁻¹ = 0 := by omega
        have h2 : 0 ≤ D.what₂.places.val w (a : D.what₂.LL)⁻¹ := by
          rw [hval _ (inv_ne_zero ha), h0]; rfl
        obtain ⟨y, hy⟩ := (B.ec_w j w _).1 h2
        apply hnu
        have hzy : z * y = 1 := hinj (by rw [map_mul, map_one, hz, hy, ← map_mul, mul_inv_cancel₀ ha, map_one])
        exact ⟨⟨z, y, hzy, by rw [mul_comm]; exact hzy⟩, rfl⟩

end GlobalTheory.NLocPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAutCbCbTop
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section
open Filter Topology

namespace GlobalTheory.WeakClosed

theorem continuous_frac_act {A K G : Type} [CommRing A] [IsDomain A] [ValuationRing A] [Field K]
    [Algebra A K] [IsFractionRing A K] [TopologicalSpace G] (τ : G → (A ≃+* A))
    (σ : G → (K ≃+* K)) (hσ : ∀ g a, σ g (algebraMap A K a) = algebraMap A K (τ g a))
    (ho : ∀ (x a : A) (g₀ : G), a ≠ 0 → ∀ᶠ g in 𝓝 g₀, ¬ (τ g x - τ g₀ x ∣ a)) :
    letI : Valued K (ValuationRing.ValueGroup A K) := Valued.mk' (ValuationRing.valuation A K)
    Continuous fun p : G × K => σ p.1 p.2 := by
  letI V : Valued K (ValuationRing.ValueGroup A K) := Valued.mk' (ValuationRing.valuation A K)
  have hle : ∀ x y : K, Valued.v x ≤ Valued.v y ↔ ∃ c : A, algebraMap A K c * y = x := by
    intro x y
    change (∃ c : A, c • y = x) ↔ _
    simp only [Algebra.smul_def]
  have hinj := IsFractionRing.injective A K
  refine GlobalTheory.WeakTop.continuous_act_of_orbits σ ?_ ?_
  · intro g x y
    simp only [← not_le, hle]
    rintro h ⟨c, hc⟩
    refine h ⟨(τ g).symm c, (σ g).injective ?_⟩
    rw [map_mul, hσ, RingEquiv.apply_symm_apply, hc]
  · have hA : ∀ x : A, Continuous fun g => σ g (algebraMap A K x) := by
      intro x
      rw [continuous_iff_continuousAt]
      intro g₀ s hs
      obtain ⟨c, hc, hs⟩ := GlobalTheory.WeakTop.mem_nhds_iff_lt.1 hs
      obtain ⟨a, d, hd, rfl⟩ := IsFractionRing.div_surjective A c
      have hd0 : algebraMap A K d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
      have ha : a ≠ 0 := by
        rintro rfl
        simp at hc
      rw [mem_map]
      filter_upwards [ho x a g₀ ha] with g hg
      apply hs
      change Valued.v (σ g (algebraMap A K x) - σ g₀ (algebraMap A K x)) < _
      rw [← not_le, hle, hσ, hσ, ← map_sub]
      rintro ⟨e, he⟩
      refine hg ⟨e * d, hinj ?_⟩
      rw [eq_div_iff hd0] at he
      rw [← he, map_mul, map_mul]
      ring
    intro x
    obtain ⟨a, d, hd, rfl⟩ := IsFractionRing.div_surjective A x
    have hd0 : algebraMap A K d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
    simp only [map_div₀]
    exact (hA a).div (hA d) fun g => by simpa using hd0

theorem continuous_autCb_cbTop : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P),
    letI := cbTop l; Continuous fun q : GQ l × Cb l => autCb l (AI.actT q.1) q.2 := by
  intro l _ P AI
  refine continuous_frac_act (A := OCb l) (fun g => AI.actT g) (fun g => autCb l (AI.actT g))
    (fun g a => autCb_alg l _ a) fun x a g₀ ha => ?_
  obtain ⟨n, hn⟩ : ∃ n, PreTilt.coeff n a ≠ 0 := by
    by_contra! h
    refine ha (Perfection.ext fun n => ?_)
    change PreTilt.coeff n a = PreTilt.coeff n 0
    rw [h, map_zero]
  filter_upwards [GlobalTheory.WeakTop.eventually_coeff_eq AI x n g₀] with g hg
  rintro ⟨c, hc⟩
  apply hn
  rw [hc, map_mul, map_sub, hg, sub_self, zero_mul]

end GlobalTheory.WeakClosed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousGaloisCharacterFiltrationOne
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.LTChar

theorem char_cont : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (x : P.R.B), P.ιB x ∈ Fil P 1 → P.ιB x ∉ Fil P 2 → ∀ (c : ↥(GK K) → ↥(MaximalUnramifiedExtension l)), (∀ g : ↥(GK K), P.actQ (g : GQ l) x = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (c g) * x) → Continuous fun g => ((c g : ↥(MaximalUnramifiedExtension l)) : Om l) := by
  intro l _ P AI T K x h1 h2 c hc
  obtain ⟨-, -, hsh, -, -, -, -, hact, -⟩ := GlobalTheory.PMon.bdR_tied l P AI T
  obtain ⟨S, θ, hS, -, hker, hOm, hθ⟩ := GlobalTheory.PMon.exists_theta_deRhamFilZero_surjective_alt l P AI T
  have hu0 : tz P (-1) * P.ιB x ∈ Fil P 0 := by
    have := (hsh 1 (-1) _).1 h1
    simpa using this
  have hu1 : tz P (-1) * P.ιB x ∉ Fil P 1 := by
    intro h
    apply h2
    rw [hsh 2 (-1)]
    simpa using h
  set u : S := ⟨tz P (-1) * P.ιB x, (hS _).2 hu0⟩ with hu
  have hy : θ u ≠ 0 := fun h => hu1 ((hker u).1 h)
  have key : ∀ g : ↥(GK K), (((c g : ↥(MaximalUnramifiedExtension l)) : Om l) : ℂ_[l]) =
      algebraMap ℚ_[l] ℂ_[l] ((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) * Formalism.Per.σC (g : GQ l) (θ u) / θ u := by
    intro g
    obtain ⟨hg, hg'⟩ := hθ g u
    obtain ⟨ha, ha'⟩ := hOm (algebraMap ℚ_[l] (Om l) ((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]))
    obtain ⟨hb, hb'⟩ := hOm ((c g : ↥(MaximalUnramifiedExtension l)) : Om l)
    have e : (⟨_, ha⟩ : S) * ⟨_, hg⟩ = ⟨_, hb⟩ * u := by
      apply Subtype.ext
      show algebraMap (Om l) P.R.BdR _ * P.actQdR g (tz P (-1) * P.ιB x) = kd P (c g) * (tz P (-1) * P.ιB x)
      rw [map_mul, hact, ← iota_act, hc, map_mul, iota_kur, ← IsScalarTower.algebraMap_apply, ← mul_assoc, ← mul_assoc, ← mul_assoc,
        ← map_mul, ← Units.val_mul]
      simp only [zpow_neg, zpow_one, mul_inv_cancel, Units.val_one, map_one]
      ring
    have e' := congrArg θ e
    rw [map_mul θ, map_mul θ, ha', hb', hg'] at e'
    rw [eq_div_iff hy, ← e']
    rfl
  have hemb : Topology.IsEmbedding (fun y : Om l => (y : ℂ_[l])) :=
    UniformSpace.Completion.coe_isometry.isEmbedding
  refine hemb.continuous_iff.2 ?_
  have : ((fun y : Om l => (y : ℂ_[l])) ∘ fun g => ((c g : ↥(MaximalUnramifiedExtension l)) : Om l)) = _ := funext key
  rw [this]
  refine Continuous.div_const (Continuous.mul ?_ ?_) _
  · exact (continuous_algebraMap ℚ_[l] ℂ_[l]).comp
      ((GlobalTheory.Cyc.IsCyc.continuous P.χQ_cyc).comp continuous_subtype_val)
  · exact (orbit_cont (θ u)).comp continuous_subtype_val

end GlobalTheory.LTChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousGaloisCharacterOfBcrisUnitFilOne
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical

namespace GlobalTheory.LtCharCont

open GlobalTheory.ExpImage Filter Topology Formalism.MainNotions.LocalSituation

variable {l : ℕ} [Fact l.Prime]

theorem oB_mem {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (w : Om l) :
    oB P w ∈ FilB P 0 := by
  obtain ⟨y, h1, -⟩ := T.om w
  exact (GlobalTheory.ThetaTie.fil_zero T _).2 ⟨y, h1.symm⟩

theorem norm_th_le_of_mem_Lat {P : LocPrime l} {AI : LocAinf l P} (Θ : ThetaL P AI) {n : ℕ}
    {y : P.R.BdR} (hy : y ∈ Lat AI 1 n) : ‖Θ.θ y‖ ≤ ‖(l : ℚ_[l])‖ ^ n := by
  obtain ⟨a, ha⟩ := hy
  have hy0 : y ∈ FilB P 0 := Lat_mem_zero AI ⟨a, ha⟩
  have hi0 : io AI (((l : ℕ) : Ainf l) ^ n * a) ∈ FilB P 0 := io_mem AI _
  have hd0 : y - io AI (((l : ℕ) : Ainf l) ^ n * a) ∈ FilB P 0 := sub_mem hy0 hi0
  have h1 : Θ.θ (y - io AI (((l : ℕ) : Ainf l) ^ n * a)) = 0 :=
    (Θ.θ_ker _ hd0).2 (by simpa using ha)
  have h2 : Θ.θ y = Θ.θ (io AI (((l : ℕ) : Ainf l) ^ n * a)) := by
    have := Θ.θ_add _ hd0 _ hi0
    rw [sub_add_cancel, h1, zero_add] at this
    exact this
  have e : io AI (((l : ℕ) : Ainf l) ^ n * a) = qB P ((l : ℚ_[l]) ^ n) * io AI a := by
    rw [map_mul, map_pow, map_natCast, map_pow, map_natCast]
  rw [h2, e, Θ.θ_mul _ (qB_mem _) _ (io_mem AI a), norm_mul]
  have e2 : qB P ((l : ℚ_[l]) ^ n) = oB P (algebraMap ℚ_[l] (Om l) ((l : ℚ_[l]) ^ n)) :=
    IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR _
  rw [e2, Θ.θ_Om, PadicComplex.norm_extends]
  have e3 : ‖algebraMap ℚ_[l] (Om l) ((l : ℚ_[l]) ^ n)‖ = ‖(l : ℚ_[l])‖ ^ n := by
    rw [← norm_pow]; exact PadicAlgCl.norm_extends (p := l) _
  rw [e3]
  have := Θ.θ_int a
  rw [← io_apply AI a] at this
  calc _ ≤ ‖(l : ℚ_[l])‖ ^ n * 1 := by gcongr
    _ = _ := mul_one _

theorem continuous_char_of_act : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    LocTied l P AI → ∀ (K : FinExt l) (x : P.R.B), IsUnit x → P.ιB x ∈ (P.PD K).Fil 1 →
    P.ιB x ∉ (P.PD K).Fil 2 → ∀ c : ↥(GK K) →* (↥(K0 K))ˣ,
    (∀ g : ↥(GK K), P.actQ (g : GQ l) x =
      algebraMap ↥(K0 K) P.R.B ((c g : (↥(K0 K))ˣ) : ↥(K0 K)) * x) →
    Continuous (fun g : ↥(GK K) => (((c g : (↥(K0 K))ˣ) : ↥(K0 K)) : Om l)) := by
  intro l _ P AI T K x _hxu hx1 hx2 c hc
  let Θ := GlobalTheory.ThetaTie.thetaL T
  have hF : ∀ (a : ℤ) (y : P.R.BdR), y ∈ (P.PD K).Fil a ↔ y ∈ FilB P a := fun a y =>
    Set.ext_iff.1 (P.PD_Fil K (botExt l) a) y
  have hX1 : P.ιB x ∈ FilB P 1 := (hF 1 _).1 hx1
  have hX2 : P.ιB x ∉ FilB P 2 := fun h => hx2 ((hF 2 _).2 h)
  obtain ⟨s, hs, hts⟩ := GlobalTheory.ThetaTie.exists_inverse_fontaineElement_mem_fil_neg_one T
  have hb0 : s * P.ιB x ∈ FilB P 0 := by
    have := FilB_mul hs hX1
    simpa using this
  have hθb : Θ.θ (s * P.ιB x) ≠ 0 := by
    intro h0
    have h1 : s * P.ιB x ∈ FilB P 1 := (Θ.θ_ker _ hb0).1 h0
    apply hX2
    have := FilB_mul (tD_mem (P := P)) h1
    have e : tD P * (s * P.ιB x) = P.ιB x := by
      rw [← mul_assoc]
      change P.ιB P.tB * s * P.ιB x = P.ιB x
      rw [hts, one_mul]
    rw [e] at this
    simpa using this
  let cv : ↥(GK K) → Om l := fun g => (((c g : (↥(K0 K))ˣ) : ↥(K0 K)) : Om l)
  let χv : ↥(GK K) → Om l := fun g => algebraMap ℚ_[l] (Om l) (P.χQ (g : GQ l) : ℚ_[l])
  let uv : ↥(GK K) → Om l := fun g => cv g * (χv g)⁻¹
  have hK0 : ∀ z : ↥(K0 K), P.ιB (algebraMap ↥(K0 K) P.R.B z) = oB P (z : Om l) := fun z =>
    GlobalTheory.LocIota.ιB_algebraMap_Kur P (IntermediateField.inclusion (inf_le_right : K0 K ≤ MaximalUnramifiedExtension l) z)
  have hqo : ∀ z : ℚ_[l], qB P z = oB P (algebraMap ℚ_[l] (Om l) z) := fun z =>
    IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR z
  have hact : ∀ g : ↥(GK K), P.actQdR (g : GQ l) (s * P.ιB x) = oB P (uv g) * (s * P.ιB x) := by
    intro g
    have hX : P.actQdR (g : GQ l) (P.ιB x) = oB P (cv g) * P.ιB x := by
      rw [← ιB_act, hc g, map_mul, hK0]
    have ht := act_tD (P := P) (g : GQ l)
    have h1 : P.actQdR (g : GQ l) (tD P) * P.actQdR (g : GQ l) s = 1 := by
      rw [← map_mul]
      change P.actQdR (g : GQ l) (P.ιB P.tB * s) = 1
      rw [hts, map_one]
    have h2 : qB P ((P.χQ (g : GQ l) : ℚ_[l]))⁻¹ * qB P (P.χQ (g : GQ l) : ℚ_[l]) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ (Units.ne_zero _), map_one]
    have hts' : tD P * s = 1 := hts
    rw [ht] at h1
    have hs' : P.actQdR (g : GQ l) s = qB P ((P.χQ (g : GQ l) : ℚ_[l]))⁻¹ * s := by
      linear_combination (qB P ((P.χQ (g : GQ l) : ℚ_[l]))⁻¹ * s) * h1
        - P.actQdR (g : GQ l) s * h2
        - (P.actQdR (g : GQ l) s * qB P ((P.χQ (g : GQ l) : ℚ_[l]))⁻¹
            * qB P (P.χQ (g : GQ l) : ℚ_[l])) * hts'
    have hu : oB P (uv g) = oB P (cv g) * qB P ((P.χQ (g : GQ l) : ℚ_[l]))⁻¹ := by
      rw [hqo, map_inv₀]
      change oB P (cv g * (χv g)⁻¹) = _
      rw [map_mul]
    rw [map_mul, hs', hX, hu]
    ring
  have hl : ‖(l : ℚ_[l])‖ < 1 := Padic.norm_p_lt_one
  have hθpos : 0 < ‖Θ.θ (s * P.ιB x)‖ := norm_pos_iff.2 hθb
  have htv : Tendsto (fun g : ↥(GK K) => (g : GQ l)) (𝓝 1) (𝓝 1) := by
    simpa using continuous_subtype_val.tendsto (1 : ↥(GK K))
  have huv : Tendsto uv (𝓝 1) (𝓝 1) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (mul_pos hε hθpos) hl
    have hev := (bounded_and_eventually_sub_mem_Lat l P AI T _ hb0 1 n).2
    filter_upwards [htv.eventually hev] with g hg
    rw [hact g] at hg
    have e : oB P (uv g) * (s * P.ιB x) - s * P.ιB x = oB P (uv g - 1) * (s * P.ιB x) := by
      rw [map_sub, map_one]; ring
    rw [e] at hg
    have h3 := norm_th_le_of_mem_Lat Θ hg
    rw [Θ.θ_mul _ (oB_mem T _) _ hb0, Θ.θ_Om, norm_mul, PadicComplex.norm_extends] at h3
    rw [dist_eq_norm]
    have h4 : ‖uv g - 1‖ * ‖Θ.θ (s * P.ιB x)‖ < ε * ‖Θ.θ (s * P.ιB x)‖ := h3.trans_lt hn
    exact lt_of_mul_lt_mul_right h4 hθpos.le
  have hqc : Continuous (algebraMap ℚ_[l] (Om l)) :=
    (AddMonoidHomClass.isometry_of_norm (algebraMap ℚ_[l] (Om l))
      (fun z => PadicAlgCl.norm_extends (p := l) z)).continuous
  have hχ : Tendsto χv (𝓝 1) (𝓝 1) := by
    have hcont : Continuous χv :=
      hqc.comp ((GlobalTheory.Cyc.IsCyc.continuous P.χQ_cyc).comp continuous_subtype_val)
    simpa [χv] using hcont.tendsto 1
  have hcv1 : Tendsto cv (𝓝 1) (𝓝 1) := by
    have := huv.mul hχ
    rw [mul_one] at this
    refine this.congr fun g => ?_
    have hne : χv g ≠ 0 := by
      simp only [χv, ne_eq, map_eq_zero]
      exact Units.ne_zero _
    exact inv_mul_cancel_right₀ hne (cv g)
  have hmul : ∀ g h : ↥(GK K), cv (g * h) = cv g * cv h := by
    intro g h
    simp [cv, map_mul]
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  have t1 : Tendsto (fun g : ↥(GK K) => g₀⁻¹ * g) (𝓝 g₀) (𝓝 1) := by
    simpa using (continuous_const_mul g₀⁻¹).tendsto g₀
  have t2 := (hcv1.comp t1).const_mul (cv g₀)
  rw [mul_one] at t2
  refine t2.congr fun g => ?_
  change cv g₀ * cv (g₀⁻¹ * g) = cv g
  rw [← hmul, mul_inv_cancel_left]

end GlobalTheory.LtCharCont
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfTail
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.WeakClosed

theorem tailDecomp {O : Type} [CommRing O] {n : ℕ} (k : ℕ) (a : LetA O n) :
    a = (∑ j ∈ Finset.range k, fun i => PowerSeries.C (PowerSeries.coeff j (a i)) * PowerSeries.X ^ j) +
      (letπ : LetA O n) ^ k * (fun i => PowerSeries.mk fun m => PowerSeries.coeff (m + k) (a i)) := by
  funext i
  ext m
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Pi.add_apply, Finset.sum_apply, Pi.mul_apply, Pi.pow_apply, letπ, map_add (f := _), map_sum,
    PowerSeries.coeff_C_mul_X_pow, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_mk,
    Finset.sum_ite_eq, Finset.mem_range]
  by_cases hk : m < k
  · simp [hk, Nat.not_le.2 hk]
  · simp [hk, Nat.le_of_not_lt hk, Nat.sub_add_cancel (Nat.le_of_not_lt hk)]

theorem continuous_of_tail {O : Type} [CommRing O] [TopologicalSpace O] {n : ℕ} {M : Type}
    [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] (Φ : LetA O n →+ M)
    (hsmall : ∀ U ∈ 𝓝 (0 : M), ∃ k : ℕ, ∀ r : LetA O n, Φ (letπ ^ k * r) ∈ U)
    (hmono : ∀ j : ℕ, Continuous fun c : ZMod n → O => Φ (fun i => PowerSeries.C (c i) * PowerSeries.X ^ j)) :
    Continuous Φ := by
  rw [continuous_iff_continuousAt]
  intro a₀
  rw [ContinuousAt, ← tendsto_sub_nhds_zero_iff]
  intro U hU
  obtain ⟨V, hV, hVV⟩ := exists_nhds_zero_half hU
  obtain ⟨k, hk⟩ := hsmall V hV
  let mono : ℕ → LetA O n → M := fun j a =>
    Φ (fun i => PowerSeries.C (PowerSeries.coeff j (a i)) * PowerSeries.X ^ j)
  have hcont : ∀ j, Continuous (mono j) := fun j =>
    (hmono j).comp (continuous_pi fun i =>
      (PowerSeries.WithPiTopology.continuous_coeff O j).comp (continuous_apply i))
  let S : LetA O n → M := fun a => ∑ j ∈ Finset.range k, (mono j a - mono j a₀)
  have hS : Continuous S := continuous_finsetSum _ fun j _ => (hcont j).sub continuous_const
  have hS0 : S a₀ = 0 := by simp [S]
  have hSV : ∀ᶠ a in 𝓝 a₀, S a ∈ V := by
    have := hS.continuousAt (x := a₀)
    rw [ContinuousAt, hS0] at this
    exact this hV
  rw [Filter.mem_map]
  filter_upwards [hSV] with a ha
  let tl : LetA O n → LetA O n := fun b i => PowerSeries.mk fun m => PowerSeries.coeff (m + k) (b i)
  have hΦ : ∀ b, Φ b = (∑ j ∈ Finset.range k, mono j b) + Φ (letπ ^ k * tl b) := by
    intro b
    conv_lhs => rw [tailDecomp k b]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_add (f := _), map_sum]
  have : Φ a - Φ a₀ = S a + Φ (letπ ^ k * (tl a - tl a₀)) := by
    rw [hΦ a, hΦ a₀, mul_sub, map_sub]
    simp only [S, Finset.sum_sub_distrib]
    abel
  show Φ a - Φ a₀ ∈ U
  rw [this]
  exact hVV _ ha _ (hk _)

end GlobalTheory.WeakClosed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTowerFixesEpsilonRootsResGammaTrivialStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomicTower_fixes_epsilonRoots_resGamma_trivial : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l), (∀ g ∈ Hinf K, ∀ j : ℕ, AI.actT g (AI.εroot j) = AI.εroot j) ∧ ∀ (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (W : Wach P K LL), ∀ g ∈ Hinf K, ∃ hg : g ∈ GK K, W.resΓ ⟨g, hg⟩ = 1 := by
  first | exact @GlobalTheory.Decompl.hinf_fixes_εroot_and_resΓ_eq_one | exact GlobalTheory.Decompl.hinf_fixes_εroot_and_resΓ_eq_one | (intros; apply GlobalTheory.Decompl.hinf_fixes_εroot_and_resΓ_eq_one <;> assumption)
end

