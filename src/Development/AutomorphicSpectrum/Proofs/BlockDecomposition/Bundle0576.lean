module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0236
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLtOneOfEq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0468
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0514
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0544
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0519
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0551
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0529
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0537
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionCardLeAbsNormPow
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0543
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0530
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0546
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0528
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0553
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerResidueCongruence
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt

namespace GlobalTheory.CompanionTheory.LTPer.Tilt

variable {l : ℕ} [Fact l.Prime]

theorem norm_pow_sub_pow_le {a b : ℂ_[l]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (n : ℕ) :
    ‖a ^ n - b ^ n‖ ≤ ‖a - b‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : a ^ (n + 1) - b ^ (n + 1) = a ^ n * (a - b) + (a ^ n - b ^ n) * b := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha)
    · rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) hb).trans ih

theorem norm_pow_prime_sub_le {a b : ℂ_[l]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) {s : ℝ}
    (hl : ‖(l : ℂ_[l])‖ ≤ s) (hs : ‖a - b‖ ≤ s) : ‖a ^ l - b ^ l‖ ≤ s * ‖a - b‖ := by
  have hs0 : 0 ≤ s := (norm_nonneg _).trans hl
  have hbp : ∀ n : ℕ, ‖b ^ n‖ ≤ 1 := fun n => by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hb
  have hap : ∀ n : ℕ, ‖a ^ n‖ ≤ 1 := fun n => by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha
  have e : a ^ l - b ^ l = (∑ i ∈ Finset.range l, a ^ i * b ^ (l - 1 - i)) * (a - b) :=
    (geom_sum₂_mul a b l).symm
  have e2 : (∑ i ∈ Finset.range l, a ^ i * b ^ (l - 1 - i))
      = (∑ i ∈ Finset.range l, (a ^ i * b ^ (l - 1 - i) - b ^ (l - 1))) + (l : ℂ_[l]) * b ^ (l - 1) := by
    simp [Finset.sum_sub_distrib]
  have h1 : ‖∑ i ∈ Finset.range l, (a ^ i * b ^ (l - 1 - i) - b ^ (l - 1))‖ ≤ s := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hs0 fun i hi => ?_
    have hi' : i ≤ l - 1 := by
      have := Finset.mem_range.1 hi
      omega
    have e3 : a ^ i * b ^ (l - 1 - i) - b ^ (l - 1) = (a ^ i - b ^ i) * b ^ (l - 1 - i) := by
      rw [sub_mul, ← pow_add, Nat.add_sub_cancel' hi']
    rw [e3, norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (hbp _)).trans
      ((norm_pow_sub_pow_le ha hb i).trans hs)
  have h2 : ‖(l : ℂ_[l]) * b ^ (l - 1)‖ ≤ s := by
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (hbp _)).trans hl
  rw [e, norm_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  rw [e2]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)

theorem norm_pow_prime_pow_sub_le {a b : ℂ_[l]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) {s : ℝ}
    (hs1 : s ≤ 1) (hl : ‖(l : ℂ_[l])‖ ≤ s) (hs : ‖a - b‖ ≤ s) (n : ℕ) :
    ‖a ^ l ^ n - b ^ l ^ n‖ ≤ s ^ n * ‖a - b‖ := by
  have hs0 : 0 ≤ s := (norm_nonneg _).trans hl
  induction n with
  | zero => simp
  | succ n ih =>
    have ha' : ‖a ^ l ^ n‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha
    have hb' : ‖b ^ l ^ n‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hb
    have hle : ‖a ^ l ^ n - b ^ l ^ n‖ ≤ s :=
      ih.trans ((mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hs0 hs1)).trans hs)
    have h := norm_pow_prime_sub_le ha' hb' hl hle
    rw [← pow_mul, ← pow_mul, ← pow_succ] at h
    refine h.trans ?_
    rw [pow_succ, mul_comm (s ^ n) s, mul_assoc]
    exact mul_le_mul_of_nonneg_left ih hs0

theorem isClosed_range_finExt (K : FinExt l) :
    IsClosed (Set.range fun y : ↥K.1 => omC (l := l) (y : Om l)) := by
  haveI := K.2
  let L : ↥K.1 →ₗ[ℚ_[l]] ℂ_[l] :=
    (IsScalarTower.toAlgHom ℚ_[l] (Om l) ℂ_[l]).toLinearMap ∘ₗ K.1.val.toLinearMap
  have h := Submodule.closed_of_finiteDimensional (LinearMap.range L)
  have e : (Set.range fun y : ↥K.1 => omC (l := l) (y : Om l)) = (LinearMap.range L : Set ℂ_[l]) := by
    ext z
    rfl
  rw [e]
  exact h

theorem exists_int_of_norm_le (K : FinExt l) (y : ↥K.1) (hy : ‖(y : Om l)‖ ≤ 1) :
    ∃ c : ↥(OL K), (c : ↥K.1) = y :=
  ⟨(GlobalTheory.CompanionTheory.LTHodge.CharEx.intEquiv K).symm
    ⟨y, (GlobalTheory.CompanionTheory.LTHodge.CharEx.mem_integer_iff K y).2 hy⟩, rfl⟩

theorem sh_root_near_integer : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)) (f : ℕ), 0 < f → qOf π = l ^ f →
    ‖(l : ℂ_[l])‖ ≤ ‖oc K π‖ → ‖oc K π‖ < 1 → π ≠ 0 → ∀ (x : Tl l) (c : ↥(OL K)), x ^ l ^ f = x →
    ‖sh x - oc K c‖ ≤ ‖oc K π‖ → ∃ c' : ↥(OL K), sh x = oc K (c + π * c') := by
  intro l _ K π f hf _ hl hπ1 hπ0 x c hx hc
  set s := ‖oc K π‖ with hsdef
  have hs0 : 0 ≤ s := norm_nonneg _
  have hζ1 : ‖sh x‖ ≤ 1 := norm_sh_le_one x
  have hc1 : ‖oc K c‖ ≤ 1 := norm_oc_le_one K c
  have hfix1 : sh x ^ l ^ f = sh x := by rw [← sh_pow, hx]
  have hfix : ∀ m : ℕ, sh x ^ (l ^ f) ^ m = sh x := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, pow_mul, ih, hfix1]
  have hdist : ‖oc K c - sh x‖ ≤ s := by rw [norm_sub_rev]; exact hc
  have hbound : ∀ m : ℕ, ‖oc K (c ^ (l ^ f) ^ m) - sh x‖ ≤ s ^ m := by
    intro m
    have h := norm_pow_prime_pow_sub_le hc1 hζ1 hπ1.le hl hdist (f * m)
    rw [pow_mul, hfix m, ← map_pow] at h
    refine h.trans ?_
    have h1 : s ^ (f * m) ≤ s ^ m :=
      pow_le_pow_of_le_one hs0 hπ1.le (Nat.le_mul_of_pos_left m hf)
    exact (mul_le_of_le_one_right (pow_nonneg hs0 _) (hdist.trans hπ1.le)).trans h1
  have hlim : Filter.Tendsto (fun m : ℕ => oc K (c ^ (l ^ f) ^ m)) Filter.atTop (nhds (sh x)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) hbound
      (tendsto_pow_atTop_nhds_zero_of_lt_one hs0 hπ1)
  have hmem : sh x ∈ Set.range fun y : ↥K.1 => omC (l := l) (y : Om l) :=
    (isClosed_range_finExt K).mem_of_tendsto hlim
      (Filter.Eventually.of_forall fun m => ⟨((c ^ (l ^ f) ^ m : ↥(OL K)) : ↥K.1), rfl⟩)
  obtain ⟨y, hy⟩ := hmem
  have hy : omC (l := l) (y : Om l) = sh x := hy
  have hcK : oc K c = omC (l := l) ((c : ↥K.1) : Om l) := rfl
  have hπK : oc K π = omC (l := l) ((π : ↥K.1) : Om l) := rfl
  have hπ0' : (π : ↥K.1) ≠ 0 := fun h => hπ0 (Subtype.ext h)
  have hπ0'' : ((π : ↥K.1) : Om l) ≠ 0 := fun h => hπ0' (Subtype.ext h)
  have hnum : ‖((y - (c : ↥K.1) : ↥K.1) : Om l)‖ ≤ ‖((π : ↥K.1) : Om l)‖ := by
    have : ‖sh x - oc K c‖ = ‖((y - (c : ↥K.1) : ↥K.1) : Om l)‖ := by
      rw [← hy, hcK, ← map_sub, norm_omC]
      rfl
    rw [← this, ← norm_omC, ← hπK]
    exact hc
  have hq : ‖(((y - (c : ↥K.1)) / (π : ↥K.1) : ↥K.1) : Om l)‖ ≤ 1 := by
    have e : (((y - (c : ↥K.1)) / (π : ↥K.1) : ↥K.1) : Om l)
        = ((y - (c : ↥K.1) : ↥K.1) : Om l) / ((π : ↥K.1) : Om l) := rfl
    rw [e, norm_div]
    exact div_le_one_of_le₀ hnum (norm_nonneg _)
  obtain ⟨c', hc'⟩ := exists_int_of_norm_le K _ hq
  refine ⟨c', ?_⟩
  have hsum : ((c + π * c' : ↥(OL K)) : ↥K.1) = y := by
    have : ((c + π * c' : ↥(OL K)) : ↥K.1) = (c : ↥K.1) + (π : ↥K.1) * (c' : ↥K.1) := rfl
    rw [this, hc']
    field_simp
    ring
  rw [← hy]
  show _ = omC (l := l) (((c + π * c' : ↥(OL K)) : ↥K.1) : Om l)
  rw [hsum]

end GlobalTheory.CompanionTheory.LTPer.Tilt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionNormZetaBound
section
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS

theorem summable_absNorm_rpow_neg (K : Type) [Field K] [NumberField K] {r : ℝ} (hr : 1 < r) :
    Summable (fun I : Ideal (𝓞 K) => (Ideal.absNorm I : ℝ) ^ (-r)) := by
  have h := (GlobalTheory.Mem.summable_norm_absNorm_cpow K (s := (r : ℂ)) (by simpa using hr))
  refine h.congr fun I => ?_
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_neg, ← Complex.ofReal_cpow (Nat.cast_nonneg _),
    Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]

theorem sum_torsion_le (K : Type) [Field K] [NumberField K] (m : ℕ)
    (L : Submodule (𝓞 K) (Fin m → K)) (hL : IsLat L) {r : ℝ} (hr : 1 < r)
    (S : Finset ((Fin m → K) ⧸ L)) :
    ∑ x ∈ S, (Ideal.absNorm (Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ L) x) : ℝ) ^ (-((m : ℝ) + r))
      ≤ zetaR K r := by
  classical
  set τ : (Fin m → K) ⧸ L → Ideal (𝓞 K) := fun x => Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ L) x
    with hτ
  have hg := summable_absNorm_rpow_neg K hr
  have hfib : ∀ 𝔞 ∈ S.image τ,
      ∑ x ∈ S.filter (fun x => τ x = 𝔞), (Ideal.absNorm (τ x) : ℝ) ^ (-((m : ℝ) + r))
        ≤ (Ideal.absNorm 𝔞 : ℝ) ^ (-r) := by
    intro 𝔞 h𝔞
    obtain ⟨x₀, -, rfl⟩ := Finset.mem_image.mp h𝔞
    have hne : τ x₀ ≠ ⊥ := _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.torsionOf_quot_lat_ne_bot K m L hL x₀
    obtain ⟨hfin, hcard⟩ := _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.TorCard.tor_card K m L hL (τ x₀) hne
    have hN : (0 : ℝ) < (Ideal.absNorm (τ x₀) : ℝ) := by
      have : Ideal.absNorm (τ x₀) ≠ 0 := fun h => hne (Ideal.absNorm_eq_zero_iff.mp h)
      exact_mod_cast Nat.pos_of_ne_zero this
    have hc : ((S.filter (fun x => τ x = τ x₀)).card : ℝ) ≤ (Ideal.absNorm (τ x₀) : ℝ) ^ m := by
      have hinj : (S.filter (fun x => τ x = τ x₀)).card ≤
          Nat.card {x : (Fin m → K) ⧸ L // ∀ a ∈ τ x₀, a • x = 0} := by
        haveI := Fintype.ofFinite {x : (Fin m → K) ⧸ L // ∀ a ∈ τ x₀, a • x = 0}
        rw [Nat.card_eq_fintype_card, ← Fintype.card_coe]
        refine Fintype.card_le_of_injective (fun x => ⟨x.1, fun a ha => ?_⟩) (fun x y h => ?_)
        · have hx := (Finset.mem_filter.mp x.2).2
          rw [← hx] at ha
          exact (Ideal.mem_torsionOf_iff _ _).mp ha
        · have h' : (x : (Fin m → K) ⧸ L) = y :=
            congrArg (fun z : {x : (Fin m → K) ⧸ L // ∀ a ∈ τ x₀, a • x = 0} => z.1) h
          exact Subtype.ext h'
      exact_mod_cast hinj.trans hcard
    have hsum : ∑ x ∈ S.filter (fun x => τ x = τ x₀), (Ideal.absNorm (τ x) : ℝ) ^ (-((m : ℝ) + r))
        = ((S.filter (fun x => τ x = τ x₀)).card : ℝ) *
          (Ideal.absNorm (τ x₀) : ℝ) ^ (-((m : ℝ) + r)) := by
      rw [Finset.sum_congr rfl (g := fun _ => (Ideal.absNorm (τ x₀) : ℝ) ^ (-((m : ℝ) + r)))
        (fun x hx => by rw [(Finset.mem_filter.mp hx).2])]
      simp
    rw [hsum]
    calc _ ≤ (Ideal.absNorm (τ x₀) : ℝ) ^ m * (Ideal.absNorm (τ x₀) : ℝ) ^ (-((m : ℝ) + r)) :=
          mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hN.le _)
      _ = (Ideal.absNorm (τ x₀) : ℝ) ^ (-r) := by
          rw [← Real.rpow_natCast, ← Real.rpow_add hN]
          congr 1
          ring
  calc ∑ x ∈ S, (Ideal.absNorm (τ x) : ℝ) ^ (-((m : ℝ) + r))
      = ∑ 𝔞 ∈ S.image τ, ∑ x ∈ S.filter (fun x => τ x = 𝔞),
          (Ideal.absNorm (τ x) : ℝ) ^ (-((m : ℝ) + r)) :=
        (Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem τ hx) _).symm
    _ ≤ ∑ 𝔞 ∈ S.image τ, (Ideal.absNorm 𝔞 : ℝ) ^ (-r) := Finset.sum_le_sum hfib
    _ ≤ zetaR K r :=
        hg.sum_le_tsum _ (fun I _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem sum_torsion (K : Type) [Field K] [NumberField K] (m : ℕ)
    (L : Submodule (𝓞 K) (Fin m → K)) (hL : IsLat L) (r : ℝ) (hr : 1 < r) :
    Summable (fun x : (Fin m → K) ⧸ L =>
      (Ideal.absNorm (Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ L) x) : ℝ) ^ (-((m : ℝ) + r))) ∧
    ∑' x : (Fin m → K) ⧸ L,
      (Ideal.absNorm (Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ L) x) : ℝ) ^ (-((m : ℝ) + r))
        ≤ zetaR K r := by
  have hnn : ∀ x : (Fin m → K) ⧸ L,
      0 ≤ (Ideal.absNorm (Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ L) x) : ℝ) ^ (-((m : ℝ) + r)) :=
    fun x => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hs := summable_of_sum_le hnn (sum_torsion_le K m L hL hr)
  exact ⟨hs, hs.tsum_le_of_sum_le (sum_torsion_le K m L hL hr)⟩

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionOrthogonalityIntegralSolution
section
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DualCover

variable {E : Type} [Field E] [NumberField E]

def kcSub {m : ℕ} (c : Matrix (Fin m) (Fin m) E) : Submodule (𝓞 E) (Fin m → 𝓞 E) where
  carrier := (Kc c : Set (Fin m → 𝓞 E))
  add_mem' := fun hx hy => (Kc c).add_mem hx hy
  zero_mem' := (Kc c).zero_mem
  smul_mem' := by
    intro r y hy i
    obtain ⟨o, ho⟩ := hy i
    refine ⟨r * o, ?_⟩
    have h : (fun j => algebraMap (𝓞 E) E ((r • y) j)) =
        (algebraMap (𝓞 E) E r) • fun j => algebraMap (𝓞 E) E (y j) := by
      funext j
      simp
    rw [h, Matrix.mulVec_smul, Pi.smul_apply, ← ho, map_mul, smul_eq_mul]

def pair {m : ℕ} (w : Fin m → E) : (Fin m → 𝓞 E) →ₗ[𝓞 E] E where
  toFun y := ∑ j, w j * (y j : E)
  map_add' := by
    intro y z
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro r y
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    change w j * ((r * y j : 𝓞 E) : E) = r • (w j * (y j : E))
    rw [Algebra.smul_def]
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul]
    ring

def bMod {m : ℕ} (c : Matrix (Fin m) (Fin m) E) (w : Fin m → E) : Submodule (𝓞 E) E :=
  1 ⊔ (kcSub c).map (pair w)

theorem bMod_fg {m : ℕ} (c : Matrix (Fin m) (Fin m) E) (w : Fin m → E) : (bMod c w).FG := by
  refine Submodule.FG.sup ?_ (Submodule.FG.map _ (IsNoetherian.noetherian _))
  rw [Submodule.one_eq_span]
  exact Submodule.fg_span_singleton _

variable {F : Type} [Field F] [Algebra F E]

theorem sO_mem_tor (σ : E →ₐ[F] E) (hinv : ∀ x, σ (σ x) = x)
    (hsO : ∀ o : 𝓞 E, ((sO σ o : 𝓞 E) : E) = σ (o : E)) {m : ℕ}
    (c : Matrix (Fin m) (Fin m) E) (hc : ∀ a b, σ (c b a) = c a b) (u : Fin m → E) (a : 𝓞 E)
    (ha : ∀ y ∈ Kc c, (a : E) * ∑ j, σ (u j) * (y j : E) ∈ (1 : Submodule (𝓞 E) E)) :
    sO σ a ∈ tor c u := by
  have hmem : (sO σ a) • u ∈ lam c := by
    refine _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.LatticeDualityAlt.mem_of_dot_integral E m (lam c) (_root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.isLat_lam_of_matrix E m c) _ ?_
    intro a' hL

    have hstd : ∀ j, (Pi.single j (1 : E) : Fin m → E) ∈ intVec E m := by
      intro j i
      by_cases h : i = j
      · subst h
        exact ⟨1, by simp⟩
      · exact ⟨0, by simp [Pi.single_apply, h]⟩
    have hent : ∀ j, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = a' j := by
      intro j
      have h1 := hL _ (Submodule.mem_sup_left (hstd j) : _ ∈ lam c)
      rw [Submodule.mem_one] at h1
      obtain ⟨o, ho⟩ := h1
      exact ⟨o, by rw [ho]; simp⟩
    choose o ho using hent
    have hcol : ∀ i, ∃ p : 𝓞 E, algebraMap (𝓞 E) E p = ∑ j, a' j * c j i := by
      intro i
      have hx : c *ᵥ (Pi.single i (1 : E) : Fin m → E) ∈ lam c :=
        Submodule.mem_sup_right (Submodule.mem_map_of_mem (f := c.mulVecLin.restrictScalars (𝓞 E)) (hstd i))
      have h1 := hL _ hx
      rw [Submodule.mem_one] at h1
      obtain ⟨p, hp⟩ := h1
      refine ⟨p, ?_⟩
      rw [hp]
      simp [dotProduct, Matrix.mulVec_single_one, Matrix.col_apply]
    have hy : (fun j => sO σ (o j)) ∈ Kc c := by
      intro i
      obtain ⟨p, hp⟩ := hcol i
      refine ⟨sO σ p, ?_⟩
      have e1 : algebraMap (𝓞 E) E (sO σ p) = σ (algebraMap (𝓞 E) E p) := hsO p
      set_option synthInstance.maxHeartbeats 100000 in
        rw [e1, hp, map_sum]
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun j _ => ?_
      have e2 : algebraMap (𝓞 E) E (sO σ (o j)) = σ (a' j) := by
        rw [← ho j]; exact hsO (o j)
      rw [e2, map_mul, hc i j, mul_comm]
    have h2 := ha _ hy
    rw [Submodule.mem_one] at h2 ⊢
    obtain ⟨q, hq⟩ := h2
    refine ⟨sO σ q, ?_⟩
    have e1 : algebraMap (𝓞 E) E (sO σ q) = σ (algebraMap (𝓞 E) E q) := hsO q
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e1, hq, map_mul, map_sum]
    simp only [dotProduct, Finset.mul_sum, Pi.smul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e3 : ((sO σ (o j) : 𝓞 E) : E) = σ (a' j) := by
      rw [hsO, ← ho j]
    simp only [e3, map_mul, hinv, Algebra.smul_def]
    have e4 : algebraMap (𝓞 E) E (sO σ a) = σ (a : E) := hsO a
    rw [e4]
    ring
  rw [tor, Ideal.mem_torsionOf_iff, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact hmem

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DualCover


open GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DualCover in
theorem GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.dual_cover : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (m : ℕ) (c : Matrix (Fin m) (Fin m) E), (∀ a b, σ (c b a) = c a b) → ∀ (u : Fin m → E) (b : E), (∀ t ∈ tor c u, σ (t : E) * b ∈ (1 : Submodule (𝓞 E) E)) → ∃ y : Fin m → 𝓞 E, y ∈ Kc c ∧ b - ∑ j, σ (u j) * (y j : E) ∈ (1 : Submodule (𝓞 E) E) := by
  open GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DualCover in
  intro F E _ _ _ _ _ σ hcm m c hc u b hb
  obtain ⟨hinv, -, hsO, -⟩ := _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.isCMExt_conj_fixed_integers F E σ hcm
  set w : Fin m → E := fun j => σ (u j) with hw
  let B : FractionalIdeal (nonZeroDivisors (𝓞 E)) E :=
    ⟨bMod c w, FractionalIdeal.isFractional_of_fg (bMod_fg c w)⟩
  have hB1 : (1 : E) ∈ B := by
    change (1 : E) ∈ bMod c w
    exact Submodule.mem_sup_left (Submodule.one_le.mp le_rfl)
  have hB0 : B ≠ 0 := by
    intro h
    rw [h, FractionalIdeal.mem_zero_iff] at hB1
    exact one_ne_zero hB1
  have hBi : B⁻¹ ≠ 0 := inv_ne_zero hB0
  have hbB : b ∈ B := by
    have hbi : b ∈ (B⁻¹)⁻¹ := by
      rw [FractionalIdeal.mem_inv_iff hBi]
      intro x hx
      rw [FractionalIdeal.mem_inv_iff hB0] at hx
      have hx1 := hx 1 hB1
      rw [mul_one, FractionalIdeal.mem_one_iff] at hx1
      obtain ⟨a, rfl⟩ := hx1
      have ht : sO σ a ∈ tor c u := by
        refine sO_mem_tor σ hinv hsO c hc u a ?_
        intro y hy
        have hyB : ∑ j, σ (u j) * (y j : E) ∈ B := by
          change _ ∈ bMod c w
          exact Submodule.mem_sup_right (Submodule.mem_map_of_mem (f := pair w) (show y ∈ kcSub c from hy))
        have := hx _ hyB
        rw [FractionalIdeal.mem_one_iff] at this
        obtain ⟨q, hq⟩ := this
        rw [Submodule.mem_one]
        exact ⟨q, hq⟩
      have h := hb _ ht
      rw [hsO, hinv] at h
      rw [Submodule.mem_one] at h
      obtain ⟨q, hq⟩ := h
      rw [FractionalIdeal.mem_one_iff]
      refine ⟨q, ?_⟩
      rw [mul_comm]
      exact hq
    rwa [inv_inv] at hbi
  have hbB' : b ∈ bMod c w := hbB
  obtain ⟨p, hp, z, hz, hpz⟩ := Submodule.mem_sup.mp hbB'
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hz
  refine ⟨y, hy, ?_⟩
  have : b - ∑ j, σ (u j) * (y j : E) = p := by
    rw [← hpz]
    change p + ∑ j, σ (u j) * (y j : E) - _ = p
    ring
  rw [this]
  exact hp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WordOccursIrreducibleSubquotientStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.word_occurs_irreducible_subquotient : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), ∀ {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → HasFiniteLength π → ∀ w : List (IrrGL (k := k)), Wd π w → ∃ τ : IrrRep (GL (Fin N) k), IsSubquotient τ.ρ π ∧ Wd τ.ρ w := by
  first | exact @GlobalTheory.CompanionTheory.WordIrr.exists_irrRep_wd | exact GlobalTheory.CompanionTheory.WordIrr.exists_irrRep_wd | (intros; apply GlobalTheory.CompanionTheory.WordIrr.exists_irrRep_wd <;> assumption)
end

