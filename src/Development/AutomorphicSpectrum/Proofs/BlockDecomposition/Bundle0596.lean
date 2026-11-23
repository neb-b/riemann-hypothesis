module

public import Mathlib
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0576
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0557
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0558
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0591
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.PullHEq
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HdgAffIso
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlockLowerBoundTorsion
section
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.LocalBound

section
variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem blk_mulVec_castSucc {m : ℕ} (σ : E →ₐ[F] E) (c : Matrix (Fin m) (Fin m) E)
    (u : Fin m → E) (d : E) (y : Fin m → E) (s : E) (a : Fin m) :
    (blk σ c u d *ᵥ (Fin.snoc (α := fun _ => E) y s)) a.castSucc = (c *ᵥ y) a + u a * s := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, blk]

theorem blk_mulVec_last {m : ℕ} (σ : E →ₐ[F] E) (c : Matrix (Fin m) (Fin m) E)
    (u : Fin m → E) (d : E) (y : Fin m → E) (s : E) :
    (blk σ c u d *ᵥ (Fin.snoc (α := fun _ => E) y s)) (Fin.last m) =
      ∑ j, σ (u j) * y j + d * s := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, blk]

variable [NumberField E]

theorem mem_lastFib_blk {m : ℕ} (σ : E →ₐ[F] E) (c : Matrix (Fin m) (Fin m) E)
    (u : Fin m → E) (d : E) (y l : Fin m → 𝓞 E) (s : 𝓞 E)
    (h : ∀ a, (c *ᵥ fun j => algebraMap (𝓞 E) E (y j)) a + u a * algebraMap (𝓞 E) E s =
      algebraMap (𝓞 E) E (l a)) :
    (∑ j, σ (u j) * algebraMap (𝓞 E) E (y j) + d * algebraMap (𝓞 E) E s) ∈
      lastFib (blk σ c u d) := by
  have hvI : (Fin.snoc (α := fun _ => E) (fun j => algebraMap (𝓞 E) E (y j))
      (algebraMap (𝓞 E) E s) : Fin (m + 1) → E) ∈ intVec E (m + 1) := by
    intro i
    refine Fin.lastCases ?_ (fun a => ?_) i
    · exact ⟨s, by simp⟩
    · exact ⟨y a, by simp⟩
  have h1 := Submodule.mem_sup_right (S := intVec E (m + 1))
    (Submodule.mem_map_of_mem (f := (blk σ c u d).mulVecLin.restrictScalars (𝓞 E)) hvI)
  have h2 : (Fin.snoc (α := fun _ => E) (fun j => algebraMap (𝓞 E) E (l j)) 0 :
      Fin (m + 1) → E) ∈ lam (blk σ c u d) := by
    refine Submodule.mem_sup_left ?_
    intro i
    refine Fin.lastCases ?_ (fun a => ?_) i
    · exact ⟨0, by simp⟩
    · exact ⟨l a, by simp⟩
  have h3 := (lam (blk σ c u d)).sub_mem h1 h2
  show LinearMap.single (𝓞 E) (fun _ : Fin (m + 1) => E) (Fin.last m) _ ∈ lam (blk σ c u d)
  convert h3 using 1
  ext i
  refine Fin.lastCases ?_ (fun a => ?_) i
  · simp [blk_mulVec_last]
  · have hne : a.castSucc ≠ Fin.last m := Fin.castSucc_ne_last a
    simp [blk_mulVec_castSucc, h a, hne]

theorem one_le_lastFib {m : ℕ} (C : Matrix (Fin (m + 1)) (Fin (m + 1)) E) :
    (1 : Submodule (𝓞 E) E) ≤ lastFib C := by
  intro x hx
  obtain ⟨o, rfl⟩ := Submodule.mem_one.1 hx
  refine Submodule.mem_sup_left (show _ ∈ intVec E (m + 1) from ?_)
  intro i
  by_cases hi : i = Fin.last m
  · subst hi
    exact ⟨o, by simp⟩
  · exact ⟨0, by simp [hi]⟩

theorem lastFib_fg {m : ℕ} (C : Matrix (Fin (m + 1)) (Fin (m + 1)) E) :
    (lastFib C).FG := by
  have hfg : (lam C).FG := (_root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.isLat_lam_of_matrix E (m + 1) C).1
  have hmap : ((lastFib C).map
      (LinearMap.single (𝓞 E) (fun _ : Fin (m + 1) => E) (Fin.last m))).FG :=
    Submodule.FG.of_le hfg (Submodule.map_comap_le _ _)
  exact Submodule.fg_of_fg_map_injective (LinearMap.single (𝓞 E) (fun _ : Fin (m + 1) => E) (Fin.last m))
    (fun a b h => by simpa using congrFun h (Fin.last m)) hmap

theorem tor_decomp {m : ℕ} (c : Matrix (Fin m) (Fin m) E) (u : Fin m → E) (t : 𝓞 E)
    (ht : t ∈ tor c u) :
    ∃ yo lo : Fin m → 𝓞 E, ∀ a, (c *ᵥ fun j => algebraMap (𝓞 E) E (yo j)) a +
      u a * algebraMap (𝓞 E) E t = algebraMap (𝓞 E) E (lo a) := by
  have h : t • u ∈ lam c := by
    have h0 := (Ideal.mem_torsionOf_iff _ _).1 ht
    rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h0
  obtain ⟨l, hl, z, ⟨y, hy, rfl⟩, hz⟩ := Submodule.mem_sup.1 h
  choose lo hlo using hl
  choose yo hyo using hy
  refine ⟨-yo, lo, fun a => ?_⟩
  have h1 := congrFun hz a
  have hy' : (fun j => algebraMap (𝓞 E) E ((-yo) j)) = -y := by
    funext j
    simp [hyo j]
  rw [hy', Matrix.mulVec_neg, hlo a]
  simp only [LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply, Pi.add_apply, Pi.smul_apply,
    Algebra.smul_def] at h1
  simp only [Pi.neg_apply]
  linear_combination -h1
end

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.LocalBound

open GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS

set_option maxHeartbeats 1000000 in
theorem GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.LocalBound.local_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (m : ℕ) (c : Matrix (Fin m) (Fin m) E), (∀ a b, σ (c b a) = c a b) → ∀ (u : Fin m → E) (t : 𝓞 E), t ∈ tor c u → t ≠ 0 → ∃ f : F, ∀ d : F, delta c * Ideal.absNorm (tor c u) ^ 2 * Ideal.absNorm (den F (f + ((RingOfIntegers.norm F t : 𝓞 F) : F) * d)) ^ 2 ≤ delta (blk σ c u (algebraMap F E d)) := by
  intro F E _ _ _ _ _ σ hCM m c hc u t ht ht0
  obtain ⟨hinv, hfix, hsO, hN⟩ := _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.isCMExt_conj_fixed_integers F E σ hCM
  obtain ⟨yo, lo, hyl⟩ := LocalBound.tor_decomp c u t ht
  have hf0 : σ (-∑ j, σ ((c *ᵥ fun j => algebraMap (𝓞 E) E (yo j)) j) * algebraMap (𝓞 E) E (yo j)) =
      -∑ j, σ ((c *ᵥ fun j => algebraMap (𝓞 E) E (yo j)) j) * algebraMap (𝓞 E) E (yo j) := by
    have hs : ∑ j, σ ((c *ᵥ fun j => algebraMap (𝓞 E) E (yo j)) j) * algebraMap (𝓞 E) E (yo j) =
        ∑ j, (c *ᵥ fun j => algebraMap (𝓞 E) E (yo j)) j * σ (algebraMap (𝓞 E) E (yo j)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      rw [hc]
      ring
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_neg, map_sum]
    simp only [map_mul, hinv]
    rw [hs]
  obtain ⟨f, hf⟩ := hfix _ hf0
  refine ⟨f, fun d => ?_⟩
  have hT : tor c u ≠ ⊥ := fun h => ht0 (by simpa [h] using ht)
  have hsOt : sO σ t ≠ 0 := by
    intro h0
    apply ht0
    have h1 : σ (algebraMap (𝓞 E) E t) = 0 := by
      have := hsO t
      rw [h0] at this
      simpa using this.symm
    have h2 : algebraMap (𝓞 E) E t = 0 := by
      rw [← hinv (algebraMap (𝓞 E) E t), h1, map_zero]
    exact (map_eq_zero_iff _ (RingOfIntegers.coe_injective)).1 h2
  have hmem : ∀ t' ∈ tor c u, sO σ t' ∈ (tor c u).map (sO σ) :=
    fun t' h' => Ideal.mem_map_of_mem _ h'
  have h𝔱 : (tor c u).map (sO σ) ≠ ⊥ := by
    intro h0
    have := hmem t ht
    rw [h0] at this
    exact hsOt (by simpa using this)
  have hw := LocalBound.mem_lastFib_blk σ c u (algebraMap F E d) yo lo t hyl
  have hinvb : ∀ b : E, (∀ a ∈ (tor c u).map (sO σ), (a : E) * b ∈ (1 : Submodule (𝓞 E) E)) →
      b ∈ lastFib (blk σ c u (algebraMap F E d)) := by
    intro b hb
    obtain ⟨y, hy, hby⟩ := _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.dual_cover F E σ hCM m c hc u b (fun t' h' => by
      have := hb _ (hmem t' h')
      rwa [show ((sO σ t' : 𝓞 E) : E) = σ (t' : E) from hsO t'] at this)
    choose lo' hlo' using hy
    have h1 := LocalBound.mem_lastFib_blk σ c u (algebraMap F E d) y lo' 0 (fun a => by
      rw [hlo' a]
      simp)
    have h2 := LocalBound.one_le_lastFib (blk σ c u (algebraMap F E d)) hby
    have h3 := Submodule.add_mem _ h1 h2
    have h4 : (∑ j, σ (u j) * algebraMap (𝓞 E) E (y j) + algebraMap F E d * algebraMap (𝓞 E) E 0) +
        (b - ∑ j, σ (u j) * (y j : E)) = b := by
      simp only [map_zero, mul_zero, add_zero]
      exact add_sub_cancel _ _
    rwa [h4] at h3
  have hnorm := (_root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.NormSig.norm_eq_mul_conj_and_absNorm F E σ hCM t).1
  have hkey : ((sO σ t : 𝓞 E) : E) * (∑ j, σ (u j) * algebraMap (𝓞 E) E (yo j) +
      algebraMap F E d * algebraMap (𝓞 E) E t) -
      algebraMap F E (f + ((RingOfIntegers.norm F t : 𝓞 F) : F) * d) ∈ (1 : Submodule (𝓞 E) E) := by
    refine Submodule.mem_one.2 ⟨∑ j, sO σ (lo j) * yo j, ?_⟩
    have hsum : σ (algebraMap (𝓞 E) E t) * ∑ j, σ (u j) * algebraMap (𝓞 E) E (yo j) =
        ∑ j, σ (algebraMap (𝓞 E) E (lo j)) * algebraMap (𝓞 E) E (yo j) -
          ∑ j, σ ((c *ᵥ fun j => algebraMap (𝓞 E) E (yo j)) j) * algebraMap (𝓞 E) E (yo j) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hyl j, map_add (f := _), map_mul]
      ring
    have hs2 : algebraMap (𝓞 E) E (∑ j, sO σ (lo j) * yo j) =
        ∑ j, σ (algebraMap (𝓞 E) E (lo j)) * algebraMap (𝓞 E) E (yo j) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul]
      exact congrArg (· * _) (hsO (lo j))
    rw [hs2, show ((sO σ t : 𝓞 E) : E) = σ (algebraMap (𝓞 E) E t) from hsO t, map_add (f := _), map_mul,
      hf, hnorm]
    have hnorm' : (t : E) = algebraMap (𝓞 E) E t := rfl
    rw [hnorm']
    linear_combination -hsum
  have hmain := _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.IdxGe.absNorm_mul_den_le_idx E ((tor c u).map (sO σ)) h𝔱
    (lastFib (blk σ c u (algebraMap F E d))) (LocalBound.lastFib_fg _)
    (LocalBound.one_le_lastFib _) hinvb (sO σ t) _ _ (hmem t ht) hw hkey
  rw [hN, _root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.DenMap.absNorm_den_algebraMap F E hCM.2.2.1] at hmain
  rw [_root_.GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.IndexFormula.delta_blk F E σ m c u (algebraMap F E d)]
  calc delta c * Ideal.absNorm (tor c u) ^ 2 *
        Ideal.absNorm (den F (f + ((RingOfIntegers.norm F t : 𝓞 F) : F) * d)) ^ 2
      = delta c * Ideal.absNorm (tor c u) * (Ideal.absNorm (tor c u) *
        Ideal.absNorm (den F (f + ((RingOfIntegers.norm F t : 𝓞 F) : F) * d)) ^ 2) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hmain
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexClassSurjective
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

namespace GlobalTheory.CompanionTheory.CechSerre

theorem clsZ_mem_Ff_succ {R : Type} [CommRing R] (K : DCx.{w} R) {n p q : ℕ} (hpq : p + q = n)
    (hS : Subsingleton ((K.col p).H q)) (z : Zf K n p) : clsZ K n p z ∈ Ff K n (p + 1) := by
  have hv : (K.col p).d q (z.1.1.1 p q) = 0 := dv_lead K z.1.1.1 (D_zero K z.1) p q z.2
  have h1 : (K.col p).cls (z.1.1.1 p q) hv = 0 := Subsingleton.elim _ _
  rw [(P.cls_surj _ q).2.1] at h1
  obtain ⟨W, hW, hl⟩ := lower_vert K z.1.1.1 z.1.1.2 hpq z.2 0 0 (fun _ _ _ => rfl) (by simp)
    (by simpa using h1)
  exact lower K z W hW hl

theorem Ff_eq_top_of_acyclic {R : Type} [CommRing R] (K : DCx.{w} R) (a j : ℕ)
    (h : ∀ p q, a < q → Subsingleton ((K.col p).H q)) : ∀ p, p ≤ j → Ff K (a + j) p = ⊤ := by
  intro p
  induction p with
  | zero =>
    intro _
    refine (Submodule.eq_top_iff').2 fun x => ?_
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ x
    exact ⟨⟨z, fun p q hp => absurd hp (Nat.not_lt_zero p)⟩, rfl⟩
  | succ p ih =>
    intro hp
    refine (Submodule.eq_top_iff').2 fun x => ?_
    have hx : x ∈ Ff K (a + j) p := by rw [ih (by omega)]; exact Submodule.mem_top
    obtain ⟨z, rfl⟩ := hx
    exact clsZ_mem_Ff_succ K (q := a + j - p) (by omega) (h p _ (by omega)) z

theorem clsZ_surjective_of_acyclic : ∀ {R : Type} [CommRing R] (K : DCx.{w} R) (a j : ℕ),
    (∀ p q, a < q → Subsingleton ((K.col p).H q)) →
    Function.Surjective (clsZ K (a + j) j) := by
  intro R _ K a j h
  exact LinearMap.range_eq_top.1 (Ff_eq_top_of_acyclic K a j h j le_rfl)

end GlobalTheory.CompanionTheory.CechSerre
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexClassZeroOfLeadZero
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

namespace GlobalTheory.CompanionTheory.RowInj

theorem clsZ_mem_of_leadE {R : Type} [CommRing R] (K : DCx.{w} R) (n a q : ℕ) (haq : a + q = n)
    (z : Zf K n a) (hz : leadE K a q z = 0) : clsZ K n a z ∈ Ff K n (a + 1) := by
  have hT : (Subtype.val (Subtype.val (Subtype.val z)) : (p q : ℕ) → K.X p q) ∈ K.T n :=
    Subtype.prop (Subtype.val (Subtype.val z))
  have h0 : ∀ p r, p < a → (Subtype.val (Subtype.val (Subtype.val z)) : (p q : ℕ) → K.X p q) p r = 0 :=
    fun p r hp => z.2 p r hp
  have hdv : K.dv a q ((Subtype.val (Subtype.val (Subtype.val z)) : (p q : ℕ) → K.X p q) a q) = 0 :=
    dv_lead K _ (D_zero K (Subtype.val z)) a q h0
  have hB : leadC K a q z ∈ (colH K q).B a := by
    have hz' := hz
    rw [leadE_eq] at hz'
    unfold CrystallineSemistableComparison.Cx.cls at hz'
    rw [Submodule.Quotient.mk_eq_zero] at hz'
    exact hz'
  have hL := leadC_eq K a q z hdv
  obtain ⟨v₁, W₁, hW₁, hD, hv⟩ : ∃ (v₁ : K.X a q) (W₁ : (p q : ℕ) → K.X p q),
      (∀ p r, p + r + 1 ≠ n → W₁ p r = 0) ∧ K.D W₁ = K.sgl a q v₁ ∧
      (Subtype.val (Subtype.val (Subtype.val z)) : (p q : ℕ) → K.X p q) a q - v₁ ∈ (K.col a).B q := by
    cases a with
    | zero =>
      refine ⟨0, 0, fun _ _ _ => rfl, by simp, ?_⟩
      have hb : leadC K 0 q z ∈ (⊥ : Submodule R ((colH K q).X 0)) := hB
      rw [Submodule.mem_bot, hL] at hb
      unfold CrystallineSemistableComparison.Cx.cls at hb
      rw [Submodule.Quotient.mk_eq_zero] at hb
      simpa using hb
    | succ a' =>
      have hb : leadC K (a' + 1) q z ∈ LinearMap.range ((colH K q).d a') := hB
      obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hb
      obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective
        (Submodule.comap ((K.col a').Z q).subtype ((K.col a').B q)) y
      have hw : K.dv a' q (w : K.X a' q) = 0 := w.2
      refine ⟨K.dh a' q w, K.sgl a' q w, ?_, ?_, ?_⟩
      · intro p r hpr
        apply K.sgl_ne
        by_cases hp : p = a'
        · right
          intro hr
          apply hpr
          omega
        · left
          exact hp
      · rw [DCx.D_sgl, hw, map_zero, smul_zero, add_zero]
      · rw [hL] at hy
        unfold CrystallineSemistableComparison.Cx.cls at hy
        change (colMap K a').mapH q (Submodule.Quotient.mk w) = _ at hy
        unfold CrystallineSemistableComparison.Cx.Hom.mapH at hy
        rw [Submodule.mapQ_apply, Submodule.Quotient.eq] at hy
        have h2 := Submodule.neg_mem _ hy
        rw [neg_sub] at h2
        exact h2
  obtain ⟨W, hW, hW'⟩ := lower_vert K _ hT haq h0 v₁ W₁ hW₁ hD hv
  exact lower K z W hW hW'

theorem leadE_eq_zero_of_subsingleton {R : Type} [CommRing R] (K : DCx.{w} R) (n a q : ℕ)
    (hs : Subsingleton ((K.col a).H q)) (z : Zf K n a) : leadE K a q z = 0 := by
  have h0 : leadC K a q z = 0 := Subsingleton.elim _ _
  rw [leadE_eq]
  unfold CrystallineSemistableComparison.Cx.cls
  rw [Submodule.Quotient.mk_eq_zero]
  show leadC K a q z ∈ (colH K q).B a
  rw [h0]
  exact Submodule.zero_mem _

theorem Ff_eq_zero {R : Type} [CommRing R] (K : DCx.{w} R) (a j : ℕ)
    (hK : ∀ p q, q < a → Subsingleton ((K.col p).H q)) :
    ∀ k b, j < b → b + k = a + j + 1 → ∀ x ∈ Ff K (a + j) b, x = 0 := by
  intro k
  induction k with
  | zero =>
    intro b _ hbk x hx
    have hb' : b = a + j + 1 := by omega
    subst hb'
    have hs := Ff_top_subsingleton K (a + j)
    have hxx := Subsingleton.elim (⟨x, hx⟩ : ↥(Ff K (a + j) (a + j + 1))) 0
    simpa using congrArg Subtype.val hxx
  | succ k ih =>
    intro b hb hbk x hx
    have hx' : x ∈ LinearMap.range (clsZ K (a + j) b) := hx
    obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hx'
    have hq : b + (a + j - b) = a + j := by omega
    have hz : leadE K b (a + j - b) z = 0 :=
      leadE_eq_zero_of_subsingleton K (a + j) b (a + j - b) (hK b _ (by omega)) z
    exact ih (b + 1) (by omega) (by omega) _ (clsZ_mem_of_leadE K (a + j) b (a + j - b) hq z hz)

theorem clsZ_eq_zero_of_leadE : ∀ {R : Type} [CommRing R] (K : DCx.{w} R) (a j : ℕ), (∀ p q, q < a → Subsingleton ((K.col p).H q)) →
    ∀ z : Zf K (a + j) j, leadE K j a z = 0 → clsZ K (a + j) j z = 0 := by
  intro R _ K a j hK z hz
  exact Ff_eq_zero K a j hK a (j + 1) (by omega) (by omega) _
    (clsZ_mem_of_leadE K (a + j) j a (by omega) z hz)

end GlobalTheory.CompanionTheory.RowInj
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexLeadSurjective
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

namespace GlobalTheory.CompanionTheory.CechSerre

theorem extend_step {R : Type} [CommRing R] (K : DCx.{w} R) (n b : ℕ) (x : ∀ p q, K.X p q) (hx : x ∈ K.T n)
    (h0 : ∀ p r, p < b → K.D x p r = 0)
    (hB : ∀ q, b + q = n + 1 → K.D x b q ∈ (K.col b).B q) :
    ∃ x' : ∀ p q, K.X p q, x' ∈ K.T n ∧ (∀ p r, p < b → x' p r = x p r) ∧
      ∀ p r, p < b + 1 → K.D x' p r = 0 := by
  have hD : K.D x ∈ K.T (n + 1) := K.D_mem n x hx
  by_cases hbn : b ≤ n
  · obtain ⟨r, rfl⟩ : ∃ r, n = b + r := ⟨n - b, by omega⟩
    obtain ⟨y, hy⟩ := CrystallineSemistableComparison.Cx.mem_B_succ.mp (hB (r + 1) (by omega))
    have hy' : K.dv b r y = K.D x b (r + 1) := hy
    refine ⟨x - K.sgl b r (((-1 : ℤ) ^ b) • y), sub_mem hx ?_, ?_, ?_⟩
    · intro p q hpq
      exact K.sgl_ne _ (by omega)
    · intro p r' hp
      simp only [Pi.sub_apply]
      rw [K.sgl_ne _ (Or.inl (by omega)), sub_zero]
    · intro p r' hp
      simp only [map_sub, CrystallineSemistableComparison.DCx.D_sgl, Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
      rw [K.sgl_ne _ (Or.inl (by omega)), zero_add]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hp with hp | rfl
      · rw [h0 p r' hp, K.sgl_ne _ (Or.inl (by omega)), smul_zero, sub_zero]
      · by_cases hr : r' = r + 1
        · subst hr
          rw [K.sgl_self, map_zsmul, hy', smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul, sub_self]
        · have h1 : K.D x p r' = 0 := hD p r' (by omega)
          rw [h1, K.sgl_ne _ (Or.inr hr), smul_zero, sub_zero]
  · refine ⟨x, hx, fun _ _ _ => rfl, ?_⟩
    intro p r hp
    rcases Nat.lt_succ_iff_lt_or_eq.mp hp with hp | rfl
    · exact h0 p r hp
    · by_cases hr : p + r = n + 1
      · obtain rfl : r = 0 := by omega
        exact CrystallineSemistableComparison.Cx.mem_B_zero.mp (hB 0 hr)
      · exact hD p r hr

theorem leadE_surjective {R : Type} [CommRing R] (K : DCx.{w} R) (a j : ℕ)
    (hac : ∀ p q, q < a → Subsingleton ((K.col p).H q)) :
    Function.Surjective (leadE K j a (n := a + j)) := by
  intro t
  obtain ⟨c, hc, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (colH K a) j).1 t
  obtain ⟨y, hy, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (K.col j) a).1 c
  have hcls : ∀ (C : CrystallineSemistableComparison.Cx R) (m : ℕ) (u v : C.X m) (hu : C.d m u = 0) (hv : C.d m v = 0),
      u = v → C.cls u hu = C.cls v hv := by
    rintro C m u v hu hv rfl
    rfl
  have hy' : K.dv j a y = 0 := hy
  have hdh : K.dh j a y ∈ (K.col (j + 1)).B a := by
    have hb : (K.col (j + 1)).d a ((colMap K j).f a y) = 0 := by
      show K.dv (j + 1) a (K.dh j a y) = 0
      rw [← K.hv j a y, hy', map_zero]
    have h1 : (colMap K j).mapH a ((K.col j).cls y hy) = 0 := hc
    rw [CrystallineSemistableComparison.P.mapH_cls (colMap K j) a y hy hb] at h1
    exact ((CrystallineSemistableComparison.P.cls_surj (K.col (j + 1)) a).2.1 _ hb).mp h1
  have hmemT : ∀ (m : ℕ) (u : ∀ p q, K.X p q), u ∈ K.T m ↔ ∀ p q, p + q ≠ m → u p q = 0 :=
    fun _ _ => Iff.rfl
  have hx0 : K.sgl j a y ∈ K.T (a + j) := (hmemT _ _).2 fun p q hpq => K.sgl_ne y (by omega)
  have hDx0 : ∀ p r, p < j + 1 → K.D (K.sgl j a y) p r = 0 := by
    intro p r hp
    rw [CrystallineSemistableComparison.DCx.D_sgl, hy', map_zero, smul_zero, add_zero, K.sgl_ne _ (Or.inl (by omega))]
  have hstep : ∀ k : ℕ, ∃ x ∈ K.T (a + j), (∀ p r, p < j + 1 → x p r = K.sgl j a y p r) ∧
      ∀ p r, p < j + 2 + k → K.D x p r = 0 := by
    intro k
    induction k with
    | zero =>
      obtain ⟨x', hx', hag, hD'⟩ := extend_step K (a + j) (j + 1) (K.sgl j a y) hx0 hDx0 (by
        intro q hq
        obtain rfl : q = a := by omega
        rw [CrystallineSemistableComparison.DCx.D_sgl, hy', map_zero, smul_zero, add_zero, K.sgl_self]
        exact hdh)
      exact ⟨x', hx', hag, fun p r hp => hD' p r (by omega)⟩
    | succ k ih =>
      obtain ⟨x, hx, hag, hD⟩ := ih
      obtain ⟨x', hx', hag', hD'⟩ := extend_step K (a + j) (j + 2 + k) x hx hD (by
        intro q hq
        have hqa : q < a := by omega
        have hdv : (K.col (j + 2 + k)).d q (K.D x (j + 2 + k) q) = 0 :=
          dv_lead K (K.D x) (K.DD x) (j + 2 + k) q hD
        have := hac (j + 2 + k) q hqa
        exact ((CrystallineSemistableComparison.P.cls_surj (K.col (j + 2 + k)) q).2.1 _ hdv).mp (Subsingleton.elim _ _))
      exact ⟨x', hx', fun p r hp => (hag' p r (by omega)).trans (hag p r hp),
        fun p r hp => hD' p r (by omega)⟩
  obtain ⟨x, hx, hag, hD⟩ := hstep a
  have hD0 : K.D x = 0 := by
    funext p r
    by_cases hp : p < j + 2 + a
    · exact hD p r hp
    · exact (hmemT _ _).1 (K.D_mem _ x hx) p r (by omega)
  have hZ : (⟨x, hx⟩ : K.T (a + j)) ∈ K.tot.Z (a + j) := LinearMap.mem_ker.2 (Subtype.ext hD0)
  have hxy : x j a = y := (hag j a (by omega)).trans (K.sgl_self j a y)
  have hzf : (⟨⟨x, hx⟩, hZ⟩ : K.tot.Z (a + j)) ∈ Zf K (a + j) j := by
    intro p q hp
    exact (hag p q (by omega)).trans (K.sgl_ne y (Or.inl (by omega)))
  refine ⟨⟨⟨⟨x, hx⟩, hZ⟩, hzf⟩, ?_⟩
  rw [leadE_eq]
  apply hcls
  rw [leadC_eq K j a _ (by show (K.col j).d a (x j a) = 0; rw [hxy]; exact hy)]
  exact hcls _ _ _ _ _ _ hxy

end GlobalTheory.CompanionTheory.CechSerre
end

