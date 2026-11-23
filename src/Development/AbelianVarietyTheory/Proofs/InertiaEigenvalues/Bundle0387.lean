module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0353
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0382
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0379
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PropEOfAdmissible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAuxiliaryPlaceFamilyAtLevelMono
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0355
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemOfForallAnnihilatorAnnihilatorFieldModInteger

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisFrobeniusMatrixEqZeroOfDvd
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
namespace GlobalTheory.CrZero

theorem pow_cancel {A : Type*} [CommRing A] (p : A) (hp : ∀ x : A, p * x = 0 → x = 0)
    (k : ℕ) (a b : A) (h : p ^ k * a = p ^ k * b) : a = b := by
  induction k generalizing a b with
  | zero => simpa using h
  | succ k ih =>
    apply ih
    have h' : p * (p ^ k * a - p ^ k * b) = 0 := by
      rw [mul_sub, ← mul_assoc, ← mul_assoc, ← pow_succ', h, sub_self]
    exact sub_eq_zero.mp (hp _ h')

theorem eq_zero_of_forall_dvd {A : Type*} [CommRing A] (p : A)
    (hH : IsHausdorff (Ideal.span {p}) A) (x : A) (h : ∀ M : ℕ, p ^ M ∣ x) : x = 0 := by
  refine hH.haus x fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  exact Ideal.mem_span_singleton.mpr (h n)

end GlobalTheory.CrZero


open GlobalTheory.CrZero in
theorem GlobalTheory.BKLim.acris_frob_eq_zero : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d c : ℕ)
    (D₀ F F' : Matrix (Fin d) (Fin d) (Per.Acris l)),
    (∀ i j, ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) X ∣ D₀ i j) →
    (l : Per.Acris l) ^ c • D₀ = F * D₀.map (phiA l) * F' → D₀ = 0 := by
  intro l _ K bk d c D₀ F F' hdiv hfr
  obtain ⟨htor, hcomp, -, hphi, -⟩ := _root_.GlobalTheory.AcrisFrobE.main l K bk
  set u := ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) X with hu
  have hφu : phiA l u = u ^ l := by
    rw [hu, RingHom.comp_apply, hphi, ← bk.ev_frob]
    have : frobS l bk.a X = X ^ l := by simp [frobS]
    rw [this, map_pow, map_pow]
  have hφl : ∀ k : ℕ, phiA l ((l : Per.Acris l) ^ k) = (l : Per.Acris l) ^ k := by
    intro k; simp

  have key : ∀ n : ℕ, ∃ N : Matrix (Fin d) (Fin d) (Per.Acris l),
      (l : Per.Acris l) ^ (c * n) • D₀ = u ^ (l ^ n) • N := by
    intro n
    induction n with
    | zero =>
      refine ⟨Matrix.of fun i j => (hdiv i j).choose, ?_⟩
      ext i j
      simp only [mul_zero, pow_zero, pow_one, one_smul, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
      rw [one_mul]; exact (hdiv i j).choose_spec
    | succ n ih =>
      obtain ⟨N, hN⟩ := ih
      refine ⟨F * N.map (phiA l) * F', ?_⟩
      have hmap : ((l : Per.Acris l) ^ (c * n) • D₀).map (phiA l)
          = (l : Per.Acris l) ^ (c * n) • D₀.map (phiA l) := by
        ext i j; simp [hφl]
      have hmap2 : (u ^ (l ^ n) • N).map (phiA l) = u ^ (l ^ (n + 1)) • N.map (phiA l) := by
        ext i j; simp [hφu, ← pow_mul]; ring
      calc (l : Per.Acris l) ^ (c * (n + 1)) • D₀
          = (l : Per.Acris l) ^ (c * n) • ((l : Per.Acris l) ^ c • D₀) := by
            rw [smul_smul, ← pow_add, mul_add, mul_one]
        _ = F * (((l : Per.Acris l) ^ (c * n) • D₀).map (phiA l)) * F' := by
            rw [hfr, hmap, Matrix.mul_smul, Matrix.smul_mul]
        _ = u ^ (l ^ (n + 1)) • (F * N.map (phiA l) * F') := by
            rw [hN, hmap2, Matrix.mul_smul, Matrix.smul_mul]
  ext i j
  have hH : IsHausdorff (Ideal.span {(l : Per.Acris l)}) (Per.Acris l) := hcomp.toIsHausdorff
  refine eq_zero_of_forall_dvd _ hH _ fun M => ?_
  obtain ⟨n₀, hn₀⟩ := _root_.GlobalTheory.AcrisPow.main l K bk c M
  obtain ⟨N, hN⟩ := key n₀
  obtain ⟨y, hy⟩ := hn₀ n₀ le_rfl
  have hent : (l : Per.Acris l) ^ (c * n₀) * D₀ i j = u ^ (l ^ n₀) * N i j := by
    have := congrFun (congrFun hN i) j
    simpa using this
  have hpos : 1 ≤ l ^ n₀ := Nat.one_le_pow _ _ (Fact.out : l.Prime).pos
  have hsplit : u ^ (l ^ n₀) = u * u ^ (l ^ n₀ - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hpos]
  refine ⟨u * y * N i j, ?_⟩
  apply pow_cancel _ htor (c * n₀)
  rw [hent, hsplit, hy]
  ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdicCompletionRegularAndTorsionBounded
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.ComplLD

theorem smodEq_iff {Q : Type} [CommRing Q] (I : Ideal Q) (n : ℕ) (x y : Q) :
    x ≡ y [SMOD (I ^ n • ⊤ : Submodule Q Q)] ↔ x - y ∈ I ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]

theorem eq_zero_of_mem {Q : Type} [CommRing Q] (I : Ideal Q) [IsHausdorff I Q] (x : Q)
    (h : ∀ n, x ∈ I ^ n) : x = 0 :=
  IsHausdorff.haus' x fun n => (smodEq_iff I n x 0).2 (by simpa using h n)

theorem exists_lim {Q : Type} [CommRing Q] (I : Ideal Q) [IsPrecomplete I Q] (f : ℕ → Q)
    (h : ∀ m n, m ≤ n → f n - f m ∈ I ^ m) : ∃ z, ∀ n, f n - z ∈ I ^ n := by
  obtain ⟨z, hz⟩ := IsPrecomplete.prec' (I := I) f fun {m n} hmn =>
    (smodEq_iff I m _ _).2 (by rw [show f m - f n = -(f n - f m) by ring]; exact neg_mem (h m n hmn))
  exact ⟨z, fun n => (smodEq_iff I n _ _).1 (hz n)⟩

theorem regular_and_torsion_bounded : ∀ (l : ℕ) [Fact l.Prime] (L : Type) [CommRing L] (Q : Type) [CommRing Q] (i : L →+* Q) (d : L) (N : ℕ), d ∈ nonZeroDivisors L → (∀ (x : L) (m : ℕ), (l : L) ^ m * x ∈ Ideal.span {d} → (l : L) ^ N * x ∈ Ideal.span {d}) → IsCompl i (Ideal.span {(l : L)} ⊔ Ideal.span {d}) → i d ∈ nonZeroDivisors Q ∧ ∀ (x : Q) (m : ℕ), (l : Q) ^ m * x ∈ Ideal.span {i d} → (l : Q) ^ N * x ∈ Ideal.span {i d} := by
  intro l _ L _ Q _ i d N hd hbd hc
  set J : Ideal L := Ideal.span {(l : L)} ⊔ Ideal.span {d} with hJ
  set I : Ideal Q := J.map i with hI
  haveI : IsAdicComplete I Q := hc.complete
  have hpow : ∀ n, (J ^ n).map i = I ^ n := fun n => Ideal.map_pow _ _ _
  have surj : ∀ (x : Q) n, ∃ a, x - i a ∈ I ^ n := fun x n => by
    obtain ⟨a, ha⟩ := hc.surj x n; exact ⟨a, by rwa [← hpow]⟩
  have ker : ∀ a n, i a ∈ I ^ n → a ∈ J ^ n := fun a n h => hc.ker a n (by rwa [hpow])
  have strict : ∀ n z, i d * z ∈ I ^ (2 * (n + N + 1)) → z ∈ I ^ n := by
    intro n z hz
    obtain ⟨a, ha⟩ := surj z (2 * (n + N + 1))
    have h1 : i (d * a) ∈ I ^ (2 * (n + N + 1)) := by
      have e : i (d * a) = i d * z - i d * (z - i a) := by rw [map_mul]; ring
      rw [e]; exact sub_mem hz (Ideal.mul_mem_left _ _ ha)
    have h2 := _root_.GlobalTheory.div_d_continuous_of_bdd_ltorsion l L d N hd hbd n a (ker _ _ h1)
    have h3 : i a ∈ I ^ n := by rw [← hpow]; exact Ideal.mem_map_of_mem i h2
    have h4 : z - i a ∈ I ^ n := Ideal.pow_le_pow_right (by omega) ha
    simpa using add_mem h4 h3
  have reg : i d ∈ nonZeroDivisors Q := by
    rw [mem_nonZeroDivisors_iff]
    exact ⟨fun z hz => eq_zero_of_mem I z fun n => strict n z (by rw [hz]; exact zero_mem _),
      fun z hz => eq_zero_of_mem I z fun n => strict n z (by rw [mul_comm (i d) z, hz]; exact zero_mem _)⟩
  have closed : ∀ x, (∀ n, ∃ z, x - i d * z ∈ I ^ n) → x ∈ Ideal.span {i d} := by
    intro x hx
    choose z hz using fun n => hx (2 * (n + N + 1))
    obtain ⟨w, hw⟩ := exists_lim I z fun m n hmn => strict m _ (by
      have e : i d * (z n - z m) = (x - i d * z m) - (x - i d * z n) := by ring
      rw [e]; exact sub_mem (hz m) (Ideal.pow_le_pow_right (by omega) (hz n)))
    have h0 : x - i d * w = 0 := eq_zero_of_mem I _ fun n => by
      have e : x - i d * w = (x - i d * z n) + i d * (z n - w) := by ring
      rw [e]; exact add_mem (Ideal.pow_le_pow_right (by omega) (hz n)) (Ideal.mul_mem_left _ _ (hw n))
    exact Ideal.mem_span_singleton'.2 ⟨w, by rw [mul_comm]; exact (sub_eq_zero.1 h0).symm⟩
  refine ⟨reg, fun x m hx => closed _ fun n => ?_⟩
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hx
  obtain ⟨a, ha⟩ := surj x (m + n + 1)
  obtain ⟨b, hb⟩ := surj y (m + n + 1)
  have h1 : i ((l : L) ^ m * a - d * b) ∈ I ^ (m + n + 1) := by
    have e : i ((l : L) ^ m * a - d * b) = -((l : Q) ^ m * (x - i a)) + i d * (y - i b) := by
      rw [map_sub, map_mul, map_mul, map_pow, map_natCast]; linear_combination (-1 : Q) * hy
    rw [e]; exact add_mem (neg_mem (Ideal.mul_mem_left _ _ ha)) (Ideal.mul_mem_left _ _ hb)
  have h2 : (l : L) ^ m * a - d * b ∈ Ideal.span {(l : L) ^ (m + n)} ⊔ Ideal.span {d} := by
    have hle : J ^ (m + n + 1) ≤ Ideal.span {(l : L)} ^ (m + n) ⊔ Ideal.span {d} ^ 1 :=
      Ideal.sup_pow_add_le_pow_sup_pow
    simpa [Ideal.span_singleton_pow] using hle (ker _ _ h1)
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 h2
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hu
  obtain ⟨e, rfl⟩ := Ideal.mem_span_singleton'.1 hv
  have h3 : (l : L) ^ m * (a - (l : L) ^ n * c) ∈ Ideal.span {d} :=
    Ideal.mem_span_singleton'.2 ⟨b + e, by linear_combination huv⟩
  obtain ⟨f, hf⟩ := Ideal.mem_span_singleton'.1 (hbd _ _ h3)
  refine ⟨i f, ?_⟩
  have hf' := congrArg i hf
  simp only [map_mul, map_pow, map_natCast, map_sub] at hf'
  have e : (l : Q) ^ N * x - i d * i f = (l : Q) ^ N * (x - i a) + i ((l : L) ^ (N + n) * c) := by
    rw [map_mul, map_pow, map_natCast]; linear_combination (-1 : Q) * hf'
  rw [e]
  refine add_mem (Ideal.pow_le_pow_right (by omega) (Ideal.mul_mem_left _ _ ha)) ?_
  rw [← hpow]
  refine Ideal.mem_map_of_mem i (Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right (by omega : n ≤ N + n)
    (Ideal.pow_mem_pow (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)) (N + n))))

end GlobalTheory.BSP.ComplLD
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdicTopologicalBasisBasisModPowStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adicTopologicalBasis_basis_mod_pow : ∀ (S A : Type) [CommRing S] [CommRing A] (s : S →+* A) (I : Ideal S) (ι : Type) (tb : TopBasis s I ι) (m : ℕ), letI := (Ideal.quotientMap ((I ^ m).map s) s Ideal.le_comap_map).toAlgebra; ∃ b : Module.Basis ι (S ⧸ I ^ m) (A ⧸ (I ^ m).map s), ∀ i, b i = Ideal.Quotient.mk _ (tb.b i) := by
  first | exact @GlobalTheory.BSP.TopBasis.basis_mod_pow | exact GlobalTheory.BSP.TopBasis.basis_mod_pow | (intros; apply GlobalTheory.BSP.TopBasis.basis_mod_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleIndexBoundAllPowersOfConditions
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.TwistChoice
open scoped TensorProduct

namespace GlobalTheory.TwistChoiceAll

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem root_pow_prim (i : X.Tw) {k e : ℕ} {ζ : (X.Ok i k)ˣ} (hζ : IsPrimitiveRoot (ζ : X.Ok i k) (X.l i ^ k))
    (he : e < k) : IsPrimitiveRoot ((ζ ^ (X.l i ^ e) : (X.Ok i k)ˣ) : X.Ok i k) (X.l i ^ (k - e)) := by
  have hl : (X.l i).Prime := (X.lPrime i).out
  rw [Units.val_pow_eq_pow_val]
  refine hζ.pow (pow_pos hl.pos _) ?_
  rw [← pow_add]
  congr 1
  omega

theorem side_root (i : X.Tw) (k : ℕ) {ζ : (X.Ok i k)ˣ} (hζ : IsPrimitiveRoot (ζ : X.Ok i k) (X.l i ^ k)) (b : Bool) :
    IsPrimitiveRoot (((if b then ζ else ζ⁻¹ : (X.Ok i k)ˣ)) : X.Ok i k) (X.l i ^ k) := by
  rw [IsPrimitiveRoot.coe_units_iff] at hζ ⊢
  cases b
  · exact hζ.inv
  · exact hζ

theorem zpow_prim (i : X.Tw) (k : ℕ) {a : ℤ} (ha : IsCoprime a (X.l i : ℤ)) :
    IsPrimitiveRoot ((X.zk i k ^ a : (X.Ok i k)ˣ) : X.Ok i k) (X.l i ^ k) := by
  rw [IsPrimitiveRoot.coe_units_iff]
  refine (IsPrimitiveRoot.coe_units_iff.1 (X.zk_prim i k)).zpow_of_gcd_eq_one a ?_
  rw [← Int.isCoprime_iff_gcd_eq_one, Nat.cast_pow]
  exact ha.pow_right

theorem psiOk_partD_root (Y : NExp D.R D.host D.what₂ D.LL0 N X) {i : X.Tw} {M k : ℕ} (hM : 1 ≤ M) (hk : 1 ≤ k)
    {A0 : Finset (PlE D.host)} {ι : Type} [Fintype ι]
    {P : ι → PlE D.host} {d} (h : SlopeTestRemainingChoices X i M A0 P d) {Q : Finset (PlE D.host)} (hQ : IsQ P Q) (e : ι → ℕ) {ε : ℝ}
    (he : ∀ q, e q < k ∧ (X.l i : ℝ) ^ e q / (Nat.totient (X.l i ^ k) : ℝ) ≤ ε)
    (ζ : (X.Ok i k)ˣ) (hζ : IsPrimitiveRoot (ζ : X.Ok i k) (X.l i ^ k)) (hζm : ζ ∈ Subgroup.zpowers (X.zk i k))
    (ψ' : X.RCG i Q →* (X.Ok i k)ˣ) (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ)
    (hχ : ψ'.comp (X.art i Q) = χ.comp (Y.delU i Q M))
    (hψ : ∀ g, ψ' (X.art i Q g) = ∏ q, (ζ ^ (X.l i ^ e q)) ^ (Multiplicative.toAdd (d q g)).val) :
    PsiOk i A0 Q k ψ' ∧ ∑ v ∈ Q, tameVal (X.l i) (ψ'.comp (X.art i Q)) (N.plOm.1 v) ≤ Q.card * ε := by
  classical
  have hl : (X.l i).Prime := (X.lPrime i).out
  have hF : ∀ q, ((ζ ^ (X.l i ^ e q) : (X.Ok i k)ˣ) : X.Ok i k) - 1 ≠ 0 ∧
      nval (X.Ok i k) (X.l i) (((ζ ^ (X.l i ^ e q) : (X.Ok i k)ˣ) : X.Ok i k) - 1) ≤ ε := by
    intro q
    have := _root_.GlobalTheory.nval_primitiveRoot_prime_pow_sub_one (X.Ok i k) (X.l i) (k - e q) hl (by have := (he q).1; omega) (l_ne_zero_Ok i k).1
      (l_not_unit i k).1 _ (root_pow_prim i hζ (he q).1)
    refine ⟨this.1, ?_⟩
    rw [this.2, totient_bound hl (he q).1]
    exact (he q).2
  have hne : ∀ q, ζ ^ (X.l i ^ e q) ≠ 1 := fun q h => (hF q).1 (by rw [h]; simp)
  refine ⟨⟨fun v hv => ?_, ?_, hk, ?_, ?_, fun g => ?_, fun v A hA => ⟨?_, fun hv => ?_⟩, ?_⟩, ?_⟩
  · obtain ⟨q, hq⟩ := (hQ v).1 hv
    obtain ⟨a, b, c, -⟩ := h.1 q v hq
    exact ⟨a, b, c⟩
  · rw [Finset.disjoint_left]
    intro v hv hv'
    obtain ⟨q, hq⟩ := (hQ v).1 hv
    obtain ⟨-, -, -, a, b, -⟩ := h.1 q v hq
    rcases Finset.mem_union.1 hv' with h | h
    · exact a h
    · exact b h
  · refine Subgroup.isOpen_mono (H₁ := (X.art i Q).ker) (fun g hg => ?_) (X.art_cont i Q)
    rw [MonoidHom.mem_ker] at hg ⊢
    rw [MonoidHom.comp_apply, hg, map_one]
  · intro g g' hg
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, X.art_anti i Q g g' hg, map_inv]
  · rw [MonoidHom.comp_apply, hψ]
    exact prod_mem fun q _ => pow_mem (pow_mem hζm _) _
  · rintro ⟨σ, hσ, h1⟩
    by_contra hv
    exact h1 (by rw [MonoidHom.comp_apply, X.art_unr i Q v hv A hA σ hσ, map_one])
  · obtain ⟨q, hq⟩ := (hQ v).1 hv
    obtain ⟨σ, hσ, h1⟩ := exists_ine hM h _ (ψ'.comp (X.art i Q)) hψ hq A hA
    exact ⟨σ, hσ, h1 ▸ hne q⟩
  · intro v hv A hA σ hσ
    rw [hχ, MonoidHom.comp_apply, Y.delU_l i Q M v hv A hA σ hσ, map_one]
  · rw [← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun v hv => ?_
    obtain ⟨q, hq⟩ := (hQ v).1 hv
    obtain ⟨σ, hσ, h1⟩ := exists_ine hM h _ (ψ'.comp (X.art i Q)) hψ hq (N.plOm.1 v) (N.plOm.2 v)
    refine (tameVal_le _ _ _ hσ (h1 ▸ hne q)).trans ?_
    rw [h1]
    exact (hF q).2

theorem admissibleIndexBoundAllPowers_of_conditions (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X)
    (N0 : X.Tw → ℕ) (hU : DelUTie bkP.ex) (hAB : PropABCD bkP.ex) (hX : GaloisSideTwistedSelmerAuxiliaryPrimes bkP) (hadm : AdmACD bkP N0) :
    admissibleIndexBoundAllPowers bkP.ex bkP N0 := by
  classical
  intro i hi hS eps' heps F hF A0
  have hl : (X.l i).Prime := (X.lPrime i).out
  obtain ⟨h1, h2, h3, -, h9, h10⟩ := hadm
  obtain ⟨sNC, sSD, sNJ, sth, sS, sr, -⟩ := hS
  obtain ⟨z, hz⟩ := GlobalTheory.TwSys.exists_tameInertiaElementAtAuxiliaryPrime D N X i
  obtain ⟨R, Dd, M₀, hM₀, hR⟩ := hX i {s | goodS bkP i s}
    (fun s hs => ⟨h1 i hi s, h2 i hi s, sSD s hs, sNJ s hs, sNC, h3, sr⟩)
  choose HE vE hHEo hHEn hvE hE using fun lam => GlobalTheory.ToricFactor.propE D N X N0 h9 h10 i lam z hi (sS lam) (sth lam) hz
  choose HB AB vB nB hHBo hHBn hB using fun y : ↥(Finset.Icc 1 D.R.m) × Bool =>
    hAB i F y.1 y.2 z hi y.1.2 (hF _ y.1.2 _) hz
  have hopen : IsOpen (((⨅ lam, HE lam) ⊓ ⨅ y, HB y : Subgroup (GE N)) : Set (GE N)) := by
    rw [Subgroup.coe_inf, Subgroup.coe_iInf, Subgroup.coe_iInf]
    exact (isOpen_iInter_of_finite hHEo).inter (isOpen_iInter_of_finite hHBo)
  have hnorm : ((⨅ lam, HE lam) ⊓ ⨅ y, HB y : Subgroup (GE N)).Normal := by
    haveI := Subgroup.normal_iInf_normal hHEn
    haveI := Subgroup.normal_iInf_normal hHBn
    infer_instance
  choose H0 S0 d hd hco using fun M (h : M₀ ≤ M) => hU i M hi (hM₀.trans h)
  choose P hPa hPs hPF using fun M (h : M₀ ≤ M) =>
    hR M h _ _ _ (hd M h) z hz _ hopen hnorm (A0 ∪ Finset.univ.biUnion AB)
  choose Q hQ hQc using fun M (h : M₀ ≤ M) => exists_isQ (P M h)
  choose Fs hFs hFc using fun M (h : M₀ ≤ M) (s : {s // goodS bkP i s}) => hPF M h s.1 s.2 (Q M h) (hQ M h)
  choose fE hfE hfE' using fun M (h : M₀ ≤ M) lam => hE lam M R (P M h) _ (Q M h) (hM₀.trans h)
    (isAuxiliaryPlaceFamilyAtLevel_mono (hPa M h) (Finset.empty_subset _)) (steps_mono (hPs M h) (inf_le_left.trans (iInf_le _ lam))) (hQ M h)
  choose fB hfB hfB' using fun M (h : M₀ ≤ M) y => hB y M R (P M h) (d M h) (Q M h) (hM₀.trans h) (hco M h)
    (isAuxiliaryPlaceFamilyAtLevel_mono (hPa M h) ((Finset.subset_biUnion_of_mem AB (Finset.mem_univ y)).trans Finset.subset_union_right))
    (steps_mono (hPs M h) (inf_le_right.trans (iInf_le _ y))) (hQ M h)
  set C : ℝ := (SigG bkP i).card + 2 * D.R.m + D.R.t * (4 * R) + 1 with hC
  have hCpos : 0 < C := by positivity
  have hεC : C * (eps' / C) = eps' := by field_simp
  have hε : 0 < eps' / C := div_pos heps hCpos
  generalize eps' / C = ε at hε hεC
  have hle : ∀ c : ℝ, c ≤ C → c * ε ≤ eps' := fun c hc => hεC ▸ mul_le_mul_of_nonneg_right hc hε.le
  have c1 : (0 : ℝ) ≤ (SigG bkP i).card := Nat.cast_nonneg _
  have c2 : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
  have c3 : (0 : ℝ) ≤ D.R.t * (4 * R) := by positivity
  have he0 := e_pos (l_ne_zero_Ok i 0).2.2 (l_not_unit i 0).2.2
  obtain ⟨M, hM, k, e, hk, hkM, he, Hev⟩ := exists_level i R Dd (2 + ∑ y, nB y) M₀ {s // goodS bkP i s}
    (X.abelian₂ i ⊕ (↥(Finset.Icc 1 D.R.m) × Bool))
    (nu X i * (IsDiscreteValuationRing.addVal (X.O0 i) (X.l i : X.O0 i)).toNat) (Sum.elim vE vB) Fs
    (fun M h => Sum.elim (fE M h) (fB M h))
    (fun M h x => by
      obtain ⟨m, hm, hv⟩ := hFc M h x
      exact ⟨m, hm, hv.trans (addVal_l_pow (l_ne_zero_Ok i 0).2.2 _).le⟩)
    (fun M h y => by
      rcases y with lam | y
      · exact ordHyp_mono (hfE M h lam) (Nat.le_add_right _ _)
      · exact ordHyp_mono (hfB M h y)
          ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ y)).trans (Nat.le_add_left _ _))) hε
  haveI : NeZero (X.l i ^ M) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hu0 : ∀ ζ : (X.Ok i k)ˣ, IsPrimitiveRoot (ζ : X.Ok i k) (X.l i ^ k) →
      ∀ q, (ζ ^ (X.l i ^ e q)) ^ (X.l i ^ M) = 1 := by
    intro ζ hζ q
    rw [← pow_mul]
    exact ((IsPrimitiveRoot.coe_units_iff.1 hζ).pow_eq_one_iff_dvd _).2
      (Dvd.dvd.mul_left (pow_dvd_pow _ hkM) _)
  have hmem : ∀ q, P M hM q ∈ Q M hM := fun q => (hQ M hM _).2 ⟨q, Or.inl rfl⟩
  let χ₀ : Multiplicative (DelQM D.host (X.l i) (Q M hM) M) →* (X.Ok i k)ˣ :=
    prodChar (X.l i ^ M) (fun q => (⟨P M hM q, hmem q⟩ : ↥(Q M hM))) (fun q => X.zk i k ^ (X.l i ^ e q))
      (hu0 _ (X.zk_prim i k))
  have hχ₀ : ∀ x : DelQM D.host (X.l i) (Q M hM) M, χ₀ (Multiplicative.ofAdd x) =
      ∏ q, (X.zk i k ^ (X.l i ^ e q)) ^ (x ⟨P M hM q, hmem q⟩).val := fun _ => rfl
  obtain ⟨φ, hφ⟩ := exists_factor bkP.ex i M (Q := Q M hM) (fun v hv => by
    obtain ⟨q, hq⟩ := (hQ M hM v).1 hv
    exact ((hPa M hM).1 q v hq).2.2.2.1)
  refine ⟨Q M hM, k, χ₀.comp φ, fun a ha => ?_⟩
  have hζ := zpow_prim i k ha
  have hζm : X.zk i k ^ a ∈ Subgroup.zpowers (X.zk i k) := Subgroup.zpow_mem_zpowers _ _
  have hχ : ∀ x : DelQM D.host (X.l i) (Q M hM) M, (χ₀ ^ a) (Multiplicative.ofAdd x) =
      ∏ q, ((X.zk i k ^ a) ^ (X.l i ^ e q)) ^ (x ⟨P M hM q, hmem q⟩).val := by
    intro x
    rw [MonoidHom.zpow_apply, hχ₀, ← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun q _ => ?_
    simp only [← zpow_natCast, ← zpow_mul]
    congr 1
    ring
  have hψχ : ((χ₀.comp φ) ^ a).comp (X.art i (Q M hM)) = (χ₀ ^ a).comp (bkP.ex.delU i (Q M hM) M) := by
    rw [← hφ]
    rfl
  generalize X.zk i k ^ a = ζ at hζ hζm hχ
  generalize χ₀ ^ a = χ at hχ hψχ
  generalize (χ₀.comp φ) ^ a = ψ' at hψχ ⊢
  have hu : ∀ (b : Bool) q, ((if b then ζ else ζ⁻¹) ^ (X.l i ^ e q)) ^ (X.l i ^ M) = 1 :=
    fun b => hu0 _ (side_root i k hζ b)
  have hψ : ∀ g, ψ' (X.art i (Q M hM) g) =
      ∏ q, (ζ ^ (X.l i ^ e q)) ^ (Multiplicative.toAdd (d M hM (P M hM q) g)).val := by
    intro g
    refine (DFunLike.congr_fun hψχ g).trans ((hχ (Multiplicative.toAdd (bkP.ex.delU i (Q M hM) M g))).trans ?_)
    refine Finset.prod_congr rfl fun q _ => ?_
    rw [hco M hM _ (conjCl_of_isQ (hQ M hM))]
  obtain ⟨hok, hD⟩ := psiOk_partD_root bkP.ex (hM₀.trans hM) hk (isAuxiliaryPlaceFamilyAtLevel_mono (hPa M hM) Finset.subset_union_left) (hQ M hM) e he
    ζ hζ hζm ψ' χ hψχ hψ
  refine ⟨hok, ⟨fun _ => ε, fun _ => hε.le, ?_, fun s hs => ?_⟩, fun lam => ?_, ?_,
    M, χ, hψχ, fun _ _ => ε, fun _ _ => hε.le, ?_, fun j hj b Tψ hT hmemT => ?_⟩
  · rw [Finset.sum_const, nsmul_eq_mul]
    exact hle _ (by linarith)
  · obtain ⟨hne, hv⟩ := (Hev _ (side_root i k hζ (X.side i s))).1 ⟨s, hs⟩
    rw [hFs M hM ⟨s, hs⟩ k _ _ (hu (X.side i s)) (fun g => psiAt_prod _ _ _ _ _ g (hψ g)),
      valE_eq (l_ne_zero_Ok i k).1 (l_not_unit i k).1 hne]
    refine ENNReal.ofReal_le_ofReal (hv.trans (le_of_eq ?_))
    congr 1
    rw [Nat.cast_mul, mul_div_assoc, div_self (by exact_mod_cast he0.ne'), mul_one]
  · obtain ⟨hne, hv⟩ := (Hev _ (side_root i k hζ (X.sideL i lam))).2 (.inl lam)
    have := hfE' M hM lam k _ (psiAt (X.sideL i lam) ψ') (hu (X.sideL i lam)) (fun g => psiAt_prod _ _ _ _ _ _ (hψ g))
    obtain ⟨hx, hvK⟩ := vK_bounds (l_ne_zero_Ok i k).1 (l_not_unit i k).1 hne this
    simp only [Sum.elim_inl] at hv hvK
    rw [hvE] at hv
    have h0 := hle 1 (by linarith)
    refine ⟨hx, ?_, ?_⟩
    · rw [hvK]
      exact le_sub_iff_add_le.2 (by rw [neg_add_cancel]; exact nval_nonneg _)
    · rw [hvK]
      linarith
  · have hc : ((Q M hM).card : ℝ) ≤ 4 * R := by
      have := hQc M hM
      rw [Fintype.card_sum, Fintype.card_fin] at this
      exact_mod_cast (by omega : (Q M hM).card ≤ 4 * R)
    refine (mul_le_mul_of_nonneg_left (hD.trans (mul_le_mul_of_nonneg_right hc hε.le)) (Nat.cast_nonneg _)).trans ?_
    rw [← mul_assoc]
    exact hle _ (by linarith)
  · have := hle (D.R.m * 2) (by linarith)
    simpa [mul_assoc] using this
  · obtain ⟨hne, hv⟩ := (Hev _ (side_root i k hζ b)).2 (.inr (⟨j, hj⟩, b))
    have := hfB' M hM (⟨j, hj⟩, b) k _ (psiAt b χ) (hu b) (fun x => psiAt_prod _ _ _ _ _ _ (hχ x)) hne Tψ hT hmemT
    simp only [Sum.elim_inr] at hv
    refine this.trans (add_le_add_right ?_ _)
    linarith

end GlobalTheory.TwistChoiceAll

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ApproxBdRPlusFilMatrixMulStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.approx_bdRPlus_fil_matrix_mul : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (n d : ℕ) (X Z : Matrix (Fin d) (Fin d) (Per.BdRp l)), (∃ (k : ℕ) (s : Matrix (Fin d) (Fin d) bk.S), ∀ i j, aDp l (bk.ev (s i j)) - (l : Per.BdRp l) ^ k * X i j ∈ Per.FilP l n) → (∃ (k : ℕ) (s : Matrix (Fin d) (Fin d) bk.S), ∀ i j, aDp l (bk.ev (s i j)) - (l : Per.BdRp l) ^ k * Z i j ∈ Per.FilP l n) → ∃ (k : ℕ) (s : Matrix (Fin d) (Fin d) bk.S), ∀ i j, aDp l (bk.ev (s i j)) - (l : Per.BdRp l) ^ k * (X * Z) i j ∈ Per.FilP l n := by
  first | (exact @GlobalTheory.use₁₀) | (exact GlobalTheory.use₁₀) | (intros; apply GlobalTheory.use₁₀  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AtMOfParamRec
section
noncomputable section

namespace GlobalTheory.LiftLeaf

open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem atMOfParam_rec {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
    (i : N.Loc) : AtMOfParam N A i := by
  intro x _ Sig hX σ hW
  obtain ⟨P, hP, hB⟩ := hX
  refine ⟨Sig, hW, x, fun w hw => ⟨heckePol N i x w, ?_, rfl⟩⟩
  rw [hB.2.2.2.1 w hw.1]
  exact A.pt_loc i P x hP w hw

theorem atMOfParam (D : D7) (i : D.nd.Loc) : AtMOfParam D.nd D.naut i :=
  atMOfParam_rec D.nd D.naut i

end GlobalTheory.LiftLeaf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundedFiniteCohomologyQuotientsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_finite_cohomology_quotients : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A' : GRep ↥(GK K) ℚ_[l] LL O) (LA' : Lattice (O := O) A'.ρ), ∃ C0 k0 : ℕ, ∀ (r : ℕ) (hI' : StableSub LA' (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)), ∃ F : Finset (QuotientCohomology LA' _ hI'), F.card ≤ C0 ∧ ∀ c' : ↥(quotientCocycles LA' _ hI'), (fun g => (Submodule.Quotient.mk ((((l : ℕ) : LL) ^ r)⁻¹ • Formalism.MainNotions.LocalSituation.liftQ LA' _ ((c' : ↥(GK K) → ↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) g)) : A'.V ⧸ LA'.T)) ∈ BD LA' → (Submodule.Quotient.mk c' : QuotientCohomology LA' _ hI') ∈ F ∧ (((l : ℕ) : O) ^ k0) • (Submodule.Quotient.mk c' : QuotientCohomology LA' _ hI') = 0 := by
  first | exact @GlobalTheory.KerToDivisible.ker_bounded | exact GlobalTheory.KerToDivisible.ker_bounded | (intros; apply GlobalTheory.KerToDivisible.ker_bounded <;> assumption)
end

