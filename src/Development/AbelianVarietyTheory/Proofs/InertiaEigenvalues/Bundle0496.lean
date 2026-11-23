module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0458
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0004
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0460
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimeNatCastNeZeroWittOfTiltFiniteField
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter
  GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism.Compl

theorem smodEq_span_pow {R : Type} [CommRing R] (r x y : R) (n : ℕ) :
    x ≡ y [SMOD (Ideal.span {r} ^ n • ⊤ : Submodule R R)] ↔ ∃ z, x - y = r ^ n * z := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  exact ⟨fun ⟨z, hz⟩ => ⟨z, by rw [← hz, mul_comm]⟩, fun ⟨z, hz⟩ => ⟨z, by rw [hz, mul_comm]⟩⟩

theorem natCast_ne_zero_K (l : ℕ) [Fact l.Prime] {K : Type} [NormedField K] [NormedAlgebra ℚ_[l] K] {n : ℕ}
    (hn : n ≠ 0) : (n : K) ≠ 0 := by
  rw [← map_natCast (algebraMap ℚ_[l] K) n]
  exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hn)

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  (t : Wq l a →ₐ[ℤ_[l]] O) (K : Type)
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (e : ℕ)

def iota (τ : ZMod a) : Wq l a →+* K := (algebraMap O K).comp (emb t τ).toRingHom

variable {K}

theorem iota_injective (τ : ZMod a) : Function.Injective (iota t K τ) := by
  have := Fintype.ofFinite (Fq l a)
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro w hw
  by_contra h0
  obtain ⟨m, b, hb, rfl⟩ := WittVector.exists_eq_pow_p_mul w h0
  have hu : IsUnit b := WittVector.isUnit_of_coeff_zero_ne_zero b hb
  rw [map_mul, map_pow, map_natCast] at hw
  exact mul_ne_zero (pow_ne_zero _ (natCast_ne_zero_K l (K := K) hl.out.ne_zero)) (hu.map (iota t K τ)).ne_zero hw

include t K in
theorem prime_natCast_ne_zero_wittOfTiltFiniteField : (l : Wq l a) ≠ 0 := fun h => by
  have h1 := congrArg (iota t K 0) h
  rw [map_natCast, map_zero] at h1
  exact natCast_ne_zero_K l (K := K) hl.out.ne_zero h1


variable (K) in
def Rep (F : ZMod a → K⟦X⟧) (w : ℕ → Wq l a) : Prop :=
  ∀ τ n, ((n / e).factorial : K) * coeff n (F τ) = iota t K τ (w n)

variable {t e}

theorem rep_unique {F : ZMod a → K⟦X⟧} {w v : ℕ → Wq l a} (hw : Rep t K e F w) (hv : Rep t K e F v) : w = v :=
  funext fun n => iota_injective t 0 (by rw [← hw 0 n, ← hv 0 n])

theorem eq_of_rep {F G : ZMod a → K⟦X⟧} {w : ℕ → Wq l a} (hF : Rep t K e F w) (hG : Rep t K e G w) : F = G := by
  funext τ
  ext n
  exact mul_left_cancel₀ (natCast_ne_zero_K l (K := K) (Nat.factorial_ne_zero _)) ((hF τ n).trans (hG τ n).symm)

theorem rep_sub {F G : ZMod a → K⟦X⟧} {w v : ℕ → Wq l a} (hF : Rep t K e F w) (hG : Rep t K e G v) :
    Rep t K e (F - G) (w - v) := fun τ n => by
  simp only [Pi.sub_apply, map_sub, mul_sub, hF τ n, hG τ n]

theorem rep_pow_mul (m : ℕ) {F : ZMod a → K⟦X⟧} {w : ℕ → Wq l a} (hF : Rep t K e F w) :
    Rep t K e ((l : ZMod a → K⟦X⟧) ^ m * F) (fun n => (l : Wq l a) ^ m * w n) := fun τ n => by
  have h1 : ((l : ZMod a → K⟦X⟧) ^ m * F) τ = C ((l : K) ^ m) * F τ := by
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply, map_pow, map_natCast]
  rw [h1, coeff_C_mul, map_mul, map_pow, map_natCast, ← hF τ n]
  ring


variable (t e) in
def ofRep (w : ℕ → Wq l a) : ZMod a → K⟦X⟧ :=
  fun τ => PowerSeries.mk fun n => iota t K τ (w n) / ((n / e).factorial : K)

theorem rep_ofRep (w : ℕ → Wq l a) : Rep t K e (ofRep (K := K) t e w) w := fun τ n => by
  rw [ofRep, coeff_mk]
  exact mul_div_cancel₀ _ (natCast_ne_zero_K l (K := K) (Nat.factorial_ne_zero _))

variable (t e) in
theorem isHausdorff_of (hsd : ∀ F ∈ Sd t K e, F ∈ SdSet t K e) :
    IsHausdorff (Ideal.span {(l : ↥(Sd t K e))}) ↥(Sd t K e) := by
  have := Fintype.ofFinite (Fq l a)
  refine ⟨fun x hx => ?_⟩
  obtain ⟨w, -, hw⟩ := hsd x.1 x.2
  have hdiv : ∀ m k, ∃ q, w k = (l : Wq l a) ^ m * q := by
    intro m k
    obtain ⟨z, hz⟩ := (smodEq_span_pow _ _ _ m).1 (hx m)
    rw [sub_zero] at hz
    obtain ⟨v, -, hv⟩ := hsd z.1 z.2
    have h1 : x.1 = (l : ZMod a → K⟦X⟧) ^ m * z.1 := by rw [hz]; push_cast; rfl
    have h2 := rep_pow_mul m hv
    rw [← h1] at h2
    exact ⟨v k, congrFun (rep_unique hw h2) k⟩
  have hw0 : w = 0 := funext fun k => IsHausdorff.haus' (I := Ideal.span {(l : Wq l a)}) (w k) fun m => by
    obtain ⟨q, hq⟩ := hdiv m k
    exact (smodEq_span_pow _ _ _ m).2 ⟨q, by rw [sub_zero, hq]⟩
  apply Subtype.ext
  refine eq_of_rep (F := x.1) (G := 0) hw ?_
  rw [hw0]
  intro τ n
  simp

variable (t e) in
theorem isPrecomplete_of (hsd : ∀ F ∈ Sd t K e, F ∈ SdSet t K e) :
    IsPrecomplete (Ideal.span {(l : ↥(Sd t K e))}) ↥(Sd t K e) := by
  have := Fintype.ofFinite (Fq l a)
  refine ⟨fun f hf => ?_⟩
  choose w hw0 hw using fun j => hsd (f j).1 (f j).2
  have hc : ∀ {m j : ℕ}, m ≤ j → ∀ k,
      w m k ≡ w j k [SMOD (Ideal.span {(l : Wq l a)} ^ m • ⊤ : Submodule (Wq l a) (Wq l a))] := by
    intro m j hmj k
    obtain ⟨z, hz⟩ := (smodEq_span_pow _ _ _ m).1 (hf hmj)
    obtain ⟨v, -, hv⟩ := hsd z.1 z.2
    have h1 : (f m).1 - (f j).1 = (l : ZMod a → K⟦X⟧) ^ m * z.1 := by
      have h0 := congrArg Subtype.val hz
      push_cast at h0
      exact h0
    have h2 := rep_pow_mul m hv
    rw [← h1] at h2
    have h3 := congrFun (rep_unique (rep_sub (hw m) (hw j)) h2) k
    exact (smodEq_span_pow _ _ _ m).2 ⟨v k, by simpa using h3⟩
  choose W hW using fun k => IsPrecomplete.prec' (I := Ideal.span {(l : Wq l a)}) (fun j => w j k)
    (fun {m j} h => hc h k)
  have hW0 : LTo0 l W := fun r => (hw0 r r).mono fun k hk => by
    obtain ⟨q, hq⟩ := (smodEq_span_pow _ _ _ r).1 (hW k r)
    have h1 : W k = w r k - (l : Wq l a) ^ r * q := by rw [← hq]; ring
    rw [h1]
    exact dvd_sub hk (dvd_mul_right _ _)
  have hLmem : ofRep (K := K) t e W ∈ Sd t K e := Subring.subset_closure ⟨W, hW0, rep_ofRep W⟩
  refine ⟨⟨_, hLmem⟩, fun n => ?_⟩
  choose v hv using fun k => (smodEq_span_pow _ _ _ n).1 (hW k n)
  have hl0 : (l : Wq l a) ^ n ≠ 0 := pow_ne_zero _ (prime_natCast_ne_zero_wittOfTiltFiniteField t (K := K))
  have hv0 : LTo0 l v := fun r => ((hw0 n (r + n)).and (hW0 (r + n))).mono fun k hk => by
    have h1 : (l : Wq l a) ^ n * (l : Wq l a) ^ r ∣ (l : Wq l a) ^ n * v k := by
      rw [← hv k, ← pow_add, add_comm]
      exact dvd_sub hk.1 hk.2
    exact (mul_dvd_mul_iff_left hl0).1 h1
  have hymem : ofRep (K := K) t e v ∈ Sd t K e := Subring.subset_closure ⟨v, hv0, rep_ofRep v⟩
  refine (smodEq_span_pow _ _ _ n).2 ⟨⟨_, hymem⟩, Subtype.ext ?_⟩
  have h1 := rep_sub (hw n) (rep_ofRep (K := K) (t := t) (e := e) W)
  have h2 := rep_pow_mul n (rep_ofRep (K := K) (t := t) (e := e) v)
  have h3 : (fun k => (l : Wq l a) ^ n * v k) = w n - W := funext fun k => by rw [Pi.sub_apply, hv k]
  rw [h3] at h2
  have h4 := eq_of_rep h1 h2
  push_cast
  exact h4


variable (t e) in
theorem isAdicComplete_of (hsd : ∀ F ∈ Sd t K e, F ∈ SdSet t K e) :
    IsAdicComplete (Ideal.span {(l : ↥(Sd t K e))}) ↥(Sd t K e) :=
  { toIsHausdorff := isHausdorff_of t e hsd, toIsPrecomplete := isPrecomplete_of t e hsd }

end GlobalTheory.CrysPrism.Compl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelIndexNeZeroOfCover
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section
namespace GlobalTheory.ClassPet

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem cong_mul {N : ℕ} {a b : GAf L n} (ha : NG.Cong L n N a) (hb : NG.Cong L n N b) :
    NG.Cong L n N (a * b) := by
  refine ⟨Subgroup.mul_mem _ ha.1 hb.1, fun i j => ?_⟩
  choose y hy e using ha.2
  choose z hz e' using hb.2
  have hbU : ∀ k l, (b.1 : Matrix (Fin n) (Fin n) (AL L)) k l ∈ ALint L := hb.1
  refine ⟨∑ k, y i k * (b.1 : Matrix (Fin n) (Fin n) (AL L)) k j + z i j,
    Subring.add_mem _ (Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hy i k) (hbU k j)) (hz i j), ?_⟩
  have hA : (a.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 + (N : AL L) • Matrix.of y := by
    ext k l; simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]; rw [← e]; ring
  have hB : (b.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 + (N : AL L) • Matrix.of z := by
    ext k l; simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]; rw [← e']; ring
  have : ((a * b).1 : Matrix (Fin n) (Fin n) (AL L)) = (a.1 : Matrix _ _ _) * (b.1 : Matrix _ _ _) := rfl
  rw [this]
  conv_lhs => rw [hA, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul]
  rw [hB]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.of_apply, smul_eq_mul]
  ring

theorem cong_one (N : ℕ) : NG.Cong L n N (1 : GAf L n) := by
  refine ⟨Subgroup.one_mem _, fun i j => ⟨0, Subring.zero_mem _, ?_⟩⟩
  simp

theorem cong_inv {N : ℕ} {a : GAf L n} (ha : NG.Cong L n N a) : NG.Cong L n N a⁻¹ := by
  refine ⟨Subgroup.inv_mem _ ha.1, fun i j => ?_⟩
  choose y hy e using ha.2
  have hiU : ∀ k l, ((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) k l ∈ ALint L := Subgroup.inv_mem _ ha.1
  refine ⟨-(∑ k, ((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) i k * y k j),
    Subring.neg_mem _ (Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hiU i k) (hy k j)), ?_⟩
  have hA : (a.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 + (N : AL L) • Matrix.of y := by
    ext k l; simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]; rw [← e]; ring
  have hinv : ((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) * (a.1 : Matrix _ _ _) = 1 := by
    have : (a⁻¹ * a).1 = 1 := by simp
    exact congrArg (fun u : GL (Fin n) (AL L) => (u : Matrix (Fin n) (Fin n) (AL L))) this
  have key : ((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) - 1 =
      -((N : AL L) • (((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) * Matrix.of y)) := by
    calc ((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) - 1
        = ((a⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) - ((a⁻¹).1 : Matrix _ _ _) * (a.1 : Matrix _ _ _) := by rw [hinv]
      _ = _ := by rw [hA, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]; abel
  have := congrFun (congrFun key i) j
  simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.of_apply, smul_eq_mul] at this
  rw [this]; ring


variable (L n) in
def congSub (N : ℕ) : Subgroup (GAf L n) where
  carrier := {κ | NG.Cong L n N κ}
  mul_mem' := cong_mul
  one_mem' := cong_one N
  inv_mem' := cong_inv

theorem congSub_le_umax (N : ℕ) : congSub L n N ≤ Umax L n := fun _ h => h.1

theorem congSub_mul_le (N M : ℕ) : congSub L n (N * M) ≤ congSub L n N := fun _ h => NG.Cong.of_mul_left L n h

end GlobalTheory.ClassPet

namespace GlobalTheory.ClassPet

section Grp
variable {G : Type*} [Group G]

theorem relIndex_ne_zero_of_cover {H K : Subgroup G} (F : Finset G) (hF : ∀ κ ∈ K, ∃ f ∈ F, f⁻¹ * κ ∈ H)
    (hle : H ≤ K) : H.relIndex K ≠ 0 := by
  classical
  haveI : Finite (K ⧸ H.subgroupOf K) := by
    let φ : F → K ⧸ H.subgroupOf K := fun f =>
      if h : (f : G) ∈ K then ((⟨f, h⟩ : K) : K ⧸ H.subgroupOf K) else ((1 : K) : K ⧸ H.subgroupOf K)
    refine Finite.of_surjective φ (fun q => ?_)
    induction q using QuotientGroup.induction_on with
    | H κ =>
      obtain ⟨f, hf, hfκ⟩ := hF κ κ.2
      have hfK : f ∈ K := by
        have := K.mul_mem κ.2 (K.inv_mem (hle hfκ))
        simpa using this
      refine ⟨⟨f, hf⟩, ?_⟩
      simp only [φ, dif_pos hfK]
      exact QuotientGroup.eq.2 (by simpa [Subgroup.mem_subgroupOf] using hfκ)
  show (H.subgroupOf K).index ≠ 0
  exact Subgroup.index_ne_zero_of_finite

theorem exists_cosetReps {H K : Subgroup G} (hle : H ≤ K) (hne : H.relIndex K ≠ 0) :
    ∃ F : Finset G, (∀ u ∈ F, u ∈ K) ∧ (∀ κ ∈ K, ∃! u, u ∈ F ∧ u⁻¹ * κ ∈ H) ∧ F.card = H.relIndex K := by
  classical
  haveI : (H.subgroupOf K).FiniteIndex := ⟨hne⟩
  haveI : Fintype (K ⧸ H.subgroupOf K) := Fintype.ofFinite _
  let o : K ⧸ H.subgroupOf K → G := fun q => ((Quotient.out q : K) : G)
  have ho : Function.Injective o := by
    intro q q' h
    have : Quotient.out q = Quotient.out q' := Subtype.ext h
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', this]
  refine ⟨Finset.univ.image o, ?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hu
    exact (Quotient.out q).2
  · intro κ hκ
    refine ⟨o ((⟨κ, hκ⟩ : K) : K ⧸ H.subgroupOf K), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩, ?_⟩
    · have h := QuotientGroup.eq.1 (QuotientGroup.out_eq' ((⟨κ, hκ⟩ : K) : K ⧸ H.subgroupOf K))
      simpa [Subgroup.mem_subgroupOf, o] using h
    · rintro u ⟨hu, hu'⟩
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hu
      have : q = ((⟨κ, hκ⟩ : K) : K ⧸ H.subgroupOf K) := by
        rw [← QuotientGroup.out_eq' q]
        exact QuotientGroup.eq.2 (by simpa [Subgroup.mem_subgroupOf, o] using hu')
      rw [this]
  · rw [Finset.card_image_of_injective _ ho, Finset.card_univ]
    show _ = (H.subgroupOf K).index
    rw [Subgroup.index, Nat.card_eq_fintype_card]

theorem norm_eq_one_of_relIndex {J K : Subgroup G} (hle : K ≤ J) (hne : K.relIndex J ≠ 0) (χ : J →* ℂˣ)
    (hχ : ∀ κ (h : κ ∈ K), χ ⟨κ, hle h⟩ = 1) (κ : J) : ‖((χ κ : ℂˣ) : ℂ)‖ = 1 := by
  haveI : (K.subgroupOf J).FiniteIndex := ⟨hne⟩
  obtain ⟨i, j, hij, e⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun i : ℕ => ((κ ^ i : J) : J ⧸ K.subgroupOf J))
  have hmem : ((κ ^ i)⁻¹ * κ ^ j : J) ∈ K.subgroupOf J := QuotientGroup.eq.1 e
  have h1 : χ ((κ ^ i)⁻¹ * κ ^ j) = 1 := by
    have := hχ _ (Subgroup.mem_subgroupOf.1 hmem)
    rwa [Subtype.coe_eta] at this
  have h2 : ((χ κ : ℂˣ) : ℂ) ^ i = ((χ κ : ℂˣ) : ℂ) ^ j := by
    rw [map_mul, map_inv, map_pow, map_pow, inv_mul_eq_one] at h1
    have := congrArg (fun u : ℂˣ => (u : ℂ)) h1
    simpa using this
  have h3 : ‖((χ κ : ℂˣ) : ℂ)‖ ^ i = ‖((χ κ : ℂˣ) : ℂ)‖ ^ j := by rw [← norm_pow, ← norm_pow, h2]
  have hpos : 0 < ‖((χ κ : ℂˣ) : ℂ)‖ := norm_pos_iff.2 (Units.ne_zero _)
  by_contra hne1
  exact hij (pow_right_injective₀ hpos hne1 h3)

end Grp

section Sum
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (a : NG.AlgWt L n)
  (β : a.W →ₗ⋆[ℂ] a.W →ₗ[ℂ] ℂ) (J : Subgroup (GAf L n)) (T : Finset (GAf L n))

theorem classSum_add_left (f₁ f₂ f' : GAf L n → a.W) :
    classSum a β J T (f₁ + f₂) f' = classSum a β J T f₁ f' + classSum a β J T f₂ f' := by
  simp only [classSum, Pi.add_apply, LinearMap.map_add₂, mul_add, Finset.sum_add_distrib]

theorem classSum_smul_left (c : ℂ) (f f' : GAf L n → a.W) :
    classSum a β J T (c • f) f' = starRingEnd ℂ c * classSum a β J T f f' := by
  simp only [classSum, Pi.smul_apply, LinearMap.map_smulₛₗ₂, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => by ring

theorem classSum_add_right (f f₁ f₂ : GAf L n → a.W) :
    classSum a β J T f (f₁ + f₂) = classSum a β J T f f₁ + classSum a β J T f f₂ := by
  simp only [classSum, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem classSum_smul_right (c : ℂ) (f f' : GAf L n → a.W) :
    classSum a β J T f (c • f') = c * classSum a β J T f f' := by
  simp only [classSum, Pi.smul_apply, map_smul, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => by ring

theorem classSum_conj (hβ : IsInvForm a β) (f f' : GAf L n → a.W) :
    classSum a β J T f' f = starRingEnd ℂ (classSum a β J T f f') := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [classSum, map_sum, map_mul, map_inv₀, map_natCast]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [hβ.1 (f' t) (f t)]

end Sum

end GlobalTheory.ClassPet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualAbsIrredGoodPointOfResidualIrred
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.ResAbsIrrGood

theorem absIrrSub_top_of_irred {k L : Type} [Field k] [Field L] [IsAlgClosed L] (φ : k →+* L)
    {Γ : Type} [Group Γ] {a : ℕ} (ha : 0 < a) (ρ : Γ →* GL (Fin a) k)
    (h : ∀ W : Submodule L (Fin a → L),
      (∀ g, ∀ x ∈ W, ((mapRep φ ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L).mulVec x ∈ W) →
        W = ⊥ ∨ W = ⊤) :
    AbsIrrSub ρ ⊤ := by
  classical
  set K := AlgebraicClosure k
  set f := algebraMap k K with hf
  letI : Algebra k L := φ.toAlgebra
  let ψ : K →ₐ[k] L := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hψ : ∀ x : k, ψ (f x) = φ x := fun x => ψ.commutes x
  have hψinj : Function.Injective ψ := ψ.toRingHom.injective
  haveI : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
  have hspan : Submodule.span K ((fun v : Fin a → k => f ∘ v) '' ((⊤ : Submodule k (Fin a → k)) : Set _)) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    rw [← Finset.univ_sum_single v]
    refine Submodule.sum_mem _ fun i _ => ?_
    have : (Pi.single i (v i) : Fin a → K) = v i • (f ∘ (Pi.single i (1 : k) : Fin a → k)) := by
      ext j
      by_cases hij : j = i
      · subst hij; simp
      · simp [Pi.single_apply, hij]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, trivial, rfl⟩)
  unfold AbsIrrSub
  rw [hspan]
  have hmat : ∀ g, ((mapRep φ ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) =
      (((mapRep f ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K)).map ψ := by
    intro g
    ext i j
    simp [mapRep, hψ]
  refine ⟨top_ne_bot, fun _ _ _ => trivial, fun W' _ hW' => ?_⟩
  set W'' : Submodule L (Fin a → L) := Submodule.span L ((fun v : Fin a → K => ψ ∘ v) '' (W' : Set _))
  have hst : ∀ g, ∀ x ∈ W'', ((mapRep φ ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L).mulVec x ∈ W'' := by
    intro g x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, hu, rfl⟩ := hx
      refine Submodule.subset_span ⟨_, hW' g u hu, ?_⟩
      ext p
      rw [hmat g]
      exact RingHom.map_mulVec ψ.toRingHom _ u p
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ _ hx
  rcases h W'' hst with h1 | h1
  · left
    rw [Submodule.span_eq_bot] at h1
    rw [eq_bot_iff]
    intro v hv
    have := h1 _ ⟨v, hv, rfl⟩
    rw [Submodule.mem_bot]
    ext p
    apply hψinj
    simpa using congrFun this p
  · right
    by_contra hne
    obtain ⟨θ, hθ0, hθ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    let c : Fin a → L := fun i => ψ (θ (Pi.single i 1))
    have hθv : ∀ v : Fin a → K, θ v = ∑ i, v i * θ (Pi.single i 1) := by
      intro v
      conv_lhs => rw [← Finset.univ_sum_single v]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show (Pi.single i (v i) : Fin a → K) = v i • (Pi.single i (1 : K) : Fin a → K) by
        ext j; by_cases hij : j = i <;> simp [Pi.single_apply, hij], map_smul, smul_eq_mul]
    have hkill : ∀ X ∈ W'', ∑ i, X i * c i = 0 := by
      intro X hX
      induction hX using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨u, hu, rfl⟩ := hx
        have h0 : θ u = 0 := hθ hu
        have := congrArg ψ (hθv u)
        set_option synthInstance.maxHeartbeats 100000 in
          rw [h0, map_zero, map_sum] at this
        rw [this]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [c]
      | zero => simp
      | add x y _ _ hx hy => simp [add_mul, Finset.sum_add_distrib, hx, hy]
      | smul s x _ hx => simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, hx, mul_zero]
    apply hθ0
    apply LinearMap.pi_ext
    intro i x
    have hci : c i = 0 := by
      have := hkill (Pi.single i 1) (h1 ▸ Submodule.mem_top)
      simpa [Pi.single_apply] using this
    have : θ (Pi.single i 1) = 0 := hψinj (by simpa [c] using hci)
    rw [show (Pi.single i x : Fin a → K) = x • (Pi.single i (1 : K) : Fin a → K) by
      ext j; by_cases hij : j = i <;> simp [Pi.single_apply, hij], map_smul, this]
    simp

end GlobalTheory.ResAbsIrrGood

theorem GlobalTheory.PtCore.residualAbsIrredGoodPoint_of_residualIrred : ∀ D : D7, ResidualIrreducibleRankR D → GlobalTheory.PtCore.ResAbsIrr D := by
  intro D hN9 a π hπ ρ hρ
  obtain ⟨hcont, r, hr, e, he⟩ := hρ
  have hdec : Formalism.MainNotions.TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) a (fun _ => r) (fun _ => ρ) π := ⟨e, he⟩
  have hrb : IsRhoBar D.nd a (redRep D.nd a ρ) := by
    refine ⟨isOpen_ker_redRep D a ρ hcont, ?_⟩
    intro x w hw B σ hB hσ
    have e2 := congrArg (Polynomial.map (IsLocalRing.residue (D.nd.O a)))
      (charpoly_of_decomp D a _ _ π hdec σ)
    rw [Polynomial.map_mul, Polynomial.map_prod, ← Matrix.charpoly_map, ← Matrix.charpoly_map] at e2
    rw [heckePol_res D a x π w, ← hr.2.2 w hw B σ hB hσ, ← Matrix.charpoly_map]
    refine (e2.trans ?_).symm
    congr 1
    refine Finset.prod_congr rfl fun c _ => ?_
    simp
  have hHG : HG D.nd D.naut a := ⟨π, (D.Zgood_tie a π).1 hπ⟩
  have hirr := (hN9 a hHG _ hrb).1
  have hpos : 0 < D.R.r := by
    have := D.R.two_le_m
    unfold Ranks.r
    omega
  exact GlobalTheory.ResAbsIrrGood.absIrrSub_top_of_irred (D.naut.kFbar a) hpos _
    fun W hW => hirr W fun g _ x hx => hW g x hx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanRepMatrixEqTopOfResidueSpanEqTopStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_repMatrix_eq_top_of_residue_span_eq_top : ∀ {Γ A : Type} [Group Γ] [CommRing A] [IsLocalRing A] {r : ℕ} (ρ : Γ →* GL (Fin r) A), Submodule.span (IsLocalRing.ResidueField A) (Set.range (mat (mapRep (IsLocalRing.residue A) ρ))) = ⊤ → Submodule.span A (Set.range (mat ρ)) = ⊤ := by
  first | exact @GlobalTheory.span_mat_eq_top_of_residue | exact GlobalTheory.span_mat_eq_top_of_residue | (intros; apply GlobalTheory.span_mat_eq_top_of_residue <;> assumption)
end

