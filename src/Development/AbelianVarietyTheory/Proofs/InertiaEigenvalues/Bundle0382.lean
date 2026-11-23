module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0232
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0305

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimeNotMemSqAndDeltaNotMem
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.LSq

def cInt (l : ℕ) (n : ℕ) : ℤ := ((n : ℤ) - (n : ℤ) ^ l) / l

theorem l_mul_cInt (l : ℕ) [hl : Fact l.Prime] (n : ℕ) : (l : ℤ) * cInt l n = (n : ℤ) - (n : ℤ) ^ l := by
  unfold cInt
  apply Int.mul_ediv_cancel'
  have h : (((n : ℤ) - (n : ℤ) ^ l : ℤ) : ZMod l) = 0 := by
    push_cast; rw [ZMod.pow_card, sub_self]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h

theorem δ_natCast (l : ℕ) [hl : Fact l.Prime] {A : Type} [CommRing A] (D : Delta l A) (n : ℕ) :
    D.δ (n : A) = ((cInt l n : ℤ) : A) := by
  induction n with
  | zero =>
    have : cInt l 0 = 0 := by
      unfold cInt; simp [zero_pow hl.out.ne_zero]
    simp [this, Delta.δ_zero]
  | succ n ih =>
    have h := D.δ_add (n : A) 1
    rw [D.δ_one, ih] at h
    push_cast
    rw [h]
    have key : cInt l (n + 1) = cInt l n - ∑ k ∈ Finset.Ioo 0 l, ((l.choose k / l : ℕ) : ℤ) * (n : ℤ) ^ k := by
      have h0 : (l : ℤ) ≠ 0 := by exact_mod_cast hl.out.ne_zero
      apply mul_left_cancel₀ h0
      have e1 := l_mul_cInt l (n + 1)
      have e2 := l_mul_cInt l n
      have h5 : ((n : ℤ) + 1) ^ l = (n : ℤ) ^ l + 1 ^ l + (l : ℤ) *
          ∑ k ∈ Finset.Ioo 0 l, ((l.choose k / l : ℕ) : ℤ) * (n : ℤ) ^ k * (1 : ℤ) ^ (l - k) := by
        rw [add_pow_prime_eq' hl.out]
        congr 2
        refine Finset.sum_congr rfl fun k _ => by ring
      simp only [one_pow, mul_one] at h5
      push_cast at e1
      rw [mul_sub, e1, e2, h5]; ring
    rw [key, Int.cast_sub, Int.cast_sum]
    simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast, one_pow, mul_one, add_zero]

theorem cInt_self (l : ℕ) [hl : Fact l.Prime] : cInt l l = 1 - (l : ℤ) ^ (l - 1) := by
  have h0 : (l : ℤ) ≠ 0 := by exact_mod_cast hl.out.ne_zero
  apply mul_left_cancel₀ h0
  rw [l_mul_cInt, mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel hl.out.one_le]

theorem δ_l (l : ℕ) [hl : Fact l.Prime] {A : Type} [CommRing A] (D : Delta l A) :
    D.δ (l : A) = 1 - (l : A) ^ (l - 1) := by
  rw [δ_natCast, cInt_self]; push_cast; ring

theorem δ_mem_of_mem_sq (l : ℕ) [hl : Fact l.Prime] {A : Type} [CommRing A] (D : Delta l A) (m : Ideal A)
    (hlm : (l : A) ∈ m) {x : A} (hx : x ∈ m ^ 2) : D.δ x ∈ m := by
  rw [sq] at hx
  have hl0 := hl.out.ne_zero
  suffices x ∈ m ∧ D.δ x ∈ m from this.2
  refine Submodule.mul_induction_on hx (fun a ha b hb => ⟨m.mul_mem_right b ha, ?_⟩) ?_
  · rw [D.δ_mul]
    refine m.add_mem (m.add_mem (m.mul_mem_right _ (m.pow_mem_of_mem ha _ (Nat.pos_of_ne_zero hl0)))
      (m.mul_mem_right _ (m.pow_mem_of_mem hb _ (Nat.pos_of_ne_zero hl0)))) ?_
    exact m.mul_mem_right _ (m.mul_mem_right _ hlm)
  · rintro x y ⟨hx, hδx⟩ ⟨hy, hδy⟩
    refine ⟨m.add_mem hx hy, ?_⟩
    rw [D.δ_add]
    refine m.sub_mem (m.add_mem hδx hδy) (m.sum_mem fun k hk => ?_)
    obtain ⟨hk0, hkl⟩ := Finset.mem_Ioo.1 hk
    exact m.mul_mem_left _ (m.pow_mem_of_mem hy _ (Nat.sub_pos_of_lt hkl))

theorem l_not_mem_sq : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (m : Ideal A),
    m ≠ ⊤ → (l : A) ∈ m → (l : A) ∉ m ^ 2 ∧ D.δ (l : A) ∉ m := by
  intro l hl A _ D m hm hlm
  have hδ : D.δ (l : A) ∉ m := by
    intro h
    rw [δ_l] at h
    have h2 : (l : A) ^ (l - 1) ∈ m :=
      m.pow_mem_of_mem hlm _ (Nat.sub_pos_of_lt hl.out.one_lt)
    exact hm ((Ideal.eq_top_iff_one _).2 (by simpa using m.add_mem h h2))
  exact ⟨fun h => hδ (δ_mem_of_mem_sq l D m hlm h), hδ⟩

end GlobalTheory.BSP.LSq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowDvdTiltUniformizerPowAcrisEventually
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section
namespace GlobalTheory.AcrisPow
variable {l : ℕ} [hl : Fact l.Prime]

theorem eventually_lt_two_pow (A B : ℕ) : ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → A * n + B < 2 ^ n := by
  refine ⟨4 * (A + B + 1), fun n hn => ?_⟩
  set m := 2 * (A + B + 1) with hm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show m ≤ n by omega)
  have hk : m ≤ k := by omega
  have h1 : m < 2 ^ m := Nat.lt_two_pow_self
  have h2 : k < 2 ^ k := Nat.lt_two_pow_self
  have h3 : (m + 1) * (k + 1) ≤ 2 ^ m * 2 ^ k := Nat.mul_le_mul h1 h2
  rw [pow_add]
  have h4 : A * (m + k) + B < (m + 1) * (k + 1) := by nlinarith
  omega

theorem dvd_pow_acris0 (ξ : Ainf l) (hξ : Per.θ l ξ = 0) :
    ((l : ℕ) : Per.Acris0 l) ∣ algebraMap (Ainf l) (Per.Acris0 l) ξ ^ l := by
  have hp : l.Prime := Fact.out
  have hlu : IsUnit ((l : ℕ) : Per.AinfP l) := by
    have := IsLocalization.Away.algebraMap_isUnit (S := Per.AinfP l) ((l : ℕ) : Per.Ainf l)
    rwa [map_natCast] at this
  have hf : IsUnit ((l.factorial : ℕ) : Per.AinfP l) := by
    obtain ⟨c, hc⟩ := GlobalTheory.Per.exists_factorial_mul_eq_pow_ainf l l
    have h2 := congrArg (algebraMap (Per.Ainf l) (Per.AinfP l)) hc
    rw [map_mul, map_pow, map_natCast, map_natCast] at h2
    exact isUnit_of_mul_isUnit_left (h2 ▸ hlu.pow l)
  obtain ⟨v, hv⟩ := hf.exists_right_inv
  have hx : ((l.factorial : ℕ) : Per.AinfP l) * (v * algebraMap (Per.Ainf l) (Per.AinfP l) ξ ^ l) =
      algebraMap (Per.Ainf l) (Per.AinfP l) ξ ^ l := by rw [← mul_assoc, hv, one_mul]
  generalize v * algebraMap (Per.Ainf l) (Per.AinfP l) ξ ^ l = x at hx
  have hxD : x ∈ Per.Acris0 l := GlobalTheory.RingIface.dividedPower_mem_Acris0 l ξ l x hξ hx
  have hfac : ((l.factorial : ℕ) : Per.AinfP l) =
      ((l : ℕ) : Per.AinfP l) * (((l - 1).factorial : ℕ) : Per.AinfP l) := by
    rw [← Nat.cast_mul, Nat.mul_factorial_pred hp.ne_zero]
  refine ⟨(((l - 1).factorial : ℕ) : Per.Acris0 l) * ⟨x, hxD⟩, Subtype.ext ?_⟩
  simp only [SubmonoidClass.coe_pow, Subalgebra.coe_algebraMap, Subalgebra.coe_mul, SubringClass.coe_natCast]
  rw [← hx, hfac, mul_assoc]

theorem dvd_X_pow {K : FinExt l} (bk : BK K) :
    (l : Per.Acris l) ∣ ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) X ^ (bk.Ep.natDegree * l) := by
  set f := algebraMap (Ainf l) (Per.Acris l)
  have hξ : Per.θ l (bk.ev bk.E) = 0 := by
    rw [← RingHom.mem_ker, ← bk.span_ev]; exact Ideal.mem_span_singleton_self _
  have h1 : (l : Per.Acris l) ∣ f (bk.ev bk.E) ^ l := by
    have := map_dvd (algebraMap (Per.Acris0 l) (Per.Acris l)) (dvd_pow_acris0 _ hξ)
    rw [map_natCast, map_pow, ← GlobalTheory.RingIface.tower l] at this
    exact this
  have h2 : (l : Per.Acris l) ∣ f (bk.ev bk.E) - f (bk.ev X) ^ bk.Ep.natDegree := by
    have := map_dvd f (AinfDiv.dvd_E bk)
    rwa [map_natCast, map_sub, map_pow] at this
  have h3 : (l : Per.Acris l) ∣ f (bk.ev bk.E) ^ l - (f (bk.ev X) ^ bk.Ep.natDegree) ^ l :=
    h2.trans (sub_dvd_pow_sub_pow _ _ l)
  have h4 := dvd_sub h1 h3
  rw [sub_sub_cancel, ← pow_mul] at h4
  simpa [RingHom.comp_apply] using h4

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (c M : ℕ), ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
    (l : Per.Acris l) ^ (c * n + M) ∣ ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) X ^ (l ^ n - 1) := by
  intro l _ K bk c M
  set e := bk.Ep.natDegree
  obtain ⟨n₀, hn₀⟩ := eventually_lt_two_pow (e * l * c) (e * l * M)
  refine ⟨n₀, fun n hn => ?_⟩
  have hlt := hn₀ n hn
  have h2l : 2 ^ n ≤ l ^ n := Nat.pow_le_pow_left (Fact.out : l.Prime).two_le n
  have hle : e * l * (c * n + M) ≤ l ^ n - 1 := by
    have : e * l * (c * n + M) = e * l * c * n + e * l * M := by ring
    omega
  have hk := pow_dvd_pow_of_dvd (dvd_X_pow bk) (c * n + M)
  rw [← pow_mul] at hk
  exact hk.trans (pow_dvd_pow _ hle)

end GlobalTheory.AcrisPow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismLocalizationSpanNonZeroDivisorBoundedTorsio
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem pow_mul_eq_zero_of_invertible {A : Type} [CommRing A] (I : Ideal A) (hI : Module.Invertible A ↥I)
    (f c : A) (h : ∀ x ∈ I, ∃ k : ℕ, f ^ k * (c * x) = 0) : ∃ K : ℕ, f ^ K * c = 0 := by
  classical
  have hfg : I.FG := Module.Finite.iff_fg.1 inferInstance
  obtain ⟨S, hS⟩ := hfg
  let k : A → ℕ := fun x => if hx : x ∈ I then (h x hx).choose else 0
  have hk : ∀ x ∈ I, f ^ k x * (c * x) = 0 := fun x hx => by
    simp only [k, dif_pos hx]; exact (h x hx).choose_spec
  refine ⟨S.sup k, ?_⟩
  have hle : I ≤ LinearMap.ker (LinearMap.mulLeft A (f ^ S.sup k * c)) := by
    rw [← hS, Submodule.span_le]
    intro x hx
    have hxI : x ∈ I := hS ▸ Submodule.subset_span hx
    have hkx : k x ≤ S.sup k := Finset.le_sup (f := k) hx
    rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.mulLeft_apply]
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hkx
    rw [hj, pow_add]
    linear_combination (f ^ j) * hk x hxI
  apply eq_of_smul_eq_smul (α := ↥I)
  intro y
  have := hle y.2
  rw [LinearMap.mem_ker, LinearMap.mulLeft_apply] at this
  ext
  simp [this]

theorem locAway_span_nzd_bdd (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B : Obj l R) (f d : B.A)
    (hG : GenAway B f d) (M : Submonoid B.A) (hf : f ∈ M) :
    B.I.map (algebraMap B.A (Localization M)) = Ideal.span {algebraMap B.A (Localization M) d} ∧
    algebraMap B.A (Localization M) d ∈ nonZeroDivisors (Localization M) ∧
    ∃ N : ℕ, ∀ (x : Localization M) (m : ℕ), (l : Localization M) ^ m * x ∈
      Ideal.span {algebraMap B.A (Localization M) d} →
      (l : Localization M) ^ N * x ∈ Ideal.span {algebraMap B.A (Localization M) d} := by
  set φ := algebraMap B.A (Localization M) with hφ
  have hu : IsUnit (φ f) := IsLocalization.map_units (Localization M) (⟨f, hf⟩ : M)
  have h1 : B.I.map φ = Ideal.span {φ d} := by
    refine le_antisymm ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      obtain ⟨k, hk⟩ := hG.2 x hx
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hk
      rw [Ideal.mem_comap, ← Ideal.unit_mul_mem_iff_mem _ (hu.pow k), ← map_pow, ← map_mul, ← hc, map_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.mem_map_of_mem _ hG.1
  refine ⟨h1, ?_, ?_⟩
  · rw [mem_nonZeroDivisors_iff_right]
    intro x hx
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective M x
    rw [mul_comm, hφ, IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_zero_iff] at hx
    obtain ⟨t, ht⟩ := hx
    obtain ⟨K, hK⟩ := pow_mul_eq_zero_of_invertible B.I B.inv f ((t : B.A) * a) (fun x hx => by
      obtain ⟨k, hk⟩ := hG.2 x hx
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hk
      exact ⟨k, by linear_combination c * ht - (t : B.A) * a * hc⟩)
    rw [IsLocalization.mk'_eq_zero_iff]
    exact ⟨⟨f ^ K * t, M.mul_mem (M.pow_mem hf K) t.2⟩, by simp only; linear_combination hK⟩
  · obtain ⟨n, hn⟩ := B.bdd
    refine ⟨n, fun x m hx => ?_⟩
    rw [← h1] at hx ⊢
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective M x
    have e : ∀ j : ℕ, (l : Localization M) ^ j * IsLocalization.mk' (Localization M) a s =
        IsLocalization.mk' (Localization M) ((l : B.A) ^ j * a) s := fun j => by
      rw [← IsLocalization.mul_mk'_eq_mk'_of_mul, map_pow, map_natCast]
    rw [e, IsLocalization.mk'_mem_map_algebraMap_iff] at hx ⊢
    obtain ⟨s', hs', hI⟩ := hx
    refine ⟨s', hs', ?_⟩
    have h0 : (l : B.A ⧸ B.I) ^ m * Ideal.Quotient.mk B.I (s' * a) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk B.I), ← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      convert hI using 1; ring
    have h2 := hn _ ⟨m, h0⟩
    rw [← map_natCast (Ideal.Quotient.mk B.I), ← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at h2
    convert h2 using 1; ring

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RangeAdjointLeOfComp
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

noncomputable section

namespace GlobalTheory.EtaJoin

theorem prj_mul_goodOp {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
    {B : BlockDat K G Pl0} {ℓ : Lvl K G} (Z : Submodule K B.S.Forms) {v0 : InfinitePlace K} {s : ℕ}
    (h : BlockHyp B ℓ v0 s) :
    B.lPr ℓ Z * B.S.lvlOp B.r ℓ.P ℓ.ψ (idemOf ℓ.X) = B.lPr ℓ Z := by
  have hc := idempotent_central K G ℓ.X h.irr
  have h1 := (level_operator_spec K v0 h.conj B.S (h.ok.hpos v0) G B.r h.ok.act ℓ.P ℓ.ψ (idemOf ℓ.X) (hc.2 _).symm).1
  obtain ⟨⟨h2, -⟩, h3⟩ := BlockDat.lf_v_proj h
  have h4 : Formalism.L2.DIV.goodAt ℓ.X ℓ.P ℓ.ψ * idemOf ℓ.X = Formalism.L2.DIV.goodAt ℓ.X ℓ.P ℓ.ψ := by
    unfold Formalism.L2.DIV.goodAt
    rw [mul_assoc, hc.2, ← mul_assoc, hc.1]
  have h5 : B.vPr ℓ * B.S.gaMat B.r (idemOf ℓ.X) = B.vPr ℓ := by
    calc B.vPr ℓ * B.S.gaMat B.r (idemOf ℓ.X)
        = B.vPr ℓ * B.vE ℓ * B.vPr ℓ * B.S.gaMat B.r (idemOf ℓ.X) := by rw [h2, Matrix.one_mul]
      _ = B.vPr ℓ * (B.vE ℓ * B.vPr ℓ * B.S.gaMat B.r (idemOf ℓ.X)) := by simp only [Matrix.mul_assoc]
      _ = B.vPr ℓ * (B.vE ℓ * B.vPr ℓ) := by rw [h3, ← (group_action_matrix_hom K B.S G B.r).2, h4]
      _ = B.vPr ℓ := by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  unfold BlockDat.lPr
  rw [Matrix.mul_assoc, h1, ← Matrix.mul_assoc, Matrix.mul_assoc (B.Pq ℓ Z), h5]

theorem range_adjoint_le_of_comp {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (θ : V →ₗ[ℂ] W) (e : V →ₗ[ℂ] V)
    (hs : e.IsSymmetric) (h : θ ∘ₗ e = θ) : LinearMap.range (LinearMap.adjoint θ) ≤ LinearMap.range e := by
  rintro y ⟨x, rfl⟩
  refine ⟨LinearMap.adjoint θ x, ?_⟩
  refine ext_inner_right ℂ fun z => ?_
  rw [hs (LinearMap.adjoint θ x) z, LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_left]
  have := LinearMap.congr_fun h z
  rw [LinearMap.comp_apply] at this
  rw [this]

theorem thetaCut_of_tie : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (m : ℕ) (A : FamIn D.what₂.LL G Pl0 T m) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup) (eMt : ∀ (i : Fin m) (t : T), (Fin (lDim D A P ψ i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)) (s : ℕ), A.fam.Ok s → ∀ (S0 : IndefData (A.side P ψ Zs)) (jW : ∀ i : Fin m, (Fin (S0.dW i) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Mj ((i : ℕ) + 1)) (i : Fin m) (t : T), FormsTie D.what₂.embLL ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lH D A P ψ i t) (lE D A P ψ i t) (D.what₂.eMt (tup t) ((i : ℕ) + 1)) → (∀ x, D.what₂.thetaP (tup t) ((i : ℕ) + 1) (D.what₂.jMt (tup t) ((i : ℕ) + 1) (eMt i t x)) = jW i ((S0.θ i t).mulVec ((lPrj D A P ψ Zs i t).mulVec x))) → ThetaCut D (tup t) ((i : ℕ) + 1) := by
  intro D G _ _ Pl0 T m A P ψ Zs tup eMt s hOk S0 jW i t hF hθ
  have hB : BlockHyp (A.fam.L i t) (A.fam.lvlA P ψ) A.fam.v0 s := ⟨hOk.conj, fun χ hχ => hOk.irr χ hχ, hOk.lifts i t⟩
  have hP : lPrj D A P ψ Zs i t * lE D A P ψ i t = lPrj D A P ψ Zs i t := prj_mul_goodOp (Zs.Zl i t) hB
  refine range_adjoint_le_of_comp _ _ (D.what₂.eMt_sa _ _) ?_
  refine LinearMap.ext_on_range hF.span fun k => ?_
  rw [LinearMap.comp_apply, hF.op_eq]
  refine (hθ _).trans (Eq.trans ?_ (hθ _).symm)
  rw [Matrix.mulVec_mulVec (Pi.single k 1), hP]

end GlobalTheory.EtaJoin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RegularAndBoundedTorsionOfAdicTopologicalBasis
section
namespace GlobalTheory.BSP

section TopFree

variable {A Q : Type} [CommRing A] [CommRing Q] {i : A →+* Q} {J : Ideal A} {ι : Type}

theorem TopBasis.eq_zero_of_forall_mem (B : TopBasis i J ι) {x : Q} (h : ∀ n : ℕ, x ∈ (J ^ n).map i) :
    x = 0 := by
  have := B.complete
  refine IsHausdorff.haus (I := J.map i) this.toIsHausdorff x fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, ← Ideal.map_pow]
  exact h n

theorem TopBasis.eq_zero_of_coeff (B : TopBasis i J ι) {x : Q} (h : ∀ k, B.c k x = 0) : x = 0 :=
  B.eq_zero_of_forall_mem fun n => by
    simpa using B.approx x n ∅ fun k _ => by rw [h k]; exact zero_mem _

theorem TopBasis.exists_sum (B : TopBasis i J ι) (z : ι → A) (hz : ∀ n : ℕ, {k | z k ∉ J ^ n}.Finite) :
    ∃ y : Q, ∀ n : ℕ, (∑ k ∈ (hz n).toFinset, i (z k) * B.b k) - y ∈ (J ^ n).map i := by
  classical
  have hc := B.complete
  obtain ⟨y, hy⟩ := IsPrecomplete.prec (I := J.map i) hc.toIsPrecomplete
    (f := fun n => ∑ k ∈ (hz n).toFinset, i (z k) * B.b k) (fun {m n} hmn => by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Ideal.map_pow]
      have hsub : (hz m).toFinset ⊆ (hz n).toFinset := fun k hk => by
        simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hk ⊢
        exact fun h => hk (Ideal.pow_le_pow_right hmn h)
      rw [← Finset.sum_sdiff hsub, sub_add_cancel_right]
      refine neg_mem (Ideal.sum_mem _ fun k hk => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_))
      have := (Finset.mem_sdiff.1 hk).2
      simpa using this)
  refine ⟨y, fun n => ?_⟩
  have := hy n
  rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Ideal.map_pow] at this

theorem exists_eq_of_mem_pow_succ_pair (a d : A) (n : ℕ) {x : A}
    (hx : x ∈ (Ideal.span {a} ⊔ Ideal.span {d}) ^ (n + 1)) :
    ∃ u : A, ∃ w ∈ (Ideal.span {a} ⊔ Ideal.span {d}) ^ n, x = a ^ (n + 1) * u + d * w := by
  first
  | exact @_root_.GlobalTheory.PowerBound.main
  | exact _root_.GlobalTheory.PowerBound.main
  | (apply _root_.GlobalTheory.PowerBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowerBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowerBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowerBound.main ..)

theorem mem_pow_of_mul_mem_pow_pair (a d : A) (N : ℕ) (hd : d ∈ nonZeroDivisors A)
    (hN : ∀ (x : A) (m : ℕ), a ^ m * x ∈ Ideal.span {d} → a ^ N * x ∈ Ideal.span {d}) (n : ℕ) {z : A}
    (hz : d * z ∈ (Ideal.span {a} ⊔ Ideal.span {d}) ^ (n + N + 1)) :
    z ∈ (Ideal.span {a} ⊔ Ideal.span {d}) ^ n := by
  have ha : a ∈ Ideal.span {a} ⊔ Ideal.span {d} := Ideal.mem_sup_left (Ideal.mem_span_singleton_self a)
  obtain ⟨u, w, hw, e⟩ := exists_eq_of_mem_pow_succ_pair a d (n + N) hz
  have h1 : a ^ (n + N + 1) * u ∈ Ideal.span {d} :=
    Ideal.mem_span_singleton'.2 ⟨z - w, by linear_combination e⟩
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 (hN u _ h1)
  have h2 : d * (z - (a ^ n * (a * v) + w)) = 0 := by
    linear_combination e - a ^ n * a * hv
  have h3 := (mem_nonZeroDivisors_iff.1 hd).1 _ h2
  rw [sub_eq_zero.1 h3]
  exact add_mem (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow ha _))
    (Ideal.pow_le_pow_right (Nat.le_add_right n N) hw)

end TopFree

theorem TopBasis.regular_and_torsion_bounded (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (Q : Type) [CommRing Q]
    (i : A →+* Q) (d : A) (N : ℕ) (ι : Type) (hd : d ∈ nonZeroDivisors A)
    (hN : ∀ (x : A) (m : ℕ), (l : A) ^ m * x ∈ Ideal.span {d} → (l : A) ^ N * x ∈ Ideal.span {d})
    (B : TopBasis i (Ideal.span {(l : A)} ⊔ Ideal.span {d}) ι) :
    i d ∈ nonZeroDivisors Q ∧
      ∀ (x : Q) (m : ℕ), (l : Q) ^ m * x ∈ Ideal.span {i d} → (l : Q) ^ N * x ∈ Ideal.span {i d} := by
  have hl : ∀ (m : ℕ) (k : ι) (x : Q), B.c k ((l : Q) ^ m * x) = (l : A) ^ m * B.c k x := fun m k x => by
    rw [← B.c_mul, map_pow, map_natCast]
  have hreg : ∀ x : Q, i d * x = 0 → x = 0 := fun x hx =>
    B.eq_zero_of_coeff fun k => (mem_nonZeroDivisors_iff.1 hd).1 _ (by rw [← B.c_mul, hx, map_zero])
  refine ⟨mem_nonZeroDivisors_iff.2 ⟨hreg, fun x hx => hreg x (by rwa [mul_comm])⟩, fun x m hx => ?_⟩
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hx
  have h1 : ∀ k, ∃ z : A, d * z = B.c k ((l : Q) ^ N * x) := fun k => by
    have : (l : A) ^ m * B.c k x ∈ Ideal.span {d} := by
      rw [← hl, ← hy, mul_comm, B.c_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self d)
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 (hN _ _ this)
    exact ⟨z, by rw [hl, ← hz, mul_comm]⟩
  choose z hz using h1
  have hfin : ∀ n : ℕ, {k | z k ∉ (Ideal.span {(l : A)} ⊔ Ideal.span {d}) ^ n}.Finite := fun n =>
    (B.fin ((l : Q) ^ N * x) (n + N + 1)).subset fun k hk h =>
      hk (mem_pow_of_mul_mem_pow_pair _ d N hd hN n (by rwa [hz]))
  obtain ⟨w, hw⟩ := B.exists_sum z hfin
  have key : (l : Q) ^ N * x - i d * w = 0 := B.eq_zero_of_forall_mem fun n => by
    have h2 := B.approx ((l : Q) ^ N * x) n (hfin n).toFinset fun k hk => by
      rw [← hz]
      refine Ideal.mul_mem_left _ _ ?_
      simpa using hk
    have h3 := add_mem h2 (Ideal.mul_mem_left _ (i d) (hw n))
    convert h3 using 1
    simp only [← hz, map_mul, mul_sub, Finset.mul_sum, mul_assoc]
    ring
  rw [sub_eq_zero.1 key]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingOfIntegersFiniteExtIsDVRFiniteUnitIff
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.IntDvr

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), IsDiscreteValuationRing ↥(OL K) ∧
    Module.Finite ℤ_[l] ↥(OL K) ∧ ∀ x : ↥(OL K), IsUnit x ↔ IsUnit (intToOC K x) := by
  intro l _ K
  refine ⟨Formalism.BasicNotions.Examples₂.LB.OL_dvr K, Formalism.BasicNotions.Examples₂.LB.OL_finite K,
    fun x => ⟨fun h => h.map _, fun h => ?_⟩⟩
  rw [Formalism.BasicNotions.Examples₂.LB.isUnit_iff]
  obtain ⟨u, hu⟩ := h
  have h1 := (GlobalTheory.RingBasics.mem_OC _).1 (u : OC l).2
  have h2 := (GlobalTheory.RingBasics.mem_OC _).1 ((u⁻¹ : (OC l)ˣ) : OC l).2
  have h3 : ((u : OC l) : ℂ_[l]) * (((u⁻¹ : (OC l)ˣ) : OC l) : ℂ_[l]) = 1 := by
    have := congrArg (fun z : OC l => (z : ℂ_[l])) u.mul_inv
    exact this
  have h4 : ‖((u : OC l) : ℂ_[l])‖ = 1 := by
    have h5 := congrArg norm h3
    rw [norm_mul, norm_one] at h5
    nlinarith [norm_nonneg ((u : OC l) : ℂ_[l]), norm_nonneg (((u⁻¹ : (OC l)ˣ) : OC l) : ℂ_[l])]
  have h6 : ((u : OC l) : ℂ_[l]) = (((x : ↥K.1) : Om l) : ℂ_[l]) := by
    rw [hu, coe_intToOC]
  rw [h6, PadicComplex.norm_extends] at h4
  exact h4

end GlobalTheory.IntDvr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameLocalRelationDualNumberCocycleStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_local_relation_dualNumber_cocycle : TameQuotient → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (M : ℕ) (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → 1 ≤ M → normV v % (2 * l ^ M) = 1 → ∀ d : G F Ω →* Multiplicative (ZMod (l ^ M)), IsOpen (d.ker : Set (G F Ω)) → (∀ c, ∃ σ ∈ Ine (F := F) A, d σ = c) → ∀ φ : G F Ω, IsFrob A (normV v) φ → ∃ γ ∈ Ine (F := F) A, d γ = Multiplicative.ofAdd 1 ∧ ∀ (K : Type) [Field K] [CharP K l] (W : Type) [AddCommGroup W] [Module K W] (z0 : G F Ω → W), IsLocallyConstant z0 → (∀ g ∈ Dec (F := F) A, ∀ h ∈ Dec (F := F) A, z0 (g * h) = z0 g + z0 h) → (z0 γ = 0 → ∀ σ ∈ Ine (F := F) A, z0 σ = 0) ∧ ∀ (lam : G F Ω → K) (z1 : G F Ω → W), IsLocallyConstant lam → IsLocallyConstant z1 → (∀ g ∈ Dec (F := F) A, ∀ h ∈ Dec (F := F) A, lam (g * h) = lam g + lam h) → (∀ g ∈ Dec (F := F) A, ∀ h ∈ Dec (F := F) A, z1 (g * h) = z1 g + z1 h + lam g • z0 h) → lam γ • z0 φ = lam φ • z0 γ := by
  first | exact @GlobalTheory.TameRel.tame_relation | exact GlobalTheory.TameRel.tame_relation | (intros; apply GlobalTheory.TameRel.tame_relation <;> assumption)
end

