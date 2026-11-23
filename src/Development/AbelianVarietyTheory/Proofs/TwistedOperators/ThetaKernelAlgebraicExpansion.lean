module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LinearIndependentWave
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0592

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.AlgWave

open GlobalTheory.PlaceModel

abbrev Qb : IntermediateField ℚ ℂ := algebraicClosure ℚ ℂ

variable {G : Type} [AddCommGroup G]

def algSpan (χ : G → G → ℂ) (X Y L : AddSubgroup G) : Submodule Qb (G → ℂ) :=
  Submodule.span Qb {Φ | ∃ x ∈ X, ∃ y ∈ Y, Φ = wave χ L x y}

theorem smul_mem_of_mem {M : Submodule Qb (G → ℂ)} {a : ℂ} (ha : a ∈ Qb) {Φ : G → ℂ} (hΦ : Φ ∈ M) : a • Φ ∈ M :=
  M.smul_mem (⟨a, ha⟩ : Qb) hΦ

variable {χ : G → G → ℂ} {X Y L L' : AddSubgroup G}

theorem wave_mem {x y : G} (hx : x ∈ X) (hy : y ∈ Y) : wave χ L x y ∈ algSpan χ X Y L :=
  Submodule.subset_span ⟨x, hx, y, hy, rfl⟩

theorem trans_mem {Φ : G → ℂ} (hΦ : Φ ∈ algSpan χ X Y L) {x : G} (hx : x ∈ X) :
    (fun t => Φ (t + x)) ∈ algSpan χ X Y L := by
  induction hΦ using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    rw [wave_trans]
    exact wave_mem (add_mem hx ha) hb
  | zero => exact zero_mem _
  | add f g _ _ hf hg => exact add_mem hf hg
  | smul c f _ hf => exact Submodule.smul_mem _ c hf

theorem modul_mem (h : IsBichar χ) (hχ : ∀ x ∈ X, ∀ y ∈ Y, χ x y ∈ Qb) {Φ : G → ℂ} (hΦ : Φ ∈ algSpan χ X Y L) {y : G}
    (hy : y ∈ Y) : (fun t => χ t y * Φ t) ∈ algSpan χ X Y L := by
  induction hΦ using Submodule.span_induction with
  | mem _ hh =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hh
    rw [wave_modul h]
    exact smul_mem_of_mem (hχ _ (neg_mem ha) _ hy) (wave_mem ha (add_mem hy hb))
  | zero => convert (algSpan χ X Y L).zero_mem using 1; funext t; simp
  | add f g _ _ hf hg => convert add_mem hf hg using 1; funext t; simp [mul_add]
  | smul c f _ hf =>
    convert Submodule.smul_mem _ c hf using 1
    funext t
    show χ t y * ((c : ℂ) * f t) = (c : ℂ) * (χ t y * f t)
    ring
end GlobalTheory.AlgWave

namespace GlobalTheory.AlgWave

open GlobalTheory.PlaceModel

variable {G : Type} [AddCommGroup G] {χ : G → G → ℂ} {X Y L L' : AddSubgroup G}

theorem ind_nsmul_mem (h : IsBichar χ) (hχ : ∀ x ∈ X, ∀ y ∈ Y, χ x y ∈ Qb) (hL : L ≤ X) (hL' : L' ≤ Y)
    (hLL' : ∀ u ∈ L, ∀ y ∈ L', χ u y = 1)
    (hX : ∀ x ∈ X, (∀ y ∈ L', χ x y = 1) → x ∈ L) {k : ℕ}
    (dX : ∀ x ∈ X, ∃ x' ∈ X, k • x' = x) (dY : ∀ y ∈ Y, ∃ y' ∈ Y, k • y' = y)
    (R : Set G) (hR : R.Finite) (hfin : ∀ t ∈ L, ∃ r ∈ R, ∃ u ∈ L, t = r + k • u) :
    ind (L.map (nsmulAddMonoidHom k)) ∈ algSpan χ X Y L := by
  classical
  set K := L.map (nsmulAddMonoidHom k) with hK
  have hKL : K ≤ L := by
    rintro _ ⟨u, hu, rfl⟩
    exact nsmul_mem hu k
  have key : ∀ R : Finset G, ∃ Φ ∈ algSpan χ X Y L, (∀ t ∈ K, Φ t = 1) ∧ (∀ t ∉ L, Φ t = 0) ∧
      ∀ r ∈ R, r ∈ L → r ∉ K → ∀ u ∈ K, Φ (r + u) = 0 := by
    intro R
    induction R using Finset.induction_on with
    | empty =>
      refine ⟨ind L, ?_, fun t ht => ?_, fun t ht => ?_, by simp⟩
      · rw [← wave_zero h]; exact wave_mem (zero_mem _) (zero_mem _)
      · simp [ind, hKL ht]
      · simp [ind, ht]
    | insert r R _ ih =>
      obtain ⟨Φ, hΦ, h1, h2, h3⟩ := ih
      by_cases hr : r ∈ L ∧ r ∉ K
      · obtain ⟨r', hr', rfl⟩ := dX r (hL hr.1)
        have : ¬ ∀ y ∈ L', χ r' y = 1 := fun hh => hr.2 ⟨r', hX r' hr' hh, rfl⟩
        push_neg at this
        obtain ⟨y, hy, hne⟩ := this
        obtain ⟨y', hy', rfl⟩ := dY y (hL' hy)
        rw [← h.nsmul] at hne
        have hK1 : ∀ u ∈ K, χ u y' = 1 := by
          rintro _ ⟨u, hu, rfl⟩
          exact (h.nsmul k u y').trans (hLL' u hu _ hy)
        have hne' : χ (k • r') y' - 1 ≠ 0 := sub_ne_zero.2 hne
        have hq : χ (k • r') y' ∈ Qb := hχ _ (hL hr.1) _ hy'
        refine ⟨(χ (k • r') y' - 1)⁻¹ • (χ (k • r') y' • Φ - fun t => χ t y' * Φ t),
          smul_mem_of_mem (inv_mem (sub_mem hq (one_mem _)))
            (sub_mem (smul_mem_of_mem hq hΦ) (modul_mem h hχ hΦ hy')), fun t ht => ?_,
          fun t ht => ?_, fun s hs hsL hsK u hu => ?_⟩
        · simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, h1 t ht, hK1 t ht, mul_one]
          exact inv_mul_cancel₀ hne'
        · simp [h2 t ht]
        · rcases Finset.mem_insert.1 hs with rfl | hs
          · simp [h.left, hK1 u hu]
          · simp [h3 s hs hsL hsK u hu]
      · refine ⟨Φ, hΦ, h1, h2, fun s hs hsL hsK u hu => ?_⟩
        rcases Finset.mem_insert.1 hs with rfl | hs
        · exact absurd ⟨hsL, hsK⟩ hr
        · exact h3 s hs hsL hsK u hu
  obtain ⟨Φ, hΦ, h1, h2, h3⟩ := key hR.toFinset
  convert hΦ using 1
  funext t
  by_cases ht : t ∈ K
  · simp [ind, ht, h1 t ht]
  · rw [ind, if_neg ht]
    by_cases htL : t ∈ L
    · obtain ⟨r, hr, u, hu, rfl⟩ := hfin t htL
      have huK : k • u ∈ K := ⟨u, hu, rfl⟩
      exact (h3 r (hR.mem_toFinset.2 hr) ((add_mem_cancel_right (hKL huK)).1 htL)
        (fun hh => ht (add_mem hh huK)) _ huK).symm
    · exact (h2 t htL).symm

theorem mem_of_finite_cosets {K : AddSubgroup G} (hK : ind K ∈ algSpan χ X Y L) (P : Finset G) :
    ∀ Φ : G → ℂ, (∀ t, Φ t ∈ Qb) → (∀ t, Φ t ≠ 0 → t ∈ X) → (∀ u ∈ K, ∀ t, Φ (t + u) = Φ t) →
      (∀ t, Φ t ≠ 0 → ∃ s ∈ P, ∃ u ∈ K, t = s + u) → Φ ∈ algSpan χ X Y L := by
  classical
  induction P using Finset.induction_on with
  | empty =>
    intro Φ _ _ _ h3
    convert (algSpan χ X Y L).zero_mem using 1
    funext t
    by_contra ht
    simpa using h3 t ht
  | insert s P _ ih =>
    intro Φ h0 h1 h2 h3
    by_cases hs : Φ s = 0
    · refine ih Φ h0 h1 h2 fun t ht => ?_
      obtain ⟨s', hs', u, hu, rfl⟩ := h3 t ht
      rcases Finset.mem_insert.1 hs' with rfl | hs'
      · exact absurd ((h2 u hu _).trans hs) ht
      · exact ⟨s', hs', u, hu, rfl⟩
    · have hsX := h1 s hs
      have hm := smul_mem_of_mem (h0 s) (trans_mem hK (neg_mem hsX))
      have hval : ∀ t, (Φ - Φ s • fun t => ind K (t + -s)) t ≠ 0 → Φ t ≠ 0 ∧ t + -s ∉ K := by
        intro t ht
        have hn : t + -s ∉ K := fun hh => ht (by
          have := h2 _ hh s
          rw [show s + (t + -s) = t by abel] at this
          simp [ind, hh, this])
        exact ⟨by simpa [ind, hn] using ht, hn⟩
      have h0' : ∀ t, (Φ - Φ s • fun t => ind K (t + -s)) t ∈ Qb := fun t => by
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        refine sub_mem (h0 t) (mul_mem (h0 s) ?_)
        unfold ind
        split_ifs
        exacts [one_mem _, zero_mem _]
      have := ih (Φ - Φ s • fun t => ind K (t + -s)) h0' (fun t ht => h1 t (hval t ht).1) (fun u hu t => by
        simp only [Pi.sub_apply, Pi.smul_apply, h2 u hu]
        rw [add_right_comm, ind_add K _ hu]) fun t ht => by
          obtain ⟨s', hs', u, hu, rfl⟩ := h3 t (hval t ht).1
          rcases Finset.mem_insert.1 hs' with rfl | hs'
          · exact absurd (by simpa using hu) (hval _ ht).2
          · exact ⟨s', hs', u, hu, rfl⟩
      simpa using add_mem this hm

theorem mem_algSpan (h : IsBichar χ) (hχ : ∀ x ∈ X, ∀ y ∈ Y, χ x y ∈ Qb)
    (hL : L ≤ X) (hL' : L' ≤ Y) (hLL' : ∀ u ∈ L, ∀ y ∈ L', χ u y = 1) (hX : ∀ x ∈ X, (∀ y ∈ L', χ x y = 1) → x ∈ L)
    (dX : ∀ k : ℕ, 0 < k → ∀ x ∈ X, ∃ x' ∈ X, k • x' = x) (dY : ∀ k : ℕ, 0 < k → ∀ y ∈ Y, ∃ y' ∈ Y, k • y' = y)
    (tf : ∀ k : ℕ, 0 < k → Function.Injective fun t : G => k • t)
    (hfin : ∀ k : ℕ, 0 < k → ∃ R : Set G, R.Finite ∧ ∀ t ∈ L, ∃ r ∈ R, ∃ u ∈ L, t = r + k • u)
    (Φ : G → ℂ) (h0 : ∀ t, Φ t ∈ Qb) (h1 : ∀ t, Φ t ≠ 0 → t ∈ X) (k : ℕ) (hk : 0 < k)
    (h2 : ∀ u ∈ L, ∀ t, Φ (t + k • u) = Φ t) (h3 : ∀ t, Φ t ≠ 0 → k • t ∈ L) : Φ ∈ algSpan χ X Y L := by
  obtain ⟨R, hR, hR'⟩ := hfin k hk
  obtain ⟨R2, hR2, hR2'⟩ := hfin (k * k) (Nat.mul_pos hk hk)
  have hP : ((fun t : G => k • t) ⁻¹' R2).Finite := hR2.preimage (tf k hk).injOn
  refine mem_of_finite_cosets (K := L.map (nsmulAddMonoidHom k))
    (ind_nsmul_mem h hχ hL hL' hLL' hX (dX k hk) (dY k hk) R hR hR') hP.toFinset Φ h0 h1 ?_ fun t ht => ?_
  · rintro _ ⟨u, hu, rfl⟩
    exact h2 u hu
  · obtain ⟨r, hr, u, hu, e⟩ := hR2' _ (h3 t ht)
    refine ⟨t - k • u, hP.mem_toFinset.2 ?_, k • u, ⟨u, hu, rfl⟩, by abel⟩
    change k • (t - k • u) ∈ R2
    rwa [smul_sub, e, smul_smul, add_sub_cancel_right]

end GlobalTheory.AlgWave

namespace GlobalTheory.BotFourier

open GlobalTheory.PlaceModel GlobalTheory.AlgWave GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle

variable {D : D7}

theorem nsmul_finite {S T : HSp D} {x : WO S T} (hx : x.map (infPart D) = 0) (k : ℕ) :
    (k • x).map (infPart D) = 0 := by
  refine Matrix.ext fun i j => ?_
  have : infPart D (x i j) = 0 := congrFun (congrFun hx i) j
  change infPart D (k • x i j) = 0
  rw [nsmul_eq_mul, RingHom.map_mul, this, mul_zero]

theorem bichar_pow_left {G : Type} [AddCommGroup G] {χ : G → G → ℂ} (h : IsBichar χ) (k : ℕ) (x y : G) :
    χ (k • x) y = χ x y ^ k := by
  induction k with
  | zero => simp [h.zero_left]
  | succ k ih => rw [succ_nsmul, h.left, ih, pow_succ]

theorem psi_mem {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {x y : WO S T} (hx : x.map (infPart D) = 0)
    (hy : y.map (infPart D) = 0) : ψ (symplO S T x y) ∈ Qb := by
  obtain ⟨k, hk, hkx⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO'
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hS)
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hT) x hx
  obtain ⟨k', hk', hky⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO'
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hS)
    (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hT) y hy
  have hd := ((GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT).1 _ (nsmul_finite hx k)).1 hkx _ hky
  have hb : IsBichar (fun x y : WO S T => ψ (symplO S T x y)) := by
    have hl (a b y : WO S T) : symplO S T (a + b) y = symplO S T a y + symplO S T b y := by
      unfold symplO hO
      simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)]
    have hr (x a b : WO S T) : symplO S T x (a + b) = symplO S T x a + symplO S T x b := by
      unfold symplO hO
      simp only [Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib, map_add (f := _)]
    have hz₁ (y : WO S T) : symplO S T 0 y = 0 := by simpa using hl 0 0 y
    have hz₂ (y : WO S T) : symplO S T y 0 = 0 := by simpa using hr y 0 0
    exact ⟨fun a b y => by rw [hl, AddChar.map_add_eq_mul],
      fun a b y => by rw [hr, AddChar.map_add_eq_mul],
      fun y => by rw [hz₁, AddChar.map_zero_eq_one],
      fun y => by rw [hz₂, AddChar.map_zero_eq_one]⟩
  rw [bichar_pow_left hb, ← hb.nsmul, bichar_pow_left hb, ← pow_mul] at hd
  refine mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow (n := k' * k) (Nat.mul_pos hk' hk) ?_)
  rw [hd]
  exact isAlgebraic_one

theorem psiH_mem {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {x y : WO S T} (hx : x.map (infPart D) = 0)
    (hy : y.map (infPart D) = 0) : ψ (symplOH S T x y) ∈ Qb := by
  have h2 : symplOH S T x y + symplOH S T x y = symplO S T x y := by
    unfold symplOH
    rw [← add_mul, ← map_add (f := _)]
    norm_num
  have hp : ψ (symplOH S T x y) ^ 2 = ψ (symplO S T x y) := by
    rw [sq, ← AddChar.map_add_eq_mul, h2]
  exact mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow (n := 2) two_pos
    (hp ▸ mem_algebraicClosure_iff.1 (psi_mem hψ hS hT hx hy)))

theorem stdFst_mem {ν : (AE D)ˣ →* Circle} (hν : Continuous ν) {e : AE D} {S : Finset (Pl D.host.E)}
    (he : IsIdemSum e S) (I : Ideal (𝓞 D.host.E)) (A WW : HSp D) (βA : GL (Fin A.rank) (Lev.EAf D))
    (βW : GL (Fin WW.rank) (Lev.EAf D)) (x : WO A WW) : stdFst ν e I A WW βA βW x ∈ Qb := by
  obtain ⟨-, -, -, m, hm, hord⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D ν hν
  unfold stdFst
  split_ifs with hc
  · unfold unitChar
    split_ifs with hu
    · obtain ⟨h1, h2, h3⟩ := hu.choose_spec
      have hN : IsIntM (topL A.rank (frMapO A WW βA βW x)) := StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.isIntM_topL hc.2.1
      have hdet : (topL A.rank (frMapO A WW βA βW x)).det ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
        let B : Matrix (Fin A.rank) (Fin A.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E) := fun a b => ⟨_, hN a b⟩
        have hB : topL A.rank (frMapO A WW βA βW x) = (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype.mapMatrix B := rfl
        rw [hB, ← RingHom.map_det]
        exact (B.det).2
      have hE : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
        GlobalTheory.IdemRes.toEAf_mem_of_finPart (GlobalTheory.AdIdem.idempotent_mem_intAE D _
          (by rw [← RingHom.map_mul, GlobalTheory.PlaceDatum.idemSum_mul_self he]))
      have hfu : Formalism.L2.Pj.FinUnit hu.choose := ⟨h1, GlobalTheory.PlaceDatum.finPart_mem_of_toEAf (by
        rw [h2]; exact add_mem (sub_mem (one_mem _) hE) (mul_mem hE hdet)), GlobalTheory.PlaceDatum.finPart_mem_of_toEAf h3⟩
      have hpow := hord _ hfu
      refine mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow (n := m) hm ?_)
      have e1 : (((ν hu.choose)⁻¹ : Circle) : ℂ) ^ m = Circle.coeHom (((ν hu.choose) ^ m)⁻¹) := by
        rw [← inv_pow, map_pow]; rfl
      rw [e1, hpow, inv_one, map_one]
      exact isAlgebraic_one
    · exact zero_mem _
  · exact zero_mem _

end GlobalTheory.BotFourier

namespace GlobalTheory.BotFourier

open GlobalTheory.PlaceModel GlobalTheory.AlgWave


end GlobalTheory.BotFourier
