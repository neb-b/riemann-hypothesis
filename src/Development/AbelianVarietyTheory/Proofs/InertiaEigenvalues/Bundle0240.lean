module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0205
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0175
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0193
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0179
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0183
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0028
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthTorsionByQuotientDivisibleLe
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory

theorem length_torsionBy_quotient_divisible_le (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (Z Q : Type) [AddCommGroup Z] [Module O Z] [AddCommGroup Q]
    [Module O Q] (π : Z →ₗ[O] Q) (hs : Function.Surjective π)
    (hdiv : ∀ b : O, b ≠ 0 → ∀ x, π x = 0 → ∃ y, π y = 0 ∧ b • y = x)
    (htor : ∃ x, x ≠ 0 ∧ π x = 0 ∧ ∃ b : O, b ≠ 0 ∧ b • x = 0) (a : O) (ha : a ≠ 0) (k : ℕ)
    (hle : Module.length O ↥(Submodule.torsionBy O Z a) ≤
      ((k + 1 : ℕ) : ℕ∞) * Module.length O (O ⧸ Ideal.span {a})) :
    Module.length O ↥(Submodule.torsionBy O Q a) ≤
      (k : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) := by
  classical

  have hLfin : Module.length O (O ⧸ Ideal.span {a}) ≠ ⊤ := by
    rw [Module.length_ne_top_iff]
    exact isFiniteLength_quotient_span_singleton O (mem_nonZeroDivisors_of_ne_zero ha)

  let φ : Submodule.torsionBy O Z a →ₗ[O] Submodule.torsionBy O Q a :=
    LinearMap.codRestrict (Submodule.torsionBy O Q a) (π ∘ₗ (Submodule.torsionBy O Z a).subtype)
      (fun z => by
        rw [Submodule.mem_torsionBy_iff, LinearMap.comp_apply, Submodule.subtype_apply,
          ← map_smul, (Submodule.mem_torsionBy_iff _ _).mp z.2, map_zero])

  have hφ : Function.Surjective φ := by
    rintro ⟨q, hq⟩
    obtain ⟨z, rfl⟩ := hs q
    have h1 : π (a • z) = 0 := by
      rw [map_smul]; exact (Submodule.mem_torsionBy_iff _ _).mp hq
    obtain ⟨y, hy0, hy⟩ := hdiv a ha (a • z) h1
    refine ⟨⟨z - y, ?_⟩, ?_⟩
    · rw [Submodule.mem_torsionBy_iff, smul_sub, hy, sub_self]
    · apply Subtype.ext
      simp [φ, hy0]
  have hexact := Module.length_eq_add_of_exact (LinearMap.ker φ).subtype φ
    (Submodule.subtype_injective _) hφ (LinearMap.exact_subtype_ker_map φ)

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hdvd_unit : ∀ c : O, ¬ ϖ ∣ c → IsUnit c := by
    intro c hc
    by_contra hnu
    apply hc
    have hmem := (IsLocalRing.mem_maximalIdeal c).mpr hnu
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ,
      Ideal.mem_span_singleton] at hmem
    exact hmem
  obtain ⟨x, hx0, hxK, b, hb0, hbx⟩ := htor
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  have hxm : ϖ ^ m • x = 0 := by
    rw [mul_smul, ← Units.smul_def, smul_eq_zero_iff_eq] at hbx
    exact hbx
  have hex : ∃ j, ϖ ^ j • x = 0 := ⟨m, hxm⟩
  have hj : ϖ ^ Nat.find hex • x = 0 := Nat.find_spec hex
  have hj0 : Nat.find hex ≠ 0 := by
    intro h
    rw [h, pow_zero, one_smul] at hj
    exact hx0 hj
  obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  have he0 : ϖ ^ i • x ≠ 0 := Nat.find_min hex (by omega)
  have hϖe : ϖ • (ϖ ^ i • x) = 0 := by
    rw [hi] at hj
    rw [smul_smul, ← pow_succ']; exact hj
  have heK : π (ϖ ^ i • x) = 0 := by rw [map_smul, hxK, smul_zero]
  have hunit_e : ∀ w : O, IsUnit w → w • (ϖ ^ i • x) ≠ 0 := by
    intro w hw h
    exact he0 ((hw.smul_eq_zero).mp h)
  obtain ⟨n, v, hav⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  have hadvd : ∀ c : O, a ∣ c ↔ ϖ ^ n ∣ c := by
    intro c; rw [hav, Units.mul_left_dvd]
  obtain ⟨y₀, hy₀K, hy₀⟩ : ∃ y₀ : Z, π y₀ = 0 ∧ ∀ c : O, c • y₀ = 0 ↔ a ∣ c := by
    cases n with
    | zero =>
      refine ⟨0, map_zero π, fun c => ?_⟩
      rw [hadvd, pow_zero]
      simp
    | succ n' =>
      obtain ⟨y, hyK, hy⟩ := hdiv (ϖ ^ n') (pow_ne_zero _ hϖ.ne_zero) _ heK
      refine ⟨y, hyK, fun c => ?_⟩
      rw [hadvd]
      constructor
      · intro hc
        by_cases hc0 : c = 0
        · rw [hc0]; exact dvd_zero _
        obtain ⟨r, w, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc0 hϖ
        by_cases hr : n' + 1 ≤ r
        · exact Dvd.dvd.mul_left (pow_dvd_pow ϖ hr) _
        · exfalso
          obtain ⟨d, hd⟩ : ∃ d, n' = r + d := ⟨n' - r, by omega⟩
          apply hunit_e (w : O) w.isUnit
          have hmul : (w : O) * ϖ ^ n' = ϖ ^ d * ((w : O) * ϖ ^ r) := by rw [hd, pow_add]; ring
          rw [← hy, smul_smul, hmul, mul_smul, hc, smul_zero]
      · rintro ⟨d, rfl⟩
        have hmul : ϖ ^ (n' + 1) * d = d * ϖ * ϖ ^ n' := by ring
        rw [hmul, mul_smul, hy, mul_smul, hϖe, smul_zero]
  have hy₀T : y₀ ∈ Submodule.torsionBy O Z a :=
    (Submodule.mem_torsionBy_iff _ _).mpr ((hy₀ a).mpr dvd_rfl)
  have hy₀ker : (⟨y₀, hy₀T⟩ : Submodule.torsionBy O Z a) ∈ LinearMap.ker φ := by
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    simp [φ, hy₀K]
  let f : O →ₗ[O] LinearMap.ker φ := LinearMap.toSpanSingleton O _ ⟨⟨y₀, hy₀T⟩, hy₀ker⟩
  have hker : Ideal.span {a} = LinearMap.ker f := by
    ext c
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, Ideal.mem_span_singleton, ← hy₀ c]
    simp [Subtype.ext_iff]
  have hK : Module.length O (O ⧸ Ideal.span {a}) ≤ Module.length O (LinearMap.ker φ) := by
    calc Module.length O (O ⧸ Ideal.span {a})
        = Module.length O (O ⧸ LinearMap.ker f) :=
          (Submodule.quotEquivOfEq _ _ hker).length_eq
      _ = Module.length O (LinearMap.range f) := f.quotKerEquivRange.length_eq
      _ ≤ Module.length O (LinearMap.ker φ) :=
          Module.length_le_of_injective (LinearMap.range f).subtype (Submodule.subtype_injective _)
  have h2 : Module.length O ↥(Submodule.torsionBy O Q a) + Module.length O (O ⧸ Ideal.span {a}) ≤
      (k : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) + Module.length O (O ⧸ Ideal.span {a}) := by
    calc _ ≤ Module.length O ↥(Submodule.torsionBy O Q a) + Module.length O (LinearMap.ker φ) := by
            gcongr
      _ = Module.length O ↥(Submodule.torsionBy O Z a) := by rw [hexact, add_comm]
      _ ≤ _ := hle
      _ = _ := by push_cast; ring
  exact (ENat.add_le_add_iff_right hLfin).mp h2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftingTheoremPhiModulesExactTriple
section
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.InertiaEigenvalues

theorem lifting_along_exact_triple : GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.Lifting := by
  intro O K _ _ _ _ _ l e a _ _ _ _ _ _ ι₀ ι₁ ι₂ _ _ _ _ _ _ η H D₀ D₁ D₂ F G N Sig U hH y₂ hy₂ m₂ hm₂ h0
  obtain ⟨hex, hnum, htype, hch2⟩ := hH
  have hl : l.Prime := Fact.out
  have hts : e + 1 = l ^ a := TameDescentExponentData.succ_eq (K := K)
  have ha : 1 ≤ a := Nat.one_le_iff_ne_zero.2 (NeZero.ne a)
  obtain ⟨hr1, hr4, hrper⟩ := _root_.GlobalTheory.BK.maxPeriod_bounds l e a hl ha hts Sig N hnum.frob_mem hnum.zero_mem_Sig
    hnum.card_Sig hnum.two_le
  set r := maxPeriod l Sig with hr
  obtain ⟨hL1, hL2, hL3, -, -, hL6⟩ :=
    _root_.GlobalTheory.numerical_bounds_of_forty_mul_lt l H N η r hnum.two_le hnum.one_le hnum.lt hr4 hnum.large
  have hl2 : l ≠ 2 := by
    have h8 : 8 ≤ N ^ 3 := by
      calc 8 = 2 ^ 3 := rfl
        _ ≤ N ^ 3 := Nat.pow_le_pow_left hnum.two_le 3
    have := hnum.large
    generalize H * N ^ 2 = A at this
    generalize N ^ 3 = B at this h8
    omega

  have hB : GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.Bounds l e Sig U N η H :=
    ⟨hnum.frob_mem, hnum.zero_mem_Sig, hnum.card_Sig, hnum.two_le, hnum.range_U, hnum.zero_mem_U,
      hnum.card_U, hnum.one_le, hnum.lt, hnum.large⟩
  obtain ⟨-, hkM, -, hkMinv, -, hkY'⟩ :=
    _root_.GlobalTheory.Proof.cokernel_latticeMap_killed_by_prime_pow.main O K l e a ι₁ ι₂ Sig U N η H hB D₁ D₂ htype hch2 G hex.finiteLength
  set ρ := GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.eW N r with hρ
  have hcast : ∀ v : Vec K a ι₂, (l ^ GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.rho l Sig N : ℕ) • v = (l : K) ^ ρ • v := by
    intro v
    rw [← Nat.cast_smul_eq_nsmul K]
    push_cast
    rfl
  obtain ⟨y₁, hy₁, hGy₁⟩ := hkY' y₂ hy₂
  obtain ⟨m₁, hm₁, hGm₁⟩ := hkMinv m₂ hm₂
  rw [hcast] at hGy₁ hGm₁
  have hG1 : G.app (y₁ + D₁.phi m₁) = (l : K) ^ ρ • (y₂ + D₂.phi m₂) := by
    rw [map_add (f := _), G.app_phi, hGy₁, hGm₁, map_smul, smul_add]

  set ω := D₁.Mon (y₁ + D₁.phi m₁) with hω
  have hω1 : (l : K) ^ (η * (r + 1)) • ω ∈ D₁.Z :=
    _root_.GlobalTheory.BK.pow_smul_Mon_add_phi_mem_Z O K l e a ι₁ η H D₁ hnum.one_le hnum.lt (by omega) hL2 r hr1
      (fun τ c hc => hrper c (htype.chars_subset τ hc)) hL6 hl2 y₁ hy₁ m₁ hm₁

  obtain ⟨hjmp, -, hinj, hker⟩ := _root_.GlobalTheory.exactTriple_jumps_chars_lift O K l e a ι₀ ι₁ ι₂ η H D₀ D₁ D₂ F G hex
  have hGω : G.onPol ((l : K) ^ (η * (r + 1)) • ω) = 0 := by
    rw [map_smul, hω, G.onPol_Mon, hG1, map_smul, h0, smul_zero, smul_zero]
  obtain ⟨w₀, hw₀, hFw₀⟩ := hker ρ (fun y hy => by
      obtain ⟨x, hx, h⟩ := hkM y hy
      exact ⟨x, hx, h.trans (hcast y)⟩) _ hω1 hGω
  rw [smul_smul, ← pow_add] at hFw₀
  have hy₁Y : y₁ + D₁.phi m₁ ∈ D₁.Yl := by
    refine D₁.desc.mem_Yl_iff.2 ⟨0, ?_⟩
    rw [pow_zero, one_smul]
    refine add_mem (D₁.desc.Y'_le_Y η hy₁) ⟨?_, fun g => ?_⟩
    · exact (mem_divE (l := l) (e := e)).2 (D₁.upper _ (D₁.phi_mem_L hm₁.1))
    · rw [D₁.desc.act_phi, hm₁.2 g]
  obtain ⟨-, wm, hwm, hLcwm⟩ := _root_.GlobalTheory.BK.BKDat.Mon_mem_range_Lc O K l e a ι₁ η H D₁ _ hy₁Y
  have hIm := (_root_.GlobalTheory.LcImage.image_valuation_integralImage O K l e a ι₁ η H D₁ U N htype.jumps_subset
    (fun i hi => Finset.mem_Icc.2 (hnum.range_U i hi)) hnum.card_U hnum.lt).1
  obtain ⟨w', hw', hFw'⟩ := _root_.GlobalTheory.Proof.LiftImage.lift_image O K l e a ι₀ ι₁ η H D₀ D₁ F U hIm ω
    ⟨wm, hwm, hLcwm⟩ _ ⟨w₀, D₀.desc.mem_Zl_of_mem_Z hw₀, hFw₀⟩

  set c₂ := GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.c₂ N η r with hc₂
  have hw₀eq : (l : K) ^ c₂ • D₀.Lc w' = w₀ := by
    apply hinj
    rw [map_smul, hFw', hFw₀, hc₂, GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.c₂, GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.c₁, add_comm]
  have hjmp0 : D₀.jumps ⊆ (U : Set ℤ) := hjmp.trans htype.jumps_subset
  have hIcc : U ⊆ Finset.Icc (-(η : ℤ)) H := fun i hi => Finset.mem_Icc.2 (hnum.range_U i hi)
  obtain ⟨y, hy, hLcy⟩ := _root_.GlobalTheory.LcImage.exists_mem_Y'_Lc_cls_eq O K l e a ι₀ η H D₀ U N hjmp0 hIcc hnum.card_U
    hnum.lt (by omega) hL2 c₂ w' hw' (hw₀eq ▸ hw₀)

  have hff := (_root_.GlobalTheory.ZFin.finiteFree_and_localisation O K l e a ι₀ η H D₀).1
  obtain ⟨y₀, hy₀, hMy₀⟩ := _root_.GlobalTheory.Proof.exists_monodromy_eq_leadingCoeff_breuilKisinDescent.exists_Mon_eq_Lc_cls O K l e a ι₀ η H D₀ U N hjmp0 hIcc hnum.card_U
    hnum.one_le hnum.lt hL3 hL2 (GlobalTheory.T.isAdicComplete_twistedInvariantLattice O K l e a ι₀ η H D₀)
    (_root_.GlobalTheory.InertiaEigenvalues.isHausdorff_Z_of_finiteFree O K l e a ι₀ η H D₀ hff) y hy

  have hGF : ∀ v : Vec K a ι₀, G.app (F.app v) = 0 := by
    intro v
    set_option synthInstance.maxHeartbeats 100000 in
      rw [eq_sum_bas v, map_sum, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [F.app_smul_tot, G.app_smul_tot]
    have h1 : F.app (bas i) ∈ D₁.M := F.app_mem_M (D₀.bas_mem_M i)
    rw [(hex.exact _ h1).2 ⟨bas i, D₀.bas_mem_M i, rfl⟩, smul_zero]
  set n := c₂ + η + GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.eL N η with hn
  have hs {κ : Type} (v : Vec K a κ) : ((l : O) ^ n) • v = (l : K) ^ n • v := by
    rw [← algebraMap_smul K, map_pow, map_natCast]
  have h3 : ((l : O) ^ n • y₁ - F.app y₀) + D₁.phi ((l : O) ^ n • m₁) =
      (l : K) ^ n • (y₁ + D₁.phi m₁) - F.app y₀ := by
    rw [hs, hs, map_smul, smul_add]
    abel
  refine ⟨_, sub_mem (Submodule.smul_mem _ ((l : O) ^ n) hy₁) (F.app_mem_Y' hy₀), _,
    Submodule.smul_mem _ ((l : O) ^ n) hm₁, ?_, ?_⟩
  · rw [h3, map_sub, map_smul, ← hω, ← F.onPol_Mon, hMy₀, hLcy, map_smul, hFw']
    exact sub_self _
  · rw [h3, map_sub, G.app.map_smul_of_tower, hGF, sub_zero, hG1, smul_smul, ← pow_add]
    rfl

end GlobalTheory.InertiaEigenvalues
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndepOnOfInvariant
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Module TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.Per.FontaineBound

theorem linearIndepOn_of_invariant {K B W G ι : Type} [Field K] [CommRing B] [IsDomain B] [Algebra K B]
    [AddCommGroup W] [Module B W] [Module K W] [IsScalarTower K B W] [Module.IsTorsionFree B W]
    (a : G → B → B) (σ : G → W →+ W) (hσ : ∀ g b w, σ g (b • w) = a g b • σ g w)
    (hreg : ∀ b b' : B, b ≠ 0 → (∀ g, b * a g b' = a g b * b') → ∃ c : K, b' = algebraMap K B c * b)
    (v : ι → W) (hv : ∀ g i, σ g (v i) = v i)
    (s : Finset ι) (h : LinearIndepOn K v s) : LinearIndepOn B v s := by
  first
  | (rename_i h_5 h_6 h_7 h_8 h_9 h_10 h_11 h_12 h_13; revert K B W G ι h_5 h_6 h_7 h_8 h_9 h_10 h_11 h_12 h_13 a σ hσ hreg v hv s h; exact @_root_.GlobalTheory.SimpStatement.main)
  | exact @_root_.GlobalTheory.SimpStatement.main
  | exact _root_.GlobalTheory.SimpStatement.main
  | (apply _root_.GlobalTheory.SimpStatement.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SimpStatement.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SimpStatement.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SimpStatement.main ..)

section General

variable {G Qp K B LL V : Type} [Group G] [Field Qp] [Field K] [Algebra Qp K] [CommRing B] [IsDomain B]
  [Algebra Qp B] [Algebra K B] [IsScalarTower Qp K B] [Field LL] [Algebra Qp LL]
  [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

def invs (act : G →* (B ≃ₐ[K] B)) (ρ : Representation LL G V) : Submodule LL (V ⊗[Qp] B) :=
  ⨅ g : G, LinearMap.ker (AlgebraTensorModule.map (ρ g)
    (((act g).toAlgHom.toLinearMap).restrictScalars Qp) - LinearMap.id)

theorem finite_finrank_le_base [FiniteDimensional Qp K] [FiniteDimensional Qp V] (act : G →* (B ≃ₐ[K] B))
    (hreg : ∀ b b' : B, b ≠ 0 → (∀ g, b * act g b' = act g b * b') → ∃ c : K, b' = algebraMap K B c * b)
    (ρ : Representation LL G V) :
    Module.Finite Qp (invs (Qp := Qp) act ρ) ∧
      finrank Qp (invs (Qp := Qp) act ρ) ≤ finrank Qp K * finrank Qp V := by
  let σ : G → B ⊗[Qp] V →ₗ[Qp] B ⊗[Qp] V := fun g =>
    TensorProduct.map (((act g).toAlgHom.toLinearMap).restrictScalars Qp) ((ρ g).restrictScalars Qp)
  have hσ : ∀ g (b : B) w, σ g (b • w) = act g b • σ g w := by
    intro g b w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul c v => simp [σ, TensorProduct.smul_tmul']
    | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]
  let U : Submodule K (B ⊗[Qp] V) :=
    { carrier := {x | ∀ g, σ g x = x}
      zero_mem' := fun g => map_zero _
      add_mem' := fun hx hy g => by rw [map_add (f := _), hx g, hy g]
      smul_mem' := fun c x hx g => by
        rw [← algebraMap_smul B c x, hσ, hx g, AlgEquiv.commutes] }
  have hr : Module.rank K U ≤ finrank Qp V := by
    refine rank_le fun s hs => ?_
    have h1 : LinearIndepOn K (fun x : U => (x : B ⊗[Qp] V)) s := hs.map' U.subtype U.ker_subtype
    have h2 := linearIndepOn_of_invariant (fun g b => act g b) (fun g => (σ g).toAddMonoidHom) hσ hreg
      (fun x : U => (x : B ⊗[Qp] V)) (fun g x => x.2 g) s h1
    simpa using LinearIndependent.fintype_card_le_finrank h2
  haveI : Module.Finite K U := by
    rw [← Module.rank_lt_aleph0_iff]
    exact lt_of_le_of_lt hr Cardinal.natCast_lt_aleph0
  have hr' : finrank K U ≤ finrank Qp V := finrank_le_of_rank_le hr
  haveI : Module.Finite Qp U := Module.Finite.trans K U
  have hc : ∀ g x, σ g (TensorProduct.comm Qp V B x) =
      TensorProduct.comm Qp V B (AlgebraTensorModule.map (ρ g)
        (((act g).toAlgHom.toLinearMap).restrictScalars Qp) x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c v => simp [σ]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  let f : invs (Qp := Qp) act ρ →ₗ[Qp] U :=
    { toFun := fun x => ⟨TensorProduct.comm Qp V B x, fun g => by
        have := x.2
        simp only [invs, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
          LinearMap.id_apply, sub_eq_zero] at this
        rw [hc, this g]⟩
      map_add' := fun x y => Subtype.ext (map_add _ _ _)
      map_smul' := fun c x => Subtype.ext (map_smul (TensorProduct.comm Qp V B) c _) }
  have hf : Function.Injective f := fun x y h =>
    Subtype.ext ((TensorProduct.comm Qp V B).injective (congrArg Subtype.val h))
  refine ⟨Module.Finite.of_injective f hf, (LinearMap.finrank_le_finrank_of_injective hf).trans ?_⟩
  rw [← Module.finrank_mul_finrank Qp K U]
  exact Nat.mul_le_mul_left _ hr'

theorem finite_finrank_le [FiniteDimensional Qp K] [FiniteDimensional Qp LL] [FiniteDimensional LL V]
    (act : G →* (B ≃ₐ[K] B))
    (hreg : ∀ b b' : B, b ≠ 0 → (∀ g, b * act g b' = act g b * b') → ∃ c : K, b' = algebraMap K B c * b)
    (ρ : Representation LL G V) :
    Module.Finite LL (invs (Qp := Qp) act ρ) ∧
      finrank LL (invs (Qp := Qp) act ρ) ≤ finrank Qp K * finrank LL V := by
  haveI : FiniteDimensional Qp V := Module.Finite.trans LL V
  obtain ⟨h1, h2⟩ := finite_finrank_le_base (Qp := Qp) act hreg ρ
  refine ⟨Module.Finite.of_restrictScalars_finite Qp LL _, ?_⟩
  rw [← Module.finrank_mul_finrank Qp LL (invs (Qp := Qp) act ρ), ← Module.finrank_mul_finrank Qp LL V,
    mul_left_comm] at h2
  exact Nat.le_of_mul_le_mul_left h2 Module.finrank_pos

end General

section Periods

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)

theorem frac_dR (hF : IsField BdR) (b b' : BdR) (hb : b ≠ 0)
    (h : ∀ g, b * PD.actdR g b' = PD.actdR g b * b') : ∃ c : K, b' = algebraMap K BdR c * b := by
  letI : Field BdR := hF.toField
  obtain ⟨c, hc⟩ := PD.invdR (b' / b) fun g => by
    have hg : PD.actdR g b ≠ 0 := (map_ne_zero _).2 hb
    rw [map_div₀, div_eq_div_iff hg hb, mul_comm, h g, mul_comm]
  exact ⟨c, by rw [hc, div_mul_cancel₀ _ hb]⟩


include PD in
theorem isDomain_cris (hF : IsField BdR) : IsDomain B :=
  letI : Field BdR := hF.toField
  PD.ι_inj.isDomain PD.ι.toRingHom

variable {LL : Type} [Field LL] [Algebra Qp LL] [FiniteDimensional Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [FiniteDimensional LL V]

theorem ddR_finite_le (hF : IsField BdR) (ρ : Representation LL G V) :
    Module.Finite LL (DdR PD ρ) ∧ finrank LL (DdR PD ρ) ≤ finrank Qp K * finrank LL V := by
  haveI := hF.isDomain
  haveI := PD.finK
  exact finite_finrank_le PD.actdR (frac_dR PD hF) ρ

end Periods

section Tied

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {T : LocTied l P AI} {C : Core l}

theorem isField_of_tied (T : LocTied l P AI) : IsField P.R.BdR :=
  T.eD.toMulEquiv.isField (GlobalTheory.MemLoc.BdRField.bdR_isField l).2.2.1

theorem frac_cris (hfit : GlobalTheory.MemLoc.Fits T C) (hinj : C.TensorInj) (K : FinExt l) (b b' : P.R.B) (hb : b ≠ 0)
    (h : ∀ g, b * (P.PD K).actB g b' = (P.PD K).actB g b * b') :
    ∃ c : ↥(K0 K), b' = algebraMap ↥(K0 K) P.R.B c * b := by
  have hF : IsField P.R.BdR := isField_of_tied T
  obtain ⟨c, hc⟩ := frac_dR (P.PD K) hF ((P.PD K).ι b) ((P.PD K).ι b')
    (fun h0 => hb ((P.PD K).ι_inj (h0.trans (map_zero _).symm)))
    (fun g => by rw [← (P.PD K).ι_comm, ← (P.PD K).ι_comm, ← map_mul, ← map_mul, h g])
  have hcU : (c : Om l) ∈ MaximalUnramifiedExtension l := by
    by_contra hn
    have hli : LinearIndependent ↥(MaximalUnramifiedExtension l) ![(1 : Om l), (c : Om l)] := by
      rw [LinearIndependent.pair_iff' one_ne_zero]
      intro a ha
      apply hn
      rw [← ha, Algebra.smul_def, mul_one]
      exact a.2
    have h0 := hinj 2 _ hli ![T.eB b', - T.eB b] (by
      have h1 := congrArg T.eD hc
      rw [map_mul, P.PD_ι, P.PD_ι, hfit.ι, hfit.ι] at h1
      have h2 : T.eD (algebraMap ↥K.1 P.R.BdR c) = C.oD (c : Om l) := hfit.o _
      rw [h2] at h1
      simp [Fin.sum_univ_two, h1]) 1
    apply hb
    apply T.eB.injective
    simpa using h0
  refine ⟨⟨c, c.2, hcU⟩, (P.PD K).ι_inj ?_⟩
  rw [map_mul, AlgHom.commutes, hc]
  rfl

theorem dcris_finite_le (hfit : GlobalTheory.MemLoc.Fits T C) (hinj : C.TensorInj) (K LL : FinExt l)
    (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
    [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) :
    Module.Finite ↥LL.1 (Dcris (P.PD K) ρ) ∧
      finrank ↥LL.1 (Dcris (P.PD K) ρ) ≤ finrank ℚ_[l] ↥(K0 K) * finrank ↥LL.1 V := by
  haveI := isDomain_cris (P.PD K) (isField_of_tied T)
  haveI := (P.PD K).finK₀
  haveI := LL.2
  exact finite_finrank_le (P.PD K).actB (frac_cris hfit hinj K) ρ

end Tied

end GlobalTheory.Per.FontaineBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPowIndexLeOfFixed
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.Per

theorem norm_pow_index_le_of_fixed : ∀ (l : ℕ) [Fact l.Prime] (H : Subgroup (GQ l)), H.index ≠ 0 → ∀ x : Om l, (∀ g ∈ H, g x = x) → ‖x‖ < 1 → ‖x‖ ^ H.index ≤ ‖((l : ℕ) : Om l)‖ := by
  intro l _ H hidx x hx hx1
  have hfin : Fintype (GQ l ⧸ H) := Subgroup.fintypeOfIndexNeZero hidx
  have fout : ∀ g : GQ l, (g : GQ l ⧸ H).out x = g x := fun g => by
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
    rw [hh, AlgEquiv.mul_apply, hx h h.2]
  have hfix : ∀ g : GQ l, g (∏ q : GQ l ⧸ H, q.out x) = ∏ q : GQ l ⧸ H, q.out x := fun g => by
    rw [map_prod, ← Equiv.prod_comp (MulAction.toPerm g) fun q : GQ l ⧸ H => q.out x]
    refine Finset.prod_congr rfl fun q _ => ?_
    have e : MulAction.toPerm g q = ((g * q.out : GQ l) : GQ l ⧸ H) := by
      rw [MulAction.toPerm_apply, ← smul_eq_mul, MulAction.Quotient.mk_smul_out]
    rw [e, fout, AlgEquiv.mul_apply]
  obtain ⟨c, hc⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed _).2 hfix
  have hn : ‖c‖ = ‖x‖ ^ H.index := by
    rw [← norm_algebraMap' (Om l) c, hc, norm_prod]
    refine (Finset.prod_congr rfl fun q _ => GlobalTheory.RingBasics.norm_gal (Quotient.out q) x).trans ?_
    rw [Finset.prod_const, Finset.card_univ, Subgroup.index, Nat.card_eq_fintype_card]
    rfl
  have hc1 : ‖c‖ < 1 := hn ▸ pow_lt_one₀ (norm_nonneg x) hx1 hidx
  have h2 : ‖c‖ ≤ (l : ℝ) ^ (-1 : ℤ) := by
    rw [Padic.norm_le_pow_iff_norm_lt_pow_add_one]
    simpa using hc1
  rw [← hn, ← map_natCast (algebraMap ℚ_[l] (Om l)), norm_algebraMap', Padic.norm_p]
  simpa using h2

end GlobalTheory.Per
end

