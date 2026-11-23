module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOrbitOfEventually
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0246
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0260
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0229
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0250
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0248

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundedAndEventuallySubMemLat
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

namespace GlobalTheory.ExpImage

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)

theorem io_mem_Lat_of_mem_span {M n : ℕ} {x : Ainf l}
    (hx : x ∈ Ideal.span {((l : ℕ) : Ainf l) ^ n, AI.ξ ^ M}) : io AI x ∈ Lat AI M n := by
  obtain ⟨p, q, rfl⟩ := Ideal.mem_span_pair.1 hx
  rw [map_add (f := _), mul_comm p]
  refine add_mem (io_mem_Lat AI M n p) (FilB_le_Lat AI ?_)
  rw [map_mul, map_pow]
  exact FilB_zero_mul (io_mem AI q) (by simpa using FilB_pow (io_ξ_mem AI) M)

theorem bounded_and_eventually_sub_mem_Lat : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l)
    (AI : LocAinf l P), LocTied l P AI → ∀ b ∈ FilB P 0, ∀ M n : ℕ,
    (∃ k : ℕ, (l : P.R.BdR) ^ k * b ∈ Lat AI M n) ∧
      ∀ᶠ σ in nhds (1 : GQ l), P.actQdR σ b - b ∈ Lat AI M n := by
  intro l _ P AI T b hb M n
  obtain ⟨k, a, ha⟩ := GlobalTheory.BdRQuot.exists_approx T M b hb
  change (l : P.R.BdR) ^ k * b - io AI a ∈ FilB P (M : ℤ) at ha
  constructor
  · have h0 : (l : P.R.BdR) ^ k * b ∈ Lat AI M 0 := ⟨a, by simpa using ha⟩
    refine ⟨n + k, ?_⟩
    rw [pow_add, mul_assoc]
    exact (pow_mul_mem_Lat_iff AI (k := n) (n := 0)).2 h0
  · filter_upwards [GlobalTheory.AinfCont.eventually_sub_mem AI (k + n) M a] with g hg
    rw [← pow_mul_mem_Lat_iff AI (k := k)]
    have h1 := io_mem_Lat_of_mem_span AI hg
    have h2 := FilB_le_Lat AI (n := k + n) (sub_mem (act_mem g ha) ha)
    have h3 := add_mem h1 h2
    rw [map_sub, io_act, map_sub, map_mul, map_pow, map_natCast] at h3
    convert h3 using 1
    ring

end GlobalTheory.ExpImage
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CLLUnitIntervalLe
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.HubLoc Module

namespace GlobalTheory.HubLoc

theorem cLL_unit_interval_le : ∀ (l h N v : ℕ) (U : Finset ℤ) (U' : Set ℤ), l.Prime → 1 ≤ N → U' ⊆ U → U.card ≤ N →
    (∀ u ∈ U, -(h : ℤ) ≤ u ∧ u ≤ h) → v ≤ LocalSituation.mN l 1 (h + h) - 1 →
    LocalSituation.cLL l (LocalSituation.mN l 1 (h + h)) v U' 0 1 ≤ 5 + Nat.log l (2 * h) + N * (4 + 2 * Nat.log l (2 * h)) := by
  classical
  intro l h N v U U' hl hN hU hcard hb hv
  haveI : Fact l.Prime := ⟨hl⟩
  unfold LocalSituation.cLL LocalSituation.mN LocalSituation.rI LocalSituation.n0 at *
  set L := Nat.log l (2 * h) with hL
  set n0 := sInf {n | h + h ≤ l ^ n * (l - 1)} with hn0
  have hl1 : 1 < l := hl.one_lt

  have hn0le : n0 ≤ L + 1 := by
    apply Nat.sInf_le
    show h + h ≤ l ^ (L + 1) * (l - 1)
    have h1 : 2 * h < l ^ (L + 1) := Nat.lt_pow_succ_log_self hl1 (2 * h)
    have h2 : l ^ (L + 1) ≤ l ^ (L + 1) * (l - 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hI : Finset.Ico (0 : ℤ) 1 = {0} := by
    ext x
    simp only [Finset.mem_Ico, Finset.mem_singleton]
    omega
  rw [hI, Finset.sum_singleton]

  have hterm : ∀ u ∈ U,
      (∑ᶠ (_ : u ∈ U') (_ : u ≠ 0), (2 * 1 + n0 + 1 + LocalSituation.vZ l (u - 0))) ≤ 4 + 2 * L := by
    intro u hu
    have hz : LocalSituation.vZ l u ≤ Nat.log l h := vZ_le_log l h u (hb u hu)
    have hlog : Nat.log l h ≤ L := Nat.log_mono_right (by omega)
    simp only [finsum_eq_if, sub_zero]
    split_ifs <;> omega

  have hS : (∑ᶠ (u : ℤ) (_ : u ∈ U') (_ : u ≠ 0), (2 * 1 + n0 + 1 + LocalSituation.vZ l (u - 0)))
      ≤ N * (4 + 2 * L) := by
    rw [finsum_eq_sum_of_support_subset _ (s := U) ?_]
    · calc _ ≤ U.card • (4 + 2 * L) := Finset.sum_le_card_nsmul _ _ _ hterm
        _ ≤ N * (4 + 2 * L) := by
          rw [smul_eq_mul]
          exact Nat.mul_le_mul_right _ hcard
    · intro u hu
      rw [Function.mem_support] at hu
      by_contra hnot
      have hnU' : u ∉ U' := fun h' => hnot (Finset.mem_coe.mpr (hU h'))
      exact hu (by simp only [finsum_eq_if, if_neg hnU'])
  have hNL : 1 ≤ N * (4 + 2 * L) := by
    have := Nat.mul_le_mul hN (show 1 ≤ 4 + 2 * L by omega)
    omega
  have hmax := max_le hNL hS
  omega

end GlobalTheory.HubLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardH1LocalEulerFormula
section
open GlobalTheory.AdmLoc Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Filter Topology
open scoped TensorProduct

namespace GlobalTheory.EulerFree

theorem card_Z1_of_invariants_eq_bot {O G M : Type} [CommRing O] [Group G] [TopologicalSpace G]
    [AddCommGroup M] [Module O M] (π : Representation O G M)
    (hlc : ∀ m, IsLocallyConstant fun g => π g m) (h0 : π.invariants = ⊥) :
    Nat.card (ReciprocityTheory.Def.Z1 π ⊤) = Nat.card (ReciprocityTheory.Def.H1 π ⊤) * Nat.card M := by
  have hle : ReciprocityTheory.Def.B1 π ⊤ ≤ ReciprocityTheory.Def.Z1 π ⊤ := by
    rintro _ ⟨m, -, rfl⟩
    refine ⟨⟨(hlc m).comp (fun x => x - m), fun _ => Submodule.mem_top⟩, ?_⟩
    funext x
    change π x.1 (π x.2 m - m) - (π (x.1 * x.2) m - m) + (π x.1 m - m) = 0
    simp only [map_mul, Module.End.mul_apply, map_sub]
    abel
  have h1 := Submodule.card_eq_card_quotient_mul_card
    ((ReciprocityTheory.Def.B1 π ⊤).submoduleOf (ReciprocityTheory.Def.Z1 π ⊤))
  have h2 : Nat.card ((ReciprocityTheory.Def.B1 π ⊤).submoduleOf (ReciprocityTheory.Def.Z1 π ⊤)) =
      Nat.card (ReciprocityTheory.Def.B1 π ⊤) := Nat.card_congr (Submodule.comapSubtypeEquivOfLe hle).toEquiv
  have hinj : Function.Injective (ReciprocityTheory.Def.d0 π) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff, ← h0]
    intro m hm g
    exact sub_eq_zero.1 (congrFun (LinearMap.mem_ker.1 hm) g)
  have h3 : Nat.card (ReciprocityTheory.Def.B1 π ⊤) = Nat.card M :=
    (Nat.card_congr (Submodule.topEquiv.symm.trans
      (Submodule.equivMapOfInjective _ hinj ⊤)).toEquiv).symm
  rw [h1, h2, h3, mul_comm]

theorem card_H1_of_euler (R O G G' : Type) [CommRing R] [CommRing O] [Group G] [TopologicalSpace G]
    [Group G'] [TopologicalSpace G'] (φ : G' ≃* G) (hφ : Continuous φ ∧ Continuous φ.symm)
    (M : Type) [AddCommGroup M] [Module R M] [Module O M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M] (rho : Representation R G M) (hrho : ReciprocityTheory.Gal.ContAction rho) (d : ℕ)
    (hEu : Nat.card (ReciprocityTheory.Gal.H1 rho) =
      Nat.card (ReciprocityTheory.Gal.H0 rho) * Nat.card (ReciprocityTheory.Gal.H2 rho) * Nat.card M ^ d)
    (π : Representation O G' M) (ha : ∀ g m, rho g m = π (φ.symm g) m)
    (hlc : ∀ m, IsLocallyConstant fun g => π g m) (h0 : π.invariants = ⊥)
    (h2 : Subsingleton (ReciprocityTheory.Def.H2 π ⊤)) :
    Nat.card (ReciprocityTheory.Def.H1 π ⊤) = Nat.card M ^ d := by
  have ha' : ∀ g m, rho (φ g) m = π g m := fun g m => by rw [ha, φ.symm_apply_apply]
  have hH0 : Nat.card (ReciprocityTheory.Gal.H0 rho) = 1 := by
    have : ReciprocityTheory.Gal.H0 rho = ⊥ := by
      rw [eq_bot_iff]
      intro m hm
      have : m ∈ π.invariants := fun g => by rw [← ha']; exact hm (φ g)
      rw [h0] at this
      exact this
    rw [this]
    exact Nat.card_unique
  have hH2 : Nat.card (ReciprocityTheory.Gal.H2 rho) = 1 := by
    have : Subsingleton (ReciprocityTheory.Gal.H2 rho) := by
      refine Submodule.Quotient.subsingleton_iff.2 (eq_top_iff.2 fun z _ => ?_)
      let z' : ReciprocityTheory.Def.Z2 π ⊤ := ⟨fun x => z.1 (φ x.1, φ x.2),
        ⟨(IsLocallyConstant.iff_continuous _).2 (z.2.1.comp
          ((hφ.1.comp continuous_fst).prodMk (hφ.1.comp continuous_snd))), fun _ => Submodule.mem_top⟩, by
        funext x
        have := z.2.2 (φ x.1) (φ x.2.1) (φ x.2.2)
        rw [ha', ← map_mul, ← map_mul] at this
        exact this⟩
      have hz' : z' ∈ (ReciprocityTheory.Def.B2 π ⊤).submoduleOf (ReciprocityTheory.Def.Z2 π ⊤) := by
        rw [Submodule.Quotient.subsingleton_iff.1 h2]
        exact Submodule.mem_top
      obtain ⟨b, hb, hbz⟩ := hz'
      refine ⟨fun g => b (φ.symm g), hb.1.continuous.comp hφ.2, ?_⟩
      funext x
      have h : π (φ.symm x.1) (b (φ.symm x.2)) - b (φ.symm x.1 * φ.symm x.2) + b (φ.symm x.1) =
          z.1 (φ (φ.symm x.1), φ (φ.symm x.2)) := congrFun hbz (φ.symm x.1, φ.symm x.2)
      rw [φ.apply_symm_apply, φ.apply_symm_apply, ← map_mul, ← ha] at h
      exact h
    exact Nat.card_unique
  have hZ := GlobalTheory.CocycleCount.card_cocycles_mul_invariants_discrete _ _ M rho hrho
  let E : ↥(ReciprocityTheory.Def.Z1 π ⊤) ≃ ↥(ReciprocityTheory.Gal.Z1 rho) :=
    { toFun := fun c => ⟨fun g => c.1 (φ.symm g), c.2.1.1.continuous.comp hφ.2, fun g h => by
        beta_reduce
        rw [ha, map_mul, cocycle_mul]⟩
      invFun := fun c => ⟨fun g => c.1 (φ g),
        ⟨(IsLocallyConstant.iff_continuous _).2 (c.2.1.comp hφ.1), fun _ => Submodule.mem_top⟩, by
          funext x
          have := c.2.2 (φ x.1) (φ x.2)
          rw [ha', ← map_mul] at this
          change π x.1 (c.1 (φ x.2)) - c.1 (φ (x.1 * x.2)) + c.1 (φ x.1) = 0
          rw [this]
          abel⟩
      left_inv := fun c => Subtype.ext (funext fun g => congrArg c.1 (φ.symm_apply_apply g))
      right_inv := fun c => Subtype.ext (funext fun g => congrArg c.1 (φ.apply_symm_apply g)) }
  have hM : 0 < Nat.card M := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hM
  rw [← card_Z1_of_invariants_eq_bot π hlc h0, Nat.card_congr E]
  rw [hEu, hH0, hH2] at hZ
  simpa using hZ

theorem card_H1_eq_pow :
    Formalism.GaloisCohomology.LocalEulerCharK → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] [Finite M] (π : Representation O ↥(GK K) M), (∀ m : M, l • m = 0) → (∀ m, IsLocallyConstant fun g => π g m) → π.invariants = ⊥ → Subsingleton (ReciprocityTheory.Def.H2 π ⊤) → Nat.card (ReciprocityTheory.Def.H1 π ⊤) = Nat.card M ^ Module.finrank ℚ_[l] ↥K.1 := by
  intro hE l _ K O M _ _ _ _ π hl hlc h0 h2
  have hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  let _ : TopologicalSpace M := ⊥
  have _ : DiscreteTopology M := ⟨rfl⟩
  have hr' : ∀ m : M, l ^ 1 • m = 0 := fun m => by rw [pow_one, hl]
  have _ : NeZero (l ^ 1) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  let _ : Module (ZMod (l ^ 1)) M := AddCommGroup.zmodModule hr'
  let φ : ↥(GK K) ≃* Formalism.GaloisCohomology.GK l K.1 := IntermediateField.fixingSubgroupEquiv K.1
  have hφ : Continuous φ ∧ Continuous φ.symm :=
    GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[l] (Om l) K.1
  let rho : Representation (ZMod (l ^ 1)) (Formalism.GaloisCohomology.GK l K.1) M :=
    GlobalTheory.CocycleCount.repOfAction _ (fun g => (π (φ.symm g)).toAddMonoidHom)
      (fun m => by simp) (fun g h m => by simp)
  have hrho : ReciprocityTheory.Gal.ContAction rho := by
    refine continuous_prod_of_discrete_right.2 fun m => ?_
    exact (hlc m).continuous.comp hφ.2
  exact card_H1_of_euler _ O _ _ φ hφ M rho hrho _ (hE l K.1 hK 1 M rho Nat.one_pos hrho) π
    (fun _ _ => rfl) hlc h0 h2

end GlobalTheory.EulerFree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralIdempotentMulMirabolicDetAverageEqZero
section
open GlobalTheory.GLq GlobalTheory.MirAvg Polynomial

noncomputable section

namespace GlobalTheory.MirAvg.Kill

theorem idem_eq_zero {G : Type} [Group G] [Fintype G] (E : MonoidAlgebra ℂ G) (h : E * E = E)
    (h1 : E.coeff 1 = 0) : E = 0 := by
  classical
  haveI : Module.Finite ℂ (MonoidAlgebra ℂ G) := Module.Finite.of_basis (MonoidAlgebra.basis G ℂ)
  haveI : Module.Free ℂ (MonoidAlgebra ℂ G) := Module.Free.of_basis (MonoidAlgebra.basis G ℂ)
  have hi : IsIdempotentElem (LinearMap.mulLeft ℂ E) := by
    refine LinearMap.ext fun x => ?_
    simp [← mul_assoc, h]
  have ht : LinearMap.trace ℂ _ (LinearMap.mulLeft ℂ E) = 0 := by
    rw [LinearMap.trace_eq_matrix_trace ℂ (MonoidAlgebra.basis G ℂ), Matrix.trace]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
    have : (MonoidAlgebra.basis G ℂ) x = MonoidAlgebra.single x 1 := by simp
    rw [this]
    show (E * MonoidAlgebra.single x 1).coeff x = 0
    rw [MonoidAlgebra.coeff_mul_single_apply]
    simp [h1]
  have h0 := LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero hi ht
  simpa using LinearMap.congr_fun h0 1

variable {G : Type} [Group G] [Fintype G]

theorem coeff_sum_single (F : G → ℂ) (x : G) :
    (∑ h : G, MonoidAlgebra.single h (F h)).coeff x = F x := by
  classical
  simp [MonoidAlgebra.coeff_sum, Finset.sum_apply', Finsupp.single_apply]

theorem coeff_mul' (a b : MonoidAlgebra ℂ G) (x : G) :
    (a * b).coeff x = ∑ q, a.coeff q * b.coeff (q⁻¹ * x) := by
  rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype]
  intro q; simp

def avg (P : G → Prop) [DecidablePred P] (χ : G →* ℂ) : MonoidAlgebra ℂ G :=
  ∑ h : G, MonoidAlgebra.single h (if P h then χ h else 0)

theorem avg_coeff (P : G → Prop) [DecidablePred P] (χ : G →* ℂ) (x : G) :
    (avg P χ).coeff x = if P x then χ x else 0 :=
  coeff_sum_single _ x

theorem avg_mul_self (P : G → Prop) [DecidablePred P] (χ : G →* ℂ)
    (hm : ∀ x y, P x → P y → P (x * y)) (hi : ∀ x, P x → P x⁻¹) :
    avg P χ * avg P χ = ((Finset.univ.filter P).card : ℂ) • avg P χ := by
  ext x
  rw [coeff_mul', MonoidAlgebra.coeff_smul_apply, avg_coeff, smul_eq_mul]
  have key : ∀ q, (avg P χ).coeff q * (avg P χ).coeff (q⁻¹ * x) = if P q then (if P x then χ x else 0) else 0 := by
    intro q
    simp only [avg_coeff]
    by_cases hq : P q
    · have hiff : P (q⁻¹ * x) ↔ P x := ⟨fun h => by simpa using hm _ _ hq h, fun h => hm _ _ (hi _ hq) h⟩
      by_cases hx : P x
      · rw [if_pos hq, if_pos (hiff.2 hx), if_pos hq, if_pos hx, ← map_mul, mul_inv_cancel_left]
      · rw [if_pos hq, if_neg (fun h => hx (hiff.1 h)), if_pos hq, if_neg hx, mul_zero]
    · rw [if_neg hq, if_neg hq, zero_mul]
  simp only [key]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

theorem coeff_one_zOf_mul (ψ : G → ℂ) (a : MonoidAlgebra ℂ G) :
    (zOf ψ * a).coeff 1 = ψ 1 / (Fintype.card G : ℂ) * tr a ψ := by
  rw [coeff_mul', tr, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.inv G) _ _ fun q => ?_
  rw [zOf, coeff_sum_single]
  simp only [Equiv.inv_apply, inv_inv, mul_one]
  ring

theorem zOf_mul_avg_eq_zero (ψ : G → ℂ) (hψ : IsIrr ψ) (P : G → Prop) [DecidablePred P] (χ : G →* ℂ) (h1 : P 1)
    (hm : ∀ x y, P x → P y → P (x * y)) (hi : ∀ x, P x → P x⁻¹) (htr : tr (avg P χ) ψ = 0) :
    zOf ψ * avg P χ = 0 := by
  obtain ⟨hid, hcen, -⟩ := GlobalTheory.GLq.ZOrth.zorth G ψ ψ hψ hψ
  rw [if_pos rfl] at hid
  set m := avg P χ with hmdef
  set n : ℂ := ((Finset.univ.filter P).card : ℂ) with hn
  have hn0 : n ≠ 0 := by
    rw [hn, Nat.cast_ne_zero]
    exact Finset.card_ne_zero.2 ⟨1, by simp [h1]⟩
  have hmm : m * m = n • m := avg_mul_self P χ hm hi
  have hE : (n⁻¹ • (zOf ψ * m)) * (n⁻¹ • (zOf ψ * m)) = n⁻¹ • (zOf ψ * m) := by
    rw [smul_mul_smul_comm]
    have : zOf ψ * m * (zOf ψ * m) = n • (zOf ψ * m) := by
      calc zOf ψ * m * (zOf ψ * m) = zOf ψ * (m * zOf ψ) * m := by simp only [mul_assoc]
        _ = zOf ψ * (zOf ψ * m) * m := by rw [← hcen m]
        _ = (zOf ψ * zOf ψ) * (m * m) := by simp only [mul_assoc]
        _ = n • (zOf ψ * m) := by rw [hid, hmm, mul_smul_comm]
    rw [this, smul_smul, mul_assoc, inv_mul_cancel₀ hn0, mul_one]
  have h1' : (n⁻¹ • (zOf ψ * m)).coeff 1 = 0 := by
    rw [MonoidAlgebra.coeff_smul_apply, coeff_one_zOf_mul, htr]
    simp
  have h0 := idem_eq_zero _ hE h1'
  rwa [smul_eq_zero, or_iff_right (inv_ne_zero hn0)] at h0

end GlobalTheory.MirAvg.Kill

namespace GlobalTheory.MirAvg

theorem mirSet_one {g : ℕ} [Fact g.Prime] {r : ℕ} (a : Fin r → ZMod g) (b : Bool) : mirSet a b (1 : Gn g r) := by
  cases b
  · intro x _; simp
  · intro x; exact ⟨0, by simp⟩

theorem mirSet_mul {g : ℕ} [Fact g.Prime] {r : ℕ} (a : Fin r → ZMod g) (b : Bool) (h h' : Gn g r)
    (hh : mirSet a b h) (hh' : mirSet a b h') : mirSet a b (h * h') := by
  cases b
  · intro x hx
    simp only [mirSet, Bool.false_eq_true, if_false] at hh hh'
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hh' x hx, hh x hx]
  · intro x
    simp only [mirSet, if_true] at hh hh'
    obtain ⟨c₂, hc₂⟩ := hh' x
    obtain ⟨c₁, hc₁⟩ := hh ((h' : Mt g r).mulVec x)
    refine ⟨c₁ + c₂, ?_⟩
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, add_smul, ← hc₁, ← hc₂]
    abel

theorem mirSet_inv {g : ℕ} [Fact g.Prime] {r : ℕ} (a : Fin r → ZMod g) (b : Bool) (h : Gn g r)
    (hh : mirSet a b h) : mirSet a b h⁻¹ := by
  have hhi : ∀ x, (h : Mt g r).mulVec (((h⁻¹ : Gn g r) : Mt g r).mulVec x) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hih : ∀ x, ((h⁻¹ : Gn g r) : Mt g r).mulVec ((h : Mt g r).mulVec x) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  cases b
  · intro x hx
    simp only [mirSet, Bool.false_eq_true, if_false] at hh
    conv_lhs => rw [← hh x hx]
    exact hih x
  · intro x
    simp only [mirSet, if_true] at hh
    obtain ⟨c, hc⟩ := hh (((h⁻¹ : Gn g r) : Mt g r).mulVec x)
    refine ⟨-c, ?_⟩
    rw [hhi x] at hc
    rw [neg_smul, ← hc]
    abel


open Classical in
theorem zOf_mul_mirEl_eq_zero : ∀ (g : ℕ) [Fact g.Prime] (r : ℕ) (ψ : Gn g r → ℂ), IsIrr ψ →
    ∀ (θ : (ZMod g)ˣ →* ℂˣ) (a : Fin r → ZMod g)
    (b : Bool), tr (mirEl θ a b) ψ = 0 → zOf ψ * mirEl θ a b = 0 := by
  intro g _ r ψ hψ θ a b htr
  let χ : Gn g r →* ℂ := (Units.coeHom ℂ).comp (θ.comp Matrix.GeneralLinearGroup.det)
  have hm : mirEl θ a b = Kill.avg (mirSet a b) χ := rfl
  rw [hm] at htr ⊢
  exact Kill.zOf_mul_avg_eq_zero ψ hψ (mirSet a b) χ (mirSet_one a b) (mirSet_mul a b) (mirSet_inv a b) htr

end GlobalTheory.MirAvg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Cocycle
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

namespace GlobalTheory.ConnCoc

section General

variable {G Qp LL O : Type} [Group G] [TopologicalSpace G] [Field Qp] [Field LL]
  [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]

theorem cocycle (Y Yt : LocLat G Qp LL O) (ι : LatHom Y.L Yt.L) (hι : Function.Injective ι.f)
    (yt : Yt.V) (f : G → ↥Y.L.T) (hf : ∀ g, ι.f (f g : Y.V) = Yt.ρ g yt - yt) (g h : G) :
    f (g * h) = f g + actT Y.L g (f h) := by
  apply Subtype.ext
  apply hι
  have e : ((f g + actT Y.L g (f h) : ↥Y.L.T) : Y.V) = (f g : Y.V) + Y.ρ g (f h : Y.V) := rfl
  rw [e, map_add (f := _), ι.equiv, hf, hf, hf, map_sub, map_mul, Module.End.mul_apply]
  abel

theorem continuous (Y Yt : LocLat G Qp LL O) (ι : LatHom Y.L Yt.L) (hι : Function.Injective ι.f)
    (yt : Yt.V) (f : G → ↥Y.L.T) (hf : ∀ g, ι.f (f g : Y.V) = Yt.ρ g yt - yt) :
    Continuous fun g => (f g : Y.V) := by
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective ι.f (LinearMap.ker_eq_bot.2 hι)
  have : ContinuousSMul LL Y.V := IsModuleTopology.toContinuousSMul LL Y.V
  have hc : Continuous r := IsModuleTopology.continuous_of_linearMap r
  have e : (fun g => (f g : Y.V)) = fun g => r (Yt.ρ g yt) + (- r yt) := by
    funext g
    rw [← sub_eq_add_neg, ← map_sub, ← hf]
    exact (LinearMap.congr_fun hr _).symm
  rw [e]
  exact (hc.comp (Yt.cont yt)).add continuous_const

end General

theorem locConst {l : ℕ} [Fact l.Prime] {G V : Type} [TopologicalSpace G] [AddCommGroup V]
    [Module ℚ_[l] V] [TopologicalSpace V] (T : Set V) {m : ℕ} (w : Module.Basis (Fin m) ℚ_[l] V)
    (hw : ∀ x : V, x ∈ T ↔ ∀ i, ‖w.repr x i‖ ≤ 1) (hc : Continuous w.equivFun)
    (F : G → V) (hF : Continuous F) (n : ℕ) (g : G) :
    ∀ᶠ h in nhds g, ∃ y ∈ T, F h - F g = (l ^ n : ℕ) • y := by
  have hl : ((l : ℚ_[l]) ^ n) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have key : ∀ i, ∀ᶠ h in nhds g,
      ‖((l : ℚ_[l]) ^ n)⁻¹ * (w.equivFun (F h) i - w.equivFun (F g) i)‖ < 1 := by
    intro i
    have c : Continuous fun h =>
        ‖((l : ℚ_[l]) ^ n)⁻¹ * (w.equivFun (F h) i - w.equivFun (F g) i)‖ :=
      (continuous_const.mul (((continuous_apply i).comp (hc.comp hF)).sub continuous_const)).norm
    apply c.continuousAt.eventually_lt continuousAt_const
    simp
  filter_upwards [Filter.eventually_all.2 key] with h hh
  refine ⟨((l : ℚ_[l]) ^ n)⁻¹ • (F h - F g), (hw _).2 fun i => ?_, ?_⟩
  · have := (hh i).le
    simpa [Module.Basis.equivFun_apply] using this
  · rw [← Nat.cast_smul_eq_nsmul ℚ_[l], smul_smul, Nat.cast_pow, mul_inv_cancel₀ hl, one_smul]

theorem conn : ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] (LL : FinExt l) (Y Yt : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) (ι : LatHom Y.L Yt.L), Function.Injective ι.f → ∀ (yt : Yt.V) (f : G → ↥Y.L.T), (∀ g, ι.f (f g : Y.V) = Yt.ρ g yt - yt) → (∀ g h, f (g * h) = f g + actT Y.L g (f h)) ∧ ∀ (n : ℕ) (g : G), ∀ᶠ h in nhds g, ∃ y : ↥Y.L.T, f h - f g = (l ^ n : ℕ) • y := by
  intro l _ G _ _ LL Y Yt ι hι yt f hf
  refine ⟨cocycle Y Yt ι hι yt f hf, fun n g => ?_⟩
  obtain ⟨m, w, hw, hc, -⟩ := GlobalTheory.Cyc.LatBasis.exists_basis l G LL Y
  have := locConst (Y.L.T : Set Y.V) w hw hc _ (continuous Y Yt ι hι yt f hf) n g
  filter_upwards [this] with h hh
  obtain ⟨y, hy, e⟩ := hh
  exact ⟨⟨y, hy⟩, Subtype.ext e⟩

end GlobalTheory.ConnCoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicActionOnRootTowerStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomic_action_on_root_tower : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (g : GQ l) (u : ℕ), (P.χQ g : ℚ_[l]) = (u : ℚ_[l]) → ∀ j : ℕ, AI.actT g (AI.εroot j) = AI.εroot j ^ u := by
  first | exact @GlobalTheory.ExpImage.actT_εroot_eq_pow | exact GlobalTheory.ExpImage.actT_εroot_eq_pow | (intros; apply GlobalTheory.ExpImage.actT_εroot_eq_pow <;> assumption)
end

