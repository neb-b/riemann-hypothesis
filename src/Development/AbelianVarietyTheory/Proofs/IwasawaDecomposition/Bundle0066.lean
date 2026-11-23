module

public import Mathlib
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLogAExtends
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0062
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisIncl
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
public import Formalism.SharpRestriction.GrowthBounds.DataG

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisLogTeichmullerUniqueGaloisFrobeniusBdR
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.LogFun

theorem partial_eq {R : Type} [CommRing R] (u : ℕ → R) (hu : ∀ k : ℕ, ((k + 1 : ℕ) : R) * u k = 1)
    (x s : R) (n : ℕ) (hn : IsUnit ((n.factorial : ℕ) : R))
    (hs : ((n.factorial : ℕ) : R) * s =
      ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : R) * x ^ (k + 1)) :
    s = ∑ k ∈ Finset.range n, (-1) ^ k * u k * x ^ (k + 1) := by
  apply hn.mul_left_cancel
  rw [hs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have h1 : n.factorial = n.factorial / (k + 1) * (k + 1) :=
    (Nat.div_mul_cancel (Nat.dvd_factorial k.succ_pos (Finset.mem_range.1 hk))).symm
  have h2 : ((n.factorial : ℕ) : R) = ((n.factorial / (k + 1) : ℕ) : R) * ((k + 1 : ℕ) : R) := by
    rw [← Nat.cast_mul, ← h1]
  generalize ((n.factorial / (k + 1) : ℕ) : R) = q at h2 ⊢
  rw [h2]
  linear_combination (-((-1) ^ k * q * x ^ (k + 1))) * hu k

theorem partial_sub_mem {R : Type} [CommRing R] (I : Ideal R) (u : ℕ → R) (x : R) (hx : x ∈ I)
    {n m : ℕ} (h : n ≤ m) :
    ∑ k ∈ Finset.range m, (-1) ^ k * u k * x ^ (k + 1) -
      ∑ k ∈ Finset.range n, (-1) ^ k * u k * x ^ (k + 1) ∈ I ^ n := by
  rw [← Finset.sum_Ico_eq_sub _ h]
  refine Ideal.sum_mem _ fun k hk => Ideal.mul_mem_left _ _ ?_
  exact Ideal.pow_le_pow_right (by have := (Finset.mem_Ico.1 hk).1; omega) (Ideal.pow_mem_pow hx (k + 1))

variable {l : ℕ} [Fact l.Prime]

theorem mu_mem {e : Per.Fl l} (he : e.untilt = 1) :
    algebraMap (Per.Ainf l) (Per.AinfP l) (mu e) ∈ Per.kerP l := by
  exact GlobalTheory.RingIface.alg_mem_kerP l (by rw [Model.theta_mu, he, sub_self])

theorem ev_alg (n : ℕ) (a : Per.AinfP l) :
    Per.ev l n (algebraMap (Per.AinfP l) (Per.BdRp l) a) = Ideal.Quotient.mk _ a :=
  GlobalTheory.RingIface.ev_alg l n a

theorem isLog_map {e : Per.Fl l} (he : e.untilt = 1) {t : Per.Acris l} (ht : IsLogA e t)
    {j : Per.Acris l →+* Per.BdRp l} (hj : IsCrisP j) : Per.IsLog l e (j t) := by
  refine GlobalTheory.CrisIncl.isLog_of_partial l e he _ fun n => ?_
  have hu : ∀ k : ℕ, ∃ u : Per.AinfP l, ((k + 1 : ℕ) : Per.AinfP l) * u = 1 := fun k =>
    (GlobalTheory.RingBasics.isUnit_nat l _ k.succ_ne_zero).exists_right_inv
  choose u hu using hu
  have hf : ∀ k : ℕ, IsUnit ((k.factorial : ℕ) : Per.AinfP l) := fun k =>
    GlobalTheory.RingBasics.isUnit_nat l _ k.factorial_ne_zero
  obtain ⟨d, hd⟩ := (hf n).exists_right_inv
  obtain ⟨c, hc⟩ : ∃ c : Per.AinfP l, ((n.factorial : ℕ) : Per.AinfP l) * c =
      ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) *
        (algebraMap (Per.Ainf l) (Per.AinfP l) (mu e)) ^ (k + 1) :=
    ⟨d * _, by rw [← mul_assoc, hd, one_mul]⟩
  have key := (_root_.GlobalTheory.MemLoc.crisP_unique_equivariant l j hj).2.2 n t (algebraMap (Per.AinfP l) (Per.BdRp l) c) (by
    intro r
    obtain ⟨N, hN⟩ := ht r
    obtain ⟨s, hs, z, hz⟩ := hN (max N n) (le_max_left _ _)
    refine ⟨s, z, 0, by rw [← hz]; ring, ?_⟩
    rw [map_zero, mul_zero, map_zero, ← map_sub, ev_alg, Ideal.Quotient.eq_zero_iff_mem,
      partial_eq u hu _ _ _ (hf _) hs, partial_eq u hu _ _ _ (hf _) hc, ← neg_sub]
    exact neg_mem (partial_sub_mem _ u _ (mu_mem he) (le_max_right _ _)))
  exact ⟨c, hc, by rw [key, ev_alg]⟩

theorem log_fun : ∀ (l : ℕ) [Fact l.Prime], ∀ (e : Per.Fl l) (t : Per.Acris l), e.untilt = 1 → IsLogA e t → (∀ t' : Per.Acris l, IsLogA e t' → t' = t) ∧ (∀ g : Per.Gq l, IsLogA (Per.σF g e) (sigA g t)) ∧ IsLogA (e ^ l) (phiA l t) ∧ ∀ j : Per.Acris l →+* Per.BdRp l, IsCrisP j → Per.IsLog l e (j t) :=
  fun _ _ _ _ he ht => ⟨fun _ h => Model.isLogA_unique h ht, fun g => Model.isLogA_sigA g ht,
    Model.isLogA_phiA ht, fun _ hj => isLog_map he ht hj⟩

end GlobalTheory.MemLoc.LogFun
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRFiltrationLaws
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.FilLaws

theorem toNat_iff_zpow {R K : Type} [CommRing R] [CommRing K] (ι : R →+* K) (ξ : R) (u : Kˣ)
    (hu : (u : K) = ι ξ) (a : ℤ) (x : K) :
    (∃ y : R, x * ι ξ ^ (-a).toNat = ι (ξ ^ a.toNat * y)) ↔ ∃ y : R, x = ((u ^ a : Kˣ) : K) * ι y := by
  refine exists_congr fun y => ?_
  rw [map_mul, map_pow, ← hu]
  have h : u ^ a * u ^ (-a).toNat = u ^ a.toNat := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add]
    congr 1
    omega
  have h' : ((u ^ a : Kˣ) : K) * (u : K) ^ (-a).toNat = (u : K) ^ a.toNat := by
    rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul, h]
  rw [← h', mul_right_comm]
  exact (u.isUnit.pow _).mul_left_inj

theorem exists_isEps (l : ℕ) [Fact l.Prime] : ∃ e : Per.Fl l, IsEps e := by
  obtain ⟨ζ, ε, h0, -, h1, hr⟩ := GlobalTheory.T.exists_compatible_rootsOfUnity_and_tilt_padic l
  refine ⟨ε, ?_, ?_⟩
  · have := hr 0
    rw [h0, map_one] at this
    exact Subtype.ext this
  · intro h
    have := hr 1
    have e : rootT ε 1 = 1 := h
    rw [e] at this
    apply h1
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← this, map_one]
    rfl

variable {l : ℕ} [Fact l.Prime]

theorem σDp_alg (g : Per.Gq l) (x : Per.AinfP l) :
    Per.σDp g (algebraMap (Per.AinfP l) (Per.BdRp l) x) =
      algebraMap (Per.AinfP l) (Per.BdRp l) (Per.extP (Per.σA g) x) :=
  GlobalTheory.RingIface.sigDp_alg l g x

theorem σD_alg (g : Per.Gq l) (y : Per.BdRp l) :
    Per.σD g (algebraMap (Per.BdRp l) (Per.BdR l) y) =
      algebraMap (Per.BdRp l) (Per.BdR l) (Per.σDp g y) :=
  GlobalTheory.RingIface.sigD_alg l g y

theorem σDp_mem_FilP (g : Per.Gq l) (n : ℕ) (y : Per.BdRp l) (hy : y ∈ Per.FilP l n) :
    Per.σDp g y ∈ Per.FilP l n := by
  obtain ⟨e, he⟩ := exists_isEps l
  obtain ⟨hP, -, -, -⟩ := _root_.GlobalTheory.MemLoc.filtration_eq_xi_pow l e he
  have hk := _root_.GlobalTheory.MemLoc.ker_localizedTheta_eq_span_xi l e he
  have h1 : algebraMap (Per.Ainf l) (Per.AinfP l) (xi e) ∈ Per.kerP l := by
    rw [hk]; exact Ideal.mem_span_singleton_self _
  have h2 : Per.extP (Per.σA g) (algebraMap (Per.Ainf l) (Per.AinfP l) (xi e)) ∈ Per.kerP l :=
    Ideal.mem_comap.1 (GlobalTheory.RingBasics.ker_σ g h1)
  rw [hk, Ideal.mem_span_singleton] at h2
  have h3 : aDp l (xi e) ∣ Per.σDp g (aDp l (xi e)) := by
    unfold aDp
    rw [RingHom.comp_apply, σDp_alg]
    exact map_dvd _ h2
  obtain ⟨z, rfl⟩ := (hP n y).1 hy
  rw [hP, map_mul, map_pow]
  exact (pow_dvd_pow_of_dvd h3 n).mul_right _

theorem σDp_xi (e : Per.Fl l) (he : IsEps e) (g : Per.Gq l) :
    ∃ c d : Per.BdRp l, Per.σDp g (aDp l (xi e)) = aDp l (xi e) * c ∧ c * d = 1 := by
  obtain ⟨hP, hreg, -, -⟩ := _root_.GlobalTheory.MemLoc.filtration_eq_xi_pow l e he
  have hξ : aDp l (xi e) ∈ Per.FilP l 1 := (hP 1 _).2 (by rw [pow_one])
  have hd : ∀ g : Per.Gq l, aDp l (xi e) ∣ Per.σDp g (aDp l (xi e)) := fun g => by
    have := (hP 1 _).1 (σDp_mem_FilP g 1 _ hξ)
    rwa [pow_one] at this
  obtain ⟨c, hc⟩ := hd g
  obtain ⟨c', hc'⟩ := hd g⁻¹
  have hinv : Per.σDp g (Per.σDp g⁻¹ (aDp l (xi e))) = aDp l (xi e) := by
    change Per.σDp g (Per.σDp g⁻¹ (algebraMap (Per.AinfP l) (Per.BdRp l) _)) =
      algebraMap (Per.AinfP l) (Per.BdRp l) _
    rw [σDp_alg, σDp_alg, GlobalTheory.RingBasics.extP_inv]
  refine ⟨c, Per.σDp g c', hc, ?_⟩
  rw [hc', map_mul, hc] at hinv
  have := hreg (c * Per.σDp g c' - 1) (by rw [mul_sub, mul_one, ← mul_assoc, hinv, sub_self])
  exact sub_eq_zero.1 this

theorem eq_zero_of_forall_mem_FilP (y : Per.BdRp l) (hy : ∀ n, y ∈ Per.FilP l n) : y = 0 := by
  obtain ⟨e, he⟩ := exists_isEps l
  obtain ⟨hP, -, hc, -⟩ := _root_.GlobalTheory.MemLoc.filtration_eq_xi_pow l e he
  refine hc.toIsHausdorff.haus y fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact (hP n y).1 (hy n)

end GlobalTheory.MemLoc.FilLaws


open GlobalTheory.MemLoc.FilLaws in
theorem GlobalTheory.MemLoc.filD_laws : ∀ (l : ℕ) [Fact l.Prime], (∀ a : ℤ, Per.FilD l (a + 1) ≤ Per.FilD l a) ∧ (1 : Per.BdR l) ∈ Per.FilD l 0 ∧ (∀ (a b : ℤ) (x y : Per.BdR l), x ∈ Per.FilD l a → y ∈ Per.FilD l b → x * y ∈ Per.FilD l (a + b)) ∧ (∀ x : Per.BdR l, ∃ a, x ∈ Per.FilD l a) ∧ (∀ x : Per.BdR l, (∀ a, x ∈ Per.FilD l a) → x = 0) ∧ (∀ (g : Per.Gq l) (a : ℤ) (x : Per.BdR l), x ∈ Per.FilD l a → Per.σD g x ∈ Per.FilD l a) ∧ ∀ (n : ℕ) (y : Per.BdRp l), algebraMap (Per.BdRp l) (Per.BdR l) y ∈ Per.FilD l n ↔ y ∈ Per.FilP l n := by
  intro l _
  obtain ⟨e, he⟩ := exists_isEps l
  obtain ⟨hdom, hinj, hfield, hden⟩ := _root_.GlobalTheory.MemLoc.BdRField.bdR_isField l
  obtain ⟨hP, hreg, -, -⟩ := _root_.GlobalTheory.MemLoc.filtration_eq_xi_pow l e he
  have hD := _root_.GlobalTheory.MemLoc.mem_FilD_iff_xi_pow l e he
  have hden := hden e he
  have hσ := σDp_xi e he
  generalize aDp l (xi e) = ξ at hP hreg hD hden hσ
  have hne : algebraMap (Per.BdRp l) (Per.BdR l) ξ ≠ 0 := by
    intro h
    have h0 : ξ = 0 := hinj (by rw [h, map_zero])
    exact one_ne_zero (hreg 1 (by rw [h0, zero_mul]))
  obtain ⟨v, hv⟩ := hfield.mul_inv_cancel hne
  obtain ⟨u, hu⟩ : IsUnit (algebraMap (Per.BdRp l) (Per.BdR l) ξ) := IsUnit.of_mul_eq_one v hv
  have hZ : ∀ (a : ℤ) (x : Per.BdR l), x ∈ Per.FilD l a ↔
      ∃ y, x = ((u ^ a : (Per.BdR l)ˣ) : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) y :=
    fun a x => (hD a x).trans (toNat_iff_zpow _ ξ u hu a x)
  have hlast : ∀ (n : ℕ) (y : Per.BdRp l),
      algebraMap (Per.BdRp l) (Per.BdR l) y ∈ Per.FilD l n ↔ y ∈ Per.FilP l n := by
    intro n y
    rw [hZ, hP, zpow_natCast, Units.val_pow_eq_pow_val, hu]
    refine exists_congr fun z => ?_
    rw [← map_pow, ← map_mul]
    exact hinj.eq_iff
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hlast⟩
  · intro a x hx
    obtain ⟨y, hy⟩ := (hZ _ _).1 hx
    refine (hZ _ _).2 ⟨ξ * y, ?_⟩
    rw [hy, zpow_add_one, Units.val_mul, hu, map_mul, mul_assoc]
  · exact (hZ _ _).2 ⟨1, by rw [zpow_zero, Units.val_one, map_one, mul_one]⟩
  · intro a b x y hx hy
    obtain ⟨x', rfl⟩ := (hZ _ _).1 hx
    obtain ⟨y', rfl⟩ := (hZ _ _).1 hy
    refine (hZ _ _).2 ⟨x' * y', ?_⟩
    rw [zpow_add, Units.val_mul, map_mul, mul_mul_mul_comm]
  · intro x
    obtain ⟨n, y, hy⟩ := hden x
    refine ⟨-(n : ℤ), (hD _ _).2 ⟨y, ?_⟩⟩
    rw [neg_neg, Int.toNat_natCast, Int.toNat_neg_natCast, pow_zero, one_mul, hy]
  · intro x hx
    obtain ⟨y, hy⟩ := (hZ _ _).1 (hx 0)
    rw [zpow_zero, Units.val_one, one_mul] at hy
    subst hy
    rw [eq_zero_of_forall_mem_FilP y fun n => (hlast n y).1 (hx n), map_zero]
  · intro g a x hx
    obtain ⟨c, d, hc, hcd⟩ := hσ g
    obtain ⟨y, hy⟩ := (hD _ _).1 hx
    have h1 := congrArg (Per.σD g) hy
    rw [map_mul, map_pow, σD_alg, σD_alg, map_mul (Per.σDp g), map_pow, hc] at h1
    refine (hD _ _).2 ⟨d ^ (-a).toNat * (c ^ a.toNat * Per.σDp g y), ?_⟩
    have h2 : algebraMap (Per.BdRp l) (Per.BdR l) ξ =
        algebraMap (Per.BdRp l) (Per.BdR l) (ξ * c) * algebraMap (Per.BdRp l) (Per.BdR l) d := by
      rw [← map_mul, mul_assoc, hcd, mul_one]
    rw [h2, mul_pow, ← mul_assoc, h1, ← map_pow, ← map_mul]
    congr 1
    ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvalRepsSurjective
section
open MvPolynomial Formalism.MainNotions.G Formalism.GradedWeylDivisibility

noncomputable section

namespace GlobalTheory.ClassRank

variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {P : Places p O Kf}

theorem gPos_mul (v : Fin P.nV) (s : Fin (P.n' v)) (A B : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v)) :
    P.gPos v s (A * B) = P.gPos v s A * P.gPos v s B := by
  ext a b
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Places.gPos, Matrix.mul_apply, map_sum, map_mul]

theorem gPos_one (v : Fin P.nV) (s : Fin (P.n' v)) : P.gPos v s 1 = 1 := by
  ext a b
  by_cases h : a = b <;> simp [Places.gPos, Matrix.one_apply, h]

theorem subst_comp (G H : ∀ v, Fin (P.n' v) → Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) Kf) :
    (P.subst G).comp (P.subst H) = P.subst fun v s => H v s * G v s := by
  apply MvPolynomial.algHom_ext
  intro x
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Places.subst, AlgHom.comp_apply, aeval_X, map_sum, map_mul, algHom_C, algebraMap_eq,
    Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

theorem subst_one : (P.subst fun _ _ => 1) = AlgHom.id Kf _ := by
  apply MvPolynomial.algHom_ext
  intro x
  simp only [Places.subst, aeval_X, AlgHom.id_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single x.2.2.1]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

theorem natAct_mul (A B : ∀ v, GL (Fin (P.m + 1)) (P.Qq v)) (F : P.Xsp) :
    P.natAct (fun v => A v * B v) F = P.natAct A (P.natAct B F) := by
  have h := congrArg (fun φ => φ F) (subst_comp (P := P)
    (fun v s => P.gPos v s ((A v)⁻¹ : GL (Fin (P.m + 1)) (P.Qq v)))
    (fun v s => P.gPos v s ((B v)⁻¹ : GL (Fin (P.m + 1)) (P.Qq v))))
  simp only [AlgHom.comp_apply] at h
  simp only [Places.natAct, LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_smul, smul_smul, h,
    mul_inv_rev, Units.val_mul, gPos_mul, Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib]
  first | rfl | (congr 1; exact mul_comm _ _)

theorem natAct_one (F : P.Xsp) : P.natAct (fun _ => 1) F = F := by
  simp only [Places.natAct, inv_one, Units.val_one, gPos_one, Matrix.det_one, one_zpow, Finset.prod_const_one,
    one_smul, subst_one, AlgHom.toLinearMap_apply, AlgHom.id_apply]

variable (C : Level P)

theorem actX_mul (γ δ : C.Γ) (F : P.Xsp) : C.actX (γ * δ) F = C.actX γ (C.actX δ F) := by
  simp only [Level.actX, map_mul]
  exact natAct_mul _ _ F

theorem actX_one (F : P.Xsp) : C.actX 1 F = F := by
  simp only [Level.actX, map_one]
  exact natAct_one F

theorem smul_mul (γ δ : C.Γ) (L : P.Tup) : C.smul (γ * δ) L = C.smul γ (C.smul δ L) := by
  funext v
  simp only [Level.smul, map_mul, Units.val_mul, Matrix.mulVecLin_mul, ← Submodule.map_comp]
  rfl

theorem smul_one (L : P.Tup) : C.smul 1 L = L := by
  funext v
  simp only [Level.smul, map_one, Units.val_one, Matrix.mulVecLin_one]
  exact Submodule.map_id _

theorem isLatTup_smul (γ : C.Γ) {L : P.Tup} (hL : P.IsLatTup L) : P.IsLatTup (C.smul γ L) := by
  intro v
  obtain ⟨g, hg, e⟩ := hL v
  refine ⟨(C.act v γ : Matrix _ _ _) * g, ?_, ?_⟩
  · rw [Matrix.det_mul]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (C.act v γ).isUnit).mul hg
  · simp only [Level.smul, e, colSpan, Submodule.map_span, ← Set.range_comp]
    congr 2

theorem isLatTup_smul_iff (γ : C.Γ) (L : P.Tup) : P.IsLatTup (C.smul γ L) ↔ P.IsLatTup L := by
  refine ⟨fun h => ?_, isLatTup_smul C γ⟩
  have := isLatTup_smul C γ⁻¹ h
  rwa [← smul_mul, inv_mul_cancel, smul_one] at this

theorem mem_funMod_iff (Hv : P.Tup → Submodule O P.Xsp) (F : P.Tup → P.Xsp) :
    F ∈ C.funMod Hv ↔ (∀ L, P.IsLatTup L → F L ∈ Hv L) ∧ (∀ L, ¬ P.IsLatTup L → F L = 0) ∧
      ∀ γ L, F (C.smul γ L) = (C.χ γ : O) • C.actX γ (F L) := by
  simp only [Level.funMod, Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mem_ker,
    LinearMap.proj_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, sub_eq_zero, and_assoc,
    LinearMap.restrictScalars_apply]

structure IsReps {ι : Type} (rep : ι → P.Tup) : Prop where
  lat : ∀ i, P.IsLatTup (rep i)
  surj : ∀ L, P.IsLatTup L → ∃ i γ, L = C.smul γ (rep i)
  inj : ∀ i j γ, C.smul γ (rep i) = rep j → i = j

def evalReps (Hv : P.Tup → Submodule O P.Xsp) {ι : Type} {rep : ι → P.Tup} (hr : IsReps C rep) :
    C.funMod Hv →ₗ[O] ∀ i, Hv (rep i) where
  toFun F i := ⟨F.1 (rep i), ((mem_funMod_iff C Hv F.1).1 F.2).1 _ (hr.lat i)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem evalReps_injective (Hv : P.Tup → Submodule O P.Xsp) {ι : Type} {rep : ι → P.Tup} (hr : IsReps C rep) :
    Function.Injective (evalReps C Hv hr) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro F hF
  obtain ⟨-, h0, hγ⟩ := (mem_funMod_iff C Hv F.1).1 F.2
  apply Subtype.ext
  funext L
  by_cases hL : P.IsLatTup L
  · obtain ⟨i, γ, rfl⟩ := hr.surj L hL
    have : F.1 (rep i) = 0 := congrArg Subtype.val (congrFun hF i)
    rw [hγ, this, map_zero, smul_zero]
    rfl
  · exact h0 L hL

theorem evalReps_surjective (Hv : P.Tup → Submodule O P.Xsp)
    (hact : ∀ (γ : C.Γ) (L : P.Tup), P.IsLatTup L →
      (Hv L).map ((C.actX γ).restrictScalars O) = Hv (C.smul γ L))
    (htriv : C.TrivStab) {ι : Type} {rep : ι → P.Tup} (hr : IsReps C rep) :
    Function.Surjective (evalReps C Hv hr) := by
  classical
  intro x
  choose idx gam hgam using hr.surj
  let F : P.Tup → P.Xsp := fun L =>
    if h : P.IsLatTup L then (C.χ (gam L h) : O) • C.actX (gam L h) (x (idx L h) : P.Xsp) else 0
  have key : ∀ i γ, F (C.smul γ (rep i)) = (C.χ γ : O) • C.actX γ (x i : P.Xsp) := by
    intro i γ
    have h := isLatTup_smul C γ (hr.lat i)
    have e := hgam _ h
    simp only [F, dif_pos h]
    generalize idx _ h = j at e ⊢
    generalize gam _ h = δ at e ⊢
    have e' : C.smul (δ⁻¹ * γ) (rep i) = rep j := by
      rw [smul_mul, e, ← smul_mul, inv_mul_cancel, smul_one]
    obtain rfl := hr.inj _ _ _ e'
    obtain rfl : δ = γ := inv_mul_eq_one.1 (htriv _ _ (hr.lat i) e')
    rfl
  refine ⟨⟨F, (mem_funMod_iff C Hv F).2 ⟨fun L hL => ?_, fun L hL => dif_neg hL, fun γ L => ?_⟩⟩, ?_⟩
  · obtain ⟨i, γ, rfl⟩ := hr.surj L hL
    rw [key, ← hact γ _ (hr.lat i)]
    exact Submodule.smul_mem _ _ ⟨_, (x i).2, rfl⟩
  · by_cases hL : P.IsLatTup L
    · obtain ⟨i, δ, rfl⟩ := hr.surj L hL
      rw [← smul_mul, key, key, map_mul, Units.val_mul, mul_smul, actX_mul]
      congr 1
      exact (((C.actX γ).restrictScalars O).map_smul _ _).symm
    · have h1 : F L = 0 := dif_neg hL
      have h2 : F (C.smul γ L) = 0 := dif_neg (fun h => hL ((isLatTup_smul_iff C γ L).1 h))
      rw [h1, h2, map_zero, smul_zero]
  · funext i
    apply Subtype.ext
    have := key i 1
    rw [smul_one, map_one, Units.val_one, one_smul, actX_one] at this
    exact this

def evalRepsEquiv (Hv : P.Tup → Submodule O P.Xsp)
    (hact : ∀ (γ : C.Γ) (L : P.Tup), P.IsLatTup L →
      (Hv L).map ((C.actX γ).restrictScalars O) = Hv (C.smul γ L))
    (htriv : C.TrivStab) {ι : Type} {rep : ι → P.Tup} (hr : IsReps C rep) :
    C.funMod Hv ≃ₗ[O] ∀ i, Hv (rep i) :=
  LinearEquiv.ofBijective (evalReps C Hv hr) ⟨evalReps_injective C Hv hr, evalReps_surjective C Hv hact htriv hr⟩

theorem d_eq_card_mul (G : GAtP p) (hinj : Function.Injective (algebraMap G.O G.Kf)) (htriv : G.TrivStab)
    (hact : ∀ c, (G.lev c).ActHW) {ι : G.comp → Type} [∀ c, Fintype (ι c)] (rep : ∀ c, ι c → G.P.Tup)
    (hr : ∀ c, IsReps (G.lev c) (rep c)) (hfg : ∀ c i, (G.P.HtupW (rep c i)).FG) (n : ℕ)
    (hn : ∀ c i, Module.finrank G.O (G.P.HtupW (rep c i)) = n) :
    G.d = (∑ c, Fintype.card (ι c)) * n := by
  have : FaithfulSMul G.O G.Kf := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have : Module.IsTorsionFree G.O G.P.Xsp := Module.IsTorsionFree.trans G.Kf
  have : ∀ c i, Module.Finite G.O (G.P.HtupW (rep c i)) := fun c i => Module.Finite.iff_fg.2 (hfg c i)
  have : ∀ c i, Module.Free G.O (G.P.HtupW (rep c i)) := fun c i => inferInstance
  let e0 : G.M ≃ₗ[G.O] ∀ c, (G.lev c).funMod G.P.HtupW :=
    { toFun := fun F c => ⟨F.1 c, F.2 c (Set.mem_univ c)⟩
      invFun := fun F => ⟨fun c => (F c).1, fun c _ => (F c).2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e1 := e0.trans (LinearEquiv.piCongrRight fun c =>
    evalRepsEquiv (G.lev c) G.P.HtupW (hact c) (htriv c) (hr c))
  rw [GAtP.d, e1.finrank_eq, Module.finrank_pi_fintype, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Module.finrank_pi_fintype]
  simp [hn]

end GlobalTheory.ClassRank
end
end

