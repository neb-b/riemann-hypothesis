module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0051
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0049
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0043
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0050

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTildeFiniteE
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

section ReadOnCharts

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
  (M : FinGradedSub (S := S) (x := x) E) (c : ℤ)

def chartVal {n : ℕ} (y : Cech.Cochain (locSys S N M.coneSubE) n) (I : Cech.Idx (support x) n) : E :=
  coeffE S x E c (locConeE M I.1.1 I.1.2.2 (y ⟨⟨I.1.1, I.1.2.1, Finset.subset_univ _⟩, I.2⟩))

theorem chartVal_zero {n : ℕ} (I : Cech.Idx (support x) n) :
    chartVal M c (0 : Cech.Cochain (locSys S N M.coneSubE) n) I = 0 := by
  unfold chartVal
  rw [Pi.zero_apply, map_zero, map_zero]

theorem chartVal_add {n : ℕ} (y y' : Cech.Cochain (locSys S N M.coneSubE) n) (I : Cech.Idx (support x) n) :
    chartVal M c (y + y') I = chartVal M c y I + chartVal M c y' I := by
  unfold chartVal
  rw [Pi.add_apply, map_add (f := _), map_add (f := _)]

theorem chartVal_smul {n : ℕ} (a : S) (y : Cech.Cochain (locSys S N M.coneSubE) n)
    (I : Cech.Idx (support x) n) : chartVal M c (a • y) I = a • chartVal M c y I := by
  unfold chartVal
  rw [Pi.smul_apply, LinearMap.map_smul_of_tower, map_smul]

theorem chartVal_mem {n : ℕ} {y : Cech.Cochain (locSys S N M.coneSubE) n}
    (hy : y ∈ Cech.Cdeg (locSys S N M.coneSubE) (degLoc M.coneGradedE c) n) (I : Cech.Idx (support x) n) :
    chartVal M c y I ∈ (M.tildeSys c).sub I.1 := by
  obtain ⟨v, hv, hyv⟩ := locConeE_degLoc M c _ I.1.2.2
    (hy ⟨⟨I.1.1, I.1.2.1, Finset.subset_univ _⟩, I.2⟩ (Set.mem_univ _))
  unfold chartVal
  rw [hyv, coeffE_singleE_same]
  exact hv

theorem chartVal_d {n : ℕ} (y : Cech.Cochain (locSys S N M.coneSubE) n) (J : Cech.Idx (support x) (n + 1)) :
    chartVal M c (Cech.d (locSys S N M.coneSubE) locResS n y) J =
      ∑ j : J.1.1, Cech.sgn J.1.1 j • chartVal M c y (Cech.face J j) := by
  refine (congrArg (coeffE S x E c)
    (locConeE_d M y ⟨⟨J.1.1, J.1.2.1, Finset.subset_univ _⟩, J.2⟩ J.1.2.2)).trans ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul]
  rfl

def toTildeC {n : ℕ} (y : Cech.Cochain (locSys S N M.coneSubE) n)
    (hy : y ∈ Cech.Cdeg (locSys S N M.coneSubE) (degLoc M.coneGradedE c) n) :
    Cech.Cochain (fun I : Chart x => ↥((M.tildeSys c).sub I)) n :=
  fun I => ⟨chartVal M c y I, chartVal_mem M c hy I⟩

theorem coe_d_toTildeC {n : ℕ} (y : Cech.Cochain (locSys S N M.coneSubE) n)
    (hy : y ∈ Cech.Cdeg (locSys S N M.coneSubE) (degLoc M.coneGradedE c) n) (J : Cech.Idx (support x) (n + 1)) :
    ((Cech.d (fun I : Chart x => ↥((M.tildeSys c).sub I)) (M.tildeSys c).res n (toTildeC M c y hy) J : _) : E) =
      chartVal M c (Cech.d (locSys S N M.coneSubE) locResS n y) J := by
  rw [coe_d_sub, chartVal_d]
  rfl

def toTildeCocy (n : ℕ) :
    Cech.cocyDeg (locSys S N M.coneSubE) (degLoc M.coneGradedE c) locResS n →ₗ[S]
      LinearMap.ker (Cech.d (fun I : Chart x => ↥((M.tildeSys c).sub I)) (M.tildeSys c).res n) where
  toFun y := ⟨toTildeC M c y.1 y.2.2, LinearMap.mem_ker.mpr (funext fun J => Subtype.ext (by
    rw [coe_d_toTildeC, LinearMap.mem_ker.mp y.2.1, chartVal_zero]
    rfl))⟩
  map_add' y y' := Subtype.ext (funext fun I => Subtype.ext (chartVal_add M c y.1 y'.1 I))
  map_smul' a y := Subtype.ext (funext fun I => Subtype.ext (chartVal_smul M c a y.1 I))

set_option synthInstance.maxHeartbeats 200000 in
def toTildeH (n : ℕ) : cohom M.coneGradedE n c →ₗ[S] (M.tildeSys c).H n :=
  Submodule.liftQ _ ((Submodule.mkQ _).comp (toTildeCocy M c n)) (by
    intro y hy
    rw [Submodule.mem_comap] at hy
    refine LinearMap.mem_ker.mpr ((Submodule.Quotient.mk_eq_zero _).mpr ?_)
    cases n with
    | zero =>
      change (y : Cech.Cochain (locSys S N M.coneSubE) 0) ∈ (⊥ : Submodule S _) at hy
      rw [Submodule.mem_bot] at hy
      change toTildeC M c y.1 y.2.2 ∈ (⊥ : Submodule S _)
      rw [Submodule.mem_bot]
      funext I
      apply Subtype.ext
      change chartVal M c (y : Cech.Cochain (locSys S N M.coneSubE) 0) I = 0
      rw [hy, chartVal_zero]
    | succ k =>
      change (y : Cech.Cochain (locSys S N M.coneSubE) (k + 1)) ∈
        (Cech.Cdeg (locSys S N M.coneSubE) (degLoc M.coneGradedE c) k).map
          (Cech.d (locSys S N M.coneSubE) locResS k) at hy
      obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.mp hy
      change toTildeC M c y.1 y.2.2 ∈
        LinearMap.range (Cech.d (fun I : Chart x => ↥((M.tildeSys c).sub I)) (M.tildeSys c).res k)
      refine ⟨toTildeC M c z hz, funext fun J => Subtype.ext ?_⟩
      rw [coe_d_toTildeC]
      change _ = chartVal M c (y : Cech.Cochain (locSys S N M.coneSubE) (k + 1)) J
      rw [← hzy])

theorem d_liftCochain_any {n : ℕ} (t : Cech.Cochain (fun I : Chart x => ↥((M.tildeSys c).sub I)) n)
    (ht : Cech.d (fun I : Chart x => ↥((M.tildeSys c).sub I)) (M.tildeSys c).res n t = 0) :
    Cech.d (locSys S N M.coneSubE) locResS n (liftCochain M c t) = 0 := by
  funext K
  change _ = 0
  by_cases hK : K.1.1 ⊆ support x
  · apply locConeE_injective M K.1.1 hK
    rw [locConeE_d M (liftCochain M c t) K hK, map_zero]
    have h0 := coe_d_sub (M.tildeSys c) t ⟨⟨K.1.1, K.1.2.1, hK⟩, K.2⟩
    rw [ht] at h0
    calc ∑ j : K.1.1, Cech.sgn K.1.1 j • locConeE M (Cech.face K j).1.1
          ((Cech.face_subset K j).trans hK) (liftCochain M c t (Cech.face K j))
        = ∑ j : K.1.1, Cech.sgn K.1.1 j • singleE S x E c
            (t (Cech.face (⟨⟨K.1.1, K.1.2.1, hK⟩, K.2⟩ : Cech.Idx (support x) (n + 1)) j) : E) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [liftCochain_of M c t _ ((Cech.face_subset K j).trans hK)]
          congr 1
          exact locConeE_liftTilde M c _ _ _
      _ = singleE S x E c (∑ j : K.1.1, Cech.sgn K.1.1 j •
            (t (Cech.face (⟨⟨K.1.1, K.1.2.1, hK⟩, K.2⟩ : Cech.Idx (support x) (n + 1)) j) : E)) := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_zsmul]
      _ = 0 := by
          rw [← h0]
          exact map_zero _
  · have := locModE_subsingleton (S := S) M (Finset.not_subset.mp hK).choose_spec.1
      (by simpa [mem_support] using (Finset.not_subset.mp hK).choose_spec.2)
    exact Subsingleton.elim _ _

theorem chartVal_liftCochain {n : ℕ} (t : Cech.Cochain (fun I : Chart x => ↥((M.tildeSys c).sub I)) n)
    (I : Cech.Idx (support x) n) : chartVal M c (liftCochain M c t) I = (t I : E) := by
  have e1 := liftCochain_of M c t ⟨⟨I.1.1, I.1.2.1, Finset.subset_univ _⟩, I.2⟩ I.1.2.2
  have e2 := locConeE_liftTilde M c ⟨I.1.1, I.1.2.1, Finset.subset_univ _⟩ I.1.2.2 (t I)
  unfold chartVal
  rw [e1]
  exact (congrArg (coeffE S x E c) e2).trans (coeffE_singleE_same _ _)

set_option synthInstance.maxHeartbeats 200000 in
theorem toTildeH_surjective (n : ℕ) : Function.Surjective (toTildeH M c n) := by
  intro q
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  refine ⟨Submodule.Quotient.mk ⟨liftCochain M c t.1,
    d_liftCochain_any M c t.1 (LinearMap.mem_ker.mp t.2), liftCochain_mem M c t.1⟩, ?_⟩
  change Submodule.Quotient.mk (toTildeCocy M c n _) = Submodule.Quotient.mk t
  congr 1
  exact Subtype.ext (funext fun I => Subtype.ext (chartVal_liftCochain M c t.1 I))

end ReadOnCharts

theorem TildeFiniteE.proof (h : SerreFinite.Statement.{u, v}) : TildeFiniteE.Statement.{u, v, w} := by
  intro S _ _ Ω _ _ N x E _ _ _ _ M i c
  have : Module.Finite S (cohom M.coneGradedE i c) :=
    h S N M.coneSubE M.coneGradedE M.coneSubE_finite i c
  exact Module.Finite.of_surjective (toTildeH M c i) (toTildeH_surjective M c i)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleHilbert
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open Filter

noncomputable section

universe u w

namespace VeryAmpleHilbert

theorem exists_slice (Q : MvPolynomial (Fin 2) ℚ) (e : ℕ) (hQ : Q.totalDegree ≤ e) (c : ℚ) :
    ∃ p : Polynomial ℚ, p.natDegree ≤ e ∧ p.coeff e = Q.coeff (Finsupp.single 0 e) ∧
      ∀ a : ℚ, p.eval a = MvPolynomial.eval ![a, c] Q := by
  have hdeg : ∀ m ∈ Q.support, m 0 + m 1 ≤ e := fun m hm => by
    have := MvPolynomial.le_totalDegree hm
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two] at this
    omega
  refine ⟨∑ m ∈ Q.support, Polynomial.C (Q.coeff m * c ^ m 1) * Polynomial.X ^ m 0, ?_, ?_, ?_⟩
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
    refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
    have := hdeg m hm
    omega
  · rw [Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single (Finsupp.single 0 e)]
    · simp
    · intro m hm hne
      rw [if_neg]
      intro hme
      apply hne
      have := hdeg m hm
      ext i
      fin_cases i
      · simp [hme]
      · simp
        omega
    · intro h
      rw [MvPolynomial.notMem_support_iff.mp h]
      simp
  · intro a
    rw [Polynomial.eval_finsetSum, MvPolynomial.eval_eq']
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Fin.prod_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    ring

theorem fwdDiff_iter_eval (p : Polynomial ℚ) (e : ℕ) (hp : p.natDegree ≤ e) (y : ℚ) :
    (fwdDiff 1)^[e] p.eval y = e.factorial * p.coeff e := by
  rcases hp.lt_or_eq with h | h
  · rw [Polynomial.fwdDiff_iter_eq_zero_of_degree_lt h, Polynomial.coeff_eq_zero_of_natDegree_lt h]
    simp
  · subst h
    rw [Polynomial.fwdDiff_iter_degree_eq_factorial]
    simp only [Pi.smul_apply, Pi.natCast_apply, smul_eq_mul]
    rw [Polynomial.leadingCoeff, mul_comm]

theorem sum_subsets_eq_fwdDiff (e : ℕ) (f : ℚ → ℚ) :
    ∑ T : Finset (Fin e), (-1 : ℚ) ^ (e - T.card) * f T.card = (fwdDiff 1)^[e] f 0 := by
  rw [fwdDiff_iter_eq_sum_shift, ← Finset.powerset_univ,
    Finset.sum_powerset_apply_card (fun m => (-1 : ℚ) ^ (e - m) * f m), Finset.card_univ, Fintype.card_fin]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [zsmul_eq_mul, nsmul_eq_mul]
  ring

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem foldl_twist_const (Q : SubSystem k x Ω) {n : ℕ} (l : List (Fin n)) (m : ℕ) :
    l.foldl (fun F _ => F.twist Q) (Q.pow m) = Q.pow (m + l.length) := by
  induction l generalizing m with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldl_cons, List.length_cons]
    change l.foldl _ (Q.pow (m + 1)) = _
    rw [ih]
    congr 1
    omega

theorem tensorSub_const (Q : SubSystem k x Ω) {n : ℕ} (T : Finset (Fin n)) :
    tensorSub (fun _ : Fin n => Q) T = Q.pow T.card := by
  have h := foldl_twist_const Q ((List.finRange n).filter (· ∈ T)) 0
  rw [zero_add] at h
  unfold tensorSub
  refine h.trans ?_
  congr 1
  rw [← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _)]
  congr 1
  ext i
  simp

end VeryAmpleHilbert


open VeryAmpleHilbert in
theorem VeryAmpleHilbert.proof (hS : VeryAmpleSnapper.Statement.{u, w}) : VeryAmpleHilbert.Statement.{u, w} := by
  intro k _ Ω _ _ N x e Nb hZ hN
  obtain ⟨hfin, Q, c₀, hdeg, hQ, hQ0⟩ := hS k Ω N x e Nb hZ hN
  have hpow : ∀ n : ℕ, twistMul Nb.toSubSystem n 0 = Nb.toSubSystem.pow n := fun n =>
    SubSystem.twist_twistSys_zero _
  refine ⟨fun n => hpow n ▸ hfin n 0, ?_⟩
  obtain ⟨P, hPdeg, hPe, hPev⟩ := exists_slice Q e hdeg 0
  refine ⟨P, hPdeg, ?_, ?_⟩
  · obtain ⟨j, hj⟩ := hZ.relevant
    have hxj : x j ≠ 0 := fun h0 => hj ((mem_primeOf_of_isHomogeneous x
      (MvPolynomial.isHomogeneous_X k j)).mpr (by rw [MvPolynomial.aeval_X, h0]))
    have hsum : ∀ c : ℕ, c₀ ≤ c → (interSum (primeOf (S := k) x) (fun _ : Fin e => Nb.toSubSystem) c : ℚ) =
        e.factorial * Q.coeff (Finsupp.single 0 e) := by
      intro c hc
      obtain ⟨p, hpd, hpe, hpv⟩ := exists_slice Q e hdeg c
      rw [← hpe, ← fwdDiff_iter_eval p e hpd 0, funext hpv, ← sum_subsets_eq_fwdDiff, interSum]
      push_cast
      refine Finset.sum_congr rfl fun T _ => ?_
      rw [tensorSub_const, SectionsOverLocalization.restrLen_primeOf_eq_finrank x hxj, Int.cast_natCast]
      congr 1
      have h := hQ T.card c hc
      rw [Int.cast_natCast] at h
      exact h
    set z := interSum (primeOf (S := k) x) (fun _ : Fin e => Nb.toSubSystem) c₀.toNat
    have hz : ∀ c : ℕ, c₀.toNat ≤ c →
        interSum (primeOf (S := k) x) (fun _ : Fin e => Nb.toSubSystem) c = z := fun c hc => by
      have h1 := hsum c (by omega)
      rw [← hsum c₀.toNat (by omega)] at h1
      exact_mod_cast h1
    have hlim : interNum (primeOf (S := k) x) (fun _ : Fin e => Nb.toSubSystem) = z :=
      (tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨c₀.toNat, fun c hc => (hz c hc).symm⟩)).limUnder_eq
    rw [hlim, hsum c₀.toNat (by omega), hPe, mul_comm]
  · filter_upwards [hQ0] with n hn
    rw [hn, hPev]

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SegreLiftMapMap
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing)
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver mConeMapOver)

noncomputable section

namespace SegreFibreIdeal

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
  {K : Type} [Fintype K] {ι : K → Type}

def thetaVal (ι : K → Type) (R : Type) [CommRing R] : (Σ k, segreIdx ι k) → Polynomial (MRing ι R)
  | ⟨Sum.inl _, c⟩ => Polynomial.X * Polynomial.C (∏ k, X ⟨k, c k⟩)
  | ⟨Sum.inr k, i⟩ => Polynomial.C (X ⟨k, i⟩)

def theta (ι : K → Type) (R : Type) [CommRing R] : MRing (segreIdx ι) R →+* Polynomial (MRing ι R) :=
  eval₂Hom (Polynomial.C.comp C) (thetaVal ι R)

def chi (K : Type) [Fintype K] : MvPolynomial (Unit ⊕ K) Ω →+* Polynomial (MvPolynomial K Ω) :=
  eval₂Hom (Polynomial.C.comp C)
    (Sum.elim (fun _ => Polynomial.X * Polynomial.C (∏ k, X k)) (fun k => Polynomial.C (X k)))

theorem map_cone_theta (y : (Σ k, ι k) → Ω) :
    (Polynomial.mapRingHom (mConeMapOver O y).toRingHom).comp (theta ι O) =
      (chi K).comp (mConeMapOver O (segreJoin y)).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [theta, chi, mConeMapOver]
  · rintro ⟨(u | k), i⟩
    · simp [theta, thetaVal, chi, mConeMapOver, segreJoin, IndefiniteRowSideFullHecke.Kleiman2.joinVec,
        IndefiniteRowSideFullHecke.Kleiman2.oneBlock, NumbersDVR.segreVec, Polynomial.map_prod, Finset.prod_mul_distrib]
      ring
    · simp [theta, thetaVal, chi, mConeMapOver, segreJoin, IndefiniteRowSideFullHecke.Kleiman2.joinVec]

theorem segreLiftMap_map (F : Type) [Field F] (φ : O →+* F) (W : Ideal (MRing ι F)) :
    (segreLiftMap ι F W).toRingHom.comp (MvPolynomial.map φ) =
      (Polynomial.mapRingHom ((Ideal.Quotient.mk W).comp (MvPolynomial.map φ))).comp (theta ι O) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [theta, segreLiftMap, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      coe_eval₂Hom, eval₂_C, Polynomial.coe_mapRingHom, Polynomial.map_C, map_C, aeval_C]
    rfl
  · rintro ⟨(u | k), i⟩
    · simp [theta, thetaVal, segreLiftMap, segreLiftVal, Polynomial.map_prod]
    · simp [theta, thetaVal, segreLiftMap, segreLiftVal]

end SegreFibreIdeal

open SegreFibreIdeal in
theorem SegreFibreIdeal.proof : SegreFibreIdeal.Statement := by
  intro O _ Ω _ _ F _ φ K _ _ ι _ y
  refine ⟨?_, ?_, ?_⟩
  · rintro g ⟨c, d, rfl⟩
    have hm : (segreY c * segreMon d - segreY d * segreMon c : MRing (segreIdx ι) O) ∈
        mIdealOver O (segreJoin y) := by
      simp only [mIdealOver, RingHom.mem_ker, map_sub, map_mul, map_prod, segreY, segreMon,
        mConeMapOver, aeval_X, segreJoin, IndefiniteRowSideFullHecke.Kleiman2.joinVec, IndefiniteRowSideFullHecke.Kleiman2.oneBlock,
        NumbersDVR.segreVec, Sum.elim_inr, Finset.prod_mul_distrib]
      ring
    have := Ideal.mem_map_of_mem (MvPolynomial.map φ) hm
    rw [SetLike.mem_coe]
    convert this using 1
    simp [segreY, segreMon, map_prod]
  · rw [Ideal.map_le_iff_le_comap]
    intro f hf
    simp only [Ideal.mem_comap]
    have hr : segreIncl ι F (MvPolynomial.map φ f) = MvPolynomial.map φ (segreIncl ι O f) := by
      simp [segreIncl, MvPolynomial.map_rename]
    rw [hr]
    refine Ideal.mem_map_of_mem _ ?_
    have key : (mConeMapOver O (segreJoin y)).toRingHom.comp (segreIncl ι O).toRingHom =
        (rename (R := Ω) (Sum.inr : K → Unit ⊕ K)).toRingHom.comp (mConeMapOver O y).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [segreIncl, mConeMapOver]
      · rintro ⟨k, i⟩
        simp [segreIncl, mConeMapOver, segreJoin, IndefiniteRowSideFullHecke.Kleiman2.joinVec]
    have hc : mConeMapOver O (segreJoin y) (segreIncl ι O f) =
        rename Sum.inr (mConeMapOver O y f) := by
      simpa using congrArg (fun g => g f) key
    rw [mIdealOver, RingHom.mem_ker] at hf ⊢
    rw [hc, hf, map_zero]
  · intro W hW
    rw [Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap, segreLift, RingHom.mem_ker]
    have h1 := congrArg (fun g => g f) (segreLiftMap_map F φ W)
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h1
    rw [h1]
    have h2 := congrArg (fun g => g f) (map_cone_theta (O := O) y)
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h2
    rw [mIdealOver, RingHom.mem_ker] at hf
    rw [hf, map_zero] at h2
    ext n
    simp only [Polynomial.coeff_map, Polynomial.coe_mapRingHom, Polynomial.coeff_zero,
      RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    apply hW
    apply Ideal.mem_map_of_mem
    rw [mIdealOver, RingHom.mem_ker]
    have := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p n) h2
    simpa [Polynomial.coeff_map] using this

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.XBaseMemMIdealOverGraph
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mConeMapOver mIdealOver)

section Zero

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω] {N m : ℕ} {x : Fin (N + 1) → Ω}

theorem X_mem_primeOf_of_eq_zero {i : Fin (N + 1)} (hi : x i = 0) :
    (X i : Kleiman.Poly S N) ∈ Kleiman.primeOf (S := S) x := by
  rw [Kleiman.primeOf_eq, RingHom.mem_ker]
  simp [Kleiman.cone, ReciprocityTheory.ChartRestriction.G.Geo.coneMap, hi]

theorem X_base_mem_mIdealOver_graph (s : Fin m → Ω) {i : Fin (N + 1)} (hi : x i = 0) :
    (X ⟨baseBlock, i⟩ : NumbersDVR.MRing (graphIdx N m) S) ∈ mIdealOver S (graphVec x s) := by
  change mConeMapOver S (graphVec x s) (X _) = 0
  simp [mConeMapOver, hi]
  exact hi

end Zero

theorem NefEq.proof (hC : CurveComap.Statement) (hL : CurveLift.Statement) (hD : DegEq.Statement) :
    NefEq.Statement := by
  intro k _ N Ω _ _ x Q n m s hgen
  by_cases hx : ∃ i, x i ≠ 0
  · constructor
    · intro hnef W hW hle hrel
      have hsub := (hC k N Ω x Q n m s hx hgen W hW hle 1).mp hrel
      rw [hD k N Ω x Q n m s hx hgen _ W hsub hW hle rfl]
      exact hnef _ bot_le hsub
    · intro hnef pp _ hsub
      obtain ⟨W, hW, hle, rfl⟩ := hL k N Ω x Q n m s hx hgen pp 1 hsub
      rw [← hD k N Ω x Q n m s hx hgen _ W hsub hW hle rfl]
      exact hnef W hW hle ((hC k N Ω x Q n m s hx hgen W hW hle 1).mpr hsub)
  · push Not at hx
    constructor
    · intro _ W hW hle _
      exfalso
      obtain ⟨i, hi⟩ := hW.relevant baseBlock
      exact hi (hle (X_base_mem_mIdealOver_graph s (hx i)))
    · intro _ pp _ hsub
      exfalso
      obtain ⟨i, hi⟩ := hsub.relevant
      exact hi (hsub.le (X_mem_primeOf_of_eq_zero (hx i)))

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

