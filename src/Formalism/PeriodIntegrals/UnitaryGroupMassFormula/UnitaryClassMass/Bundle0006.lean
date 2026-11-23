module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.Bundle0005

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.PHermC
section
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

theorem wPlace : WPlace := by
  intro F E _ _ _ _ _ p hp h
  exact Ring.ne_bot_of_isMaximal_of_not_isField hp (NumberField.RingOfIntegers.not_isField E)
    (Ideal.eq_bot_of_comap_eq_bot h)

theorem bcU : BcU := by
  intro F E _ _ _ σ M J R _ _ g hg
  have key : ∀ A : Matrix (Fin M) (Fin M) E,
      PI.UnitaryApproxDefs.cT (PI.UnitaryApproxDefs.sigR σ R)
          (A.map (PI.UnitaryApproxDefs.inclE (F := F) R)) =
        (PI.UnitaryApproxDefs.cT (σ : E →+* E) A).map (PI.UnitaryApproxDefs.inclE (F := F) R) := by
    intro A
    ext i j
    simp [PI.UnitaryApproxDefs.cT, PI.UnitaryApproxDefs.sigR, PI.UnitaryApproxDefs.inclE]
  have hg' : PI.UnitaryApproxDefs.cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J *
      (g : Matrix (Fin M) (Fin M) E) = J := hg
  change PI.UnitaryApproxDefs.cT _ _ * _ * _ = _
  simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe,
    RingHom.mapMatrix_apply]
  rw [key, ← Matrix.map_mul, ← Matrix.map_mul, hg']

theorem gramOK : GramOK := by
  intro F E _ _ _ _ σ hσ V _ _ _ h M b hsy hnd
  refine ⟨?_, ?_⟩
  · unfold PI.UnitaryApproxDefs.IsHerm PI.UnitaryApproxDefs.cT
    ext i j
    simp only [Matrix.transpose_apply, Matrix.map_apply, AlgHom.coe_toRingHom, hσ, gramOf]
    rw [← starRingEnd_apply]
    exact hsy.eq (b j) (b i)
  · rw [isUnit_iff_ne_zero]
    intro hdet
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    apply hc0
    have hbw : ∀ i, h (b i) (∑ j, c j • b j) = 0 := by
      intro i
      have hi := congrFun hc i
      simp only [Matrix.mulVec, dotProduct, gramOf, Pi.zero_apply] at hi
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, smul_eq_mul]
      rw [← hi]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have hw : ∀ x, h x (∑ j, c j • b j) = 0 := by
      intro x
      generalize hwd : (∑ j, c j • b j) = w at hbw ⊢
      rw [← b.sum_repr x]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, hbw, smul_zero,
        Finset.sum_const_zero]
    have hw0 := hnd.2 _ hw
    funext j
    exact Fintype.linearIndependent_iff.1 b.linearIndependent c hw0 j

end PI.UnitaryGroupMassFormula.UJClassMass

end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.PHermCL
section
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

def TensLoc : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    ∃ δ : 𝓞 F, δ ≠ 0 ∧ ∀ (t : HeightOneSpectrum (𝓞 F)) (e : E) (c : 𝓞 F),
      (∃ s ∈ PI.UnitaryApproxDefs.tensInt (F := F) (t.adicCompletion F) (PI.UnitaryApproxDefs.intOE E) (t.adicCompletionIntegers F).toSubring,
        PI.UnitaryApproxDefs.inclE (F := F) (t.adicCompletion F) e =
          PI.UnitaryApproxDefs.inclE (F := F) (t.adicCompletion F) (algebraMap F E (c : F)) * s) →
      ∃ r ∈ Sw F E t, ∃ y : 𝓞 E, (r : E) * (algebraMap F E (δ : F) * e) = algebraMap F E (c : F) * (y : E)

def LatClose : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V] (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    (∀ e, σ (σ e) = e) → PI.UnitaryApproxDefs.IsHerm (σ : E →+* E) J → IsUnit J.det → Submodule.IsFullLattice E L0 →
    ∀ g : GL (Fin M) E, g ∈ PI.UnitaryApproxDefs.UJ (σ : E →+* E) J →
    ∃ D : 𝓞 F, D ≠ 0 ∧ ∀ D' : 𝓞 F, D ∣ D' → ∀ γ : GL (Fin M) E, γ ∈ PI.UnitaryApproxDefs.UJ (σ : E →+* E) J →
      ∀ S : Submonoid (𝓞 E), (∀ r ∈ S, σ (r : E) = r) →
      (∀ i j, ∃ r ∈ S, ∃ y : 𝓞 E,
        (r : E) * ((g : Matrix (Fin M) (Fin M) E) i j - (γ : Matrix (Fin M) (Fin M) E) i j) =
          algebraMap F E (D' : F) * (y : E)) →
      locS S (gmap (linOf b γ) L0) = locS S (gmap (linOf b g) L0)

theorem closeLoc_of (hT : TensLoc) (hL : LatClose) : CloseLoc := by
  intro F E _ _ _ _ _ σ V _ _ _ _ _ M J b L0 hσσ hH hdet hL0 g hg
  obtain ⟨δ, hδ, hTδ⟩ := hT F E
  obtain ⟨D, hD, hDcl⟩ := hL F E σ V M J b L0 hσσ hH hdet hL0 g hg
  refine ⟨δ * D, mul_ne_zero hδ hD, fun D' hD' γ hγ t hcong => ?_⟩
  obtain ⟨k, rfl⟩ := hD'
  refine hDcl (D * k) (dvd_mul_right D k) γ hγ (Sw F E t) ?_ ?_
  · rintro r ⟨a, -, rfl⟩
    change σ (algebraMap F E (a : F)) = algebraMap F E (a : F)
    exact σ.commutes _
  · intro i j
    obtain ⟨s, hs, he⟩ := hcong i j
    obtain ⟨r, hr, y, hry⟩ := hTδ t (((g : Matrix (Fin M) (Fin M) E) i j) - (γ : Matrix (Fin M) (Fin M) E) i j)
      (δ * D * k) ⟨s, hs, by rw [map_sub]; exact he⟩
    refine ⟨r, hr, y, ?_⟩
    have hδF : (δ : F) ≠ 0 := by simpa using hδ
    have hδE : algebraMap F E (δ : F) ≠ 0 := (map_ne_zero_iff _ (algebraMap F E).injective).2 hδF
    apply mul_left_cancel₀ hδE
    have e1 : ((δ * D * k : 𝓞 F) : F) = (δ : F) * ((D * k : 𝓞 F) : F) := by push_cast; ring
    rw [e1, map_mul] at hry
    linear_combination hry

theorem hermitian_approximation_of_parts (hL : LocSw) (hT : TensLoc) (hC : LatClose) (hW : WPlace) (hB : BcU) (hG : GramOK) :
    HermApprox := hermApprox_of hL (closeLoc_of hT hC) hW hB hG

end PI.UnitaryGroupMassFormula.UJClassMass

end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.PHermXB
section
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

theorem local_switching_lattice : LocSw := by
  intro F E _ _ _ _ _ _ σ hσ hfix V _ _ p hp t ht X
  have hσσ : ∀ a, σ (σ a) = a := fun a => by rw [hσ, hσ, star_star]
  have hinj : Function.Injective (algebraMap (𝓞 E) E) := IsFractionRing.injective (𝓞 E) E
  have hcomm : ∀ c : 𝓞 F, algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) c) =
      algebraMap F E (algebraMap (𝓞 F) F c) := by
    intro c
    first
    | rfl
    | rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hSw : Sw F E t ≤ hcompl (K := E) p := by
    intro s hs
    obtain ⟨c, hc, rfl⟩ := Submonoid.mem_map.1 hs
    apply Submonoid.subset_closure
    rw [Set.mem_setOf_eq]
    have hcp : algebraMap (𝓞 F) (𝓞 E) c ∉ p := by
      intro h'
      apply Ideal.mem_primeCompl_iff.1 hc
      rw [ht, Ideal.mem_comap]
      exact h'
    refine ⟨hcp, fun t' ht' => ?_⟩
    have h3 : t' = algebraMap (𝓞 F) (𝓞 E) c := by
      apply hinj
      rw [ht', hcomm, ← hσ, AlgHom.commutes]
    rw [h3]
    exact hcp
  have key : ∀ s ∈ hcompl (K := E) p, ∃ r : 𝓞 E, r * s ∈ Sw F E t := by
    intro s hs
    induction hs using Submonoid.closure_induction with
    | mem s hs =>
      obtain ⟨hsp, hconj⟩ := hs
      have hint : IsIntegral ℤ (σ (algebraMap (𝓞 E) E s)) :=
        (NumberField.RingOfIntegers.isIntegral_coe s).map σ.toRingHom.toIntAlgHom
      let sb : 𝓞 E := ⟨σ (algebraMap (𝓞 E) E s), hint⟩
      have hsb : algebraMap (𝓞 E) E sb = star (algebraMap (𝓞 E) E s) := by
        rw [← hσ]
        rfl
      have hsbp : sb ∉ p := hconj sb hsb
      have hfixN : σ (algebraMap (𝓞 E) E (sb * s)) = algebraMap (𝓞 E) E (sb * s) := by
        rw [map_mul, map_mul, hsb, ← hσ, hσσ, mul_comm]
      obtain ⟨c, hc⟩ := hfix _ hfixN
      have hcint : IsIntegral ℤ c := by
        rw [← isIntegral_algebraMap_iff (B := E), hc]
        exact NumberField.RingOfIntegers.isIntegral_coe (sb * s)
      let c' : 𝓞 F := ⟨c, hcint⟩
      have hc' : algebraMap (𝓞 F) (𝓞 E) c' = sb * s := by
        apply hinj
        rw [hcomm, ← hc]
        rfl
      refine ⟨sb, Submonoid.mem_map.2 ⟨c', ?_, hc'⟩⟩
      rw [Ideal.mem_primeCompl_iff, ht, Ideal.mem_comap, hc']
      exact fun h' => (hp.isPrime.mem_or_mem h').elim hsbp hsp
    | one => exact ⟨1, by rw [one_mul]; exact (Sw F E t).one_mem⟩
    | mul x y _ _ hx hy =>
      obtain ⟨r1, h1⟩ := hx
      obtain ⟨r2, h2⟩ := hy
      refine ⟨r1 * r2, ?_⟩
      rw [show r1 * r2 * (x * y) = r1 * x * (r2 * y) by ring]
      exact (Sw F E t).mul_mem h1 h2
  unfold loc
  ext x
  constructor
  · rintro ⟨s, hs, hsx⟩
    obtain ⟨r, hr⟩ := key s hs
    exact (show ∃ s ∈ Sw F E t, s • x ∈ X from
      ⟨r * s, hr, by rw [mul_smul]; exact X.smul_mem r hsx⟩)
  · rintro ⟨s, hs, hsx⟩
    exact (show ∃ s ∈ hcompl (K := E) p, s • x ∈ X from ⟨s, hSw hs, hsx⟩)

end PI.UnitaryGroupMassFormula.UJClassMass

end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryClassMass.SigRTmulOne
section
open NumberField PI.UJClassFin PI.UnitaryGroupMassFormula.UJClassFin IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace PI.UnitaryGroupMassFormula.UJClassMass

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {M : ℕ}

theorem stabT (L : Set (Fin M → E)) {u k : ℕ} (hu : ∀ x ∈ L, ∀ i, IsIntegral ℤ ((u : F) • x i))
    (hk : ∀ i, ∀ e : E, IsIntegral ℤ e → Pi.single i ((k : F) • e) ∈ L) {a : Af F} (ha : a ∈ intAf F)
    (Y : Matrix (Fin M) (Fin M) (Af F ⊗[F] E))
    (hY : ∀ i j, ∃ o ∈ Oh F E, (a ⊗ₜ[F] (1 : E)) * (Y - 1) i j = (u * k) • o)
    {y : Fin M → Af F ⊗[F] E} (hy : y ∈ latHat F E L) :
    (a ⊗ₜ[F] (1 : E)) • Y.mulVec y ∈ latHat F E L := by
  choose o ho hoe using hY
  have hYy : Y.mulVec y = y + (Y - 1).mulVec y := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
  have e1 : (a ⊗ₜ[F] (1 : E)) • (Y - 1).mulVec y = k • fun i => ∑ j, o i j * (u • y j) := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_assoc, hoe i j]
    simp only [nsmul_eq_mul]
    push_cast
    ring
  rw [hYy, smul_add, e1]
  exact add_mem (latHat_smul L ha hy)
    (low_vec L hk fun i => AddSubgroup.sum_mem _ fun j _ => Oh_mul (ho i j) (up_Oh L hu hy j))

theorem locCmpT (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (L : Set (Fin M → E)) {k : ℕ} (hkpos : 0 < k)
    (hk : ∀ i, ∀ e : E, IsIntegral ℤ e → Pi.single i ((k : F) • e) ∈ L)
    (T : Set (HeightOneSpectrum (𝓞 F))) (p : ℕ) (hp0 : p ≠ 0) (hp : p ≠ 1)
    (hpT : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ T → (p : 𝓞 F) ∉ w.asIdeal) (g1 g2 : HA (AF F) σ J)
    (hC : ∀ y ∈ latHat F E L, (evT T ⊗ₜ[F] (1 : E)) • (finMat σ J (g2⁻¹ * g1)).mulVec y ∈ latHat F E L)
    {x : Fin M → E} (hx : x ∈ abelian₂ σ J L g1) : ∃ m2 : ℕ, ¬ p ∣ m2 ∧ (m2 : E) • x ∈ abelian₂ σ J L g2 := by
  classical
  set z := (finMat σ J g2⁻¹).mulVec (vinc (F := F) x) with hz
  have hzC : (evT T ⊗ₜ[F] (1 : E)) • z ∈ latHat F E L := by
    have : z = (finMat σ J (g2⁻¹ * g1)).mulVec ((finMat σ J g1⁻¹).mulVec (vinc (F := F) x)) := by
      rw [Matrix.mulVec_mulVec, ← finMat_mul, mul_assoc, mul_inv_cancel, mul_one]
    rw [this]; exact hC _ hx
  have hden : ∃ m : ℕ, 0 < m ∧ m • z ∈ latHat F E L := by
    choose mf hmf hmO using fun i => den (F := F) (E := E) (z i)
    refine ⟨k * ∏ i, mf i, Nat.mul_pos hkpos (Finset.prod_pos fun i _ => hmf i), ?_⟩
    rw [mul_smul]
    apply low_vec L hk
    intro i
    obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem mf (Finset.mem_univ i)
    show (∏ i, mf i) • z i ∈ Oh F E
    rw [hq, mul_comm, mul_smul]
    exact AddSubgroup.nsmul_mem _ (hmO i) _
  obtain ⟨m, hm, hmz⟩ := hden
  obtain ⟨a, m2, hm2, hmeq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.ne' p hp
  refine ⟨m2, hm2, ?_⟩
  show (finMat σ J g2⁻¹).mulVec (vinc (F := F) ((m2 : E) • x)) ∈ latHat F E L
  have e2 : (finMat σ J g2⁻¹).mulVec (vinc (F := F) ((m2 : E) • x)) = m2 • z := by
    rw [Nat.cast_smul_eq_nsmul, hz]
    have : vinc (F := F) (m2 • x) = m2 • vinc (F := F) x := by funext i; simp [vinc]
    rw [this, Matrix.mulVec_smul]
  rw [e2]
  set c : Af F := (1 - evT T) * algebraMap F (Af F) ((algebraMap (𝓞 F) F ((p : 𝓞 F) ^ a))⁻¹) with hc
  have hcI : c ∈ intAf F := one_sub_evT_inv_int T ((p : 𝓞 F) ^ a)
    (fun w hw hpw => hpT w hw (w.isPrime.mem_of_pow_mem a hpw))
  have hpa : algebraMap (𝓞 F) F ((p : 𝓞 F) ^ a) ≠ 0 := by
    rw [map_pow, map_natCast]; exact pow_ne_zero _ (by exact_mod_cast hp0)
  have hA : algebraMap F (Af F) ((algebraMap (𝓞 F) F ((p : 𝓞 F) ^ a))⁻¹) * ((p : Af F) ^ a) = 1 := by
    rw [show ((p : Af F) ^ a) = algebraMap F (Af F) (algebraMap (𝓞 F) F ((p : 𝓞 F) ^ a)) by simp,
      ← map_mul, inv_mul_cancel₀ hpa, map_one]
  have hsc : (m2 : Af F) = m2 * evT T + c * (m : Af F) := by
    rw [hmeq, hc]; push_cast at hA ⊢
    linear_combination (-(1 - evT T) * (m2 : Af F)) * hA
  have e3 : m2 • z = m2 • ((evT T ⊗ₜ[F] (1 : E)) • z) + (c ⊗ₜ[F] (1 : E)) • (m • z) := by
    have hι := congrArg (Algebra.TensorProduct.includeLeftRingHom : Af F →+* Af F ⊗[F] E) hsc
    simp only [map_add (f := _), map_mul, map_natCast] at hι
    rw [← Nat.cast_smul_eq_nsmul (Af F ⊗[F] E) m2 z, ← Nat.cast_smul_eq_nsmul (Af F ⊗[F] E) m2,
      ← Nat.cast_smul_eq_nsmul (Af F ⊗[F] E) m z, smul_smul, smul_smul, ← add_smul]
    congr 1
  rw [e3]
  exact add_mem (AddSubgroup.nsmul_mem _ hzC _) (latHat_smul L hcI hmz)

theorem sigR_tmul_one (σ : E →ₐ[F] E) (e : Af F) :
    PI.UJClassFin.sigR (Af F) σ (e ⊗ₜ[F] (1 : E)) = e ⊗ₜ[F] (1 : E) := by
  simp [PI.UJClassFin.sigR]

theorem invSmall (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (hJ : J.det ≠ 0) {dI dJ : ℕ}
    (hdI : ∀ i j, IsIntegral ℤ ((dI : E) * J⁻¹ i j)) (hdJ : ∀ i j, IsIntegral ℤ ((dJ : E) * J i j))
    (e : Af F) (kk : HA (AF F) σ J) (N : ℕ)
    (h : ∀ i j, ∃ o ∈ Oh F E, (e ⊗ₜ[F] (1 : E)) * (finMat σ J kk⁻¹ - 1) i j = (dI * dJ * N) • o) :
    ∀ i j, ∃ o ∈ Oh F E, (e ⊗ₜ[F] (1 : E)) * (finMat σ J kk - 1) i j = N • o := by
  choose o ho hoe using h
  set U := finMat σ J kk with hUd
  set W := finMat σ J kk⁻¹ with hWd
  set JI := (J⁻¹).map (inclR (F := F) (Af F)) with hJId
  set JA := JR (F := F) (Af F) J with hJAd
  set sg := PI.UJClassFin.sigR (Af F) σ with hsg
  have hJI : JI * JA = 1 := by
    rw [hJId, hJAd, JR, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hJ), Matrix.map_one _ (map_zero _) (map_one _)]
  have hWU : W * U = 1 := by rw [hWd, hUd, ← finMat_mul, inv_mul_cancel, finMat_one]
  have hunit : PI.UJClassFin.cT sg W * JA * W = JA := finMat_unitary σ J kk⁻¹
  have hU : U = JI * PI.UJClassFin.cT sg W * JA := by
    calc U = JI * JA * U := by rw [hJI, Matrix.one_mul]
      _ = JI * (PI.UJClassFin.cT sg W * JA * W) * U := by rw [hunit]
      _ = JI * PI.UJClassFin.cT sg W * JA * (W * U) := by simp only [Matrix.mul_assoc]
      _ = JI * PI.UJClassFin.cT sg W * JA := by rw [hWU, Matrix.mul_one]
  have hcs : PI.UJClassFin.cT sg (W - 1) = PI.UJClassFin.cT sg W - 1 := by
    have h1 := PI.UJClassFin.cT_one (n := Fin M) sg
    unfold PI.UJClassFin.cT at h1 ⊢
    rw [Matrix.map_sub _ (map_sub _), Matrix.transpose_sub, h1]
  have hU1 : U - 1 = JI * PI.UJClassFin.cT sg (W - 1) * JA := by
    rw [hU, hcs, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hJI]
  have key : ∀ a b, (e ⊗ₜ[F] (1 : E)) * sg ((W - 1) b a) = (dI * dJ * N) • sg (o b a) := by
    intro a b
    calc (e ⊗ₜ[F] (1 : E)) * sg ((W - 1) b a) = sg (e ⊗ₜ[F] (1 : E)) * sg ((W - 1) b a) := by
          rw [hsg, sigR_tmul_one]
      _ = sg ((e ⊗ₜ[F] (1 : E)) * (W - 1) b a) := (map_mul _ _ _).symm
      _ = sg ((dI * dJ * N) • o b a) := by rw [hoe b a]
      _ = (dI * dJ * N) • sg (o b a) := map_nsmul _ _ _
  intro i j
  refine ⟨∑ a, ∑ b, inclR (F := F) (Af F) ((dI : E) * J⁻¹ i a) * sg (o b a) *
      inclR (F := F) (Af F) ((dJ : E) * J b j),
    AddSubgroup.sum_mem _ fun a _ => AddSubgroup.sum_mem _ fun b _ =>
      Oh_mul (Oh_mul (incl_mem_Oh (hdI i a)) (sigR_Oh σ (ho b a))) (incl_mem_Oh (hdJ b j)), ?_⟩
  rw [hU1]
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have hk := key a b
  have hX : PI.UJClassFin.cT sg (W - 1) a b = sg ((W - 1) b a) := rfl
  have hJI' : JI i a = inclR (F := F) (Af F) (J⁻¹ i a) := rfl
  have hJA' : JA b j = inclR (F := F) (Af F) (J b j) := rfl
  rw [hX, hJI', hJA', map_mul, map_mul, map_natCast, map_natCast]
  calc (e ⊗ₜ[F] (1 : E)) * (inclR (F := F) (Af F) (J⁻¹ i a) * sg ((W - 1) b a) * inclR (F := F) (Af F) (J b j))
      = inclR (F := F) (Af F) (J⁻¹ i a) * ((e ⊗ₜ[F] (1 : E)) * sg ((W - 1) b a)) *
          inclR (F := F) (Af F) (J b j) := by ring
    _ = _ := by
      rw [hk]
      simp only [nsmul_eq_mul]
      push_cast
      ring

end Loc

end PI.UnitaryGroupMassFormula.UJClassMass
end
end

