module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.DirChar
section
open NumberField IsDedekindDomain Topology Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep

namespace UpperTheory.V.Af.Nf

private theorem dc_inv {M : ℕ} (hM : 1 ≤ M) : algebraMap ℚ (Af ℚ) (M : ℚ)⁻¹ * M = 1 := by
  have hM' : (M : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [← map_natCast (algebraMap ℚ (Af ℚ)), ← map_mul, inv_mul_cancel₀ hM', map_one]

private theorem dc_uniq {M : ℕ} (hM : 1 ≤ M) {x : Af ℚ} {d e : ℤ} (hd : ∃ y ∈ Ohat ℚ, x - d = M * y)
    (he : ∃ y ∈ Ohat ℚ, x - e = M * y) : (d : ZMod M) = e := by
  obtain ⟨y, hy, hd⟩ := hd
  obtain ⟨z, hz, he⟩ := he
  have hM' : (M : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have h1 : algebraMap ℚ (Af ℚ) ((M : ℚ)⁻¹ * ((e : ℚ) - d)) = y - z := by
    rw [map_mul, map_sub, map_intCast, map_intCast]
    linear_combination algebraMap ℚ (Af ℚ) (M : ℚ)⁻¹ * (hd - he) + (y - z) * dc_inv hM
  obtain ⟨n, hn⟩ := ratAd.2.2 _ (h1 ▸ sub_mem hy hz)
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  refine ⟨n, ?_⟩
  rw [inv_mul_eq_iff_eq_mul₀ hM'] at hn
  exact_mod_cast hn

private theorem dc_red {M : ℕ} (hM : 1 ≤ M) : ∃ ρ : ↥(Ohat ℚ) →* ZMod M,
    ∀ (x : ↥(Ohat ℚ)) (d : ℤ), (∃ y ∈ Ohat ℚ, (x : Af ℚ) - d = M * y) → ρ x = d := by
  choose f hf using fun x : ↥(Ohat ℚ) => ratAd.2.1 M hM x x.2
  refine ⟨⟨⟨fun x => f x, ?_⟩, fun a b => ?_⟩, fun x d h => dc_uniq hM (hf x) h⟩
  · have := dc_uniq hM (e := 1) (hf 1) ⟨0, zero_mem _, by simp⟩
    simpa using this
  · obtain ⟨y, hy, h1⟩ := hf a
    obtain ⟨z, hz, h2⟩ := hf b
    have := dc_uniq hM (e := f a * f b) (hf (a * b)) ⟨a * z + f b * y,
      add_mem (mul_mem a.2 hz) (mul_mem (intCast_mem _ _) hy), by
        rw [Subring.coe_mul, Int.cast_mul]
        linear_combination (a : Af ℚ) * h2 + (f b : Af ℚ) * h1⟩
    simpa using this

private noncomputable abbrev pF : Ideles ℚ →* (Af ℚ)ˣ := Units.map (pFin ℚ).toMonoidHom

private noncomputable abbrev pR : Ideles ℚ →* ℝˣ := Units.map (ev.comp (TR.pInf ℚ)).toMonoidHom

private noncomputable abbrev dg : ℚˣ →* Ideles ℚ := Units.map (algebraMap ℚ (Ad ℚ)).toMonoidHom

private theorem pR_dg (r : ℚˣ) : (pR (dg r) : ℝ) = ((r : ℚ) : ℝ) :=
  eq_ratCast ((ev.comp (TR.pInf ℚ)).comp (algebraMap ℚ (Ad ℚ))) (r : ℚ)

private theorem pF_dg (r : ℚˣ) : pF (dg r) = Units.map (algebraMap ℚ (Af ℚ)).toMonoidHom r := Units.ext rfl

private theorem pF_inf (t : (TR.Rinf ℚ)ˣ) : pF (TR.infId ℚ t) = 1 := by
  refine Units.ext ?_
  change (1 : Af ℚ) - 0 + 0 = 1
  simp

private theorem pR_inf (t : (TR.Rinf ℚ)ˣ) : (pR (TR.infId ℚ t) : ℝ) = t.val Rat.infinitePlace := by
  have h : ∀ x, TR.pInf ℚ (TR.sInf ℚ x) = x := fun x => (TR.infEq ℚ).symm_apply_apply x
  change ev (TR.pInf ℚ (1 - TR.sInf ℚ 1 + TR.sInf ℚ t.val)) = ev t.val
  simp [h]

private theorem pF_fin (u : (Af ℚ)ˣ) : pF (finId ℚ u) = u := by
  refine Units.ext ?_
  change (1 : Af ℚ) - 1 + u = u
  simp

private theorem pR_fin (u : (Af ℚ)ˣ) : (pR (finId ℚ u) : ℝ) = 1 := by
  have h : ∀ x, TR.pInf ℚ (sFin ℚ x) = 0 := fun x => map_zero (TR.infEq ℚ).symm
  change ev (TR.pInf ℚ (1 - sFin ℚ 1 + sFin ℚ u.val)) = 1
  simp [h]

private theorem zu_mul {u v : (Af ℚ)ˣ} (hu : IsZU u) (hv : IsZU v) : IsZU (u * v) :=
  ⟨mul_mem hu.1 hv.1, by rw [mul_inv]; exact mul_mem hu.2 hv.2⟩

private theorem zu_one : IsZU 1 := ⟨one_mem _, one_mem _⟩

private noncomputable def PU : Subgroup (Ideles ℚ) where
  carrier := {a | 0 < (pR a : ℝ) ∧ IsZU (pF a)}
  one_mem' := ⟨by rw [map_one]; exact one_pos, by rw [map_one]; exact zu_one⟩
  mul_mem' := fun {a b} ha hb => ⟨by rw [map_mul]; exact mul_pos ha.1 hb.1, by rw [map_mul]; exact zu_mul ha.2 hb.2⟩
  inv_mem' := fun {a} ha => ⟨by rw [map_inv, Units.val_inv_eq_inv_val]; exact inv_pos.2 ha.1,
    by rw [map_inv]; exact ⟨ha.2.2, ha.2.1⟩⟩

private theorem dc_ker (r : ℚˣ) (h : dg r ∈ PU) : r = 1 := by
  obtain ⟨h0, h1, h2⟩ := h
  rw [pR_dg, Rat.cast_pos] at h0
  obtain ⟨n, hn⟩ := ratAd.2.2 r h1
  obtain ⟨m, hm⟩ := ratAd.2.2 (r⁻¹ : ℚˣ) h2
  have e : n * m = 1 := by
    have := r.mul_inv
    rw [hn, hm] at this
    exact_mod_cast this
  rw [hn] at h0
  have := Int.eq_one_of_mul_eq_one_right (by exact_mod_cast h0.le) e
  exact Units.ext (by rw [hn, this]; rfl)

private theorem dc_surj : Function.Surjective (PU.subtype.coprod dg) := by
  intro a
  obtain ⟨r, u, hr, hu, e⟩ := ratAd.1 (pF a)
  have key : ∀ s : ℚˣ, s * s = 1 → IsZU (pF (dg s)) → 0 < ((s : ℚ) : ℝ) * pR a →
      ∃ p, PU.subtype.coprod dg p = a := fun s hs hz hp => by
    refine ⟨(⟨a * dg (s * r⁻¹), ?_, ?_⟩, s * r), ?_⟩
    · rw [map_mul, Units.val_mul, pR_dg, Units.val_mul, Rat.cast_mul, ← mul_assoc, mul_comm _ (((s : ℚ) : ℝ))]
      refine mul_pos hp ?_
      rw [Units.val_inv_eq_inv_val, Rat.cast_pos]
      exact inv_pos.2 hr
    · have : pF (a * dg (s * r⁻¹)) = u * pF (dg s) := by
        rw [map_mul, e, ← pF_dg, map_mul, map_mul, map_inv, map_inv, mul_comm _ u, mul_comm (pF (dg s)),
          mul_assoc, mul_inv_cancel_left]
      rw [this]
      exact zu_mul hu hz
    · change a * dg (s * r⁻¹) * dg (s * r) = a
      rw [mul_assoc, ← map_mul, mul_mul_mul_comm, hs, inv_mul_cancel, mul_one, map_one, mul_one]
  rcases lt_or_gt_of_ne (pR a).ne_zero with h | h
  · refine key (-1) (by simp) ?_ (by simpa using h)
    have : algebraMap ℚ (Af ℚ) (-1) ∈ Ohat ℚ := by rw [map_neg, map_one]; exact neg_mem (one_mem _)
    exact ⟨this, this⟩
  · exact key 1 (by simp) (by rw [map_one, map_one]; exact zu_one) (by simpa using h)

private theorem dc_nhds {M : ℕ} : ∀ᶠ a : Ideles ℚ in 𝓝 1, a ∈ PU ∧
    algebraMap ℚ (Af ℚ) (M : ℚ)⁻¹ * ((pF a : Af ℚ) - (1 : ℤ)) ∈ Ohat ℚ := by
  have c1 : Continuous pF := Continuous.units_map _ continuous_snd
  have c2 : Continuous fun a => (pR a : ℝ) :=
    ((InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal Rat.infinitePlace)).continuous.comp
      ((continuous_apply Rat.infinitePlace).comp continuous_fst)).comp Units.continuous_val
  have c3 : Continuous fun a => (pF a : Af ℚ) := Units.continuous_val.comp c1
  have c4 : Continuous fun a => (((pF a)⁻¹ : (Af ℚ)ˣ) : Af ℚ) := Units.continuous_coe_inv.comp c1
  have c5 : Continuous fun a => algebraMap ℚ (Af ℚ) (M : ℚ)⁻¹ * ((pF a : Af ℚ) - (1 : ℤ)) :=
    continuous_const.mul (c3.sub continuous_const)
  have h2 : ∀ᶠ a : Ideles ℚ in 𝓝 1, 0 < (pR a : ℝ) := (isOpen_lt continuous_const c2).mem_nhds PU.one_mem.1
  have h3 := (isOpen_Ohat.preimage c3).mem_nhds (x := 1) PU.one_mem.2.1
  have h4 := (isOpen_Ohat.preimage c4).mem_nhds (x := 1) PU.one_mem.2.2
  have h5 := (isOpen_Ohat.preimage c5).mem_nhds (x := 1) (by
    rw [Set.mem_preimage, map_one, Units.val_one, Int.cast_one, sub_self, mul_zero]; exact zero_mem (Ohat ℚ))
  filter_upwards [h2, h3, h4, h5] with a a2 a3 a4 a5
  exact ⟨⟨a2, a3, a4⟩, a5⟩

end UpperTheory.V.Af.Nf

theorem UpperTheory.V.Af.Nf.dirChar :
    UpperTheory.V.Af.Nf.DirChar := by
  intro M hM χ
  obtain ⟨ρ, hρ⟩ := dc_red hM
  let j : ↥PU →* ↥(Ohat ℚ) :=
    { toFun := fun p => ⟨pF p, p.2.2.1⟩
      map_one' := Subtype.ext (congrArg Units.val (map_one pF))
      map_mul' := fun a b => Subtype.ext (congrArg Units.val (map_mul pF a.1 b.1)) }
  let ψ : ↥PU →* ℂˣ := (χ.toMonoidHom.comp (ρ.comp j)).toHomUnits
  let φ : ↥PU × ℚˣ →* ℂˣ := ψ⁻¹.comp (MonoidHom.fst _ _)
  have hker : (PU.subtype.coprod dg).ker ≤ φ.ker := fun p hp => by
    have h1 : (p.1 : Ideles ℚ) * dg p.2 = 1 := hp
    have h2 := dc_ker p.2 (by rw [eq_inv_of_mul_eq_one_right h1]; exact PU.inv_mem p.1.2)
    rw [h2, map_one, mul_one] at h1
    change ψ⁻¹ p.1 = 1
    rw [show p.1 = 1 from Subtype.ext h1, map_one]
  let ω : Ideles ℚ →* ℂˣ := MonoidHom.liftOfSurjective _ dc_surj ⟨φ, hker⟩
  have hω : ∀ p, ω (PU.subtype.coprod dg p) = φ p := fun p => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ p
  have hv : ∀ a (ha : a ∈ PU) (d : ℤ), (∃ y ∈ Ohat ℚ, (pF a : Af ℚ) - d = M * y) → (ω a : ℂ) * χ (d : ZMod M) = 1 := by
    intro a ha d hd
    have h1 : ω (a * dg 1) = (ψ ⟨a, ha⟩)⁻¹ := hω (⟨a, ha⟩, 1)
    rw [map_one, mul_one] at h1
    rw [h1, ← hρ (j ⟨a, ha⟩) d hd]
    exact (ψ ⟨a, ha⟩).inv_mul
  have hone : ∀ a (ha : a ∈ PU), (∃ y ∈ Ohat ℚ, (pF a : Af ℚ) - (1 : ℤ) = M * y) → ω a = 1 := fun a ha h => by
    have := hv a ha 1 h
    rw [Int.cast_one, map_one, mul_one] at this
    exact Units.ext this
  refine ⟨⟨ω, continuous_of_continuousAt_one ω ?_, fun k => ?_⟩, fun t ht => ?_, fun u hu d hd => ?_⟩
  · refine (continuousAt_const (y := (1 : ℂˣ))).congr ?_
    filter_upwards [dc_nhds (M := M)] with a ha
    exact (hone a ha.1 ⟨_, ha.2, by rw [← mul_assoc, mul_comm (M : Af ℚ), dc_inv hM, one_mul]⟩).symm
  · have h1 : ω (1 * dg k) = ψ⁻¹ 1 := hω (1, k)
    rw [map_one, one_mul] at h1
    exact h1
  · exact hone _ ⟨by rw [pR_inf]; exact ht _, by rw [pF_inf]; exact zu_one⟩
      ⟨0, zero_mem _, by rw [pF_inf]; simp⟩
  · exact hv _ ⟨by rw [pR_fin]; exact one_pos, by rw [pF_fin]; exact hu⟩ d (by rw [pF_fin]; exact hd)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.HkCoef
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual UpperTheory.V.Sd

private theorem le_asIdeal_of_normV_dvd_absNorm (w : Pl ℚ) (𝔪 : Ideal (𝓞 ℚ)) (h𝔪 : 𝔪 ≠ ⊥)
    (hd : normV w ∣ Ideal.absNorm 𝔪) : 𝔪 ≤ w.asIdeal := by
  obtain ⟨hp, hspan, -, -⟩ := UpperTheory.V.Af.Nf.places w
  haveI : Fact (normV w).Prime := ⟨hp⟩
  by_contra h
  have htop : w.asIdeal ⊔ 𝔪 = ⊤ := by
    by_contra hne
    exact h (le_sup_right.trans ((w.isMaximal.eq_of_le hne le_sup_left).symm.le))
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (htop ▸ Submodule.mem_top : (1 : 𝓞 ℚ) ∈ w.asIdeal ⊔ 𝔪)
  have hne : Ideal.absNorm 𝔪 ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hd hne
  haveI : Finite (𝓞 ℚ ⧸ 𝔪) := Nat.finite_of_card_ne_zero hne
  obtain ⟨y, hy⟩ := exists_prime_addOrderOf_dvd_card' (G := 𝓞 ℚ ⧸ 𝔪) (normV w) hd
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hpx : ((normV w : ℕ) : 𝓞 ℚ) * x ∈ 𝔪 := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_natCast, ← nsmul_eq_mul, ← hy]
    exact addOrderOf_nsmul_eq_zero _
  have hx : x ∈ 𝔪 := by
    rw [hspan, Ideal.mem_span_singleton] at ha
    obtain ⟨c, rfl⟩ := ha
    have : x = c * (((normV w : ℕ) : 𝓞 ℚ) * x) + b * x := by
      rw [← mul_assoc, mul_comm c, ← add_mul, hab, one_mul]
    rw [this]
    exact 𝔪.add_mem (𝔪.mul_mem_left _ hpx) (𝔪.mul_mem_right _ hb)
  have h0 : (Ideal.Quotient.mk 𝔪 x) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hx
  rw [h0, addOrderOf_zero] at hy
  exact hp.one_lt.ne hy

private theorem coefDiv_icoef_eq_ite_dvd (g : UpperHalfPlane → ℂ) (w : Pl ℚ) (𝔪 : Ideal (𝓞 ℚ)) (h𝔪 : 𝔪 ≠ ⊥) :
    coefDiv (UpperTheory.V.Af.Nf.icoef g) w.asIdeal 𝔪 =
      if normV w ∣ Ideal.absNorm 𝔪 then UpperTheory.V.Af.coef g (Ideal.absNorm 𝔪 / normV w) else 0 := by
  obtain ⟨hp, -, hnorm, -⟩ := UpperTheory.V.Af.Nf.places w
  unfold coefDiv
  split_ifs with h1 h2 h2
  · have hc := h1.choose_spec
    have habs : Ideal.absNorm 𝔪 = normV w * Ideal.absNorm h1.choose := by
      conv_lhs => rw [hc]
      rw [map_mul, hnorm]
    simp only [UpperTheory.V.Af.Nf.icoef]
    rw [habs, Nat.mul_div_cancel_left _ hp.pos]
  · exfalso
    apply h2
    obtain ⟨n, hn⟩ := h1
    rw [hn, map_mul, hnorm]
    exact dvd_mul_right _ _
  · exfalso
    exact h1 (Ideal.dvd_iff_le.mpr (le_asIdeal_of_normV_dvd_absNorm w 𝔪 h𝔪 h2))
  · rfl

private theorem chiI_eq_of_conductor_eq_zero (ω : Formalism.L2.Host.HChar ℚ) (c : Pl ℚ → ℕ) (w : Pl ℚ) (hc : c w = 0) :
    chiI ω c w.asIdeal = ↑(ω.val w) := by
  classical
  have hirr : ∀ v : Pl ℚ, Irreducible (Associates.mk v.asIdeal) :=
    fun v => Associates.irreducible_mk.mpr v.irreducible
  unfold chiI
  rw [finprod_eq_single _ w]
  · simp only [hc, if_true]
    unfold ordI
    rw [Associates.count_self (hirr w), pow_one]
  · intro v hv
    unfold ordI
    rw [Associates.count_eq_zero_of_ne (hirr v) (hirr w), pow_zero]
    intro he
    apply hv
    rw [Associates.mk_eq_mk_iff_associated, associated_iff_eq] at he
    exact HeightOneSpectrum.ext he

theorem UpperTheory.V.Af.Nf.hkCoef :
    UpperTheory.V.Af.Nf.HkCoef := by
  intro k f ω w hw hω 𝔪 h𝔪
  obtain ⟨hp, -, hnorm, hlev⟩ := UpperTheory.V.Af.Nf.places w
  have hl : UpperTheory.V.Af.Nf.lev f.M w = 0 := hlev f.M f.pos hw
  have hn : 1 ≤ Ideal.absNorm 𝔪 := Nat.one_le_iff_ne_zero.mpr (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  have heig := f.eig (normV w) hp hw (Ideal.absNorm 𝔪) hn
  unfold UpperTheory.V.Sd.hkCoef
  rw [chiI_eq_of_conductor_eq_zero ω _ w hl, coefDiv_icoef_eq_ite_dvd _ w 𝔪 h𝔪, hω]
  simp only [UpperTheory.V.Af.Nf.icoef, map_mul, hnorm, UpperTheory.V.Af.Newform.a]
  exact heig
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.NslInv
section
open CongruenceSubgroup
open UpperHalfPlane hiding I
open scoped Matrix MatrixGroups ModularForm

namespace UpperTheory.V.Af.Nf

private def cj (δ : SL(2, ℤ)) : SL(2, ℤ) :=
  ⟨!![δ 0 0, -δ 0 1; -δ 1 0, δ 1 1], by
    have h := δ.det_coe
    rw [Matrix.det_fin_two] at h
    rw [Matrix.det_fin_two_of]
    linear_combination h⟩

private theorem eps_mul_cj (δ : SL(2, ℤ)) :
    eps * δ.1.map (Int.cast : ℤ → ℝ) = (cj δ).1.map (Int.cast : ℤ → ℝ) * eps := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eps, cj, Matrix.mul_apply, Fin.sum_univ_two]

private theorem det_map (δ : SL(2, ℤ)) : (δ.1.map (Int.cast : ℤ → ℝ)).det ≠ 0 := by
  have h := (Int.castRingHom ℝ).map_det δ.1
  rw [δ.det_coe, map_one] at h
  have h' : (δ.1.map (Int.cast : ℤ → ℝ)).det = 1 := h.symm
  rw [h']
  exact one_ne_zero

private theorem pos_case (k : ℕ) (f : ℍ → ℂ) (x : Matrix (Fin 2) (Fin 2) ℝ) (hx : 0 < x.det) (δ : SL(2, ℤ)) (c : ℂ)
    (h : f ∣[(k : ℤ)] δ = c • f) : nsl k f (δ.1.map (Int.cast : ℤ → ℝ) * x) = c • nsl k f x := by
  rw [← (nslMul k f).1 _ x (det_map δ) hx, (nslSl k f).1 δ, h, (nslMul k f).2.2.2]

private theorem gen_case (k : ℕ) (f : ℍ → ℂ) (x : Matrix (Fin 2) (Fin 2) ℝ) (hx : x.det ≠ 0) (δ : SL(2, ℤ)) (c : ℂ)
    (h : f ∣[(k : ℤ)] δ = c • f) (h' : f ∣[(k : ℤ)] (cj δ) = c • f) :
    nsl k f (δ.1.map (Int.cast : ℤ → ℝ) * x) = c • nsl k f x := by
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · have hd : 0 < (eps * x).det := by
      rw [Matrix.det_mul]
      have : eps.det = -1 := by simp [eps]
      rw [this]
      linarith
    rw [← (nslMul k f).2.1, ← Matrix.mul_assoc, eps_mul_cj, Matrix.mul_assoc, pos_case k f _ hd _ c h',
      (nslMul k f).2.1]
  · exact pos_case k f x hpos δ c h

end UpperTheory.V.Af.Nf

theorem UpperTheory.V.Af.Nf.nslInv :
    UpperTheory.V.Af.Nf.NslInv := by
  intro k M f x hx
  refine ⟨fun hf δ hδ => ?_, fun χ hχ δ hδ => ?_⟩
  · have hδ' : cj δ ∈ Gamma1 M := by
      rw [Gamma1_mem] at hδ ⊢
      obtain ⟨h1, h2, h3⟩ := hδ
      refine ⟨?_, ?_, ?_⟩
      · exact h1
      · exact h2
      · show (((-δ 1 0 : ℤ)) : ZMod M) = 0
        rw [Int.cast_neg, h3, neg_zero]
    have := gen_case k f x hx δ 1 (by rw [one_smul]; exact hf δ hδ) (by rw [one_smul]; exact hf _ hδ')
    rwa [one_smul] at this
  · have hδ' : cj δ ∈ Gamma0 M := by
      rw [Gamma0_mem] at hδ ⊢
      show (((-δ 1 0 : ℤ)) : ZMod M) = 0
      rw [Int.cast_neg, hδ, neg_zero]
    exact gen_case k f x hx δ _ (hχ δ hδ) (hχ _ hδ')
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.SatHol
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd Matrix
open GlobalTheory.CuspRep (finId locGL finGL)

private theorem fin_scalar {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ) :
    finGL F 2 (locGL F 2 w (GeneralLinearGroup.scalar (Fin 2) x)) = GeneralLinearGroup.scalar (Fin 2) (localIdele F w x) := by
  have h := GlobalTheory.CuspRep.finId_det_locGL w (GeneralLinearGroup.scalar (Fin 1) x)
  rw [locGL, GlobalTheory.CuspRep.cornerGL_scalar] at h ⊢
  rw [finGL, GlobalTheory.CuspRep.cornerGL_scalar]
  congr 1
  exact (congrArg (finId F) (GlobalTheory.CuspRep.CG.det_oneByOne _)).symm.trans
    (h.trans (congrArg (localIdele F w) (GlobalTheory.CuspRep.CG.det_oneByOne _)))

private theorem roots (s : ℂ) (p : ℂˣ) : ∃ α β : ℂˣ, (α : ℂ) + β = s ∧ α * β = p := by
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq (s ^ 2 - 4 * (p : ℂ)) (n := 2) two_pos
  have h : (s + d) / 2 * ((s - d) / 2) = p := by linear_combination (-1 / 4 : ℂ) * hd
  have h0 := h ▸ p.ne_zero
  refine ⟨Units.mk0 _ (left_ne_zero_of_mul h0), Units.mk0 _ (right_ne_zero_of_mul h0), ?_, Units.ext h⟩
  simp only [Units.val_mk0]
  ring

theorem UpperTheory.V.Af.Nf.satHol :
    UpperTheory.V.Af.Nf.SatHol := by
  intro F _ _ _ k c ω φ hφ h0 w lam hw hU
  have hq : (0 : ℝ) < normV w :=
    Nat.cast_pos.2 (zero_lt_one.trans (by
      simpa [normV, Ideal.absNorm_eq_natCard] using NumberField.HeightOneSpectrum.one_lt_absNorm w))
  have hne : ∀ t : ℝ, (((normV w : ℝ) ^ t : ℝ) : ℂ) ≠ 0 := fun t =>
    Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hq t).ne'
  obtain ⟨α, β, h1, h2⟩ := roots (lam / (((normV w : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ)) (ω.val w)
  have h3 : (((normV w : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ) * ((α : ℂ) + β) = lam := by
    rw [h1, mul_div_cancel₀ _ (hne _)]
  refine ⟨α, β, UpperTheory.V.Af.Nf.satOfU F w _ _ φ α β h0 (hw ▸ hφ.level w) ?_ ?_, h3, h2⟩
  · refine smul_right_injective _ (hne ((k : ℝ) / 2 - 1)) (hU.trans ?_)
    dsimp only
    rw [smul_smul, ← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add hq, ← h3]
    congr 4
    ring
  · rw [h2]
    refine Subtype.ext (funext fun g => ?_)
    change φ.1 (g * finGL F 2 (locGL F 2 w _)) = _
    rw [fin_scalar, ← GlobalTheory.CuspRep.scalar_comm, hφ.cent]
    rfl
end

