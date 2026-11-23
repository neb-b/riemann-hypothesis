module

public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FixedIntegersIsUnitOfNotMemPrimeSpan
public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.WdVal
public import Development.AbelianVarietyTheory.Definitions.Foundations.FrobLiftWittClosure

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.ContOf
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

private theorem cg_mono {l : ℕ} [Fact l.Prime] {n N : ℕ} (h : n ≤ N) {a b : Qbar l} (hc : Cg N a b) : Cg n a b := by
  unfold Cg at *
  refine hc.trans ?_
  rw [norm_pow, norm_pow]
  exact pow_le_pow_of_le_one (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _) h

private theorem cg_down {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {A : ValuationSubring Ω}
    {Z : Sy Ω l} (hZ : IwI c A Z) {s : G ℚ Ω} (hs : s ∈ Ine (F := ℚ) A) (n r : ℕ) :
    ∀ d, (∀ x, Cg n (Z (r + d) s x) 0) → ∀ x, Cg n (Z r s x) 0 := by
  intro d
  induction d with
  | zero => intro h; simpa using h
  | succ d ih =>
    intro h
    apply ih
    intro x
    have hsum := hZ.nrm (r + d) s hs x
    unfold Cg at h ⊢
    rw [sub_zero, hsum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) ?_
    intro x' _
    have := h x'
    rw [sub_zero] at this
    exact this

private theorem unit_lift (l : ℕ) [Fact l.Prime] (m : ℕ) (hm : 1 ≤ m) (x : (ZMod (l ^ m))ˣ) :
    ∃ u : ℤ_[l]ˣ, PadicInt.toZModPow m (u : ℤ_[l]) = x := by
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  haveI : Fact (1 < l ^ m) := ⟨Nat.one_lt_pow (by omega) (Fact.out : l.Prime).one_lt⟩
  have hsurj : Function.Surjective (PadicInt.toZModPow (p := l) m) := by
    intro y
    obtain ⟨k, rfl⟩ := ZMod.natCast_zmod_surjective y
    exact ⟨k, map_natCast _ k⟩
  obtain ⟨u, hu⟩ := IsLocalRing.surjective_units_map_of_local_ringHom _ hsurj hsurj.isLocalHom x
  exact ⟨u, congrArg Units.val hu⟩

theorem UpperTheory.Kd.C7.pContOf :
    UpperTheory.Kd.C7.SContOf := by
  unfold UpperTheory.Kd.C7.SContOf
  intro l _ hl2 Ω _ _ _ A hA c β ζ hζ Z hZ hP
  obtain ⟨c₀, m₀, hP⟩ := hP
  intro r n
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  set m := r + (m₀ + n + c₀ + 1) with hm_def
  have hm0 : m₀ ≤ m := by omega
  obtain ⟨P, hKP⟩ := hP m hm0
  set N := m - c₀ with hN
  obtain ⟨hprim, hNm, hu, ho, hk⟩ := hKP
  have hlN : 0 < l ^ N := pow_pos (Fact.out : l.Prime).pos N
  choose w hw using fun i : Fin β.d => IsAlgClosed.exists_pow_nat_eq (pv (P i) (ζ m)) hlN
  have hfe := UpperTheory.Kd.C7.pFrobEx l hl2 Ω A hA
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hlift : ∀ y : (ZMod (l ^ m))ˣ, ∃ t ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m t = y⁻¹ := by
    intro y
    obtain ⟨u, hu'⟩ := unit_lift l m (by omega) y⁻¹
    obtain ⟨t, ht, htu⟩ := hfe.2.2 u
    refine ⟨t, ht, ?_⟩
    ext
    simp [ReciprocityTheory.Gal.cycMod, htu, hu']
  choose tt htt hcyc using hlift
  let f : (ZMod (l ^ m))ˣ × Option (Fin β.d) → Ω := fun q => (tt q.1)⁻¹ (q.2.elim (ζ N) w)
  let E := IntermediateField.adjoin ℚ (Set.range f)
  haveI : FiniteDimensional ℚ E :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).isIntegral)
  refine ⟨(cycMod ℚ Ω l m).ker ⊓ E.fixingSubgroup, ?_, ?_⟩
  · rw [Subgroup.coe_inf]
    refine IsOpen.inter ?_ E.fixingSubgroup_isOpen
    have := (GlobalTheory.KZ.IwC.isLocallyConstant_cycMod (Ω := Ω) (l := l) m).isOpen_fiber 1
    rw [MonoidHom.coe_ker]
    exact this
  · intro s hsU hs
    obtain ⟨hsk, hsE⟩ := Subgroup.mem_inf.mp hsU
    have hfix : ∀ q, s (f q) = f q := by
      intro q
      exact (mem_fixingSubgroup_iff _).mp hsE (f q) (IntermediateField.subset_adjoin ℚ _ ⟨q, rfl⟩)
    apply cg_down hZ hs n r (m₀ + n + c₀ + 1)
    intro y
    have hsH : s ∈ Hm l A m := by
      unfold UpperTheory.Kd.C7.Hm
      exact Subgroup.mem_inf.mpr ⟨hs, hsk⟩
    obtain ⟨hconjH, hconj⟩ := UpperTheory.Kd.C7.pConj l hl2 Ω A hA c Z hZ m s hsH (tt y) (htt y)
    have hZeq : Z m (tt y * s * (tt y)⁻¹) 1 = Z m s y := by
      rw [hconj]
      simp [hcyc]
    have hconjH' := hconjH
    unfold UpperTheory.Kd.C7.Hm at hconjH'
    have hs'I := (Subgroup.mem_inf.mp hconjH').1
    have hs'k : cycMod ℚ Ω l m (tt y * s * (tt y)⁻¹) = 1 := (Subgroup.mem_inf.mp hconjH').2
    have hs'fix : ∀ o : Option (Fin β.d),
        (tt y * s * (tt y)⁻¹) (o.elim (ζ N) w) = o.elim (ζ N) w := by
      intro o
      have h := hfix (y, o)
      rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, h, ← AlgEquiv.mul_apply, mul_inv_cancel,
        AlgEquiv.one_apply]
    have hz : (tt y * s * (tt y)⁻¹) (ζ N) = ζ N := hs'fix none
    obtain ⟨k, hkv, hcg⟩ := hk _ hs'I hs'k hz
    have hk0 : ∀ i, k i = 0 := by
      intro i
      have hwi : (tt y * s * (tt y)⁻¹) (w i) = w i := hs'fix (some i)
      have h0 : KumVal N (ζ N) (pv (P i) (ζ m)) (tt y * s * (tt y)⁻¹) 0 :=
        ⟨w i, hw i, by rw [hwi]; simp⟩
      exact kumVal_unique hprim hz (hu i).2.1 (hkv i) h0
    rw [← hZeq]
    apply cg_mono (n := n) (N := N) (by omega)
    simpa [hk0] using hcg
end

-- bundled from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.NormLev
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

private theorem nl_det {K : Type} [Field K] {n : ℕ} (w v : Fin n → K) (hw : Function.Injective w)
    (L : Matrix (Fin n) (Fin n) K) (h : ∀ k j : Fin n, v k * w k ^ (j : ℕ) = ∑ i, L i j * w k ^ (i : ℕ)) :
    L.det = ∏ k, v k := by
  have hV : (Matrix.vandermonde w).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hw
  have hmul : Matrix.vandermonde w * L = Matrix.diagonal v * Matrix.vandermonde w := by
    ext k j
    rw [Matrix.diagonal_mul, Matrix.mul_apply, Matrix.vandermonde_apply, h k j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.vandermonde_apply]
    ring
  have key := congrArg Matrix.det hmul
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at key
  exact mul_left_cancel₀ hV (key.trans (mul_comm _ _))

private theorem nl_dec {S : Type} [CommRing S] [Nontrivial S] (n : ℕ) (hn : 0 < n) (F : Polynomial S) :
    ∃ G : Fin n → Polynomial S, F = ∑ i, Polynomial.expand S n (G i) * (Polynomial.X - 1) ^ (i : ℕ) := by
  classical
  let P : Polynomial S → Prop := fun F => ∃ G : Fin n → Polynomial S,
    F = ∑ i, Polynomial.expand S n (G i) * (Polynomial.X - 1) ^ (i : ℕ)
  suffices hall : ∀ F, P F from hall F
  have h0 : P 0 := ⟨0, by simp⟩
  have hadd : ∀ F₁ F₂, P F₁ → P F₂ → P (F₁ + F₂) := by
    rintro F₁ F₂ ⟨G₁, rfl⟩ ⟨G₂, rfl⟩
    exact ⟨G₁ + G₂, by simp [add_mul, Finset.sum_add_distrib]⟩
  have hmul : ∀ H F, P F → P (Polynomial.expand S n H * F) := by
    rintro H F ⟨G, rfl⟩
    exact ⟨fun i => H * G i, by simp [Finset.mul_sum, mul_assoc]⟩
  have hsum : ∀ (s : Finset ℕ) (f : ℕ → Polynomial S), (∀ j ∈ s, P (f j)) → P (∑ j ∈ s, f j) := by
    intro s f hf
    induction s using Finset.induction_on with
    | empty => simpa using h0
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact hadd _ _ (hf a (Finset.mem_insert_self a s)) (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
  have hbase : ∀ j, j < n → P ((Polynomial.X - 1) ^ j) := by
    intro j hj
    refine ⟨Pi.single ⟨j, hj⟩ 1, ?_⟩
    rw [Finset.sum_eq_single ⟨j, hj⟩]
    · simp
    · intro b _ hb
      simp [Pi.single_apply, hb]
    · simp
  have hXr : ∀ r, r < n → P (Polynomial.X ^ r) := by
    intro r hr
    have e : (Polynomial.X : Polynomial S) ^ r = ((Polynomial.X - 1) + 1) ^ r := by ring
    rw [e, add_pow]
    refine hsum _ _ fun j hj => ?_
    have hj' : j < n := by
      have := Finset.mem_range.mp hj
      omega
    have e2 : (Polynomial.X - 1 : Polynomial S) ^ j * 1 ^ (r - j) * (r.choose j : Polynomial S)
        = Polynomial.expand S n (Polynomial.C (r.choose j : S)) * (Polynomial.X - 1) ^ j := by
      simp [mul_comm]
    rw [e2]
    exact hmul _ _ (hbase j hj')
  intro F
  induction F using Polynomial.induction_on' with
  | add p q hp hq => exact hadd _ _ hp hq
  | monomial k c =>
    have e : Polynomial.monomial k c
        = Polynomial.expand S n (Polynomial.C c * Polynomial.X ^ (k / n)) * Polynomial.X ^ (k % n) := by
      rw [map_mul, Polynomial.expand_C, map_pow, Polynomial.expand_X, ← pow_mul, mul_assoc, ← pow_add,
        Nat.div_add_mod, Polynomial.C_mul_X_pow_eq_monomial]
    rw [e]
    exact hmul _ _ (hXr _ (Nat.mod_lt _ hn))

private theorem nl_card (l : ℕ) [hl : Fact l.Prime] (m : ℕ) (hm : 1 ≤ m) :
    (Finset.univ.filter fun x : (ZMod (l ^ (m + 1)))ˣ => red l m x = 1).card = l := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hl0 : l ≠ 0 := hl.out.ne_zero
  haveI : NeZero (l ^ (k + 1 + 1)) := ⟨pow_ne_zero _ hl0⟩
  haveI : NeZero (l ^ (k + 1)) := ⟨pow_ne_zero _ hl0⟩
  have hdvd : l ^ (k + 1) ∣ l ^ (k + 1 + 1) := pow_dvd_pow l (Nat.le_succ _)
  have hsurj : Function.Surjective (red l (k + 1)) := ZMod.unitsMap_surjective hdvd
  have hc := (red l (k + 1)).ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top,
    Nat.card_eq_fintype_card (α := (ZMod (l ^ (k + 1)))ˣ),
    Nat.card_eq_fintype_card (α := (ZMod (l ^ (k + 1 + 1)))ˣ),
    ZMod.card_units_eq_totient, ZMod.card_units_eq_totient,
    Nat.totient_prime_pow_succ hl.out, Nat.totient_prime_pow_succ hl.out] at hc
  have hker : Nat.card (red l (k + 1)).ker
      = (Finset.univ.filter fun x : (ZMod (l ^ (k + 1 + 1)))ˣ => red l (k + 1) x = 1).card := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => MonoidHom.mem_ker)
  rw [← hker]
  have hpos : 0 < l ^ k * (l - 1) :=
    Nat.mul_pos (pow_pos hl.out.pos k) (by have := hl.out.two_le; omega)
  have e : l ^ (k + 1) * (l - 1) = l * (l ^ k * (l - 1)) := by ring
  rw [e] at hc
  exact Nat.eq_of_mul_eq_mul_right hpos hc

private theorem nl_nrm {R : Type} [CommRing R] (p : ℕ) [hp : Fact p.Prime] (m : ℕ) (hm : 1 ≤ m)
    [IsAdicComplete (Ideal.span {(p : R)}) R] (hu : (p : R) ∈ nonunits R) (h : PowerSeries R)
    (c : Matrix (Fin p) (Fin p) (PowerSeries R))
    (hc : ∀ j : Fin p, h * PowerSeries.X ^ (j : ℕ) = ∑ i, phi p hp.out.pos (c i j) * PowerSeries.X ^ (i : ℕ)) :
    nrm p m hm (ev R p (m + 1) h) = ev R p m c.det := by
  classical
  have hb : ∀ j : Fin p, (Model.basis p hu j : Model.Up R p) = (PowerSeries.X ^ (j : ℕ) : PowerSeries R) := by
    intro j
    rw [Model.basis, Module.Basis.mk_apply]
  have hn : normOp p h = c.det := by
    have key := Algebra.norm_eq_matrix_det (Model.basis p hu) (show Model.Up R p from h)
    refine key.trans ?_
    congr 1
    ext i j
    rw [Algebra.leftMulMatrix_eq_repr_mul]
    have e : (show Model.Up R p from h) * Model.basis p hu j = ∑ i', c i' j • Model.basis p hu i' := by
      rw [hb j]
      refine (hc j).trans ?_
      refine Finset.sum_congr rfl fun i' _ => ?_
      rw [hb i']
      rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, map_sum]
    simp [Finsupp.single_apply]
  rw [Model.nrm_ev p m hm hu h, hn]

theorem UpperTheory.Kd.C7.pNormLev :
    UpperTheory.Kd.C7.SNormLev := by
  intro l hl hl2 Ω _ _ _ A hA jj Φ ζ hζ m hm P Q hPQ
  classical
  have hlp : l.Prime := hl.out
  have hl0 : 0 < l := hlp.pos
  haveI : IsAdicComplete (Ideal.span {(l : Φ.R)}) Φ.R := Φ.fl.complete
  have hu : (l : Φ.R) ∈ nonunits Φ.R := Φ.fl.prime.not_unit
  let ψ : Polynomial (R0 A) →+* PowerSeries Φ.R :=
    (Polynomial.eval₂RingHom PowerSeries.C (1 + PowerSeries.X)).comp (Polynomial.mapRingHom Φ.i0)
  have hψ : ∀ F, Φ.ser F = ψ F := fun F => rfl
  have hψX : ψ (Polynomial.X - 1) = PowerSeries.X := by simp [ψ]
  have hψexp : ∀ F, ψ (Polynomial.expand (R0 A) l F) = phi l hl0 (ψ F) := by
    intro F
    simp only [ψ, RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.coe_eval₂RingHom]
    rw [Polynomial.map_expand, phi_eval₂]
  have hdec : ∀ jx : Fin l, ∃ G : Fin l → Polynomial (R0 A),
      P * (Polynomial.X - 1) ^ (jx : ℕ) = ∑ i, Polynomial.expand (R0 A) l (G i) * (Polynomial.X - 1) ^ (i : ℕ) :=
    fun jx => nl_dec l hl0 _
  choose G hG using hdec
  let M : Matrix (Fin l) (Fin l) (Polynomial (R0 A)) := Matrix.of fun i jx => G jx i
  have hc : ∀ jx : Fin l, Φ.ser P * PowerSeries.X ^ (jx : ℕ)
      = ∑ i, phi l hl0 ((ψ.mapMatrix M) i jx) * PowerSeries.X ^ (i : ℕ) := by
    intro jx
    have := congrArg ψ (hG jx)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_mul, map_pow, hψX, map_sum] at this
    rw [hψ, this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, hψX, hψexp]
    rfl
  have hnorm := nl_nrm l m hm hu (Φ.ser P) (ψ.mapMatrix M) hc
  rw [hnorm, ← RingHom.map_det, ← hψ]
  have hcard : Fintype.card {x : (ZMod (l ^ (m + 1)))ˣ // red l m x = 1} = l := by
    rw [Fintype.card_subtype]
    exact nl_card l m hm
  let e : Fin l ≃ {x : (ZMod (l ^ (m + 1)))ˣ // red l m x = 1} := (Fintype.equivFinOfCardEq hcard).symm
  let w : Fin l → Ω := fun k => ζ (m + 1) ^ (((e k : (ZMod (l ^ (m + 1)))ˣ) : ZMod (l ^ (m + 1))).val)
  have hprim := (hζ (m + 1)).1
  haveI : NeZero (l ^ (m + 1)) := ⟨pow_ne_zero _ hlp.ne_zero⟩
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ hlp.ne_zero⟩
  have hmodpow : ∀ a : ℕ, ζ (m + 1) ^ a = ζ (m + 1) ^ (a % l ^ (m + 1)) := by
    intro a
    conv_lhs => rw [← Nat.mod_add_div a (l ^ (m + 1)), pow_add, pow_mul, hprim.pow_eq_one, one_pow, mul_one]
  have hwpow : ∀ k, w k ^ l = ζ m := by
    intro k
    have hx := (e k).2
    have h0 : (((e k : (ZMod (l ^ (m + 1)))ˣ) : ZMod (l ^ (m + 1))).cast : ZMod (l ^ m)) = 1 :=
      congrArg Units.val hx
    rw [ZMod.cast_eq_val] at h0
    have h1 : (((e k : (ZMod (l ^ (m + 1)))ˣ) : ZMod (l ^ (m + 1))).val : ZMod (l ^ m)) = ((1 : ℕ) : ZMod (l ^ m)) := by
      rw [Nat.cast_one]
      exact h0
    have hmod := ((ZMod.natCast_eq_natCast_iff _ _ _).mp h1).mul_right' l
    rw [← pow_succ, one_mul] at hmod
    show (ζ (m + 1) ^ _) ^ l = ζ m
    rw [← pow_mul, ← (hζ m).2, hmodpow (_ * l), hmodpow l]
    exact congrArg (fun t => ζ (m + 1) ^ t) hmod
  have hwinj : Function.Injective fun k => w k - 1 := by
    intro a b hab
    have h2 : w a = w b := by simpa using hab
    have h3 := hprim.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h2
    exact e.injective (Subtype.ext (Units.ext (ZMod.val_injective _ h3)))
  have hev : ∀ (F : Polynomial (R0 A)) (z : Ω), pv (Polynomial.expand (R0 A) l F) z = pv F (z ^ l) := by
    intro F z
    simp only [pv]
    rw [← Polynomial.eval_map, ← Polynomial.eval_map, Polynomial.map_expand, Polynomial.expand_eval]
  have hrow : ∀ k (jx : Fin l), pv P (w k) * (w k - 1) ^ (jx : ℕ)
      = ∑ i, pv (G jx i) (ζ m) * (w k - 1) ^ (i : ℕ) := by
    intro k jx
    have := congrArg (Polynomial.eval₂RingHom (R0 A).subtype (w k)) (hG jx)
    simp only [map_mul, map_pow, map_sub, map_one, map_sum] at this
    simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X] at this
    rw [show pv P (w k) = Polynomial.eval₂ (R0 A).subtype (w k) P from rfl, this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hwpow k, ← hev]
    rfl
  have hdetL := nl_det (fun k => w k - 1) (fun k => pv P (w k)) hwinj
      (Matrix.of fun i jx => pv (G jx i) (ζ m)) (fun k jx => hrow k jx)
  have hpvdet : pv M.det (ζ m) = (Matrix.of fun i jx => pv (G jx i) (ζ m)).det :=
    RingHom.map_det (Polynomial.eval₂RingHom (R0 A).subtype (ζ m)) M
  have hprod : ∏ k, pv P (w k) = pv Q (ζ m) := by
    rw [← hPQ, Finset.prod_subtype (p := fun x => red l m x = 1) _ (fun x => by simp)]
    convert e.prod_comp (fun x => pv P (ζ (m + 1) ^ ((x : (ZMod (l ^ (m + 1)))ˣ) : ZMod (l ^ (m + 1))).val))
  have hzero : pv (M.det - Q) (ζ m) = 0 := by
    have hs : pv (M.det - Q) (ζ m) = pv M.det (ζ m) - pv Q (ζ m) := Polynomial.eval₂_sub _
    rw [hs, hpvdet, hdetL, hprod, sub_self]
  have key := (pWD l hl2 Ω A hA jj Φ ζ hζ m hm (M.det - Q)).1 hzero
  rw [hψ, map_sub, ← hψ, ← hψ, map_sub] at key
  exact sub_eq_zero.mp key
end

-- bundled from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.PresTr
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7
open scoped Pointwise

private theorem pt_pv {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} {τ : G ℚ Ω}
    (hτ : τ ∈ Ine (F := ℚ) A) (P : Polynomial (R0 A)) (z : Ω) (b : ℕ) (hz : τ z = z ^ b) :
    pv (Polynomial.expand (R0 A) b P) z = τ (pv P z) := by
  unfold pv
  rw [Polynomial.expand_eq_comp_X_pow, Polynomial.eval₂_comp, Polynomial.eval₂_X_pow, ← hz]
  have hc : ((τ : Ω →+* Ω)).comp (R0 A).subtype = (R0 A).subtype := by
    ext r
    exact r.2.2 τ hτ
  have e : (τ : Ω →+* Ω) (Polynomial.eval₂ (R0 A).subtype z P)
      = Polynomial.eval₂ (R0 A).subtype ((τ : Ω →+* Ω) z) P := by
    rw [Polynomial.hom_eval₂, hc]
  exact e.symm

private theorem pt_mem {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} {τ : G ℚ Ω}
    (hτ : τ ∈ Ine (F := ℚ) A) {x : Ω} (hx : x ∈ A) : τ x ∈ A := by
  have h := mem_Dec.mp (Ine_le_Dec A hτ)
  have h2 := ValuationSubring.smul_mem_pointwise_smul τ x A hx
  rw [h] at h2
  exact h2

private theorem pt_cg {l : ℕ} [Fact l.Prime] {n : ℕ} {ι : Type} [Fintype ι] (o : ι → Qbar l) (ho : ∀ i, ‖o i‖ ≤ 1)
    (k : ι → ZMod (l ^ n)) (b : ℕ) (x : Qbar l) (h : Cg n x (∑ i, o i * ((k i).val : Qbar l))) :
    Cg n ((b : Qbar l) * x) (∑ i, o i * ((((b : ZMod (l ^ n)) * k i).val : ℕ) : Qbar l)) := by
  unfold Cg at h ⊢
  haveI : NeZero (l ^ n) := ⟨(pow_pos (Nat.Prime.pos Fact.out) n).ne'⟩
  have hc : ∀ i, (((((b : ZMod (l ^ n)) * k i).val : ℕ) : Qbar l))
      = (b : Qbar l) * ((k i).val : Qbar l) - (l : Qbar l) ^ n * (((b * (k i).val) / l ^ n : ℕ) : Qbar l) := by
    intro i
    have h1 : ((b : ZMod (l ^ n)) * k i).val = (b * (k i).val) % l ^ n := by
      rw [← ZMod.val_natCast (l ^ n) (b * (k i).val)]
      congr 1
      push_cast
      rw [ZMod.natCast_zmod_val]
    rw [h1]
    have h3 : ((b * (k i).val : ℕ) : Qbar l) = (((b * (k i).val) % l ^ n : ℕ) : Qbar l)
        + (l : Qbar l) ^ n * (((b * (k i).val) / l ^ n : ℕ) : Qbar l) := by
      rw [← Nat.cast_pow, ← Nat.cast_mul, ← Nat.cast_add, Nat.mod_add_div]
    rw [Nat.cast_mul] at h3
    linear_combination -h3
  have hs : ∑ i, o i * ((((b : ZMod (l ^ n)) * k i).val : ℕ) : Qbar l)
      = ∑ i, (b : Qbar l) * (o i * ((k i).val : Qbar l))
        - ∑ i, o i * ((l : Qbar l) ^ n * (((b * (k i).val) / l ^ n : ℕ) : Qbar l)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by rw [hc]; ring)
  have key : (b : Qbar l) * x - ∑ i, o i * ((((b : ZMod (l ^ n)) * k i).val : ℕ) : Qbar l)
      = (b : Qbar l) * (x - ∑ i, o i * ((k i).val : Qbar l))
        + ∑ i, o i * ((l : Qbar l) ^ n * (((b * (k i).val) / l ^ n : ℕ) : Qbar l)) := by
    rw [hs, mul_sub, Finset.mul_sum]
    ring
  rw [key]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]
    calc ‖(b : Qbar l)‖ * ‖x - ∑ i, o i * ((k i).val : Qbar l)‖ ≤ 1 * ‖(l : Qbar l) ^ n‖ :=
          mul_le_mul (IsUltrametricDist.norm_natCast_le_one _ _) h (norm_nonneg _) zero_le_one
      _ = ‖(l : Qbar l) ^ n‖ := one_mul _
  · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) (fun i _ => ?_)
    rw [norm_mul, norm_mul]
    calc ‖o i‖ * (‖(l : Qbar l) ^ n‖ * ‖(((b * (k i).val) / l ^ n : ℕ) : Qbar l)‖)
        ≤ 1 * (‖(l : Qbar l) ^ n‖ * 1) := by
          gcongr
          · exact ho i
          · exact IsUltrametricDist.norm_natCast_le_one _ _
      _ = ‖(l : Qbar l) ^ n‖ := by ring

theorem UpperTheory.Kd.C7.pPresTr :
    UpperTheory.Kd.C7.SPresTr := by
  intro l _ hl Ω _ _ _ A hOver c β ζ hR Z hI b hb m n P hB
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out)⟩
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  have hbu : IsUnit (b : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff]
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun h => hb ?_)
    have h' : ‖((b : ℤ) : ℤ_[l])‖ < 1 := by simpa using h
    exact Int.natCast_dvd_natCast.mp ((PadicInt.norm_int_lt_one_iff_dvd _).mp h')
  obtain ⟨τ, hτ, hτc⟩ := (pFrobEx l hl Ω A hOver).2.2 hbu.unit
  have hmodpow : ∀ (t : Ω) (N a : ℕ), t ^ N = 1 → t ^ a = t ^ (a % N) := by
    intro t N a ht
    conv_lhs => rw [← Nat.mod_add_div a N]
    rw [pow_add, pow_mul, ht, one_pow, mul_one]
  have hτpow : ∀ (t : Ω) (r : ℕ), t ^ l ^ r = 1 → τ t = t ^ b := by
    intro t r ht
    have hs := cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (G ℚ Ω) Ω τ) t ht
    have e1 : cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω τ) = hbu.unit := hτc
    rw [e1, IsUnit.unit_spec, map_natCast, ZMod.val_natCast] at hs
    rw [hmodpow t (l ^ r) b ht]
    exact hs
  have hcyc : cycMod ℚ Ω l m τ = un b hb m := by
    apply Units.ext
    show (PadicInt.toZModPow m) ((cycZ ℚ Ω l τ : ℤ_[l])) = _
    rw [hτc, IsUnit.unit_spec, map_natCast]
    simp [un]
  have hu' : ∀ i, pv (Polynomial.expand (R0 A) b (P i)) (ζ m) = τ (pv (P i) (ζ m)) := fun i =>
    pt_pv hτ (P i) (ζ m) b (hτpow (ζ m) m (hR m).1.pow_eq_one)
  unfold BPres KumPres at hB ⊢
  obtain ⟨hprim, hnm, hunits, hnorm, hmain⟩ := hB
  refine ⟨hprim, hnm, fun i => ?_, hnorm, ?_⟩
  · dsimp only
    rw [hu' i]
    obtain ⟨h1, h2, h3⟩ := hunits i
    refine ⟨pt_mem hτ h1, (map_ne_zero τ).mpr h2, ?_⟩
    rw [← map_inv₀]
    exact pt_mem hτ h3
  · intro s hs hcs hsz
    have hs' : τ⁻¹ * s * τ ∈ Ine A := mul_mem (mul_mem (inv_mem hτ) hs) hτ
    have hcs' : cycMod ℚ Ω l m (τ⁻¹ * s * τ) = 1 := by simp [hcs]
    have hsz' : (τ⁻¹ * s * τ) (ζ n) = ζ n := fix_of_cycMod hnm hcs' hprim.pow_eq_one
    obtain ⟨k, hk, hcg⟩ := hmain _ hs' hcs' hsz'
    haveI : NeZero (l ^ n) := ⟨(pow_pos (Nat.Prime.pos Fact.out) n).ne'⟩
    refine ⟨fun i => (b : ZMod (l ^ n)) * k i, fun i => ?_, ?_⟩
    · obtain ⟨v, hv1, hv2⟩ := hk i
      refine ⟨τ v, ?_, ?_⟩
      · show (τ v) ^ l ^ n = pv (Polynomial.expand (R0 A) b (P i)) (ζ m)
        rw [hu' i, ← map_pow, hv1]
      · have e2 : s (τ v) = τ ((τ⁻¹ * s * τ) v) := by
          rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
        have h1 : ((b : ZMod (l ^ n)) * k i).val = (b * (k i).val) % l ^ n := by
          rw [← ZMod.val_natCast (l ^ n) (b * (k i).val)]
          congr 1
          push_cast
          rw [ZMod.natCast_zmod_val]
        rw [e2, hv2, map_mul, map_pow, hτpow (ζ n) n hprim.pow_eq_one, ← pow_mul, h1,
          ← hmodpow (ζ n) (l ^ n) _ hprim.pow_eq_one]
    · have hHm : τ⁻¹ * s * τ ∈ Hm l A m := Subgroup.mem_inf.mpr ⟨hs', hcs'⟩
      have hC := (pConj l hl Ω A hOver c Z hI m _ hHm τ hτ).2 (un b hb m)
      have e3 : τ * (τ⁻¹ * s * τ) * τ⁻¹ = s := by group
      rw [e3, hcyc, mul_inv_cancel] at hC
      show Cg n ((b : Qbar l) * Z m s (1 * un b hb m)) _
      rw [one_mul, hC]
      exact pt_cg β.val hnorm k b _ hcg
end

