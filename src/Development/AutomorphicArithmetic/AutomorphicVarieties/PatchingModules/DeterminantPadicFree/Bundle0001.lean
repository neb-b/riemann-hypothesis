module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Central
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.central :
    ∀ {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n) (Z : Matrix (Fin n) (Fin n) F), (∀ g ∈ D.G', D.r g * Z = Z * D.r g) → (Z ∈ Od F F n D.a → Z = 0) ∧ (Z ∈ Ev F F n D.a → ∀ g, D.r g * Z = Z * D.r g) := by
  intro F G _ _ n D Z hZ
  have key : ∀ X ∈ Ev F F n D.a, X * Z = Z * X := by
    intro X hX
    rw [← D.span] at hX
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, hg, rfl⟩ := hx
      exact hZ g hg
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul, mul_add, hx, hy]
    | smul c x _ hx => rw [Matrix.smul_mul, Matrix.mul_smul, hx]
  refine ⟨fun hO => ?_, fun _ g => key _ (D.ev g)⟩
  ext i j
  by_cases hij : ((i : ℕ) < D.a ↔ (j : ℕ) < D.a)
  · simpa using (hO i j).1 hij
  · have hne : i ≠ j := fun h => hij (by rw [h])
    have hE : Matrix.diagonal (Pi.single i (1 : F)) ∈ Ev F F n D.a := by
      intro p q
      refine ⟨fun _ => Submodule.mem_top, fun h => ?_⟩
      have hpq : p ≠ q := fun e => h (by rw [e])
      simp [Matrix.diagonal_apply_ne _ hpq]
    have h := congrFun (congrFun (key _ hE) i) j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at h
    simpa [Pi.single_eq_of_ne hne.symm] using h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.ClosedOfComb
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem char_of_padic {l : ℕ} [Fact l.Prime] {K : Type} [Field K] [Finite K] (f : ℤ_[l] →+* K) :
    (l : K) = 0 := by
  obtain ⟨p, hchar⟩ := CharP.exists K
  have hp : p.Prime := CharP.char_is_prime K p
  have hpl : p = l := by
    by_contra hne
    have hunit : IsUnit (p : ℤ_[l]) := by
      by_contra hnu
      have hlt : ‖((p : ℤ) : ℤ_[l])‖ < 1 := by
        rw [Int.cast_natCast]
        exact PadicInt.mem_nonunits.mp hnu
      rw [PadicInt.norm_int_lt_one_iff_dvd, Int.natCast_dvd_natCast] at hlt
      exact hne ((Nat.prime_dvd_prime_iff_eq (Fact.out) hp).mp hlt).symm
    have h := hunit.map f
    rw [map_natCast, CharP.cast_eq_zero] at h
    exact not_isUnit_zero h
  subst hpl
  exact CharP.cast_eq_zero K p

private theorem closed_of_comb {A G ι : Type} [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    [TopologicalSpace G] [Fintype ι] (ρ : ι → G → A) (hρ : ∀ a, AdicCont (maximalIdeal A) (ρ a))
    (q : ι → FractionRing A) (ψ : G → A)
    (h : ∀ g, algebraMap A (FractionRing A) (ψ g) = ∑ a, q a * algebraMap A (FractionRing A) (ρ a g)) :
    IsClosed {g | ψ g = 1} := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors A) Finset.univ q
  choose c hc using fun a => hb a (Finset.mem_univ a)
  have key : ∀ g, ψ g = 1 ↔ ∑ a, c a * ρ a g - (b : A) = 0 := by
    intro g
    have h1 : algebraMap A (FractionRing A) ((b : A) * ψ g) =
        algebraMap A (FractionRing A) (∑ a, c a * ρ a g) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_mul, h g, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_mul, hc a, Algebra.smul_def, mul_assoc]
    have h2 := IsFractionRing.injective A (FractionRing A) h1
    have hb0 : (b : A) ≠ 0 := nonZeroDivisors.coe_ne_zero b
    rw [sub_eq_zero, ← h2]
    constructor
    · intro h
      rw [h, mul_one]
    · intro h
      exact mul_left_cancel₀ hb0 (h.trans (mul_one _).symm)
  have hset : {g | ψ g = 1} =
      ⋂ N : ℕ, {g | Ideal.Quotient.mk (maximalIdeal A ^ N) (∑ a, c a * ρ a g - (b : A)) = 0} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Ideal.Quotient.eq_zero_iff_mem, key]
    constructor
    · intro h N
      rw [h]
      exact Ideal.zero_mem _
    · intro h
      have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal A) (maximalIdeal.isMaximal A).ne_top
      have hmem : ∑ a, c a * ρ a g - (b : A) ∈ ⨅ i, maximalIdeal A ^ i := Submodule.mem_iInf _ |>.mpr h
      rw [hbot] at hmem
      exact (Submodule.mem_bot A).mp hmem
  rw [hset]
  refine isClosed_iInter fun N => ?_
  have hF : IsLocallyConstant (fun g => fun a => Ideal.Quotient.mk (maximalIdeal A ^ N) (ρ a g)) := by
    rw [IsLocallyConstant.iff_isOpen_fiber]
    intro y
    have hy : (fun g => fun a => Ideal.Quotient.mk (maximalIdeal A ^ N) (ρ a g)) ⁻¹' {y} =
        ⋂ a, {g | Ideal.Quotient.mk (maximalIdeal A ^ N) (ρ a g) = y a} := by
      ext g
      simp [funext_iff]
    rw [hy]
    exact isOpen_iInter_of_finite fun a => (hρ a N).isOpen_fiber (y a)
  have hG := (hF.comp (fun w => ∑ a, Ideal.Quotient.mk (maximalIdeal A ^ N) (c a) * w a -
    Ideal.Quotient.mk (maximalIdeal A ^ N) (b : A))).isClopen_fiber 0
  convert hG.isClosed using 1
  ext g
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sub, map_sum, map_mul]

theorem UpperTheory.V.Pa.Det.psiMu :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} {r : Resid F O n} (x : Point r) (v : F.Vl) (i : Fin n) (g : F.Gv v), g ∈ F.mu v → x.ψ v i g = 1 := by
  intro l _ F O _ _ _ n r x v i g hg
  have hl : (l : x.K) = 0 := char_of_padic ((algebraMap O x.K).comp (algebraMap ℤ_[l] O))
  haveI : CharP x.K l := (CharP.charP_iff_prime_eq_zero Fact.out).mpr hl
  haveI : CharP (PowerSeries x.K) l :=
    charP_of_injective_algebraMap (algebraMap x.K (PowerSeries x.K)).injective l
  obtain ⟨P, hP⟩ := x.flag v
  have hclosed : IsClosed {s : F.Gv v | ((x.ψ v i s : (PowerSeries x.K)ˣ) : PowerSeries x.K) = 1} := by
    refine closed_of_comb (ι := Fin n × Fin n) (fun ab s => (mat x.ρ) (F.φ v s) ab.1 ab.2) ?_
      (fun ab => (P : Matrix (Fin n) (Fin n) _) i ab.1 * ((P⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) ab.2 i)
      _ ?_
    · intro ab N
      exact (x.cont ab.1 ab.2 N).comp_continuous (F.φ_cont v)
    · intro s
      have hs := (hP s).2 i
      simp only [pushCh, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe] at hs
      rw [← hs]
      simp only [pushRep, mat, MonoidHom.comp_apply, Units.coeHom_apply, Units.val_mul, Matrix.mul_apply,
        Finset.sum_mul, Fintype.sum_prod_type, Matrix.GeneralLinearGroup.map_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
  have hker : (commutator (F.Gv v)).topologicalClosure ≤ (x.ψ v i).ker := by
    apply Subgroup.topologicalClosure_minimal
    · exact Abelianization.commutator_subset_ker (x.ψ v i)
    · convert hclosed using 1
      ext s
      rw [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_setOf_eq, Units.val_eq_one]
  obtain ⟨k, hk⟩ := CommGroup.mem_primaryComponent.mp (Subgroup.mem_comap.mp hg)
  have hgk : g ^ l ^ k ∈ (commutator (F.Gv v)).topologicalClosure := by
    rw [← QuotientGroup.eq_one_iff]
    simpa using hk
  have h1 : x.ψ v i g ^ l ^ k = 1 := by
    rw [← map_pow]
    exact hker hgk
  have h2 : ((x.ψ v i g : PowerSeries x.K) - 1) ^ l ^ k = 0 := by
    rw [sub_pow_char_pow, one_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, sub_self]
  have h3 : (x.ψ v i g : PowerSeries x.K) - 1 = 0 := pow_eq_zero_iff (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) |>.mp h2
  exact Units.ext (sub_eq_zero.mp h3)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.CompSel
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem mapL {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (j : A →+* B) (p : B →+ A)
    (hp : ∀ a y, p (j a * y) = a * p y) (M : Matrix (Fin n) (Fin n) A) (Z : Matrix (Fin n) (Fin n) B) :
    (M.map j * Z).map p = M * Z.map p := by
  ext a b
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mul_apply, map_sum, hp]

private theorem mapR {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (j : A →+* B) (p : B →+ A)
    (hp : ∀ a y, p (j a * y) = a * p y) (M : Matrix (Fin n) (Fin n) A) (Z : Matrix (Fin n) (Fin n) B) :
    (Z * M.map j).map p = Z.map p * M := by
  ext a b
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, map_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [mul_comm, hp, mul_comm]

theorem UpperTheory.V.Pa.Det.compSel :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x x' : NP F n) (j : x.A →+* x'.A), x.Ext2 x' j → ∀ (p : x'.A →+ x.A), (∀ a y, p (j a * y) = a * p y) → (∀ N : ℕ, ∃ N' : ℕ, ∀ y ∈ Ideal.span {x'.t} ^ N', p y ∈ Ideal.span {x.t} ^ N) → (∀ z ∈ SelZ F x'.t (x'.ρX x'.A) (x'.wX x'.A) (x'.wiX x'.A) (Od x'.A x'.A n x'.a), (fun g => (z g).map p) ∈ SelZ F x.t (x.ρX x.A) (x.wX x.A) (x.wiX x.A) (Od x.A x.A n x.a)) ∧ ∀ z ∈ Bd F (x'.ρX x'.A) (Od x'.A x'.A n x'.a), (fun g => (z g).map p) ∈ Bd F (x.ρX x.A) (Od x.A x.A n x.a) := by
  intro l _ F n x x' j hE p hp hc
  obtain ⟨⟨-, -, -, hρ, ha, -⟩, hw, -⟩ := hE
  have e1 : ∀ g, x'.ρX x'.A g = (x.ρX x.A g).map j := by
    intro g
    ext a b
    simp [NP.ρX, hρ, mat]
  have e2 : ∀ v, x'.wX x'.A v = (x.wX x.A v).map j := by
    intro v
    ext a b
    simp [NP.wX, hw]
  have e3 : ∀ v, x'.wiX x'.A v = (x.wiX x.A v).map j := by
    intro v
    ext a b
    simp only [NP.wiX, hw, ← map_inv]
    rfl
  have hOd : ∀ Y ∈ Od x'.A x'.A n x'.a, Y.map p ∈ Od x.A x.A n x.a := by
    intro Y hY a b
    refine ⟨fun h => ?_, fun _ => trivial⟩
    have := (hY a b).1 (by rw [ha]; exact h)
    rw [Submodule.mem_bot] at this ⊢
    simp [this]
  have hsub : ∀ Y Z : Matrix (Fin n) (Fin n) x'.A, (Y - Z).map p = Y.map p - Z.map p := by
    intro Y Z; ext a b; simp
  have hadd : ∀ Y Z : Matrix (Fin n) (Fin n) x'.A, (Y + Z).map p = Y.map p + Z.map p := by
    intro Y Z; ext a b; simp
  have hd : ∀ Y g, (dY F (x'.ρX x'.A) Y g).map p = dY F (x.ρX x.A) (Y.map p) g := by
    intro Y g
    simp only [dY]
    rw [hsub, e1, e1, mapR j p hp, mapL j p hp]
  refine ⟨?_, ?_⟩
  · rintro z ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨fun g => hOd _ (h1 g), ?_, ?_, ?_, ?_, ?_⟩
    · intro a b N
      obtain ⟨N', hN⟩ := hc N
      have := h2 a b N'
      rw [IsLocallyConstant.iff_eventually_eq] at this ⊢
      intro g
      filter_upwards [this g] with h hh
      rw [Ideal.Quotient.eq] at hh ⊢
      have := hN _ hh
      rw [map_sub] at this
      exact this
    · intro g h
      simp only
      rw [h3, hadd, e1, e1, mapR j p hp, mapL j p hp]
    · intro g
      simp only
      rw [h4]
      ext a b
      simp
    · intro u g hg
      simp only
      rw [h5 u g hg]
      ext a b
      simp
    · intro v
      obtain ⟨Y, hY, hL⟩ := h6 v
      refine ⟨Y.map p, hOd _ hY, fun g => ?_⟩
      have key : x.wiX x.A v * ((z (F.φ v g)).map p - dY F (x.ρX x.A) (Y.map p) (F.φ v g)) * x.wX x.A v =
          (x'.wiX x'.A v * (z (F.φ v g) - dY F (x'.ρX x'.A) Y (F.φ v g)) * x'.wX x'.A v).map p := by
        rw [e2, e3, mapR j p hp, mapL j p hp, hsub, hd]
      refine ⟨fun a b hab => ?_, fun hg a => ?_⟩
      · simp only
        rw [key, Matrix.map_apply, (hL g).1 a b hab, map_zero]
      · simp only
        rw [key, Matrix.map_apply, (hL g).2 hg a, map_zero]
  · rintro z ⟨Y, hY, hT, rfl⟩
    refine ⟨Y.map p, hOd _ hY, ?_, funext fun g => hd Y g⟩
    ext a b
    have := congrFun (congrFun hT a) b
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at this
    simp [this]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.ConjCont
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem adicCont_iff_eventually_sub_mem_pow {Γ R : Type} [TopologicalSpace Γ] [CommRing R] (I : Ideal R) (f : Γ → R) :
    UpperTheory.V.Alg.AdicCont I f ↔ ∀ (N : ℕ) (x : Γ), ∀ᶠ y in nhds x, f y - f x ∈ I ^ N := by
  unfold UpperTheory.V.Alg.AdicCont
  simp only [IsLocallyConstant.iff_eventually_eq, Ideal.Quotient.eq]

private theorem eventually_mul_sub_mem_pow_of_eventually_sub_mem {Γ R : Type} [TopologicalSpace Γ] [CommRing R] (I : Ideal R) (f g : Γ → R)
    (hf : ∀ (N : ℕ) (x : Γ), ∀ᶠ y in nhds x, f y - f x ∈ I ^ N)
    (hg : ∀ (N : ℕ) (x : Γ), ∀ᶠ y in nhds x, g y - g x ∈ I ^ N) :
    ∀ (N : ℕ) (x : Γ), ∀ᶠ y in nhds x, f y * g y - f x * g x ∈ I ^ N := by
  intro N x
  filter_upwards [hf N x, hg N x] with y h1 h2
  have e : f y * g y - f x * g x = f y * (g y - g x) + (f y - f x) * g x := by ring
  rw [e]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h2) (Ideal.mul_mem_right _ _ h1)

private theorem eventually_sum_sub_mem_pow_of_eventually_sub_mem {Γ R ι : Type} [TopologicalSpace Γ] [CommRing R] [Fintype ι] (I : Ideal R)
    (f : ι → Γ → R) (hf : ∀ i (N : ℕ) (x : Γ), ∀ᶠ y in nhds x, f i y - f i x ∈ I ^ N) :
    ∀ (N : ℕ) (x : Γ), ∀ᶠ y in nhds x, (∑ i, f i y) - ∑ i, f i x ∈ I ^ N := by
  intro N x
  filter_upwards [Filter.eventually_all.2 (fun i => hf i N x)] with y hy
  rw [← Finset.sum_sub_distrib]
  exact Ideal.sum_mem _ (fun i _ => hy i)

private theorem eventually_sub_mem_maxIdeal_pow_of_const_mul {Γ K' : Type} [TopologicalSpace Γ] [Field K'] (c : PowerSeries K') (hc : c ≠ 0)
    (f : Γ → PowerSeries K')
    (h : ∀ (N : ℕ) (x : Γ), ∀ᶠ y in nhds x, c * f y - c * f x ∈ maximalIdeal (PowerSeries K') ^ N) :
    ∀ (N : ℕ) (x : Γ), ∀ᶠ y in nhds x, f y - f x ∈ maximalIdeal (PowerSeries K') ^ N := by
  intro N x
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 (fun h0 => hc (PowerSeries.order_eq_top.1 h0))
  filter_upwards [h (N + k) x] with y hy
  rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hy ⊢
  rw [← mul_sub, PowerSeries.X_pow_dvd_iff] at hy
  rw [PowerSeries.X_pow_dvd_iff]
  intro m hm
  have h1 : ((N + k : ℕ) : ℕ∞) ≤ (c * (f y - f x)).order :=
    PowerSeries.le_order _ _ (fun i hi => hy i (by exact_mod_cast hi))
  rw [PowerSeries.order_mul, ← hk] at h1
  apply PowerSeries.coeff_of_lt_order
  by_cases h3 : (f y - f x).order = ⊤
  · rw [h3]
    exact ENat.coe_lt_top m
  · obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.1 h3
    rw [← hr] at h1 ⊢
    have h4 : N + k ≤ k + r := by exact_mod_cast h1
    exact_mod_cast (by omega : m < r)

theorem UpperTheory.V.Pa.Det.conjCont :
    ∀ {K K' G : Type} [Field K] [Field K'] [TopologicalSpace G] {n : ℕ} (j : PowerSeries K →+* PowerSeries K') (ρ : G → Matrix (Fin n) (Fin n) (PowerSeries K)) (Q : GL (Fin n) (FractionRing (PowerSeries K'))) (ρ' : G → Matrix (Fin n) (Fin n) (PowerSeries K')), IsLocalHom j → (∀ a b, AdicCont (maximalIdeal (PowerSeries K)) fun g => ρ g a b) → (∀ g, (ρ g).map ((algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))).comp j) * (Q : Matrix (Fin n) (Fin n) (FractionRing (PowerSeries K'))) = (Q : Matrix (Fin n) (Fin n) (FractionRing (PowerSeries K'))) * (ρ' g).map (algebraMap (PowerSeries K') (FractionRing (PowerSeries K')))) → ∀ a b, AdicCont (maximalIdeal (PowerSeries K')) fun g => ρ' g a b := by
  intro K K' G _ _ _ n j ρ Q ρ' hj hρ hQ a b
  have hX : PowerSeries.X ∈ maximalIdeal (PowerSeries K) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]
    exact Ideal.mem_span_singleton_self _
  have hjX : j PowerSeries.X ∈ maximalIdeal (PowerSeries K') := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact (IsLocalRing.mem_maximalIdeal _).1 hX (isUnit_of_map_unit j _ hu)
  have hjr : ∀ k l (N : ℕ) (x : G), ∀ᶠ y in nhds x,
      j (ρ y k l) - j (ρ x k l) ∈ maximalIdeal (PowerSeries K') ^ N := by
    intro k l N x
    filter_upwards [(adicCont_iff_eventually_sub_mem_pow _ _).1 (hρ k l) N x] with y hy
    rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hy
    obtain ⟨t, ht⟩ := hy
    rw [← map_sub, ht, map_mul, map_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hjX N)
  obtain ⟨b1, hb1⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (PowerSeries K'))
    (fun p : Fin n × Fin n => (↑(Q⁻¹) : Matrix (Fin n) (Fin n) (FractionRing (PowerSeries K'))) p.1 p.2)
  obtain ⟨b2, hb2⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (PowerSeries K'))
    (fun p : Fin n × Fin n => (↑Q : Matrix (Fin n) (Fin n) (FractionRing (PowerSeries K'))) p.1 p.2)
  choose P hP using fun p => RingHom.mem_rangeS.1 (hb1 p)
  choose R hR using fun p => RingHom.mem_rangeS.1 (hb2 p)
  have hconj : ∀ g, (ρ' g).map (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) =
      (↑(Q⁻¹) : Matrix (Fin n) (Fin n) (FractionRing (PowerSeries K'))) *
        (ρ g).map ((algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))).comp j) *
        (↑Q : Matrix (Fin n) (Fin n) (FractionRing (PowerSeries K'))) := by
    intro g
    rw [Matrix.mul_assoc, hQ g, ← Matrix.mul_assoc, Q.inv_mul, Matrix.one_mul]
  have key : ∀ g, ((b1 : PowerSeries K') * (b2 : PowerSeries K')) * ρ' g a b =
      ∑ l, ∑ k, P (a, k) * j (ρ g k l) * R (l, b) := by
    intro g
    apply IsFractionRing.injective (PowerSeries K') (FractionRing (PowerSeries K'))
    have e := congrFun (congrFun (hconj g) a) b
    simp only [Matrix.map_apply, Matrix.mul_apply, RingHom.comp_apply] at e
    rw [map_mul, e]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, hP, hR, Algebra.smul_def, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [adicCont_iff_eventually_sub_mem_pow]
  refine eventually_sub_mem_maxIdeal_pow_of_const_mul ((b1 : PowerSeries K') * (b2 : PowerSeries K'))
    (mul_ne_zero (nonZeroDivisors.coe_ne_zero b1) (nonZeroDivisors.coe_ne_zero b2)) _ ?_
  simp only [key]
  refine eventually_sum_sub_mem_pow_of_eventually_sub_mem _ (fun l y => ∑ k, P (a, k) * j (ρ y k l) * R (l, b)) ?_
  intro l
  refine eventually_sum_sub_mem_pow_of_eventually_sub_mem _ (fun k y => P (a, k) * j (ρ y k l) * R (l, b)) ?_
  intro k
  refine eventually_mul_sub_mem_pow_of_eventually_sub_mem _ (fun y => P (a, k) * j (ρ y k l)) (fun _ => R (l, b)) ?_ (fun N x => by simp)
  exact eventually_mul_sub_mem_pow_of_eventually_sub_mem _ (fun _ => P (a, k)) (fun y => j (ρ y k l)) (fun N x => by simp) (hjr k l)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.ConstMap
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.constMap :
    ∀ {K K' : Type} [Field K] [Finite K] [Field K'] (j : PowerSeries K →+* PowerSeries K'), ∃ ι : K →+* K', ∀ a, j (PowerSeries.C a) = PowerSeries.C (ι a) := by
  intro K K' _ _ _ j
  classical
  haveI := Fintype.ofFinite K
  set p := ringChar K with hpdef
  haveI : CharP K p := ringChar.charP K
  obtain ⟨n, hp, hq⟩ := FiniteField.card K p
  haveI : Fact p.Prime := ⟨hp⟩
  set e : K →+* PowerSeries K' := j.comp PowerSeries.C
  haveI : CharP (PowerSeries K') p := charP_of_injective_ringHom e.injective p
  have key : ∀ f : PowerSeries K', f ^ (p ^ (n : ℕ)) = f → f = PowerSeries.C (PowerSeries.constantCoeff f) := by
    intro f hf
    set c := PowerSeries.constantCoeff f with hcdef
    have hc : c ^ (p ^ (n : ℕ)) = c := by
      have h2 := congrArg PowerSeries.constantCoeff hf
      rw [map_pow] at h2
      exact h2
    have hd : (f - PowerSeries.C c) ^ (p ^ (n : ℕ)) = f - PowerSeries.C c := by
      rw [sub_pow_char_pow, hf, ← map_pow, hc]
    have hd0 : PowerSeries.constantCoeff (f - PowerSeries.C c) = 0 := by
      rw [map_sub, PowerSeries.constantCoeff_C, hcdef, sub_self]
    have hq1 : 1 ≤ p ^ (n : ℕ) - 1 := by
      have h1 : 2 ≤ p := hp.two_le
      have h3 : p ≤ p ^ (n : ℕ) := Nat.le_self_pow (PNat.ne_zero n) p
      omega
    have hprod : (f - PowerSeries.C c) * ((f - PowerSeries.C c) ^ (p ^ (n : ℕ) - 1) - 1) = 0 := by
      rw [mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel (by omega), hd, sub_self]
    rcases mul_eq_zero.mp hprod with h | h
    · exact sub_eq_zero.mp h
    · exfalso
      have h4 := congrArg PowerSeries.constantCoeff h
      rw [map_sub, map_pow, hd0, zero_pow (by omega), map_one, map_zero] at h4
      exact zero_ne_one (sub_eq_zero.mp h4)
  refine ⟨PowerSeries.constantCoeff.comp e, fun a => ?_⟩
  have ha : j (PowerSeries.C a) ^ (p ^ (n : ℕ)) = j (PowerSeries.C a) := by
    rw [← map_pow, ← map_pow, ← hq, FiniteField.pow_card]
  exact key _ ha
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.CornerCoc
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem cut_conj {F : Type} [Field F] {n : ℕ} (p q : Fin n → Prop) [DecidablePred p] [DecidablePred q]
    [∀ i j, Decidable (p i ∧ q j)] (A Z B : Matrix (Fin n) (Fin n) F)
    (hA : ∀ i k, ¬ (p i ↔ p k) → A i k = 0) (hB : ∀ i k, ¬ (q i ↔ q k) → B i k = 0) :
    (Matrix.of fun i j => if p i ∧ q j then (A * Z * B) i j else 0) =
      A * (Matrix.of fun i j => if p i ∧ q j then Z i j else 0) * B := by
  ext i j
  have key : (if p i ∧ q j then (A * Z * B) i j else 0) =
      ∑ m, ∑ k, if p i ∧ q j then A i k * Z k m * B m j else 0 := by
    split_ifs
    · simp only [Matrix.mul_apply, Finset.sum_mul]
    · simp
  rw [Matrix.of_apply, key]
  simp only [Matrix.mul_apply, Finset.sum_mul, Matrix.of_apply]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => ?_
  by_cases h1 : p i ↔ p k
  · by_cases h2 : q m ↔ q j
    · by_cases h : p i ∧ q j
      · rw [if_pos h, if_pos ⟨h1.1 h.1, h2.2 h.2⟩]
      · rw [if_neg h, if_neg (fun h' => h ⟨h1.2 h'.1, h2.1 h'.2⟩)]; simp
    · simp [hB m j h2]
  · simp [hA i k h1]

private theorem cV_conj {F : Type} [Field F] {n a : ℕ} {A B : Matrix (Fin n) (Fin n) F}
    (hA : A ∈ Ev F F n a) (hB : B ∈ Ev F F n a) (Z : Matrix (Fin n) (Fin n) F) :
    cV a (A * Z * B) = A * cV a Z * B ∧ cV' a (A * Z * B) = A * cV' a Z * B := by
  have hA' : ∀ i k : Fin n, ¬ ((i : ℕ) < a ↔ (k : ℕ) < a) → A i k = 0 := fun i k h => by
    simpa using (hA i k).2 h
  have hB' : ∀ i k : Fin n, ¬ ((i : ℕ) < a ↔ (k : ℕ) < a) → B i k = 0 := fun i k h => by
    simpa using (hB i k).2 h
  exact ⟨cut_conj (fun i => (i : ℕ) < a) (fun i => ¬ (i : ℕ) < a) A Z B hA'
      (fun i k h => hB' i k (fun e => h (not_congr e))),
    cut_conj (fun i => ¬ (i : ℕ) < a) (fun i => (i : ℕ) < a) A Z B
      (fun i k h => hA' i k (fun e => h (not_congr e))) hB'⟩

private theorem cV_lin {F : Type} [Field F] {n : ℕ} (a : ℕ) (c : F) (Y Z : Matrix (Fin n) (Fin n) F) :
    (cV a (Y + c • Z) = cV a Y + c • cV a Z ∧ cV' a (Y + c • Z) = cV' a Y + c • cV' a Z) ∧
    (cV a (c • Z - Y) = c • cV a Z - cV a Y ∧ cV' a (c • Z - Y) = c • cV' a Z - cV' a Y) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> ext i j <;>
    simp only [cV, cV', Matrix.of_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply] <;>
    split_ifs <;> simp

theorem UpperTheory.V.Pa.Det.cornerCoc :
    ∀ {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n) (χ : G → F) (S : Set G) (z : G → Matrix (Fin n) (Fin n) F), TwCoc χ D.r S z → (TwCoc χ D.r S fun g => cV D.a (z g)) ∧ (TwCoc χ D.r S fun g => cV' D.a (z g)) ∧ (∀ Y g, cV D.a (dTw χ D.r Y g) = dTw χ D.r (cV D.a Y) g ∧ cV' D.a (dTw χ D.r Y g) = dTw χ D.r (cV' D.a Y) g) ∧ ∀ Z : Matrix (Fin n) (Fin n) F, cV D.a Z ∈ Od F F n D.a ∧ cV' D.a Z ∈ Od F F n D.a ∧ (cV D.a Z)ᵀ = cV' D.a Zᵀ ∧ (Z ∈ Od F F n D.a → cV D.a Z + cV' D.a Z = Z) := by
  intro F G _ _ n D χ S z hz
  refine ⟨fun g hg h hh => ?_, fun g hg h hh => ?_, fun Y g => ⟨?_, ?_⟩, fun Z => ⟨?_, ?_, ?_, fun hZ => ?_⟩⟩
  · beta_reduce
    rw [hz g hg h hh, (cV_lin _ _ _ _).1.1, (cV_conj (D.ev _) (D.ev _) _).1]
  · beta_reduce
    rw [hz g hg h hh, (cV_lin _ _ _ _).1.2, (cV_conj (D.ev _) (D.ev _) _).2]
  · unfold dTw
    rw [(cV_lin _ _ _ _).2.1, (cV_conj (D.ev _) (D.ev _) _).1]
  · unfold dTw
    rw [(cV_lin _ _ _ _).2.2, (cV_conj (D.ev _) (D.ev _) _).2]
  · intro i j
    refine ⟨fun e => ?_, fun _ => Submodule.mem_top⟩
    rw [Submodule.mem_bot, cV, Matrix.of_apply, if_neg (fun h => h.2 (e.1 h.1))]
  · intro i j
    refine ⟨fun e => ?_, fun _ => Submodule.mem_top⟩
    rw [Submodule.mem_bot, cV', Matrix.of_apply, if_neg (fun h => h.1 (e.2 h.2))]
  · ext i j
    simp only [cV, cV', Matrix.of_apply, Matrix.transpose_apply, and_comm]
  · ext i j
    have h0 : ((i : ℕ) < D.a ↔ (j : ℕ) < D.a) → Z i j = 0 := fun e => by simpa using (hZ i j).1 e
    simp only [cV, cV', Matrix.of_apply, Matrix.add_apply]
    by_cases hi : (i : ℕ) < D.a <;> by_cases hj : (j : ℕ) < D.a
    · simp [hi, hj, h0 (iff_of_true hi hj)]
    · rw [if_pos ⟨hi, hj⟩, if_neg (fun h => h.1 hi), add_zero]
    · rw [if_neg (fun h => hi h.1), if_pos ⟨hi, hj⟩, zero_add]
    · rw [if_neg (fun h => hi h.1), if_neg (fun h => hj h.2), add_zero, h0 (iff_of_false hi hj)]
end

