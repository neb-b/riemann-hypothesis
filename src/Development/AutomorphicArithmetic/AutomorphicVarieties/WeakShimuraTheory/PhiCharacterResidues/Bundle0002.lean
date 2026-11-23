module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ContinuousResLe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.CharpolyGspConjInvScaled
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem charpoly_gsp_conj_inv_scaled {R Γ : Type} [CommRing R] [Group Γ] (r : Γ →* M4 R) (x y : Γ) (ν s s' t : R)
    (hr : IsGSp ν (r x)) (hs : s * s' = 1) (ht : t = s * ν) :
    (t • r (y * x * y⁻¹)⁻¹).charpoly = (s • r x).charpoly := by
  have h1 : IsGSp (s * s * ν) (s • r x) := by
    have ha : adj (s • r x) = s • adj (r x) := by
      ext i j
      simp only [adj_apply, Matrix.smul_apply]
      rw [smul_comm]
    unfold IsGSp at hr ⊢
    rw [ha, Matrix.smul_mul, Matrix.mul_smul, hr, smul_smul, smul_smul]
  have h2 : (s • r x) * (s' • r x⁻¹) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hs, one_smul, ← map_mul, mul_inv_cancel, map_one]
  have h3 := phiAdj _ _ _ h1 h2
  rw [← h3, smul_smul]
  have h4 : s * s * ν * s' = t := by rw [ht]; linear_combination (s * ν) * hs
  rw [h4]
  have h5 : t • r (y * x * y⁻¹)⁻¹ = r y * ((t • r x⁻¹) * r y⁻¹) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, ← map_mul, ← map_mul]
    congr 2
    group
  rw [h5, Matrix.charpoly_mul_comm, Matrix.mul_assoc, ← map_mul, inv_mul_cancel, map_one, Matrix.mul_one]

theorem UpperTheory.V.Ws.phiPol :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (n : ℕ), ∀ g, ∃ g', K.V.pr g' = (K.V.frame.conj (K.V.pr g))⁻¹ ∧ (((K.V.frame.eps c'.O X.A (K.V.pr g) ^ (1 - ((4 : ℕ) : ℤ)) : X.Aˣ) : X.A) • K.rho X n g').charpoly = (K.rho X n g).charpoly := by
  intro Ω _ _ _ l _ c D T c' h K X n g
  obtain ⟨cF, hc⟩ := phiConj T K.s
  obtain ⟨g₂, h1, h2⟩ := hc g
  refine ⟨g₂⁻¹, ?_, ?_⟩
  · rw [map_inv]
    congr 1
    apply Subtype.ext
    change toGS Ω K.V.S' (W.resP T.L Ω g₂) = toGS Ω K.V.S' K.s.c * toGS Ω K.V.S' (W.resP T.L Ω g) * (toGS Ω K.V.S' K.s.c)⁻¹
    rw [h1, map_mul, map_mul, map_inv]
  · obtain ⟨k1, k2, -⟩ := K.conj g g₂ h1
    have he : K.V.frame.eps c'.O X.A (K.V.pr g) =
        Units.map (algebraMap c'.O X.A : c'.O →* X.A) (chiO T.L Ω l c'.O g) := by
      have : K.V.ε (toGS Ω K.V.S' (W.resP T.L Ω g)) = cycZ T.L Ω l g := DFunLike.congr_fun K.V.hε (W.resP T.L Ω g)
      apply Units.ext
      change algebraMap c'.O X.A (algebraMap ℤ_[l] c'.O (K.V.ε (toGS Ω K.V.S' (W.resP T.L Ω g)) : ℤ_[l]ˣ)) = _
      rw [this]
      rfl
    rw [Link.rho_apply, Link.rho_apply, smul_smul, map_inv, h2, he]
    refine charpoly_gsp_conj_inv_scaled X.P.r _ _ _ _ (algebraMap c'.O X.A (K.sc n g⁻¹)) _ (X.pair.mult (resLe T.F_le g)) ?_ ?_
    · rw [← map_mul, ← Link.sc_mul, mul_inv_cancel, Link.sc_one, map_one]
    · have hb : K.β g₂⁻¹ = K.β g := by rw [map_inv]; exact (eq_inv_of_mul_eq_one_left k2).symm
      rw [← map_zpow, Units.coe_map]
      change algebraMap c'.O X.A _ * _ = _ * algebraMap c'.O X.A (inc h (D.th (resQ T.L g)))
      rw [← map_mul, ← map_mul]
      congr 1
      simp only [Link.sc, hb]
      set e := chiO T.L Ω l c'.O g
      have e1 : ((e ^ (1 - ((4 : ℕ) : ℤ)) : c'.Oˣ) : c'.O) * (e : c'.O) ^ 3 = 1 := by
        rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast, ← zpow_add]
        norm_num
      have e2 : ((K.κ g₂⁻¹ : c'.Oˣ) : c'.O) * K.κ g₂ = 1 := by
        rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
      generalize ((e ^ (1 - ((4 : ℕ) : ℤ)) : c'.Oˣ) : c'.O) = u at e1 ⊢
      generalize ((K.κ g₂⁻¹ : c'.Oˣ) : c'.O) = v at e2 ⊢
      generalize (inc h (D.th (resQ T.L g)) : c'.O) = θ at k1 ⊢
      generalize ((K.β g : c'.Oˣ) : c'.O) ^ n = b
      linear_combination (-u * v * b) * k1 + (b * (K.κ g : c'.O) * θ * u * (e : c'.O) ^ 3) * e2 + (b * (K.κ g : c'.O) * θ) * e1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.CpCont
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem ac_mul {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {I : Ideal R} {f g : Γ → R}
    (hf : AdicCont I f) (hg : AdicCont I g) : AdicCont I fun s => f s * g s := by
  intro N
  have e : (fun s => Ideal.Quotient.mk (I ^ N) (f s * g s)) =
      fun s => Ideal.Quotient.mk (I ^ N) (f s) * Ideal.Quotient.mk (I ^ N) (g s) := by
    funext s
    exact map_mul _ _ _
  rw [e]
  exact (hf N).comp₂ (hg N) (· * ·)

private theorem ac_pow {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {I : Ideal R} {f : Γ → R}
    (hf : AdicCont I f) (k : ℕ) : AdicCont I fun s => f s ^ k := by
  intro N
  have e : (fun s => Ideal.Quotient.mk (I ^ N) (f s ^ k)) =
      (fun x => x ^ k) ∘ fun s => Ideal.Quotient.mk (I ^ N) (f s) := by
    funext s
    exact map_pow _ _ _
  rw [e]
  exact (hf N).comp _

private theorem ac_alg {Γ O R : Type} [TopologicalSpace Γ] [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R]
    {f : Γ → O} (hf : AdicCont (maximalIdeal O) f) : AdicCont (maximalIdeal R) fun s => algebraMap O R (f s) := by
  haveI : IsLocalHom (algebraMap O R) := IsCO.isLocalHom
  have hm : maximalIdeal O ≤ (maximalIdeal R).comap (algebraMap O R) := by
    intro x hx
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact ((mem_maximalIdeal _).mp hx) (isUnit_of_map_unit _ _ hu)
  intro N
  have hN : maximalIdeal O ^ N ≤ (maximalIdeal R ^ N).comap (algebraMap O R) :=
    (Ideal.pow_right_mono hm N).trans (Ideal.le_comap_pow _ N)
  have e : (fun s => Ideal.Quotient.mk (maximalIdeal R ^ N) (algebraMap O R (f s))) =
      (Ideal.quotientMap (maximalIdeal R ^ N) (algebraMap O R) hN) ∘
        fun s => Ideal.Quotient.mk (maximalIdeal O ^ N) (f s) := by
    funext s
    simp [Ideal.quotientMap_mk]
  rw [e]
  exact (hf N).comp _

theorem UpperTheory.V.Ws.phiCpCont :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (n : ℕ), ∀ j, AdicCont (maximalIdeal X.B) fun g => (K.cpT X n g).coeff j := by
  intro Ω _ _ _ l _ c D T c' h K X n j
  have e : (fun g => (K.cpT X n g).coeff j) = fun g =>
      (X.cp (resLe T.F_le g)).coeff j *
        (algebraMap c'.O X.B ((K.κ g : c'.O)) * algebraMap c'.O X.B ((K.β g : c'.O)) ^ n) ^ (4 - j) := by
    funext g
    unfold Link.cpT
    rw [Polynomial.coeff_scaleRoots, (phiCpMap K X n g).2.1]
    simp [Link.sc, map_mul, map_pow]
  rw [e]
  have hcp : AdicCont (maximalIdeal X.B) fun g => (X.cp (resLe T.F_le g)).coeff j := by
    intro N
    exact (X.cp_cont j N).comp_continuous (continuous_resLe T.F_le)
  exact ac_mul hcp (ac_pow (ac_mul (ac_alg K.κ_cont) (ac_pow (ac_alg K.β_cont) n)) _)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.CpRedProdScaleRoots
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem cpRed_prod_scaleRoots {k ι : Type} [Field k] (m : Finset ι) (a : ι → k) (s : k) :
    (∏ i ∈ m, (Polynomial.X - C (a i))).scaleRoots s = ∏ i ∈ m, (Polynomial.X - C (a i * s)) := by
  classical
  induction m using Finset.induction_on with
  | empty => simp
  | insert i m hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, mul_scaleRoots_of_noZeroDivisors, ih, X_sub_C_scaleRoots]

theorem UpperTheory.V.Ws.phiCpRed :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (n : ℕ), ∀ g, (K.cpT X n g).map (res c'.O X.B : X.B →+* ResidueField c'.O) = ∏ i, (Polynomial.X - C (K.r.chib i (K.V.pr g) : ResidueField c'.O)) := by
  intro Ω _ _ _ l _ c D T c' h K X n g
  have hc := X.cp_red (resLe T.F_le g)
  unfold UpperTheory.V.Ws.Tower.fr at hc
  have hlead : (res c'.O X.B : X.B →+* ResidueField c'.O) (X.cp (resLe T.F_le g)).leadingCoeff ≠ 0 := by
    rw [(phiCpMap K X n g).1.leadingCoeff, map_one]
    exact one_ne_zero
  unfold Link.cpT
  rw [map_scaleRoots _ _ _ hlead, hc, cpRed_prod_scaleRoots]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [K.chib i g]
  have hal : (res c'.O X.B : X.B →+* ResidueField c'.O) (algebraMap c'.O X.B (K.sc n g)) =
      residue c'.O (K.sc n g) := by
    rw [RingHom.coe_coe, AlgHom.commutes]
    rfl
  rw [hal]
  unfold Link.sc
  congr 2
  rw [(residue c'.O).map_mul (K.κ g : c'.O), (residue c'.O).map_pow, K.β_red, one_pow, mul_one,
    (residue c'.O).map_mul, mul_comm]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ResLeMemDec
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

private theorem adic_mul {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {I : Ideal R} {f g : Γ → R}
    (hf : AdicCont I f) (hg : AdicCont I g) : AdicCont I fun x => f x * g x := by
  intro N
  convert (hf N).mul (hg N) using 1
  funext x
  exact map_mul _ _ _

private theorem adic_pow {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {I : Ideal R} {f : Γ → R}
    (hf : AdicCont I f) (n : ℕ) : AdicCont I fun x => f x ^ n := by
  induction n with
  | zero =>
    intro N
    simp only [pow_zero, map_one]
    exact IsLocallyConstant.const _
  | succ k ih =>
    simp only [pow_succ]
    exact adic_mul ih hf

private theorem adic_alg {Γ O R : Type} [TopologicalSpace Γ] [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R]
    [IsCO O R] {f : Γ → O} (hf : AdicCont (maximalIdeal O) f) :
    AdicCont (maximalIdeal R) fun x => algebraMap O R (f x) := by
  have hloc : IsLocalHom (algebraMap O R) := IsCO.isLocalHom
  intro N
  have hN : (maximalIdeal O) ^ N ≤ Ideal.comap (algebraMap O R) ((maximalIdeal R) ^ N) := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    refine Ideal.pow_right_mono ?_ N
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    exact map_nonunit (algebraMap O R) a ha
  have := (hf N).comp (Ideal.Quotient.lift ((maximalIdeal O) ^ N)
    ((Ideal.Quotient.mk ((maximalIdeal R) ^ N)).comp (algebraMap O R))
    (fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr (hN ha)))
  convert this using 1
  funext g
  simp only [Function.comp_apply, Ideal.Quotient.lift_mk, RingHom.coe_comp]

private theorem resLe_mem_Dec {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {F L : IntermediateField ℚ Ω}
    (h : F ≤ L) {A A' : ValuationSubring Ω} (e : A = A') (g : Dec (F := L) A) : resLe h g ∈ Dec (F := F) A' := by
  subst e
  exact g.2

theorem UpperTheory.V.Ws.phiIsPsi :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (n : ℕ), ∀ (ψ : ∀ v : W.Vl l T.L, Fin 4 → Dec (F := T.L) (K.s.A v) →* X.Bˣ), K.IsPsiT X n ψ → ∀ v i, K.r.IsPsi v i (ψ v i) := by
  intro Ω _ _ _ l _ c D T c' h K X n ψ hψ v i
  change W.Vl l T.L at v
  have hmem : ∀ g : Dec (F := T.L) (K.s.A (v : W.Plc (W.Lp T.L))),
      resLe T.F_le (g : G T.L Ω) ∈ (T.fr ∅).Gv (K.e v) :=
    fun g => resLe_mem_Dec T.F_le (K.hA v) g
  refine ⟨?_, ?_, ?_⟩
  · have hsc : AdicCont (maximalIdeal X.B)
        fun g : Dec (F := T.L) (K.s.A (v : W.Plc (W.Lp T.L))) => algebraMap c'.O X.B (K.sc n g) := by
      have h0 : AdicCont (maximalIdeal c'.O) fun g : G T.L Ω => K.sc n g :=
        adic_mul K.κ_cont (adic_pow K.β_cont n)
      have h1 : AdicCont (maximalIdeal c'.O)
          fun g : Dec (F := T.L) (K.s.A (v : W.Plc (W.Lp T.L))) => K.sc n g :=
        fun N => (h0 N).comp_continuous continuous_subtype_val
      exact adic_alg h1
    have hX : AdicCont (maximalIdeal X.B)
        fun g : Dec (F := T.L) (K.s.A (v : W.Plc (W.Lp T.L))) => X.ψ (K.e v) i (resLe T.F_le g) := by
      intro N
      have hc : Continuous fun g : Dec (F := T.L) (K.s.A (v : W.Plc (W.Lp T.L))) =>
          (⟨resLe T.F_le g, hmem g⟩ : (T.fr ∅).Gv (K.e v)) :=
        ((continuous_resLe T.F_le).comp continuous_subtype_val).subtype_mk hmem
      exact (X.ψ_cont (K.e v) i N).comp_continuous hc
    show AdicCont (maximalIdeal X.B)
      fun g : Dec (F := T.L) (K.s.A (v : W.Plc (W.Lp T.L))) => ((ψ v i g : X.Bˣ) : X.B)
    convert adic_mul hsc hX using 1
    funext g
    exact hψ v i g
  · intro g
    change Dec (F := T.L) (K.s.A (v : W.Plc (W.Lp T.L))) at g
    show (res c'.O X.B) ((ψ v i g : X.Bˣ) : X.B) = ((K.r.psib v i g : _) : ResidueField c'.O)
    rw [hψ v i g, K.psib, K.chib, map_mul, AlgHom.commutes, X.ψ_red (K.e v) i _ (hmem g)]
    simp only [Link.sc, IsLocalRing.ResidueField.algebraMap_eq, map_mul, map_pow, K.β_red, one_pow,
      mul_one]
    rfl
  · intro g
    obtain ⟨hκ, ht⟩ := K.mu v g.1 g.2
    have hβ : K.β g.1.1 = 1 := MonoidHom.mem_ker.mp (K.β_t (MonoidHom.mem_ker.mpr ht))
    have hmu : resLe T.F_le g.1.1 ∈ (T.fr ∅).Mu (K.e v) :=
      phiMu ((resLe T.F_le).comp (Dec (F := T.L) (K.s.A (v : W.Plc (W.Lp T.L)))).subtype)
        ((continuous_resLe T.F_le).comp continuous_subtype_val)
        (Dec (F := T.F) (T.pl (K.e v))) hmem g.1 g.2
    have hψ1 : X.ψ (K.e v) i (resLe T.F_le g.1.1) = 1 := by
      apply X.inj
      rw [X.ψ_map _ _ _ (hmem g.1), map_one]
      exact X.pair.mu (K.e v) _ hmu i
    have hsc1 : K.sc n g.1.1 = 1 := by
      simp [Link.sc, hκ, hβ]
    have hth : ((K.r.th v i g : c'.Oˣ) : c'.O) = 1 := by
      have := congrArg (fun f => ((f g : c'.Oˣ) : c'.O)) (K.th v i)
      simpa using this
    show ((ψ v i g.1 : X.Bˣ) : X.B) = algebraMap c'.O X.B ((K.r.th v i g : c'.Oˣ) : c'.O)
    refine Eq.trans ?_ (congrArg (algebraMap c'.O X.B) hth).symm
    rw [map_one, hψ v i g.1, hsc1, hψ1, map_one, mul_one]
end

