module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.SelmerSpannedByKappaLaurentAlt
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.k3F :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ (k : Kap x), K3 h k → SelmerSpannedByKappaLaurent h k := by
  intro l _ L G G0 h n x k hK z hz hb
  obtain ⟨s₀, hs⟩ := selScale l L G G0 h n x false z hz hb
  obtain ⟨z', hz', hzz⟩ := hs s₀ le_rfl
  obtain ⟨s', c, Y, hY, hYt, hYe⟩ := hK z' hz'
  set f := algebraMap x.A x.Fr with hf
  have ht : f x.t ≠ 0 := by
    intro h0
    apply PowerSeries.X_ne_zero (R := x.K)
    exact IsFractionRing.injective x.A x.Fr (h0.trans (map_zero f).symm)
  have hsm : ∀ (a : x.A) (M : Matrix (Fin n) (Fin n) x.A), f.mapMatrix (a • M) = f a • M.map f := by
    intro a M
    ext i j
    simp
  have key : ∀ g, x.t ^ s' • z' g - ∑ j, c j • k.κ j (h.p₀ g) =
      x.ρX x.A (h.p₀ g) * Y * x.ρX x.A (h.p₀ g⁻¹) - Y := by
    intro g
    have e := congrFun hYe g
    simpa [dY, Finset.sum_apply] using e
  have key2 : ∀ g, f x.t ^ s' • (z' g).map f - ∑ j, f (c j) • kapF h k j g =
      x.ρX x.Fr (h.p₀ g) * Y.map f * x.ρX x.Fr (h.p₀ g⁻¹) - Y.map f := by
    intro g
    have e := congrArg f.mapMatrix (key g)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sub, map_mul, map_sum, hsm, kapF, NP.ρX, Matrix.map_map, RingHom.mapMatrix_apply] using e
  set u := (f x.t ^ (s' + s₀))⁻¹ with hu
  refine ⟨fun j => u * f (c j), u • Y.map f, ?_, ?_, ?_⟩
  · intro i j
    obtain ⟨h1, h2⟩ := hY i j
    refine ⟨fun hij => ?_, fun _ => Submodule.mem_top⟩
    have h3 := h1 hij
    rw [Submodule.mem_bot] at h3 ⊢
    simp [h3]
  · ext i j
    have h3 := congrFun (congrFun hYt i) j
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at h3
    simp [Matrix.transpose_apply, h3]
  · funext g
    have e := key2 g
    rw [hzz g, smul_smul, ← pow_add] at e
    simp only [dY, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply]
    rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, ← e, smul_sub, smul_smul,
      inv_mul_cancel₀ (pow_ne_zero _ ht), one_smul, Finset.smul_sum]
    simp [smul_smul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.TrBndDen
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem trBnd_den {K : Type} [Field K] (Q : Submodule (PowerSeries K) (FractionRing (PowerSeries K)))
    (hQ : Q.FG) : ∃ s : ℕ, ∀ z ∈ Q, ∃ a : PowerSeries K,
      algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) a =
        algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) PowerSeries.X ^ s * z := by
  obtain ⟨T, rfl⟩ := hQ
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset
    (nonZeroDivisors (PowerSeries K)) T
  have hb0 : (b : PowerSeries K) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  obtain ⟨s, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 PowerSeries.X_irreducible
  refine ⟨s, fun z hz => ?_⟩
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, ha⟩ := hb z hz
    refine ⟨(u⁻¹ : (PowerSeries K)ˣ) * a, ?_⟩
    rw [map_mul, ha, Algebra.smul_def, hu, ← mul_assoc, ← map_mul, ← mul_assoc, Units.inv_mul, one_mul, map_pow]
  | zero => exact ⟨0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha⟩ := hy
    obtain ⟨c, hc⟩ := hz
    exact ⟨a + c, by rw [map_add (f := _), ha, hc, mul_add]⟩
  | smul c z _ hz =>
    obtain ⟨a, ha⟩ := hz
    exact ⟨c * a, by rw [map_mul, ha, Algebra.smul_def]; ring⟩

theorem UpperTheory.V.Pa.trBnd :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), ∀ (R : Type) [CommRing R] [Algebra S.F R] (e : R →ₐ[S.F] S.F) (θ : S.U.AA →+* R), S.Test R e θ → ∀ (lam : R →ₗ[S.F] S.F) (i j : Fin S.n), BndF S.x.t fun g : S.G.G₀ => lam (θ (S.U.vr g i j)) := by
  intro l _ S R _ _ e θ hT lam i j
  letI : Algebra S.x.A R := ((algebraMap S.F R).comp (algebraMap S.x.A S.F)).toAlgebra
  haveI : IsScalarTower S.x.A S.F R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨M, -, -, -, hM, P, hP, hPm, hMP⟩ := trLat l S R e θ hT
  obtain ⟨s, hs⟩ := trBnd_den (P.map (lam.restrictScalars S.x.A)) (hP.map _)
  have hs' : ∀ z ∈ P, ∃ a : S.x.A, algebraMap S.x.A S.F a = algebraMap S.x.A S.F S.x.t ^ s * lam z :=
    fun z hz => hs _ (Submodule.mem_map_of_mem hz)
  choose φ hφ using fun g : S.G.G₀ => hs' _ (hPm _ (S.U.vr_mem g) i j)
  refine ⟨s, φ, fun N => ?_, hφ⟩
  obtain ⟨j', hj'⟩ := hM N
  obtain ⟨V, hV⟩ := S.U.cont j'
  have key : ∀ q ∈ maximalIdeal S.B ^ j' • S.U.P, ∃ z ∈ P, θ (q i j) = S.x.t ^ N • z := by
    intro q hq
    refine Submodule.smul_induction_on hq ?_ ?_
    · intro b hb p hp
      obtain ⟨y, hy, hby⟩ := hj' b hb
      refine ⟨y * θ (p i j), hMP y hy _ (hPm p hp i j), ?_⟩
      rw [Matrix.smul_apply, Algebra.smul_def, map_mul, hby, smul_mul_assoc]
    · rintro a b ⟨z, hz, ha⟩ ⟨w, hw, hb⟩
      exact ⟨z + w, P.add_mem hz hw, by rw [Matrix.add_apply, map_add (f := _), ha, hb, smul_add]⟩
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  refine ⟨{y | g⁻¹ * y ∈ V}, V.toOpenSubgroup.isOpen.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simp only [Set.mem_setOf_eq, inv_mul_cancel]
    exact one_mem V
  · intro y hy
    obtain ⟨z, hz, hq⟩ := key _ (hV g _ hy)
    rw [mul_inv_cancel_left, Matrix.sub_apply, map_sub] at hq
    obtain ⟨a, ha⟩ := hs' z hz
    rw [Ideal.Quotient.eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    refine ⟨a, IsFractionRing.injective S.x.A S.F ?_⟩
    rw [map_sub, hφ, hφ, ← mul_sub, ← map_sub, hq, LinearMap.map_smul_of_tower, map_mul, ha, Algebra.smul_def]
    ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.TrConst
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem krull_sub {A R : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing R] [Algebra A R]
    (M : Subalgebra A R) [Module.Finite A M] (t : A) (ht : t ∈ maximalIdeal A) (d : R)
    (h : ∀ j : ℕ, ∃ y ∈ M, d = t ^ j • y) : d = 0 := by
  have hI : Ideal.span {t} ≠ ⊤ := fun h1 =>
    (mem_maximalIdeal t).1 ht (Ideal.span_singleton_eq_top.1 h1)
  obtain ⟨y0, hy0, hd0⟩ := h 0
  have hdM : d ∈ M := by simpa [hd0] using hy0
  have key := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := M) (Ideal.span {t}) hI
  have hmem : (⟨d, hdM⟩ : M) ∈ (⨅ i : ℕ, (Ideal.span {t}) ^ i • ⊤ : Submodule A M) := by
    rw [Submodule.mem_iInf]
    intro j
    obtain ⟨y, hy, hd⟩ := h j
    have e : (⟨d, hdM⟩ : M) = t ^ j • (⟨y, hy⟩ : M) := Subtype.ext hd
    rw [e, Ideal.span_singleton_pow]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  rw [key, Submodule.mem_bot] at hmem
  exact congrArg Subtype.val hmem

private theorem f_local {O B K : Type} [CommRing O] [CommRing B] [IsLocalRing B] [Algebra O B] [Field K] [Algebra O K]
    (hs : Function.Surjective (algebraMap O K)) (f : B →ₐ[O] PowerSeries K) (j : ℕ) (b : B)
    (hb : b ∈ maximalIdeal B ^ j) : ∃ c, f b = PowerSeries.X ^ j * c := by
  set φ : B →+* K := PowerSeries.constantCoeff.comp f.toRingHom with hφdef
  have hφ : Function.Surjective φ := fun k => by
    obtain ⟨o, rfl⟩ := hs k
    exact ⟨algebraMap O B o, by simp [φ, PowerSeries.algebraMap_apply]⟩
  have hker : RingHom.ker φ = maximalIdeal B :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective φ hφ)
  have hm : Ideal.map f (maximalIdeal B) ≤ Ideal.span {PowerSeries.X} := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [← hker, RingHom.mem_ker] at hy
    rw [Ideal.mem_comap, Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]
    exact hy
  have hfb : f b ∈ Ideal.span {(PowerSeries.X : PowerSeries K) ^ j} := by
    rw [← Ideal.span_singleton_pow]
    refine Ideal.pow_right_mono hm j ?_
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem f hb
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hfb
  exact ⟨c, by rw [← hc, mul_comm]⟩

theorem UpperTheory.V.Pa.trConst :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), ∀ (R : Type) [CommRing R] [Algebra S.F R] (e : R →ₐ[S.F] S.F) (θ : S.U.AA →+* R), S.Test R e θ → (∀ b ∈ pairVals S.u ∪ {b | ∃ j i, b = S.P.U j i ∨ b = S.P.y j i} ∪ {S.P.s}, θ (algebraMap S.B S.U.AA b) = algebraMap S.F R (algebraMap S.x.A S.F (S.P.f b))) → ∀ b : S.Bh, θ (algebraMap S.Bh S.U.AA b) = algebraMap S.F R (S.rF b) := by
  intro l _ S R _ _ e θ hT hgen b
  letI : Algebra S.x.A R := ((algebraMap S.F R).comp (algebraMap S.x.A S.F)).toAlgebra
  haveI : IsScalarTower S.x.A S.F R := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨M, hMfin, -, -, hMj, -⟩ := trLat l S R e θ hT
  have htow : ∀ y : S.B, algebraMap S.B S.U.AA y = algebraMap S.Bh S.U.AA (algebraMap S.B S.Bh y) :=
    fun y => by first | rfl | exact IsScalarTower.algebraMap_apply _ _ _ _
  set ψ1 : S.B →+* R := θ.comp (algebraMap S.B S.U.AA) with hψ1
  set ψ2 : S.B →+* R :=
    (algebraMap S.F R).comp ((algebraMap S.x.A S.F).comp S.P.f.toRingHom) with hψ2
  have hO : ∀ c : S.O, ψ1 (algebraMap S.O S.B c) = ψ2 (algebraMap S.O S.B c) := by
    intro c
    obtain ⟨o, ho⟩ := S.oo_O c
    have h1 := hT.oo o
    rw [ho] at h1
    show θ (algebraMap S.B S.U.AA _) = algebraMap S.F R (algebraMap S.x.A S.F (S.P.f _))
    rw [htow, h1, S.rF_f]
  have hadj : ∀ a ∈ Algebra.adjoin S.O
      (pairVals S.u ∪ {b | ∃ j i, b = S.P.U j i ∨ b = S.P.y j i} ∪ {S.P.s}), ψ1 a = ψ2 a := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem y hy => exact hgen y hy
    | algebraMap c => exact hO c
    | add y z _ _ hy hz => rw [map_add (f := _), map_add (f := _), hy, hz]
    | mul y z _ _ hy hz => rw [map_mul, map_mul, hy, hz]
  have ht : S.x.t ∈ maximalIdeal S.x.A := by
    rw [mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff]
    simp
  have hB : ∀ y : S.B, ψ1 y = ψ2 y := by
    intro y
    refine sub_eq_zero.1 (krull_sub M S.x.t ht (ψ1 y - ψ2 y) ?_)
    intro j
    obtain ⟨j', hj'⟩ := hMj j
    obtain ⟨a, ha, hya⟩ := S.P.gen (max j j') y
    have hm' : y - a ∈ maximalIdeal S.B ^ j' := Ideal.pow_le_pow_right (le_max_right _ _) hya
    have hm : y - a ∈ maximalIdeal S.B ^ j := Ideal.pow_le_pow_right (le_max_left _ _) hya
    obtain ⟨z, hz, hze⟩ := hj' (y - a) hm'
    obtain ⟨c, hc⟩ := f_local S.P.surj S.P.f j (y - a) hm
    refine ⟨z - algebraMap S.x.A R c, M.sub_mem hz (M.algebraMap_mem c), ?_⟩
    have e1 : ψ1 y - ψ2 y = ψ1 (y - a) - ψ2 (y - a) := by
      rw [map_sub, map_sub, hadj a ha]
      ring
    rw [e1, smul_sub, ← hze]
    congr 1
    show algebraMap S.F R (algebraMap S.x.A S.F (S.P.f (y - a))) = _
    rw [hc, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    simp [map_mul, map_pow]
  obtain ⟨N, hN⟩ := hT.nil
  have hker : ∀ m ∈ maximalIdeal S.Bh, e (θ (algebraMap S.Bh S.U.AA m)) = 0 := by
    intro m hm
    have hp : S.pr0 (algebraMap S.Bh S.U.AA m) = m := by
      simpa using ((prAdd l S).2.1 m 0).1
    rw [hT.res, hp]
    have hm2 : m ∈ RingHom.ker S.rF := by rw [S.rF_ker]; exact hm
    exact (RingHom.mem_ker).1 hm2
  have hkill : ∀ m ∈ maximalIdeal S.Bh ^ N, θ (algebraMap S.Bh S.U.AA m) = 0 := by
    intro m hm
    have h1 : Ideal.map (θ.comp (algebraMap S.Bh S.U.AA)) (maximalIdeal S.Bh) ≤ RingHom.ker e := by
      rw [Ideal.map_le_iff_le_comap]
      intro y hy
      exact (RingHom.mem_ker).2 (hker y hy)
    have h2 : θ.comp (algebraMap S.Bh S.U.AA) m ∈ RingHom.ker e ^ N := by
      refine Ideal.pow_right_mono h1 N ?_
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hm
    rw [hN, Ideal.mem_bot] at h2
    exact h2
  have hmax : ∀ m ∈ maximalIdeal S.Bh, θ (algebraMap S.Bh S.U.AA m) = 0 := by
    intro m hm
    obtain ⟨a, s, hs, hsa⟩ := S.cpl.dense N m
    have e1 := hkill _ hsa
    simp only [map_sub, map_mul, sub_eq_zero, ← htow] at e1
    have e2 : ψ2 s * θ (algebraMap S.Bh S.U.AA m) = ψ2 a := by
      rw [← hB, ← hB]
      exact e1
    set u := algebraMap S.x.A S.F (S.P.f s) with hudef
    have hu : u ≠ 0 := fun h0 =>
      hs ((RingHom.mem_ker).2 (IsFractionRing.injective S.x.A S.x.Fr (h0.trans (map_zero _).symm)))
    have e3 : θ (algebraMap S.Bh S.U.AA m) =
        algebraMap S.F R (u⁻¹ * algebraMap S.x.A S.F (S.P.f a)) := by
      calc θ (algebraMap S.Bh S.U.AA m)
          = algebraMap S.F R (u⁻¹ * u) * θ (algebraMap S.Bh S.U.AA m) := by
            rw [inv_mul_cancel₀ hu, map_one, one_mul]
        _ = _ := by
            rw [map_mul, mul_assoc, map_mul]
            exact congrArg _ e2
    have e4 := hker m hm
    rw [e3, AlgHom.commutes] at e4
    have e5 : u⁻¹ * algebraMap S.x.A S.F (S.P.f a) = 0 := e4
    rw [e3, e5, map_zero]
  obtain ⟨o, ho⟩ := S.oo_surj (S.rF b)
  simp only [RingHom.comp_apply] at ho
  have hm : b - algebraMap S.OO S.Bh o ∈ maximalIdeal S.Bh := by
    rw [← S.rF_ker, RingHom.mem_ker, map_sub, ho, sub_self]
  have hb := hmax _ hm
  rw [map_sub, map_sub, sub_eq_zero, hT.oo o, ho] at hb
  exact hb
end

