module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.FinKLoc
public import GroundTheory.GlobalFields.Adele.Approximation
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.FinKGlob
section
noncomputable section

namespace UpperTheory.V.Z.Sym.Glob.FK

open NumberField IsDedekindDomain Matrix Loc

theorem lmap_re {K K' : Type} [Field K] [Field K'] (f : K →+* K') {Δ : K} (x : Lsq K Δ) : (lmap f Δ x).re = f x.re := rfl

theorem lmap_im {K K' : Type} [Field K] [Field K'] (f : K →+* K') {Δ : K} (x : Lsq K Δ) : (lmap f Δ x).im = f x.im := rfl

variable {F : Type} [Field F] [NumberField F]

theorem int_iff (v : Pl F) (x : Kv v) : IsIntegral (Ov v) x ↔ x ∈ v.adicCompletionIntegers F := by
  rw [IsIntegrallyClosed.isIntegral_iff]
  exact ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩

theorem int_glob (x : F) : IsIntegral ℤ x ↔ ∀ v : Pl F, IsIntegral (Ov v) (cv v x) := by
  simp only [int_iff]
  refine ⟨fun h v => HeightOneSpectrum.coe_algebraMap_mem (𝓞 F) F v ⟨x, h⟩, fun h => ?_⟩
  obtain ⟨z, hz⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F x fun v =>
    (GroundTheory.Global.coe_mem_adicCompletionIntegers_iff v x).1 (h v)
  rw [← hz]
  exact RingOfIntegers.isIntegral_coe z

theorem den_glob (x : F) : ∃ c : ℕ, c ≠ 0 ∧ IsIntegral ℤ ((c : F) * x) := by
  obtain ⟨m, hm0, hm⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x)).exists_integral_multiple
  refine ⟨m.natAbs, Int.natAbs_ne_zero.2 hm0, ?_⟩
  rw [zsmul_eq_mul] at hm
  rcases Int.natAbs_eq m with h | h
  · rw [h] at hm; simpa using hm
  · rw [h] at hm; simpa using hm.neg

theorem approx_F (a : ∀ v : Pl F, Kv v) {e f : F} (he : e ≠ 0) (hf : f ≠ 0) (ha : ∀ v, IsIntegral (Ov v) (cv v e * a v)) :
    ∃ x : F, ∀ v, ∃ r, IsIntegral (Ov v) r ∧ a v = cv v x + cv v f * r := by
  let b : FiniteAdeleRing (𝓞 F) F := ⟨fun v => cv v e * a v, Filter.Eventually.of_forall fun v => (int_iff v _).1 (ha v)⟩
  obtain ⟨k, hk⟩ := GroundTheory.Global.exists_sub_mem_integralFiniteAdeles (algebraMap F (FiniteAdeleRing (𝓞 F) F) (e * f)⁻¹ * b)
  refine ⟨f * k, fun v => ⟨cv v (e * f)⁻¹ * (cv v e * a v) - cv v k, (int_iff v _).2 (hk v), ?_⟩⟩
  have h1 : cv v e ≠ 0 := (map_ne_zero _).2 he
  have h2 : cv v f ≠ 0 := (map_ne_zero _).2 hf
  rw [map_inv₀, map_mul, map_mul]
  field_simp
  ring

theorem den_loc (v : Pl F) (x : Kv v) : ∃ n : ℕ, n ≠ 0 ∧ IsIntegral (Ov v) ((n : Kv v) * x) := by
  have hU : IsOpen {w : Kv v | x - w ∈ v.adicCompletionIntegers F} :=
    (Valued.isOpen_valuationSubring (Kv v)).preimage (continuous_const.sub continuous_id)
  obtain ⟨z, hz⟩ := (HeightOneSpectrum.denseRange_algebraMap (K := F) v).exists_mem_open hU ⟨x, by simp⟩
  obtain ⟨n, hn, h⟩ := den_glob z
  refine ⟨n, hn, ?_⟩
  have h1 := (int_glob _).1 h v
  rw [map_mul, map_natCast] at h1
  have e : (n : Kv v) * x = n * cv v z + n * (x - cv v z) := by ring
  rw [e]
  exact h1.add ((isIntegral_natCast (R := Ov v) (B := Kv v) n).mul ((int_iff v _).2 hz))

variable {Δ : F}

theorem int_cD {c : ℕ} (hc : IsIntegral ℤ ((c : F) * Δ)) (v : Pl F) : IsIntegral (Ov v) ((c : Kv v) * cv v Δ) := by
  have h1 := (int_glob _).1 hc v
  rwa [map_mul, map_natCast] at h1

theorem approx_L (hΔ : Δ ≠ 0) (a : ∀ v : Pl F, Lsq (Kv v) (cv v Δ)) (ha : ∀ v, IsIntegral (Ov v) (a v)) {n : ℕ} (hn : n ≠ 0) :
    ∃ x : Lsq F Δ, ∀ v, ∃ r, IsIntegral (Ov v) r ∧ a v = lmap (cv v) Δ x + n • r := by
  obtain ⟨c, hc0, hc⟩ := den_glob Δ
  have hn' : (n : F) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hc' : (c : F) ≠ 0 := Nat.cast_ne_zero.2 hc0
  obtain ⟨x, hx⟩ := approx_F (fun v => (a v).re) (e := 2) two_ne_zero hn' fun v => by
    rw [map_ofNat]; exact int_re _ (ha v)
  obtain ⟨y, hy⟩ := approx_F (fun v => (a v).im) (e := 2 * c * Δ) (by simp [hc0, hΔ]) (mul_ne_zero hn' hc') fun v => by
    rw [map_mul, map_mul, map_ofNat, map_natCast]; exact int_im _ (int_cD hc v) (ha v)
  refine ⟨⟨x, y⟩, fun v => ?_⟩
  obtain ⟨r, hr, e1⟩ := hx v
  obtain ⟨s, hs, e2⟩ := hy v
  refine ⟨_, int_mk _ (int_cD hc v) hr hs, ?_⟩
  ext : 1
  · rw [e1]; simp [lmap]
  · rw [e2]; simp [lmap, mul_assoc]

variable (Δ)

abbrev MM : Type := ∀ v : Pl F, Matrix (Fin 2) (Fin 2) (Lsq (Kv v) (cv v Δ))

def RR : Subring (MM Δ) := ⨅ v, (RL (cv v Δ) (Ov v)).comap (Pi.evalRingHom _ v)

def jj : Matrix (Fin 2) (Fin 2) (Lsq F Δ) →+* MM Δ := Pi.ringHom fun v => (lmap (cv v) Δ).mapMatrix

variable {Δ}

theorem mem_RR {m : MM Δ} : m ∈ RR Δ ↔ ∀ v, m v ∈ RL (cv v Δ) (Ov v) := Subring.mem_iInf

theorem jj_apply (y : Matrix (Fin 2) (Fin 2) (Lsq F Δ)) (v : Pl F) : jj Δ y v = y.map (lmap (cv v) Δ) := rfl

theorem pl_ne : Nonempty (Pl F) := by
  obtain ⟨I, hI⟩ := Ideal.exists_maximal (𝓞 F)
  exact ⟨⟨I, hI.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hI (RingOfIntegers.not_isField F)⟩⟩

theorem lam_shape {y : Matrix (Fin 2) (Fin 2) (Lsq F Δ)} (h : y ∈ (RR Δ).comap (jj Δ)) : Shape y := by
  obtain ⟨v⟩ := pl_ne (F := F)
  exact shape_of_map (cv v) (mem_RR.1 h v).1

theorem lam_int {c : ℕ} (hc : IsIntegral ℤ ((c : F) * Δ)) {y : Matrix (Fin 2) (Fin 2) (Lsq F Δ)} (h : y ∈ (RR Δ).comap (jj Δ)) (i j : Fin 2) :
    IsIntegral ℤ (2 * (y i j).re) ∧ IsIntegral ℤ (2 * c * Δ * (y i j).im) := by
  have h1 : ∀ v : Pl F, IsIntegral (Ov v) (lmap (cv v) Δ (y i j)) := fun v => by
    have h2 := (mem_RR.1 (Subring.mem_comap.1 h) v).2 i j
    rwa [jj_apply, Matrix.map_apply] at h2
  refine ⟨(int_glob _).2 fun v => ?_, (int_glob _).2 fun v => ?_⟩
  · have h2 := int_re _ (h1 v)
    rw [lmap_re] at h2
    rwa [map_mul, map_ofNat]
  · have h2 := int_im _ (int_cD hc v) (h1 v)
    rw [lmap_im] at h2
    rwa [map_mul, map_mul, map_mul, map_ofNat, map_natCast]

theorem lam_fg (hΔ : Δ ≠ 0) : Module.Finite ℤ ((RR Δ).comap (jj Δ)) := by
  obtain ⟨c, hc0, hc⟩ := den_glob Δ
  let ψ : (RR Δ).comap (jj Δ) →+ (Fin 2 → Fin 2 → 𝓞 F × 𝓞 F) := AddMonoidHom.mk'
    (fun y i j => (⟨_, (lam_int hc y.2 i j).1⟩, ⟨_, (lam_int hc y.2 i j).2⟩)) fun x y => by
      funext i j
      refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · exact mul_add _ _ _
      · exact mul_add _ _ _
  refine Module.Finite.of_injective ψ.toIntLinearMap fun x y h => Subtype.ext (Matrix.ext fun i j => ?_)
  have h1 := congrFun (congrFun h i) j
  exact QuadraticAlgebra.ext (mul_left_cancel₀ two_ne_zero (congrArg Subtype.val (congrArg Prod.fst h1)))
    (mul_left_cancel₀ (by simp [hc0, hΔ]) (congrArg Subtype.val (congrArg Prod.snd h1)))

theorem approx_R (hΔ : Δ ≠ 0) : ∀ m ∈ RR Δ, ∀ n : ℕ, n ≠ 0 → ∃ x ∈ (RR Δ).comap (jj Δ), ∃ r ∈ RR Δ, m = jj Δ x + (n : MM Δ) * r := by
  intro m hm n hn
  obtain ⟨a, ha⟩ := approx_L hΔ (fun v => m v 0 0) (fun v => (mem_RR.1 hm v).2 0 0) hn
  obtain ⟨b, hb⟩ := approx_L hΔ (fun v => m v 0 1) (fun v => (mem_RR.1 hm v).2 0 1) hn
  choose r hr ha using ha
  choose s hs hb using hb
  have h1 : (fun v => qm (r v) (s v) : MM Δ) ∈ RR Δ := mem_RR.2 fun v => qm_mem _ (hr v) (hs v)
  have e : m = jj Δ (qm a b) + (n : MM Δ) * fun v => qm (r v) (s v) := by
    funext v
    rw [← nsmul_eq_mul, Pi.add_apply, Pi.smul_apply, jj_apply, qm_map, (mem_RR.1 hm v).1.eq, ha v, hb v]
    ext i j : 1
    fin_cases i <;> fin_cases j <;> simp [qm, add_comm]
  refine ⟨qm a b, ?_, _, h1, e⟩
  rw [Subring.mem_comap, ← sub_eq_of_eq_add e]
  exact sub_mem hm (mul_mem (natCast_mem _ n) h1)

theorem form_pos (hneg : ∀ σ : F →+* ℝ, σ Δ < 0) (σ : F →+* ℝ) (a b : Lsq F Δ) :
    let d := σ (a.re ^ 2 - Δ * a.im ^ 2 + b.re ^ 2 - Δ * b.im ^ 2)
    σ a.re ^ 2 ≤ d ∧ σ b.re ^ 2 ≤ d ∧ -σ Δ * σ a.im ^ 2 ≤ d ∧ -σ Δ * σ b.im ^ 2 ≤ d := by
  have h := hneg σ
  have h1 : 0 ≤ -σ Δ * σ a.im ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h2 : 0 ≤ -σ Δ * σ b.im ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  simp only [map_add (f := _), map_sub, map_mul, map_pow]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [sq_nonneg (σ a.re), sq_nonneg (σ b.re)]

theorem real_emb [IsTotallyReal F] (φ : F →+* ℂ) : ∃ σ : F →+* ℝ, ∀ x, (σ x : ℂ) = φ x :=
  ⟨(IsTotallyReal.complexEmbedding_isReal φ).embedding, fun x => ComplexEmbedding.IsReal.coe_embedding_apply _ x⟩

theorem unit_of_shape [IsTotallyReal F] (hneg : ∀ σ : F →+* ℝ, σ Δ < 0) {y : Matrix (Fin 2) (Fin 2) (Lsq F Δ)} (h : Shape y) (h0 : y ≠ 0) :
    ∃ g : DX Δ, mt g = y := by
  rw [h.eq]
  refine exists_DX fun hd => h0 ?_
  obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
  obtain ⟨σ, -⟩ := real_emb φ
  have := form_pos hneg σ (y 0 0) (y 0 1)
  rw [hd, map_zero] at this
  obtain ⟨h1, h2, h3, h4⟩ := this
  have hσ := hneg σ
  have z : ∀ x : F, σ x ^ 2 ≤ 0 → x = 0 := fun x hx => (map_eq_zero σ).1 (pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm hx (sq_nonneg _)))
  have a0 : y 0 0 = 0 := QuadraticAlgebra.ext (z _ h1) (z _ (by nlinarith [sq_nonneg (σ (y 0 0).im)]))
  have b0 : y 0 1 = 0 := QuadraticAlgebra.ext (z _ h2) (z _ (by nlinarith [sq_nonneg (σ (y 0 1).im)]))
  rw [h.eq, a0, b0]
  ext i j : 1
  fin_cases i <;> fin_cases j <;> simp [qm]

theorem box_fin [IsTotallyReal F] {e : F} (he : e ≠ 0) (d : F) :
    {x : F | IsIntegral ℤ (e * x) ∧ ∀ σ : F →+* ℝ, σ (e * x) ^ 2 ≤ σ d}.Finite := by
  have h := Embeddings.finite_of_norm_le F ℂ (∑ φ : F →+* ℂ, (‖φ d‖ + 1))
  refine (h.preimage (f := fun x : F => e * x) (mul_right_injective₀ he).injOn).subset ?_
  rintro x ⟨hx, hA⟩
  refine ⟨hx, fun φ => ?_⟩
  refine le_trans ?_ (Finset.single_le_sum (f := fun φ : F →+* ℂ => ‖φ d‖ + 1) (fun _ _ => by positivity) (Finset.mem_univ φ))
  obtain ⟨σ, hσ⟩ := real_emb φ
  have h1 := hA σ
  rw [← hσ, ← hσ, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  rw [← sq_abs] at h1
  nlinarith [le_abs_self (σ d), abs_nonneg (σ (e * x)), sq_nonneg (|σ (e * x)| - 1), abs_nonneg (σ d)]

theorem det_fin [IsTotallyReal F] (hneg : ∀ σ : F →+* ℝ, σ Δ < 0) (hΔ : Δ ≠ 0) (d : Lsq F Δ) :
    {y : Matrix (Fin 2) (Fin 2) (Lsq F Δ) | y ∈ (RR Δ).comap (jj Δ) ∧ y.det = d}.Finite := by
  obtain ⟨c, hc0, hc⟩ := den_glob Δ
  have h1 := box_fin (F := F) (e := 2) two_ne_zero (4 * d.re)
  have h2 := box_fin (F := F) (e := 2 * c * Δ) (by simp [hc0, hΔ]) (-(4 * c ^ 2 * Δ) * d.re)
  refine ((((h1.prod h2).prod (h1.prod h2)).image fun p => qm ⟨p.1.1, p.1.2⟩ ⟨p.2.1, p.2.2⟩)).subset ?_
  rintro y ⟨hy, hd⟩
  have hs := lam_shape hy
  refine ⟨(((y 0 0).re, (y 0 0).im), ((y 0 1).re, (y 0 1).im)), ?_, hs.eq.symm⟩
  rw [hs.eq, det_qm] at hd
  have hd' : d.re = (y 0 0).re ^ 2 - Δ * (y 0 0).im ^ 2 + (y 0 1).re ^ 2 - Δ * (y 0 1).im ^ 2 := by rw [← hd]; rfl
  have k1 : ∀ (σ : F →+* ℝ) (x : F), σ x ^ 2 ≤ σ d.re → σ (2 * x) ^ 2 ≤ σ (4 * d.re) := fun σ x h => by
    simp only [map_mul, map_ofNat]; nlinarith
  have k2 : ∀ (σ : F →+* ℝ) (x : F), -σ Δ * σ x ^ 2 ≤ σ d.re → σ (2 * c * Δ * x) ^ 2 ≤ σ (-(4 * c ^ 2 * Δ) * d.re) := fun σ x h => by
    simp only [map_mul, map_ofNat, map_neg, map_pow, map_natCast]
    have := mul_le_mul_of_nonneg_left h (show 0 ≤ 4 * (c : ℝ) ^ 2 * -σ Δ from mul_nonneg (by positivity) (by linarith [hneg σ]))
    nlinarith
  have f := fun σ => form_pos hneg σ (y 0 0) (y 0 1)
  rw [← hd'] at f
  exact ⟨⟨⟨(lam_int hc hy 0 0).1, fun σ => k1 σ _ (f σ).1⟩, (lam_int hc hy 0 0).2, fun σ => k2 σ _ (f σ).2.2.1⟩,
    ⟨(lam_int hc hy 0 1).1, fun σ => k1 σ _ (f σ).2.1⟩, (lam_int hc hy 0 1).2, fun σ => k2 σ _ (f σ).2.2.2⟩


variable (Δ) in
def rho : DA Δ →* MM Δ where
  toFun g v := mt (g.1 v)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem den_rho (g : DA Δ) : ∃ n : ℕ, n ≠ 0 ∧ (n : MM Δ) * rho Δ g ∈ RR Δ := by
  obtain ⟨c, hc0, hc⟩ := den_glob Δ
  have hT : {v : Pl F | g.1 v ∉ KD (cv v Δ) (Ov v)}.Finite := Filter.eventually_cofinite.1 g.2
  choose n hn0 hn using fun v : Pl F => den_mat (Ov v) (c := c)
    (by rw [← map_natCast (cv v)]; exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hc0)) (int_cD hc v) (den_loc v) (shape_mt (g.1 v))
  refine ⟨∏ v ∈ hT.toFinset, n v, Finset.prod_ne_zero_iff.2 fun v _ => hn0 v, mem_RR.2 fun v => ?_⟩
  rw [← nsmul_eq_mul, Pi.smul_apply]
  by_cases hv : g.1 v ∈ KD (cv v Δ) (Ov v)
  · exact nsmul_mem ((mem_KD _ _).1 hv).1 _
  · obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem n (hT.mem_toFinset.2 hv)
    rw [hk, mul_nsmul, nsmul_eq_mul (n v)]
    exact nsmul_mem (hn v) k

end UpperTheory.V.Z.Sym.Glob.FK
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.FinKTest
section
namespace UpperTheory.V.Z.Sym.Glob

open NumberField Matrix Loc

section Abs

variable {I G : Type} [Group G] {Gv : I → Type} [∀ v, Group (Gv v)] {K : ∀ v, Subgroup (Gv v)}

private theorem supp_fin (P : RPG G Gv K) (f : ∀ v, Gv v → ℂ) (S : Finset I) (h1 : ∀ v ∉ S, ∀ k ∈ K v, f v k = 1) (y : G) :
    (Function.mulSupport fun v => f v (P.p v y)).Finite := by
  refine (S.finite_toSet.union (Filter.eventually_cofinite.1 (P.ae y))).subset fun v hv => ?_
  by_contra h
  simp only [Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq, not_or, not_not] at h
  exact hv (h1 v h.1 _ h.2)

private theorem prod_law (P : RPG G Gv K) (f : ∀ v, Gv v → ℂ) (S : Finset I) (h1 : ∀ v ∉ S, ∀ k ∈ K v, f v k = 1) (x y : G)
    (c : I → ℂ) (hc : (Function.mulSupport c).Finite) (h : ∀ v, f v (P.p v x) = (c v)⁻¹ * f v (P.p v y)) :
    ∏ᶠ v, f v (P.p v x) = (∏ᶠ v, c v)⁻¹ * ∏ᶠ v, f v (P.p v y) := by
  rw [← finprod_inv_distrib, ← finprod_mul_distrib _ (supp_fin P f S h1 y)]
  · exact finprod_congr h
  · exact hc.subset fun v hv h => hv (by simp [h])

private theorem quot_fin (P : RPG G Gv K) (f : ∀ v, Gv v → ℂ) (S : Finset I) (h1 : ∀ v ∉ S, ∀ k ∈ K v, f v k = 1)
    (U : ∀ v, Subgroup (Gv v)) (hR : ∀ v, ∀ u ∈ U v, ∀ y, f v y ≠ 0 → f v (y * u) ≠ 0) (h2 : ∀ v ∉ S, ∀ g, f v g ≠ 0 → g ∈ U v)
    (h3 : ∀ v ∈ S, {x : Gv v ⧸ U v | f v x.out ≠ 0}.Finite) (H : Subgroup G) (hH : H = P.box U) :
    {x : G ⧸ H | ∏ᶠ v, f v (P.p v x.out) ≠ 0}.Finite := by
  have hne : ∀ y : G, ∏ᶠ v, f v (P.p v y) ≠ 0 → ∀ v, f v (P.p v y) ≠ 0 := fun y hy v h =>
    hy (finprod_eq_zero _ v h (supp_fin P f S h1 y))
  refine Set.Finite.of_finite_image (f := fun (x : G ⧸ H) (v : S) => (P.p v x.out : Gv v ⧸ U v)) ?_ ?_
  · refine (Set.Finite.pi' fun v : S => h3 v v.2).subset ?_
    rintro _ ⟨x, hx, rfl⟩ v
    obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul (U v) (P.p v x.out)
    change f v (Quotient.out _) ≠ 0
    rw [hu]
    exact hR v u u.2 _ (hne _ hx v)
  · intro x hx x' hx' h
    rw [← QuotientGroup.out_eq' x, ← QuotientGroup.out_eq' x', QuotientGroup.eq]
    refine hH.ge (Subgroup.mem_iInf.2 fun v => ?_)
    rw [Subgroup.mem_comap, map_mul, map_inv]
    by_cases hv : v ∈ S
    · exact QuotientGroup.eq.1 (congrFun h ⟨v, hv⟩)
    · exact mul_mem (inv_mem (h2 v hv _ (hne _ hx v))) (h2 v hv _ (hne _ hx' v))

end Abs

section Local

variable {K : Type} [Field K] {Δ : K}

private theorem scal_comm {z : Kˣ} {s : DX Δ} (h : IsScal z s) (y : DX Δ) : s * y = y * s := by
  apply Subtype.ext
  apply Units.ext
  change mt s * mt y = mt y * mt s
  rw [h]
  exact (Matrix.scalar_commute _ (fun r => Commute.all _ r) _).eq

private theorem scal_one : IsScal (1 : Kˣ) (1 : DX Δ) := by
  simp [IsScal, mt]

private theorem scal_mul {z z' : Kˣ} {s s' : DX Δ} (h : IsScal z s) (h' : IsScal z' s') : IsScal (z * z') (s * s') := by
  change mt s * mt s' = _
  rw [h, h', ← map_mul, ← map_mul, Units.val_mul]

private theorem mem_ZD {s : DX Δ} : s ∈ ZD Δ ↔ ∃ z, IsScal z s := by
  rw [ZD, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    rw [IsScal, mt, ← hz]
    rfl
  · rintro ⟨z, hz⟩
    exact ⟨z, Units.ext hz.symm⟩

private theorem sup_dec {J : Subgroup (DX Δ)} {u : DX Δ} (hu : u ∈ ZD Δ ⊔ J) : ∃ z s, IsScal z s ∧ s⁻¹ * u ∈ J := by
  have : (ZD Δ).Normal := ⟨fun s hs g => by
    obtain ⟨z, hz⟩ := mem_ZD.1 hs
    rw [← scal_comm hz g, mul_inv_cancel_right]; exact hs⟩
  obtain ⟨s, hs, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hu
  obtain ⟨z, hz⟩ := mem_ZD.1 hs
  exact ⟨z, s, hz, by simpa using hk⟩

private def Law (J : Subgroup (DX Δ)) (χ : Kˣ →* ℂˣ) (f : DX Δ → ℂ) : Prop :=
  ∀ z s u, IsScal z s → s⁻¹ * u ∈ J → ∀ y, f (u * y) = (χ z : ℂ)⁻¹ * f y ∧ f (y * u) = (χ z : ℂ)⁻¹ * f y

private theorem law_of {J : Subgroup (DX Δ)} {χ : Kˣ →* ℂˣ} {f : DX Δ → ℂ} (h1 : ∀ u ∈ J, ∀ y, f (u * y) = f y ∧ f (y * u) = f y)
    (h2 : ∀ z s, IsScal z s → ∀ y, f (s * y) = ((χ z)⁻¹ : ℂˣ) * f y) : Law J χ f := by
  intro z s u hs hu y
  obtain ⟨k, rfl⟩ : ∃ k, u = s * k := ⟨s⁻¹ * u, by simp⟩
  rw [inv_mul_cancel_left] at hu
  constructor
  · rw [mul_assoc, h2 z s hs, (h1 k hu y).1, Units.val_inv_eq_inv_val]
  · rw [← mul_assoc, ← scal_comm hs, mul_assoc, h2 z s hs, (h1 k hu y).2, Units.val_inv_eq_inv_val]

private theorem law_fzd {J : Subgroup (DX Δ)} {χ : Kˣ →* ℂˣ} {f : DX Δ → ℂ} (h1 : ∀ g, g ∉ ZD Δ ⊔ J → f g = 0)
    (h2 : ∀ z s k, IsScal z s → k ∈ J → f (s * k) = ((χ z)⁻¹ : ℂˣ)) : Law J χ f := by
  have key : ∀ y, y ∈ ZD Δ ⊔ J → ∃ z s k, IsScal z s ∧ k ∈ J ∧ y = s * k := fun y hy => by
    obtain ⟨z, s, hs, hk⟩ := sup_dec hy
    exact ⟨z, s, _, hs, hk, by simp⟩
  refine law_of (fun u hu y => ?_) fun z s hs y => ?_
  · by_cases hy : y ∈ ZD Δ ⊔ J
    · obtain ⟨z, s, k, hs, hk, rfl⟩ := key y hy
      rw [← mul_assoc, ← scal_comm hs u, mul_assoc, mul_assoc, h2 z s _ hs (mul_mem hu hk), h2 z s _ hs (mul_mem hk hu), h2 z s _ hs hk]
      exact ⟨rfl, rfl⟩
    · have hu' : u ∈ ZD Δ ⊔ J := Subgroup.mem_sup_right hu
      rw [h1 y hy, h1 _ (fun h => hy ((mul_mem_cancel_left hu').1 h)), h1 _ (fun h => hy ((mul_mem_cancel_right hu').1 h))]
      exact ⟨rfl, rfl⟩
  · by_cases hy : y ∈ ZD Δ ⊔ J
    · obtain ⟨z', s', k, hs', hk, rfl⟩ := key y hy
      rw [← mul_assoc, h2 _ _ _ (scal_mul hs hs') hk, h2 _ _ _ hs' hk, map_mul, mul_inv, Units.val_mul]
    · have hu' : s ∈ ZD Δ ⊔ J := Subgroup.mem_sup_left (mem_ZD.2 ⟨z, hs⟩)
      rw [h1 y hy, h1 _ (fun h => hy ((mul_mem_cancel_left hu').1 h)), mul_zero]

private theorem law_ne {J : Subgroup (DX Δ)} {χ : Kˣ →* ℂˣ} {f : DX Δ → ℂ} (h : Law J χ f) :
    ∀ u ∈ ZD Δ ⊔ J, ∀ y, f y ≠ 0 → f (y * u) ≠ 0 := by
  intro u hu y hy
  obtain ⟨z, s, hs, hk⟩ := sup_dec hu
  rw [(h z s u hs hk y).2]
  exact mul_ne_zero (inv_ne_zero (Units.ne_zero _)) hy

private theorem sup_dec' {J : Subgroup (DX Δ)} {u : DX Δ} (hu : u ∈ ZD Δ ⊔ J) :
    ∃ z s, (IsScal z s ∧ s⁻¹ * u ∈ J) ∧ (u ∈ J → z = 1) := by
  by_cases h : u ∈ J
  · exact ⟨1, 1, ⟨scal_one, by simpa using h⟩, fun _ => rfl⟩
  · obtain ⟨z, s, hs⟩ := sup_dec hu
    exact ⟨z, s, hs, fun h' => (h h').elim⟩

end Local

theorem finK_test : ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ch : F → ℂ)
    (B : Base (DX Δ) (DA Δ) V), D.IsBK ch B → ∀ t, D.Cone t → (Base.Tw.one B).IsTest (D.FK t) := by
  intro F _ _ Δ D hD V _ _ ch B hB t ht
  have hoffJ : ∀ v ∉ D.Sg, D.J2v v = KD _ (Ov v) := fun v hv => if_neg hv
  have hofff : ∀ v ∉ D.Sg, D.fKv t v = fZD (Ov v) (D.χ v) := fun v hv => funext fun _ => if_neg hv
  have honJ : ∀ v ∈ D.Sg, D.J2v v = (D.S v).J2 := fun v hv => if_pos hv
  have honf : ∀ v ∈ D.Sg, D.fKv t v = (D.S v).fK (t v) := fun v hv => funext fun _ => if_pos hv
  have hz := fun v (hv : v ∉ D.Sg) => Loc.fzdLaw (Ov v) (Kv v) (cv v Δ) (hD.off v hv) (D.χ v) (hD.chi v).1
  have hlaw : ∀ v, Law (D.J2v v) (D.χ v) (D.fKv t v) := fun v => by
    by_cases hv : v ∈ D.Sg
    · rw [honJ v hv, honf v hv]
      exact law_of ((hD.sig v hv).K_inv _ (ht v hv)).1 ((hD.sig v hv).K_inv _ (ht v hv)).2
    · rw [hoffJ v hv, hofff v hv]
      exact law_fzd (hz v hv).1 (hz v hv).2
  have h1 : ∀ v ∉ D.Sg, ∀ k ∈ KD (cv v Δ) (Ov v), D.fKv t v k = 1 := fun v hv k hk => by
    have := (hz v hv).2 1 1 k scal_one hk
    rw [one_mul, map_one, inv_one, Units.val_one] at this
    rw [hofff v hv, this]
  let P := rpg (fun v : Pl F => DX (cv v Δ)) fun v => KD (cv v Δ) (Ov v)
  have hu : ∀ u : B.U, ∃ c : Pl F → ℂ, (Function.mulSupport c).Finite ∧ (B.ω u : ℂ) = ∏ᶠ v, c v ∧
      ∀ v y, D.fKv t v (P.p v u.1 * y) = (c v)⁻¹ * D.fKv t v y ∧ D.fKv t v (y * P.p v u.1) = (c v)⁻¹ * D.fKv t v y := by
    intro u
    have hm : u.1 ∈ D.UZ := hB.U ▸ u.2
    have hm' : ∀ v, P.p v u.1 ∈ ZD _ ⊔ D.J2v v := fun v => Subgroup.mem_iInf.1 hm v
    choose z s hs h1' using fun v => sup_dec' (hm' v)
    refine ⟨fun v => D.χ v (z v), ?_, hB.ω u z s hs, fun v y => hlaw v _ _ _ (hs v).1 (hs v).2 y⟩
    refine (D.Sg.finite_toSet.union (Filter.eventually_cofinite.1 (P.ae u.1))).subset fun v hv => ?_
    by_contra h
    simp only [Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq, not_or, not_not] at h
    refine hv ?_
    have := h1' v (hoffJ v h.1 ▸ h.2)
    simp only [this, map_one, Units.val_one]
  refine ⟨fun u y => ?_, fun u y => ?_, ?_⟩
  · obtain ⟨c, hc, e, h⟩ := hu u
    rw [Units.val_inv_eq_inv_val, e]
    exact prod_law P (D.fKv t) D.Sg h1 (u.1 * y) y c hc fun v => by rw [map_mul]; exact (h v _).1
  · obtain ⟨c, hc, e, h⟩ := hu u
    rw [Units.val_inv_eq_inv_val, e]
    exact prod_law P (D.fKv t) D.Sg h1 (y * u.1) y c hc fun v => by rw [map_mul]; exact (h v _).2
  · refine quot_fin P (D.fKv t) D.Sg h1 (fun v => ZD _ ⊔ D.J2v v) (fun v => law_ne (hlaw v)) (fun v hv g hg => ?_) (fun v hv => ?_) B.U hB.U
    · rw [hofff v hv] at hg
      rw [hoffJ v hv]
      by_contra h
      exact hg ((hz v hv).1 g h)
    · have := (hD.sig v hv).K_fin _ (ht v hv)
      rw [← honJ v hv, ← honf v hv] at this
      exact this

end UpperTheory.V.Z.Sym.Glob
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.SideGSupp
section
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Glob.sideGSupp :
    ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∀ ι, IsIotaG ι → ∀ θ : GA Δ →* GA Δ,
    (∀ g v, (θ g).1 v = theta _ (g.1 v)) → ∀ t, D.Cone t → ∀ (δ : U3 Δ) (τ : F) (y : GA Δ), HasTau δ τ →
    D.FG t (y⁻¹ * ι δ * θ y) ≠ 0 → D.admitted t τ ∧ ∀ v ∉ D.Sg, cv v τ ∈ (algebraMap (Ov v) (Kv v)).range := by
  classical
  intro F _ _ Δ D hD ι hι θ hθ t ht δ τ y hτ hF
  obtain ⟨hc, -, hm, hi⟩ := UpperTheory.V.Z.Sym.Glob.sideGTau
  set x : GA Δ := y⁻¹ * ι δ * θ y with hx

  have hfin : (Function.mulSupport fun v => D.fGv t v (x.1 v)).Finite := by
    have h1 : ∀ᶠ v in Filter.cofinite, x.1 v ∈ KU (Ov v) (cv v Δ) := x.2
    refine ((Filter.eventually_cofinite.1 h1).union D.Sg.finite_toSet).subset fun v hv => ?_
    by_contra hn
    simp only [Set.mem_union, Set.mem_setOf_eq, Finset.mem_coe, not_or, not_not] at hn
    apply hv
    simp [Dat.fGv, hn.2, hn.1, one]
  have hne : ∀ v, D.fGv t v (x.1 v) ≠ 0 := fun v h0 =>
    hF (finprod_eq_zero (fun v => D.fGv t v (x.1 v)) v h0 hfin)

  have hloc : ∀ v, HasTau (x.1 v) (cv v τ) := by
    intro v
    have h1 : HasTau ((ι δ).1 v) (cv v τ) := hm _ _ (cv v) Δ δ _ τ (hι δ v) hτ
    have h2 := hc _ (cv v Δ) ((ι δ).1 v) (y.1 v) (cv v τ) h1
    have e : x.1 v = (y.1 v)⁻¹ * (ι δ).1 v * theta _ (y.1 v) := by
      rw [← hθ y v]; rfl
    rw [e]; exact h2
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · have h := hne v
    simp only [Dat.fGv, if_pos hv] at h
    exact (hD.sig v hv).G_supp _ (ht v hv) _ _ (hloc v) h
  · have h := hne v
    simp only [Dat.fGv, if_neg hv] at h
    have hk : x.1 v ∈ KU (Ov v) (cv v Δ) := by
      by_contra hn
      exact h (by simp [one, hn])
    have hint : IsIntegral (Ov v) (cv v τ) := hi _ _ _ _ _ hk (hloc v)
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    exact ⟨r, hr⟩
end

