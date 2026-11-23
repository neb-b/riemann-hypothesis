module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.ExistsIsInvariantSectionMemBasicOpenIff
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsAffineOpenLeOfIsQProjOver
section
open AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem exists_isAffineOpen_le_of_isQProjOver :
    ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsQProjOver s →
      ∀ (F : Set X) (U : X.Opens), F.Finite → F ⊆ U →
        ∃ V : X.Opens, IsAffineOpen V ∧ F ⊆ V ∧ V ≤ U := by
  intro R _ X s hs F U hF hFU
  haveI := FiniteSubsetsInAffineOpens.of_isQProjOver hs
  exact FiniteSubsetsInAffineOpens.exists_isAffineOpen_le hF U hFU

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HolomorphicPeriodicCocycleCoboundary
section
open Complex Matrix
open scoped ContDiff BigOperators Real Topology

namespace GlobalTheory.PeriodicCousin

variable {g : ℕ}

noncomputable def dbar (a : Fin g) (f : (Fin g → ℂ) → ℂ) (z : Fin g → ℂ) : ℂ :=
  fderiv ℝ f z (Pi.single a 1 : Fin g → ℂ) + I * fderiv ℝ f z (I • (Pi.single a 1 : Fin g → ℂ))

theorem dbar_congr {a : Fin g} {f f' : (Fin g → ℂ) → ℂ} {z : Fin g → ℂ} (h : f =ᶠ[𝓝 z] f') :
    dbar a f z = dbar a f' z := by
  unfold dbar; rw [h.fderiv_eq]

theorem dbar_sub {a : Fin g} {f f' : (Fin g → ℂ) → ℂ} {z : Fin g → ℂ}
    (h : DifferentiableAt ℝ f z) (h' : DifferentiableAt ℝ f' z) :
    dbar a (fun x => f x - f' x) z = dbar a f z - dbar a f' z := by
  unfold dbar
  rw [fderiv_fun_sub h h']
  simp only [ContinuousLinearMap.sub_apply]
  ring

theorem contDiffAt_fderiv {f : (Fin g → ℂ) → ℂ} {z : Fin g → ℂ} (h : ContDiffAt ℝ ∞ f z) :
    ContDiffAt ℝ ∞ (fderiv ℝ f) z :=
  h.fderiv_right (m := ∞) (by norm_cast)

theorem contDiffAt_dbar {a : Fin g} {f : (Fin g → ℂ) → ℂ} {z : Fin g → ℂ}
    (h : ContDiffAt ℝ ∞ f z) : ContDiffAt ℝ ∞ (dbar a f) z := by
  have h1 := contDiffAt_fderiv h
  exact (h1.clm_apply contDiffAt_const).add (contDiffAt_const.mul (h1.clm_apply contDiffAt_const))

theorem fderiv_dbar {a : Fin g} {f : (Fin g → ℂ) → ℂ} {z : Fin g → ℂ}
    (h : ContDiffAt ℝ ∞ f z) (v : Fin g → ℂ) :
    fderiv ℝ (dbar a f) z v = fderiv ℝ (fderiv ℝ f) z v (Pi.single a 1 : Fin g → ℂ) +
      I * fderiv ℝ (fderiv ℝ f) z v (I • (Pi.single a 1 : Fin g → ℂ)) := by
  have h1 : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) z) z :=
    ((contDiffAt_fderiv h).differentiableAt (by simp)).hasFDerivAt
  have h2 := fun u : Fin g → ℂ =>
    (ContinuousLinearMap.apply ℝ ℂ u).hasFDerivAt.comp z h1
  have h3 := (h2 (Pi.single a 1)).add ((h2 (I • (Pi.single a 1 : Fin g → ℂ))).const_mul I)
  have h4 : fderiv ℝ (dbar a f) z = _ := h3.fderiv
  rw [h4]
  simp

theorem dbar_comm {a b : Fin g} {f : (Fin g → ℂ) → ℂ} {z : Fin g → ℂ}
    (h : ContDiffAt ℝ ∞ f z) : dbar a (dbar b f) z = dbar b (dbar a f) z := by
  have hs : IsSymmSndFDerivAt ℝ f z := h.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  have e : ∀ u v, fderiv ℝ (fderiv ℝ f) z u v = fderiv ℝ (fderiv ℝ f) z v u := hs
  show fderiv ℝ (dbar b f) z _ + I * fderiv ℝ (dbar b f) z _ =
    fderiv ℝ (dbar a f) z _ + I * fderiv ℝ (dbar a f) z _
  rw [fderiv_dbar h, fderiv_dbar h, fderiv_dbar h, fderiv_dbar h,
    e (Pi.single b 1) (Pi.single a 1), e (Pi.single b 1) (I • (Pi.single a 1 : Fin g → ℂ)),
    e (I • (Pi.single b 1 : Fin g → ℂ)) (Pi.single a 1),
    e (I • (Pi.single b 1 : Fin g → ℂ)) (I • (Pi.single a 1 : Fin g → ℂ))]
  ring

noncomputable def antilin (t : Fin g → ℂ) : (Fin g → ℂ) →L[ℝ] ℂ :=
  ∑ a, t a • ((conjCLE : ℂ →L[ℝ] ℂ).comp (ContinuousLinearMap.proj a))

theorem antilin_apply (t z : Fin g → ℂ) : antilin t z = t ⬝ᵥ star z := by
  simp [antilin, dotProduct]

theorem dbar_antilin (t z : Fin g → ℂ) (a : Fin g) : dbar a (antilin t) z = 2 * t a := by
  unfold dbar
  rw [ContinuousLinearMap.fderiv, antilin_apply, antilin_apply]
  have h1 : star (Pi.single a 1 : Fin g → ℂ) = Pi.single a 1 := by
    ext j; by_cases h : j = a
    · subst h; simp
    · simp [h]
  rw [star_smul, h1]
  simp only [dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul, star_def, conj_I]
  linear_combination (-t a) * I_mul_I

end GlobalTheory.PeriodicCousin

namespace GlobalTheory
open PeriodicCousin

theorem holomorphic_periodic_cocycle_coboundary : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ (ι : Type) (U : ι → Set (Fin g → ℂ)) (c : ι → ι → (Fin g → ℂ) → ℂ), (∀ i, IsOpen (U i)) → (∀ i (l : Λ) z, z ∈ U i → z + l ∈ U i) → (∀ z, ∃ i, z ∈ U i) → (∀ i j, DifferentiableOn ℂ (c i j) (U i ∩ U j)) → (∀ i j (l : Λ), ∀ z ∈ U i ∩ U j, c i j (z + l) = c i j z) → (∀ i j k, ∀ z ∈ U i ∩ U j ∩ U k, c i j z + c j k z = c i k z) → ∃ (t : (Fin g → ℂ)) (h : ι → (Fin g → ℂ) → ℂ), (∀ i, DifferentiableOn ℂ (h i) (U i) ∧ ∀ (l : Λ), ∀ z ∈ U i, h i (z + l) = h i z + t ⬝ᵥ star (l : (Fin g → ℂ))) ∧ ∀ i j, ∀ z ∈ U i ∩ U j, c i j z = h j z - h i z := by
  intro g Λ hd hs ι U c hU hUΛ hcov hc hcΛ hcoc
  have hcs : ∀ i j, ContDiffOn ℝ ∞ (c i j) (U i ∩ U j) := fun i j =>
    ((_root_.GlobalTheory.cauchyRiemann_iff_differentiableOn_complex g _ (c i j) ((hU i).inter (hU j))).2 (hc i j)).1
  obtain ⟨b, hb, hcb⟩ := _root_.GlobalTheory.periodic_cech_cocycle_smooth_coboundary g Λ hd hs ι U c hU hUΛ hcov hcs hcΛ hcoc
  choose k hk using hcov
  have hbAt : ∀ i, ∀ z ∈ U i, ContDiffAt ℝ ∞ (b i) z := fun i z hz =>
    (hb i).1.contDiffAt ((hU i).mem_nhds hz)
  have hind : ∀ a i j, ∀ z ∈ U i, z ∈ U j → dbar a (b j) z = dbar a (b i) z := by
    intro a i j z hi hj
    have ho := (hU i).inter (hU j)
    have h0 : dbar a (c i j) z = 0 :=
      ((_root_.GlobalTheory.cauchyRiemann_iff_differentiableOn_complex g _ (c i j) ho).1 ((hcs i j).differentiableOn (by simp))).2 (hc i j) a z ⟨hi, hj⟩
    have h1 : c i j =ᶠ[𝓝 z] fun x => b j x - b i x := by
      filter_upwards [ho.mem_nhds ⟨hi, hj⟩] with x hx using hcb i j x hx
    rw [dbar_congr h1, dbar_sub ((hbAt j z hj).differentiableAt (by simp))
      ((hbAt i z hi).differentiableAt (by simp))] at h0
    exact sub_eq_zero.1 h0
  let w : Fin g → (Fin g → ℂ) → ℂ := fun a z => dbar a (b (k z)) z
  have hw : ∀ a i, ∀ z ∈ U i, w a z = dbar a (b i) z := fun a i z hz => hind a i (k z) z hz (hk z)
  have hw' : ∀ a i, ∀ z ∈ U i, w a =ᶠ[𝓝 z] dbar a (b i) := by
    intro a i z hz
    filter_upwards [(hU i).mem_nhds hz] with x hx using hw a i x hx
  obtain ⟨t, f, hf, hfΛ, hft⟩ := _root_.GlobalTheory.dbar_solve_complexTorus g Λ hd hs w (by
    intro a
    refine ⟨contDiff_iff_contDiffAt.2 fun z =>
      (contDiffAt_dbar (hbAt _ z (hk z))).congr_of_eventuallyEq (hw' a _ z (hk z)), fun l z => ?_⟩
    rw [hw a (k z) _ (hUΛ _ l z (hk z)), hw a (k z) z (hk z)]
    have h1 : (fun x => b (k z) (x + l)) =ᶠ[𝓝 z] b (k z) := by
      filter_upwards [(hU _).mem_nhds (hk z)] with x hx using (hb _).2 l x hx
    rw [← dbar_congr h1]
    unfold dbar
    rw [fderiv_comp_add_right]) (by
    intro a a' z
    show dbar a (w a') z = dbar a' (w a) z
    rw [dbar_congr (hw' a' _ z (hk z)), dbar_congr (hw' a _ z (hk z))]
    exact dbar_comm (hbAt _ z (hk z)))
  have hfd : ∀ z, DifferentiableAt ℝ f z := fun z => (hf.differentiable (by simp)) z
  refine ⟨-((1 / 2 : ℂ) • t), fun i z => b i z - f z - antilin ((1 / 2 : ℂ) • t) z,
    fun i => ⟨?_, ?_⟩, ?_⟩
  · have hbd : ∀ z ∈ U i, DifferentiableAt ℝ (b i) z := fun z hz =>
      (hbAt i z hz).differentiableAt (by simp)
    refine ((_root_.GlobalTheory.cauchyRiemann_iff_differentiableOn_complex g _ _ (hU i)).1 ?_).1 ?_
    · intro z hz
      exact (((hbd z hz).sub (hfd z)).sub (antilin _).differentiableAt).differentiableWithinAt
    · intro a z hz
      show dbar a (fun z => (b i z - f z) - antilin ((1 / 2 : ℂ) • t) z) z = 0
      have h3 : dbar a f z = w a z - t a := hft a z
      rw [dbar_sub ((hbd z hz).fun_sub (hfd z)) (antilin _).differentiableAt,
        dbar_sub (hbd z hz) (hfd z), dbar_antilin, h3, hw a i z hz]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
  · intro l z hz
    simp only [(hb i).2 l z hz, hfΛ l z, map_add (f := _), antilin_apply _ (l : Fin g → ℂ), neg_dotProduct]
    ring
  · intro i j z hz
    rw [hcb i j z hz]
    ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsUnitDetPairingOfBicharacterOfDvdTrace
section
open scoped TensorProduct

namespace GlobalTheory

private theorem submatrix_eq_pt_mul_map_mul_transpose {O H K Γ : Type} [CommRing O] [CommRing H] [Algebra O H] [Field K]
    [Algebra O K] {r : ℕ} (b : Module.Basis (Fin r) O H) (D : Matrix (Fin r) (Fin r) O)
    (pt : Γ → (H →ₐ[O] K)) (X : Γ → Γ → K)
    (hX : ∀ a a', X a a' = ∑ i, ∑ j, algebraMap O K (D i j) * pt a (b i) * pt a' (b j))
    (e : Fin r ≃ Γ) :
    (Matrix.of X).submatrix e e = Matrix.of (fun i j => pt (e i) (b j)) * D.map (algebraMap O K) *
      Matrix.transpose (Matrix.of (fun i j => pt (e i) (b j))) := by
  ext i k
  simp only [Matrix.submatrix_apply, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul, hX]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem isUnit_det_of_bicharacter_of_dvd_trace :
    ∀ (O H K Γ : Type) [CommRing O] [IsDomain O] [CommRing H] [Algebra O H] [Field K] [IsAlgClosed K] [Algebra O K] [CommGroup Γ] (r : ℕ) (b : Module.Basis (Fin r) O H) (D : Matrix (Fin r) (Fin r) O) (pt : Γ → (H →ₐ[O] K)) (X : Γ → Γ → K) (c : O), Function.Injective (algebraMap O K) → IsReduced (K ⊗[O] H) → Function.Bijective pt → (∀ a a', X a a' = ∑ i, ∑ j, algebraMap O K (D i j) * pt a (b i) * pt a' (b j)) → (∀ a b, X a b ≠ 0) → (∀ a a' b, X (a * a') b = X a b * X a' b) → (∀ a b b', X a (b * b') = X a b * X a b') → (∀ a, (∀ b, X a b = 1) → a = 1) → c ≠ 0 → (r : O) = c ^ 2 → (∀ h : H, c ∣ Algebra.trace O H h) → IsUnit D.det := by
  intro O H K Γ _ _ _ _ _ _ _ _ r b D pt X c hinj hred hpt hX hne hm₁ hm₂ hnd hc hr hdvd
  classical
  haveI : Module.Free O H := Module.Free.of_basis b
  haveI : Module.Finite O H := Module.Finite.of_basis b
  obtain ⟨hfin, hcard, htrace⟩ :=
    finite_card_trace_algHom_of_isReduced_baseChange O H K hred
  let E : Γ ≃ (H →ₐ[O] K) := Equiv.ofBijective pt hpt
  haveI : Finite Γ := Finite.of_equiv _ E.symm
  letI : Fintype Γ := Fintype.ofFinite Γ
  letI : Fintype (H →ₐ[O] K) := Fintype.ofFinite _
  have hcardΓ : Fintype.card Γ = r := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr E, hcard, Module.finrank_eq_card_basis b,
      Fintype.card_fin]

  let e : Fin r ≃ Γ := (Fintype.equivFinOfCardEq hcardΓ).symm
  let P : Matrix (Fin r) (Fin r) K := Matrix.of fun i j => pt (e i) (b j)
  let D' : Matrix (Fin r) (Fin r) K := D.map (algebraMap O K)

  have hXP : (Matrix.of X).submatrix e e = P * D' * Matrix.transpose P := submatrix_eq_pt_mul_map_mul_transpose b D pt X hX e

  have hsum : ∀ h : H, algebraMap O K (Algebra.trace O H h) = ∑ i, pt (e i) h := by
    intro h
    rw [htrace h, finsum_eq_sum_of_fintype]
    exact (Fintype.sum_equiv (e.trans E) (fun i => pt (e i) h) (fun ga => ga h)
      fun _ => rfl).symm
  have hdvd' : ∀ h : H, ∃ d, Algebra.trace O H h = c * d := fun h => hdvd h
  choose T hT using hdvd'
  let Tm : Matrix (Fin r) (Fin r) O := Matrix.of fun j k => T (b j * b k)

  have hPP : Matrix.transpose P * P = (algebraMap O K c) • Tm.map (algebraMap O K) := by
    ext j k
    simp only [Matrix.mul_apply, Matrix.transpose_apply, P, Matrix.of_apply, Matrix.smul_apply,
      Matrix.map_apply, Tm, smul_eq_mul]
    have hjk : algebraMap O K c * algebraMap O K (T (b j * b k)) =
        algebraMap O K (Algebra.trace O H (b j * b k)) := by
      rw [hT, map_mul]
    rw [hjk, hsum]
    exact Finset.sum_congr rfl fun i _ => (map_mul (pt (e i)) (b j) (b k)).symm
  have hTm : (Tm.map (algebraMap O K)).det = algebraMap O K Tm.det :=
    ((algebraMap O K).map_det Tm).symm
  have hD' : D'.det = algebraMap O K D.det := ((algebraMap O K).map_det D).symm
  have hdetP : P.det ^ 2 = algebraMap O K c ^ r * algebraMap O K Tm.det := by
    have h := congrArg Matrix.det hPP
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Fintype.card_fin, hTm] at h
    rw [sq, h]
  have h4 := det_bicharacter_pow_four Γ K X hne hm₁ hm₂ hnd
  rw [← Matrix.det_submatrix_equiv_self e (Matrix.of X), hXP, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, hcardΓ] at h4
  have hrK : (r : K) = algebraMap O K c ^ 2 := by
    rw [← map_natCast (algebraMap O K) r, hr, map_pow]

  have key : algebraMap O K c ^ (4 * r) * algebraMap O K (Tm.det ^ 4 * D.det ^ 4) =
      algebraMap O K c ^ (4 * r) * 1 := by
    rw [map_mul, map_pow, map_pow, ← hD', mul_one]
    calc algebraMap O K c ^ (4 * r) * (algebraMap O K Tm.det ^ 4 * D'.det ^ 4)
        = (algebraMap O K c ^ r * algebraMap O K Tm.det) ^ 4 * D'.det ^ 4 := by ring
      _ = (P.det ^ 2) ^ 4 * D'.det ^ 4 := by rw [hdetP]
      _ = (P.det * D'.det * P.det) ^ 4 := by ring
      _ = (r : K) ^ (2 * r) := h4
      _ = algebraMap O K c ^ (4 * r) := by
        rw [hrK, ← pow_mul]
        congr 1
        ring
  have hu : algebraMap O K c ^ (4 * r) ≠ 0 :=
    pow_ne_zero _ (by rwa [ne_eq, map_eq_zero_iff _ hinj])
  have h1 := mul_left_cancel₀ hu key
  rw [← map_one (algebraMap O K)] at h1
  have h2 := hinj h1
  exact isUnit_iff_exists_inv.mpr ⟨Tm.det ^ 4 * D.det ^ 3, by linear_combination h2⟩

end GlobalTheory
end

