module

public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceShift
public import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.AbsGrow
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommuteRtOfMemZalg
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.NearFinite
public import GroundTheory.AutomorphicForms.Bundle0004
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0034
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0047

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.AbsFar
section
open NumberField

private theorem exists_far {ι : Type} (s : Finset ι) (Λ : ι → ℂ) (p : ι) (hp : p ∈ s) (S₀ D : ℝ)
    (hS : ‖∑ q ∈ s, Λ q‖ ≤ S₀) (hB : D + |S₀| < ‖Λ p‖) : ∃ q ∈ s, D < ‖Λ p - Λ q‖ := by
  by_contra hne
  push Not at hne
  have hm : (1 : ℝ) ≤ s.card := by exact_mod_cast Finset.card_pos.mpr ⟨p, hp⟩
  have h1 : ‖∑ q ∈ s, (Λ p - Λ q)‖ ≤ s.card * D := by
    refine (norm_sum_le _ _).trans ?_
    have := Finset.sum_le_card_nsmul s (fun q => ‖Λ p - Λ q‖) D hne
    simpa [nsmul_eq_mul] using this
  have h2 : (s.card : ℂ) * Λ p = ∑ q ∈ s, (Λ p - Λ q) + ∑ q ∈ s, Λ q := by
    simp [Finset.sum_sub_distrib, nsmul_eq_mul]
  have h3 : (s.card : ℝ) * ‖Λ p‖ ≤ s.card * D + S₀ := by
    have : ‖(s.card : ℂ) * Λ p‖ = (s.card : ℝ) * ‖Λ p‖ := by simp
    rw [← this, h2]
    exact (norm_add_le _ _).trans (add_le_add h1 hS)
  have h4 := le_abs_self S₀
  have h5 := abs_nonneg S₀
  nlinarith

private theorem eq_zero_of_pow_le {a b y B : ℝ} (hb : 0 < b) (hab : b < a) (hy : 0 ≤ y)
    (h : ∀ k : ℕ, a ^ k * y ≤ B * b ^ k) : y = 0 := by
  by_contra hne
  have hy' : 0 < y := lt_of_le_of_ne hy (Ne.symm hne)
  have h1 : 1 < a / b := (one_lt_div hb).mpr hab
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (B / y) h1
  rw [div_pow, div_lt_div_iff₀ hy' (pow_pos hb k)] at hk
  linarith [h k]

theorem UpperTheory.ConvolutionTheory.BW.absFar :
    UpperTheory.ConvolutionTheory.BW.AbsFar := by
  classical
  intro τ _ _ n C S₀
  obtain ⟨K, hK1, hK⟩ := UpperTheory.ConvolutionTheory.FX.abs_growth τ n C
  refine ⟨2 * K + |S₀|, ?_⟩
  intro κ A V r _ _ _ _ _ _ Z H I t c idx Λ h good hs hS ⟨p, hp⟩
  obtain ⟨q, hq, hpq⟩ := exists_far _ Λ p (by simp) S₀ (2 * K) (hS (idx p.2)) hp
  have hidx : idx q.2 = idx p.2 := (Finset.mem_filter.mp hq).2
  ext φ x
  obtain ⟨B, hB⟩ := hK κ A V r Z H I t c idx Λ h good hs φ ‖x‖
  set X : τ × Fin n → A := fun q => algebraMap ℂ A (Λ q) + I (idx q.2) with hX
  have hmon : ∀ a b : ℕ, ‖c ((X p ^ a * X q ^ b) • φ) x‖ ≤ B * K ^ (a + b) := by
    intro a b
    have := hB (Finsupp.single p a + Finsupp.single q b) x le_rfl
    rw [MvPolynomial.monomial_add_single, ← MvPolynomial.X_pow_eq_monomial] at this
    simpa using this
  have hδ : X p - X q = algebraMap ℂ A (Λ p - Λ q) := by
    simp only [hX, hidx, map_sub]; ring
  have key : ∀ k : ℕ, ‖Λ p - Λ q‖ ^ k * ‖c φ x‖ ≤ B * (2 * K) ^ k := by
    intro k
    have e1 : c ((X p - X q) ^ k • φ) x = (Λ p - Λ q) ^ k * c φ x := by
      rw [hδ, ← map_pow, algebraMap_smul, map_smul]; rfl
    have e2 : (X p - X q) ^ k • φ = ∑ m ∈ Finset.range (k + 1),
        (((-1 : ℂ) ^ (m + k) * (k.choose m : ℂ)) • ((X p ^ m * X q ^ (k - m)) • φ)) := by
      rw [sub_pow, Finset.sum_smul]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← algebraMap_smul A ((-1 : ℂ) ^ (m + k) * (k.choose m : ℂ)), smul_smul]
      congr 1
      simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
      ring
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← norm_pow, ← norm_mul, ← e1, e2, map_sum, Finset.sum_apply]
    refine (norm_sum_le _ _).trans ?_
    have e3 : B * (2 * K) ^ k = ∑ m ∈ Finset.range (k + 1), (k.choose m : ℝ) * (B * K ^ k) := by
      rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
      push_cast; ring
    rw [e3]
    refine Finset.sum_le_sum fun m hm => ?_
    have hmk : m + (k - m) = k := Nat.add_sub_cancel' (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm))
    have := hmon m (k - m)
    rw [hmk] at this
    rw [map_smul, Pi.smul_apply, norm_smul]
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
  have := eq_zero_of_pow_le (by linarith) hpq (norm_nonneg _) key
  simpa using this
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.BandOps
section
noncomputable section

open NumberField GlobalTheory.CuspRep GroundTheory.Automorphic UpperTheory.V.Cm

namespace UpperTheory.ConvolutionTheory.BW

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ}

private theorem lie_right_translate_comm (X : Lie E n) (y : GL (Fin n) (Cinf E)) (k : GL (Fin n) (Af E)) :
    ∃ X' : Lie E n, lie E n X * rt E n (infGL E n y * finGL E n k) =
      rt E n (infGL E n y * finGL E n k) * lie E n X' := by
  refine ⟨toL ((y⁻¹).val * Matrix.of X * y.val), ?_⟩
  have h := GlobalTheory.CapAdInv.rt_lie y ((y⁻¹).val * Matrix.of X * y.val)
  have e : y.val * ((y⁻¹).val * Matrix.of X * y.val) * (y⁻¹).val = Matrix.of X := by
    simp [mul_assoc]
  rw [e] at h
  have h' : lie E n (toL (Matrix.of X)) = lie E n X := rfl
  rw [h'] at h
  rw [map_mul, ← mul_assoc, ← h, mul_assoc, mul_assoc, lie_rt_fin, mul_assoc]

private theorem lie_comm (X : Lie E n) (g : GA E n) :
    ∃ X' : Lie E n, lie E n X * rt E n g = rt E n g * lie E n X' := by
  have h := lie_right_translate_comm X (Matrix.GeneralLinearGroup.map (pInf E) g) (Matrix.GeneralLinearGroup.map (pFin E) g)
  rwa [infGL_mul_finGL] at h

private def itw (g : GA E n) : Subalgebra ℂ (UC E n) where
  carrier := {u | ∃ u', uC E n u * rt E n g = rt E n g * uC E n u'}
  mul_mem' := by
    rintro a b ⟨a', ha⟩ ⟨b', hb⟩
    exact ⟨a' * b', by rw [map_mul, mul_assoc, hb, ← mul_assoc, ha, map_mul, mul_assoc]⟩
  add_mem' := by
    rintro a b ⟨a', ha⟩ ⟨b', hb⟩
    exact ⟨a' + b', by rw [map_add (f := _), add_mul, ha, hb, map_add (f := _), mul_add]⟩
  algebraMap_mem' r := ⟨algebraMap _ _ r, by rw [AlgHom.commutes]; exact Algebra.commutes _ _⟩

private theorem ιC_mem (g : GA E n) (X : Lie E n) : ιC E n X ∈ itw g := by
  obtain ⟨X', h⟩ := lie_comm X g
  exact ⟨ιC E n X', by rw [uC_ιC, uC_ιC]; exact h⟩

private theorem genC_mem (g : GA E n) (τ : E →+* ℂ) (i j : Fin n) : genC τ i j ∈ itw g := by
  rw [genC, UpperTheory.V.AlgRepEndIrreducible.eL]
  exact (itw g).smul_mem ((itw g).sub_mem (ιC_mem g _) ((itw g).smul_mem (ιC_mem g _) _)) _

private theorem exists_comm (g : GA E n) (u : UC E n) :
    ∃ u', uC E n u * rt E n g = rt E n g * uC E n u' := by
  have h : Algebra.adjoin ℂ {x : UC E n | ∃ τ i j, x = genC τ i j} ≤ itw g :=
    Algebra.adjoin_le (by rintro _ ⟨τ, i, j, rfl⟩; exact genC_mem g τ i j)
  exact h (adjoin_genC (E := E) (a := n) ▸ Algebra.mem_top)

private theorem zop_comm_rt (P : MvPolynomial ((E →+* ℂ) × Fin n) ℂ) (g : GA E n) :
    Commute (zop P) (rt E n g) := by
  refine GlobalTheory.CompanionTheory.CTFin.Slice1.commute_rt_of_mem_Zalg ?_ g
  rw [Zalg_eq_map]
  exact ⟨_, (evZ E n P).2, rfl⟩

private theorem zop_comm_uC (P : MvPolynomial ((E →+* ℂ) × Fin n) ℂ) (v : UC E n) :
    zop P * uC E n v = uC E n v * zop P := by
  have h := Subalgebra.mem_center_iff.1 (evZ E n P).2 v
  unfold zop
  rw [← map_mul, ← map_mul, h]

private theorem bnd_mono {C : ℝ} (hC : 0 ≤ C) (B : ℝ) (d : ℕ) (g : GA E n) {N M : ℕ} (h : N ≤ M) :
    B * C ^ d * AutomorphicForm.height g ^ N ≤ |B| * C ^ d * AutomorphicForm.height g ^ M := by
  have h1 := AutomorphicForm.one_le_height g
  have h2 : AutomorphicForm.height g ^ N ≤ AutomorphicForm.height g ^ M := pow_le_pow_right₀ h1 h
  have h3 : 0 ≤ C ^ d := pow_nonneg hC d
  have h4 : 0 ≤ AutomorphicForm.height g ^ N := pow_nonneg (zero_le_one.trans h1) N
  exact mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self B) h3) h2 h4 (mul_nonneg (abs_nonneg B) h3)

private theorem band_zero (C : ℝ) : Band C (0 : Sm E n) :=
  { toUmg := ((umgOps E) n).1
    band := ⟨0, fun u => ⟨0, fun α g => by simp⟩⟩ }

private theorem band_add {C : ℝ} (hC : 0 ≤ C) {φ ψ : Sm E n} (h₁ : Band C φ) (h₂ : Band C ψ) : Band C (φ + ψ) := by
  refine { toUmg := (((umgOps E) n).2 φ h₁.toUmg).2.1 ψ h₂.toUmg, band := ?_ }
  obtain ⟨N, hN⟩ := h₁.band
  obtain ⟨M, hM⟩ := h₂.band
  refine ⟨max N M, fun u => ?_⟩
  obtain ⟨B, hB⟩ := hN u
  obtain ⟨D, hD⟩ := hM u
  refine ⟨|B| + |D|, fun α g => ?_⟩
  rw [map_add (f := _), map_add (f := _)]
  refine (norm_add_le _ _).trans ?_
  have := (hB α g).trans (bnd_mono hC B α.degree g (le_max_left N M))
  have := (hD α g).trans (bnd_mono hC D α.degree g (le_max_right N M))
  rw [add_mul, add_mul]
  exact add_le_add ‹_› ‹_›

private theorem band_smul {C : ℝ} {φ : Sm E n} (h : Band C φ) (c : ℂ) : Band C (c • φ) := by
  refine { toUmg := (((umgOps E) n).2 φ h.toUmg).2.2.1 c, band := ?_ }
  obtain ⟨N, hN⟩ := h.band
  refine ⟨N, fun u => ?_⟩
  obtain ⟨B, hB⟩ := hN u
  refine ⟨‖c‖ * B, fun α g => ?_⟩
  rw [map_smul, map_smul]
  show ‖c • (uC E n u (zop (MvPolynomial.monomial α 1) φ)).1 g‖ ≤ _
  rw [norm_smul, mul_assoc, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg c)
  rw [← mul_assoc]
  exact hB α g

private theorem band_uC {C : ℝ} {φ : Sm E n} (h : Band C φ) (v : UC E n) : Band C (uC E n v φ) := by
  refine { toUmg := (((umgOps E) n).2 φ h.toUmg).2.2.2.1 v, band := ?_ }
  obtain ⟨N, hN⟩ := h.band
  refine ⟨N, fun u => ?_⟩
  obtain ⟨B, hB⟩ := hN (u * v)
  refine ⟨B, fun α g => ?_⟩
  have e : uC E n u (zop (MvPolynomial.monomial α 1) (uC E n v φ)) =
      uC E n (u * v) (zop (MvPolynomial.monomial α 1) φ) := by
    rw [← Module.End.mul_apply (zop _), zop_comm_uC, map_mul]
    rfl
  rw [e]
  exact hB α g

private theorem band_rt {C : ℝ} (hC : 0 ≤ C) {φ : Sm E n} (h : Band C φ) (g : GA E n) : Band C (rt E n g φ) := by
  refine { toUmg := (((umgOps E) n).2 φ h.toUmg).2.2.2.2.1 g, band := ?_ }
  obtain ⟨N, hN⟩ := h.band
  refine ⟨N, fun u => ?_⟩
  obtain ⟨u', hu⟩ := exists_comm g u
  obtain ⟨B, hB⟩ := hN u'
  have hc : 0 ≤ AutomorphicForm.heightConst E n * AutomorphicForm.height g :=
    mul_nonneg (zero_le_one.trans AutomorphicForm.one_le_heightConst) (AutomorphicForm.height_pos g).le
  refine ⟨|B| * (AutomorphicForm.heightConst E n * AutomorphicForm.height g) ^ N, fun α x => ?_⟩
  have e : uC E n u (zop (MvPolynomial.monomial α 1) (rt E n g φ)) =
      rt E n g (uC E n u' (zop (MvPolynomial.monomial α 1) φ)) := by
    rw [← Module.End.mul_apply (zop _), (zop_comm_rt _ g).eq, Module.End.mul_apply,
      ← Module.End.mul_apply (uC E n u), hu]
    rfl
  rw [e]
  show ‖(uC E n u' (zop (MvPolynomial.monomial α 1) φ)).1 (x * g)‖ ≤ _
  refine (hB α (x * g)).trans ((bnd_mono hC B α.degree (x * g) le_rfl).trans ?_)
  have h3 : 0 ≤ |B| * C ^ α.degree := mul_nonneg (abs_nonneg B) (pow_nonneg hC _)
  have h4 : AutomorphicForm.height (x * g) ≤
      AutomorphicForm.heightConst E n * AutomorphicForm.height g * AutomorphicForm.height x := by
    have := AutomorphicForm.height_mul_le x g
    nlinarith [this]
  calc |B| * C ^ α.degree * AutomorphicForm.height (x * g) ^ N
      ≤ |B| * C ^ α.degree * (AutomorphicForm.heightConst E n * AutomorphicForm.height g * AutomorphicForm.height x) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (AutomorphicForm.height_pos _).le h4 N) h3
    _ = _ := by rw [mul_pow]; ring

private theorem band_finsum {C : ℝ} (hC : 0 ≤ C) {Q : Type*} (f : Q → Module.End ℂ (Sm E n)) {φ : Sm E n}
    (hf : ∀ c, Band C (f c φ)) : Band C ((∑ᶠ c, f c) φ) := by
  classical
  by_cases h : (Function.support f).Finite
  · rw [finsum_eq_sum_of_support_subset (s := h.toFinset) _ (by simp), LinearMap.sum_apply]
    exact Finset.sum_induction _ (Band C) (fun _ _ => band_add hC) (band_zero C) fun c _ => hf c
  · rw [finsum_of_infinite_support h]
    exact band_zero C

private theorem band_hk {C : ℝ} (hC : 0 ≤ C) {φ : Sm E n} (h : Band C φ) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 E)) (j : ℕ) :
    Band C (hk n w j φ) := by
  unfold hk
  rw [LinearMap.smul_apply]
  refine band_smul (band_finsum hC _ fun c => ?_) _
  rw [LinearMap.smul_apply]
  exact band_smul (band_rt hC h _) _

end UpperTheory.ConvolutionTheory.BW

theorem UpperTheory.ConvolutionTheory.BW.bandOps :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.BandOps E := by
  intro E _ _ _ n C hC
  exact ⟨UpperTheory.ConvolutionTheory.BW.band_zero C, fun φ h => ⟨fun ψ h₂ => UpperTheory.ConvolutionTheory.BW.band_add hC h h₂, UpperTheory.ConvolutionTheory.BW.band_smul h,
    UpperTheory.ConvolutionTheory.BW.band_uC h, UpperTheory.ConvolutionTheory.BW.band_rt hC h, fun w j => UpperTheory.ConvolutionTheory.BW.band_hk hC h w j⟩⟩
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.NearBlo
section
open NumberField IsDedekindDomain Topology GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Cm
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.BW

private theorem indep {V I J : Type} [AddCommGroup V] [Module ℂ V] (T : I → Module.End ℂ V) (v : J → V) (lam : J → I → ℂ)
    (h0 : ∀ j, v j ≠ 0) (he : ∀ j i, T i (v j) = lam j i • v j) (hinj : Function.Injective lam) : LinearIndependent ℂ v :=
  _root_.UpperTheory.Reformulated.B.IndependenceEigenvectors.indep T v lam h0 he hinj

private theorem nss {G A : Type} [Group G] [NormedRing A] [NormedAlgebra ℝ A] (ρ : G →* A) (H : Subgroup G)
    (h : ∀ g ∈ H, ‖ρ g - 1‖ ≤ 1 / 2) : ∀ g ∈ H, ρ g = 1 :=
  _root_.UpperTheory.Reformulated.B.NoSmallSubgroupsNormedAlgebra.nss ρ H h

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
private theorem openKer {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G] {d : ℕ} (ρ : G →* Matrix (Fin d) (Fin d) ℂ) (hρ : Continuous ρ) :
    ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ u ∈ U, ρ u = 1 := by
  have hc : Continuous fun g => ‖ρ g - 1‖ := (hρ.sub continuous_const).norm
  have hn : {g | ‖ρ g - 1‖ < 1 / 2} ∈ 𝓝 (1 : G) := (isOpen_lt hc continuous_const).mem_nhds (by simp)
  obtain ⟨U, -, hU⟩ := exists_openSubgroup_isCompact_subset hn
  exact ⟨U, U.isOpen, nss ρ U fun g hg => (hU hg).le⟩

private theorem trInv {R : Type} [CommRing R] {r : ℕ} (X Y Z : Matrix (Fin r) (Fin r) R) :
    Matrix.trace ((X * Y - Y * X) * Z) = -Matrix.trace (Y * (X * Z - Z * X)) := by
  rw [sub_mul, mul_sub, Matrix.trace_sub, Matrix.trace_sub, neg_sub, mul_assoc X, Matrix.trace_mul_comm X, mul_assoc, mul_assoc]

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r : ℕ}

private theorem cenScalar (z : UC E r) (hz : z ∈ Subalgebra.center ℂ (UC E r)) :
    ∃ κ : ((E →+* ℂ) → Fin r → ℂ) → ℂ, Continuous κ ∧ ∀ (f : Sm E r) Λ, (∀ τ u, cap τ u f = (∏ i, (u + Λ τ i)) • f) →
      uC E r z f = κ Λ • f := by
  rw [center_UC] at hz
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨τ, u, rfl⟩ := hx
    exact ⟨fun Λ => ∏ i, (u + Λ τ i), by fun_prop, fun f Λ h => by rw [uC_capC, h]⟩
  | algebraMap c => exact ⟨fun _ => c, continuous_const, fun f Λ _ => by rw [AlgHom.commutes]; rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, h1⟩ := hx
    obtain ⟨b, hb, h2⟩ := hy
    exact ⟨a + b, ha.add hb, fun f Λ h => by rw [map_add (f := _), LinearMap.add_apply, h1 f Λ h, h2 f Λ h, Pi.add_apply, add_smul]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, h1⟩ := hx
    obtain ⟨b, hb, h2⟩ := hy
    exact ⟨a * b, ha.mul hb, fun f Λ h => by
      rw [map_mul, Module.End.mul_apply, h2 f Λ h, map_smul, h1 f Λ h, Pi.mul_apply, smul_smul, mul_comm]⟩

private theorem typeMap (ρ : Typ E r) : ∃ (X : Submodule ℂ (Matrix (Fin ρ.d) (Fin ρ.d) ℂ)) (τ : Representation ℂ (archCompact E r) X),
    ∀ φ : cuspForms E r, Killed ρ.ρ φ.1 → ∃ f : X →ₗ[ℂ] cuspForms E r,
      (∀ k x g, (f (τ k x)).1 g = (f x).1 (g * infEmb E r (k : archGroup E r))) ∧ φ ∈ LinearMap.range f := by
  let A : (KA E r →₀ ℂ) →ₗ[ℂ] Matrix (Fin ρ.d) (Fin ρ.d) ℂ := Finsupp.linearCombination ℂ ρ.ρ
  let ι : archCompact E r →* KA E r :=
    { toFun := fun k => ⟨infEmb E r (k : archGroup E r), k.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun _ _ => Subtype.ext (map_mul _ _ _) }
  have hA : ∀ (k : KA E r) x, A (x.mapDomain (k * ·)) = ρ.ρ k * A x := by
    intro k x
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => rw [Finsupp.mapDomain_add, map_add (f := _), map_add (f := _), hx, hy, mul_add]
    | single a c => simp [A]
  have hst : ∀ (k : KA E r), ∀ y ∈ LinearMap.range A, LinearMap.mulLeft ℂ (ρ.ρ k) y ∈ LinearMap.range A := by
    rintro k _ ⟨x, rfl⟩
    exact ⟨_, hA k x⟩
  refine ⟨LinearMap.range A,
    { toFun := fun k => (LinearMap.mulLeft ℂ (ρ.ρ (ι k))).restrict (hst (ι k))
      map_one' := LinearMap.ext fun y => Subtype.ext (by simp)
      map_mul' := fun k l => LinearMap.ext fun y => Subtype.ext (by simp [mul_assoc]) }, fun φ hφ => ?_⟩
  have hmem : ∀ k : KA E r, rightTranslate (k : GA E r) φ.1 ∈ cuspForms E r :=
    fun k => ⟨φ.2.1.rightTranslate_of_mem_maxCompact k.2, φ.2.2.translate _⟩
  let B : (KA E r →₀ ℂ) →ₗ[ℂ] cuspForms E r := Finsupp.linearCombination ℂ fun k => ⟨_, hmem k⟩
  have hB : ∀ x g, (B x).1 g = x.sum fun k c => c * φ.1 (g * (k : GA E r)) := by
    intro x g
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy =>
      rw [map_add (f := _), Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _), ← hx, ← hy]
      rfl
    | single a c =>
      rw [Finsupp.sum_single_index (zero_mul _)]
      simp only [B, Finsupp.linearCombination_single]
      rfl
  have hAB : ∀ x y, A x = A y → B x = B y := by
    intro x y h
    rw [← sub_eq_zero, ← map_sub] at h ⊢
    exact Subtype.ext (funext fun g => (hB _ g).trans (hφ _ h g))
  obtain ⟨s, hs⟩ := A.rangeRestrict.exists_rightInverse_of_surjective A.range_rangeRestrict
  have hs' : ∀ y : LinearMap.range A, A (s y) = y := fun y => congrArg Subtype.val (LinearMap.congr_fun hs y)
  refine ⟨B ∘ₗ s, fun k x g => ?_, ⟨⟨_, Finsupp.single 1 1, rfl⟩, ?_⟩⟩
  · have e1 : A (s ((LinearMap.mulLeft ℂ (ρ.ρ (ι k))).restrict (hst (ι k)) x)) = A ((s x).mapDomain (ι k * ·)) :=
      (hs' _).trans (((hA (ι k) (s x)).trans (congrArg (ρ.ρ (ι k) * ·) (hs' x))).symm)
    refine (congrArg (fun z : cuspForms E r => z.1 g) (hAB _ _ e1)).trans ?_
    change _ = (B (s x)).1 _
    rw [hB, hB,
      Finsupp.sum_mapDomain_index (h := fun (k' : KA E r) c => c * φ.1 (g * (k' : GA E r))) (fun _ => zero_mul _)
        (fun _ _ _ => add_mul _ _ _)]
    simp only [Subgroup.coe_mul, ← mul_assoc]
    rfl
  · rw [LinearMap.comp_apply, hAB _ (Finsupp.single 1 1) (hs' _)]
    refine Subtype.ext (funext fun g => ?_)
    rw [hB, Finsupp.sum_single_index (zero_mul _)]
    simp

attribute [local instance 100] LieRing.ofAssociativeRing in
private theorem finSpace (ρ : Typ E r) (B : ℝ) : ∃ W : Submodule ℂ (cuspForms E r), FiniteDimensional ℂ W ∧
    ∀ (S) (b : Blo S r), Killed ρ.ρ b.f.1 → (∀ τ i, ‖b.Λ τ i‖ ≤ B) → (⟨b.f.1, b.cusp⟩ : cuspForms E r) ∈ W := by
  obtain ⟨Bf, hB, hsym, d, e, ε, hε, horth, -⟩ := UpperTheory.exists_signed_basis_lieSubalgebra_exp_compact E r
  have hε2 : ∀ i, ε i * ε i = 1 := fun i => by rcases hε i with h | h <;> rw [h] <;> norm_num
  have hc : casimir e ε ∈ Subalgebra.center ℝ _ := casimir_mem_center hε2 horth hsym fun X Y Z => by
    rw [hB, hB, C.trForm, C.trForm, ← map_neg]
    congr 1
    exact trInv (R := mixedEmbedding.mixedSpace E) (X : ArchMatrix E r) (Y : ArchMatrix E r) (Z : ArchMatrix E r)
  have hc' : ((1 : ℂ) ⊗ₜ[ℝ] casimir e ε : UC E r) ∈ Subalgebra.center ℂ (UC E r) := by
    rw [Subalgebra.mem_center_iff]
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul c x =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_comm c, Subalgebra.mem_center_iff.1 hc x]
    | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  obtain ⟨κ, hκ, hκ'⟩ := cenScalar _ hc'
  obtain ⟨c, hcb⟩ := (isCompact_closedBall (0 : (E →+* ℂ) → Fin r → ℂ) (max B 0)).exists_bound_of_continuousOn hκ.continuousOn
  let ι : AdelicGLn.integralFiniteGL E r →* KA E r :=
    { toFun := fun k => ⟨finEmb E r k, finEmb_mem_maxCompact k.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun _ _ => Subtype.ext (map_mul _ _ _) }
  have hι : Continuous ι := (continuous_finEmb.comp continuous_subtype_val).subtype_mk _
  set_option synthInstance.maxHeartbeats 200000 in
    obtain ⟨U, hU, hUρ⟩ := openKer (ρ.ρ.comp ι) (ρ.cont.comp hι)
  obtain ⟨X, τ, hX⟩ := typeMap ρ
  refine ⟨_, C.nearFinite E r (Fin d) e ε hε2 (fun i j => by rw [← hB, horth]) U hU X τ c, fun S b hk hb =>
    Submodule.subset_span ⟨fun s x => ?_, fun u hu g => ?_, hX _ hk, (smEq E r b.f).2, κ b.Λ, ?_, ?_⟩⟩
  · have := b.cen (Real.log s) x
    simpa only [zt, Real.exp_log s.2] using this
  · have h1 := hk (Finsupp.single (ι u) 1 - Finsupp.single 1 1) (by
      change Finsupp.linearCombination ℂ ρ.ρ _ = 0
      rw [map_sub, Finsupp.linearCombination_single, Finsupp.linearCombination_single, map_one,
        show ρ.ρ (ι u) = 1 from hUρ u hu, sub_self]) g
    rw [Finsupp.sum_sub_index (fun _ _ _ => sub_mul _ _ _), Finsupp.sum_single_index (zero_mul _),
      Finsupp.sum_single_index (zero_mul _), one_mul, one_mul, sub_eq_zero] at h1
    rw [OneMemClass.coe_one, mul_one] at h1
    exact h1
  · have h1 := hcb b.Λ (by
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (le_max_right _ _)]
      intro τ
      rw [pi_norm_le_iff_of_nonneg (le_max_right _ _)]
      exact fun i => (hb τ i).trans (le_max_left _ _))
    exact (abs_le.1 ((Complex.abs_re_le_norm _).trans h1)).1
  · have h1 := hκ' b.f b.Λ b.inf
    rw [uC_tmul, one_smul] at h1
    have h2 := congrArg (smEq E r) h1
    rw [smEq_uTC, map_smul] at h2
    exact h2

end UpperTheory.ConvolutionTheory.BW

open UpperTheory.ConvolutionTheory.BW in
theorem UpperTheory.ConvolutionTheory.BW.nearBlo :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.NearBlo E := by
  classical
  intro E _ _ _ S r ρ B
  obtain ⟨W, hW, hmem⟩ := finSpace ρ B
  let I := ((E →+* ℂ) × ℂ) ⊕ ({w : Pl E // w ∉ S} × Fin (r + 1))
  let T : I → Module.End ℂ (Sm E r) := Sum.elim (fun p => cap p.1 p.2) fun p => hk r p.1.1 p.2
  let lam : (((E →+* ℂ) → Fin r → ℂ) × (Pl E → Multiset ℂˣ)) → I → ℂ := fun q =>
    Sum.elim (fun p => ∏ i, (p.2 + q.1 p.1 i)) fun p =>
      (qc p.1.1 ^ ((((p.2 : ℕ) : ℂ) * ((r : ℂ) - (p.2 : ℕ))) / 2))⁻¹ * GlobalTheory.LFun.satEig (Formalism.UG.qV E p.1.1) r (q.2 p.1.1) p.2
  set P := {p : ((E →+* ℂ) → Fin r → ℂ) × (Pl E → Multiset ℂˣ) | ∃ b : Blo S r, Killed ρ.ρ b.f.1 ∧ (∀ τ i, ‖b.Λ τ i‖ ≤ B) ∧
    p.1 = b.Λ ∧ ∀ w, p.2 w = if w ∈ S then 0 else b.sat w} with hP
  have heig : ∀ (q) (b : Blo S r), q.1 = b.Λ → (∀ w, q.2 w = if w ∈ S then 0 else b.sat w) → ∀ i, T i b.f = lam q i • b.f := by
    rintro q b h1 h2 (⟨τ, u⟩ | ⟨⟨w, hw⟩, j⟩)
    · change cap τ u b.f = (∏ i, (u + q.1 τ i)) • b.f
      rw [h1, b.inf]
    · change hk r w j b.f = (_ * GlobalTheory.LFun.satEig _ r (q.2 w) j) • b.f
      rw [(hkOps E r w j).1, (b.isSat w hw).2.2.2 _ (GlobalTheory.LFun.exists_isUnifV w).choose_spec j (Nat.lt_succ_iff.1 j.2), smul_smul,
        h2, if_neg hw]
  have himg : (lam '' P).Finite := by
    have hex : ∀ x : lam '' P, ∃ b : Blo S r, Killed ρ.ρ b.f.1 ∧ (∀ τ i, ‖b.Λ τ i‖ ≤ B) ∧ ∀ i, T i b.f = x.1 i • b.f := by
      rintro ⟨_, q, ⟨b, h1, h2, h3, h4⟩, rfl⟩
      exact ⟨b, h1, h2, heig q b h3 h4⟩
    choose b h1 h2 h3 using hex
    have li := indep T (fun x => (b x).f) (fun x : lam '' P => x.1) (fun x => (b x).ne) h3 Subtype.val_injective
    have li2 : LinearIndependent ℂ fun x : lam '' P => (⟨⟨(b x).f.1, (b x).cusp⟩, hmem S (b x) (h1 x) (h2 x)⟩ : W) :=
      LinearIndependent.of_comp ((cuspForms E r).subtype ∘ₗ W.subtype) (li.map' (Sm E r).subtype (Submodule.ker_subtype _))
    exact Set.finite_coe_iff.1 li2.finite
  refine Set.Finite.of_finite_fibers lam himg ?_
  rintro _ ⟨q, ⟨b, -, -, h3, h4⟩, rfl⟩
  refine ((Set.Finite.pi' fun τ => Set.Finite.pi' fun _ : Fin r => Set.finite_range (q.1 τ)).prod
    (Set.finite_singleton q.2)).subset ?_
  rintro q' ⟨⟨b', -, -, h3', h4'⟩, he⟩
  have he : lam q' = lam q := he
  refine ⟨fun τ i => ?_, funext fun w => ?_⟩
  · have h : ∏ k, (-q'.1 τ i + q'.1 τ k) = ∏ k, (-q'.1 τ i + q.1 τ k) := congrFun he (Sum.inl (τ, -q'.1 τ i))
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (neg_add_cancel _), eq_comm, Finset.prod_eq_zero_iff] at h
    obtain ⟨k, -, hk⟩ := h
    exact ⟨k, (neg_add_eq_zero.1 hk).symm⟩
  · by_cases hw : w ∈ S
    · rw [h4, h4', if_pos hw, if_pos hw]
    · have c1 : (q'.2 w).card = r := by rw [h4', if_neg hw]; exact (b'.isSat w hw).2.2.1
      have c2 : (q.2 w).card = r := by rw [h4, if_neg hw]; exact (b.isSat w hw).2.2.1
      have hq : Formalism.UG.qV E w ≠ 0 := GlobalTheory.LFun.qV_ne_zero w
      refine GlobalTheory.LFun.eq_of_satEig_eq hq c1 c2 fun j hj => ?_
      have h := congrFun he (Sum.inr (⟨w, hw⟩, ⟨j, Nat.lt_succ_iff.2 hj⟩))
      exact mul_left_cancel₀ (inv_ne_zero (Complex.cpow_ne_zero_iff.2 (Or.inl (Nat.cast_ne_zero.2 hq)))) h
end

