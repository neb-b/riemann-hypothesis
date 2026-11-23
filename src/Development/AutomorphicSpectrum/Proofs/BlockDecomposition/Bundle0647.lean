module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0268
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EventuallySmall
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0554
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0605
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0632
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0624
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0044
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0346
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmRep

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RationalGroupLeOfGeneratorsMem
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.RatGen

open GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.Gen

variable {D : D7} {n : ℕ}

abbrev rm (x : Matrix (Fin n) (Fin n) D.host.E) : Mx D n n := x.map (incA D)

theorem rm_mul (x y : Matrix (Fin n) (Fin n) D.host.E) : rm (x * y) = rm x * rm y :=
  Matrix.map_mul

theorem rm_add (x y : Matrix (Fin n) (Fin n) D.host.E) : rm (x + y) = rm x + rm y :=
  Matrix.map_add _ (map_add _) x y

theorem rm_neg (x : Matrix (Fin n) (Fin n) D.host.E) : rm (-x) = -rm x := by
  ext i j; simp [rm]

theorem rm_one : rm (1 : Matrix (Fin n) (Fin n) D.host.E) = 1 := by
  simp [rm]

theorem blockMatrix_map (a b c d : Matrix (Fin n) (Fin n) D.host.E) :
    (blk4 a b c d).map (incA D) = blk4 (rm a) (rm b) (rm c) (rm d) := by
  ext i j
  simp only [blk4, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> rfl

def ru (u : GL (Fin n) D.host.E) : GL (Fin n) (AE D) := Units.map (incA D).mapMatrix.toMonoidHom u

theorem ru_val (u : GL (Fin n) D.host.E) : (ru u).1 = rm u.1 := rfl

theorem ru_inv_val (u : GL (Fin n) D.host.E) : ((ru u)⁻¹).1 = rm (u⁻¹).1 := rfl

variable {S : Subgroup (G D n)}
  (hm : ∀ (g : G D n) (a : GL (Fin n) D.host.E), mat g = blk4 (a.1.map (incA D)) 0 0 (adj ((a⁻¹).1.map (incA D))) → g ∈ S)
  (hn : ∀ (g : G D n) (b : Matrix (Fin n) (Fin n) D.host.E), mat g = blk4 1 (b.map (incA D)) 0 1 → g ∈ S)
  (hw : ∀ g : G D n, mat g = blk4 0 1 (-1) 0 → g ∈ S)

include hm hn in
theorem mem_of_upper {g : G D n} {a b d : Matrix (Fin n) (Fin n) D.host.E} (hg : mat g = blk4 (rm a) (rm b) 0 (rm d))
    (ha : IsUnit a) : g ∈ S := by
  obtain ⟨u, rfl⟩ := ha
  obtain ⟨m, hmm⟩ := exists_levi (D := D) (n := n) (ru u)⁻¹
  have hmm' : mat m = blk4 (rm (u⁻¹).1) 0 0 (adj (rm u.1)) := by
    rw [hmm, ru_inv_val, inv_inv, ru_val]
  have h1 : (adj (rm u.1) : Mx D n n) * rm d = 1 := by simpa using (rel hg).2.1
  have hmS : m ∈ S := hm m u⁻¹ (by rw [hmm', inv_inv])
  rw [← S.mul_mem_cancel_left hmS]
  refine hn _ ((u⁻¹).1 * b) ?_
  have h2 : rm (u⁻¹).1 * rm u.1 = 1 := by
    rw [← rm_mul, Units.inv_mul, rm_one]
  rw [mat_mul, hmm', hg, submatrix_fromBlocks_mul]
  simp only [h2, mul_zero, zero_mul, add_zero, zero_add, h1]
  change _ = blk4 1 (rm _) 0 1
  rw [rm_mul]

include hm hn hw in
theorem mem_of_lower {g : G D n} {a c d : Matrix (Fin n) (Fin n) D.host.E} (hg : mat g = blk4 (rm a) 0 (rm c) (rm d))
    (hd : IsUnit d) : g ∈ S := by
  obtain ⟨w, hww⟩ := exists_weyl (D := D) (n := n)
  rw [← S.mul_mem_cancel_left (hw w hww), ← S.mul_mem_cancel_right (hw w hww)]
  refine mem_of_upper hm hn (a := -d) (b := c) (d := -a) ?_ hd.neg
  rw [mat_mul, mat_mul, hww, hg, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul, rm_neg, rm_neg]
  simp

include hm hn hw in
theorem mem_of_isUnit {g : G D n} {a b c d : Matrix (Fin n) (Fin n) D.host.E}
    (hg : mat g = blk4 (rm a) (rm b) (rm c) (rm d)) (hd : IsUnit d) : g ∈ S := by
  obtain ⟨u, rfl⟩ := hd
  have h1 : (adj (rm u.1) : Mx D n n) * rm b = adj (rm b) * rm u.1 := neg_add_eq_zero.1 (rel hg).2.2
  have h0 : rm u.1 * rm (u⁻¹).1 = 1 := by rw [← rm_mul, Units.mul_inv, rm_one]
  have h0' : rm (u⁻¹).1 * rm u.1 = 1 := by rw [← rm_mul, Units.inv_mul, rm_one]
  have h2 : (adj (rm (u⁻¹).1) : Mx D n n) * adj (rm u.1) = 1 := by rw [← adj_mul, h0, adj_one]
  have h3 : (adj (-(rm b * rm (u⁻¹).1)) : Mx D n n) = -(rm b * rm (u⁻¹).1) := by
    rw [adj_neg, adj_mul]
    congr 1
    calc (adj (rm (u⁻¹).1) : Mx D n n) * adj (rm b) = adj (rm (u⁻¹).1) * (adj (rm b) * rm u.1) * rm (u⁻¹).1 := by
          rw [mul_assoc, mul_assoc, h0, mul_one]
      _ = rm b * rm (u⁻¹).1 := by rw [← h1, ← mul_assoc, h2, one_mul]
  obtain ⟨x, hx⟩ := (exists_unip _).2 h3
  have hxS : x ∈ S := hn x (-(b * (u⁻¹).1)) (by rw [hx]; change _ = blk4 1 (rm _) 0 1; rw [rm_neg, rm_mul])
  rw [← S.mul_mem_cancel_left hxS]
  refine mem_of_lower hm hn hw (a := a + -(b * (u⁻¹).1) * c) (c := c) (d := u.1) ?_ u.isUnit
  rw [mat_mul, hx, hg, submatrix_fromBlocks_mul, rm_add, rm_mul, rm_neg, rm_mul]
  simp only [one_mul, zero_mul, zero_add, neg_mul, mul_assoc, h0', mul_one, add_neg_cancel]

theorem adj_rm {x : Matrix (Fin n) (Fin n) D.host.E} (hx : ∀ i j, (D.sp.cm.sig : D.host.E →+* D.host.E) (x i j) = x j i) :
    adj (rm x : Mx D n n) = rm x := by
  ext i j
  simp only [adj, Matrix.transpose_apply, Matrix.map_apply]
  rw [GlobalTheory.DualPairCheck.cA_incA]
  exact congrArg _ (hx j i)

theorem exists_herm_isUnit (c d p q : Matrix (Fin n) (Fin n) D.host.E) (h : c * p + d * q = 1) :
    ∃ x : Matrix (Fin n) (Fin n) D.host.E, (∀ i j, (D.sp.cm.sig : D.host.E →+* D.host.E) (x i j) = x j i) ∧
      IsUnit (c * x + d) := by
  obtain ⟨x, hx, hu⟩ := GlobalTheory.HermTransversal.exists_herm_notMem (D.sp.cm.sig : D.host.E →+* D.host.E) D.host.xi0
    (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D) (GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg D) (RingHom.id _) (D.sp.cm.sig : D.host.E →+* D.host.E)
    (fun _ => rfl) c d p q h ⊥ Ideal.bot_isMaximal
  refine ⟨x, hx, ?_⟩
  have e : x.map (RingHom.id D.host.E) = x := by ext i j; rfl
  rw [e] at hu
  refine (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 fun h0 => hu ?_)
  rw [h0, zero_mul]
  exact Ideal.zero_mem _

end GlobalTheory.CompanionTheory.RatGen

namespace GlobalTheory.CompanionTheory

theorem RatGen.GF_le_of_levi_unip_weyl : ∀ (D : D7) (n : ℕ) (S : Subgroup (G D n)),
  (∀ (g : G D n) (a : GL (Fin n) D.host.E), mat g = blk4 (a.1.map (incA D)) 0 0 (adj ((a⁻¹).1.map (incA D))) → g ∈ S) →
  (∀ (g : G D n) (b : Matrix (Fin n) (Fin n) D.host.E), mat g = blk4 1 (b.map (incA D)) 0 1 → g ∈ S) →
  (∀ g : G D n, mat g = blk4 0 1 (-1) 0 → g ∈ S) → GF D n ≤ S := by
  intro D n S hm hn hw γ hγ
  have hrat : ∀ {γ : G D n}, γ ∈ GF D n →
      ∃ x : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E, mat γ = x.map (incA D) := by
    intro γ h
    obtain ⟨x, -, hx⟩ := h
    exact ⟨x.1, (congrArg Units.val hx).symm⟩
  obtain ⟨M, hM⟩ := hrat hγ
  obtain ⟨M', hM'⟩ := hrat ((GF D n).inv_mem hγ)
  obtain ⟨a, b, c, d, rfl⟩ := GlobalTheory.StdUnn.Gen.exists_blockMatrixTwoByTwoFin_eq M
  obtain ⟨p', p, q', q, rfl⟩ := GlobalTheory.StdUnn.Gen.exists_blockMatrixTwoByTwoFin_eq M'
  rw [RatGen.blockMatrix_map] at hM hM'
  have h1 : mat γ * mat γ⁻¹ = 1 := by rw [← GlobalTheory.StdUnn.Gen.mat_mul, mul_inv_cancel]; rfl
  rw [hM, hM', Model.submatrix_fromBlocks_mul, ← Model.block_matrix_one] at h1
  have h2 : RatGen.rm (c * p + d * q) = RatGen.rm (1 : Matrix (Fin n) (Fin n) D.host.E) := by
    rw [RatGen.rm_add, RatGen.rm_mul, RatGen.rm_mul, RatGen.rm_one]
    exact (Model.blockMatrixTwoByTwoFin_injective h1).2.2.2
  have h3 : c * p + d * q = 1 := Matrix.map_injective GlobalTheory.MixModel.incA_injective h2
  obtain ⟨x, hx, hu⟩ := RatGen.exists_herm_isUnit c d p q h3
  obtain ⟨y, hy⟩ := (Model.exists_unip (RatGen.rm x)).2 (RatGen.adj_rm hx)
  rw [← S.mul_mem_cancel_right (hn y x hy)]
  refine RatGen.mem_of_isUnit hm hn hw (a := a) (b := a * x + b) (c := c) (d := c * x + d) ?_ hu
  rw [GlobalTheory.StdUnn.Gen.mat_mul, hM, hy, Model.submatrix_fromBlocks_mul, RatGen.rm_add, RatGen.rm_add, RatGen.rm_mul, RatGen.rm_mul]
  simp only [mul_one, mul_zero, add_zero]

end GlobalTheory.CompanionTheory
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResATranslate
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ResMu

open Set GlobalTheory.Eis

variable {D : D7} {p : ℕ}

theorem law_ratInv {n : ℕ} {z : ℂ} {s : G D n → ℂ} (hs : IsLaw 1 z s) : LeftInv (P D n ⊓ GF D n) s := fun γ hγ g => by
  obtain ⟨a, ha⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_blkA hγ.1
  obtain ⟨u, hu⟩ := GlobalTheory.StdUnn.LeftInvSect.det_rat hγ.2 a ha
  have h1 : absA D (Units.map (incA D).toMonoidHom u) = 1 := absE_inclR u
  rw [hs γ hγ.1 a ha g, hu, h1]
  simp

theorem rho_right {f : G D p → ℂ} (hf : IsRho f) (x : G D p) : IsRho fun g => f (g * x) :=
  ⟨hf.1.comp (continuous_id.mul continuous_const), law_right hf.2 x⟩

theorem fam_law_real {H : G D p → ℝ≥0} (hH : IsHt H) {f : G D p → ℂ} (hf : IsRho f) (σ : ℝ) :
    IsLaw 1 (σ : ℂ) (fam H f ((p : ℂ) / 2) (σ : ℂ)) := fam_law hH hf.2 σ

theorem fam_cont_at {H : G D p → ℝ≥0} (hH : IsHt H) {f : G D p → ℂ} (hf : Continuous f) (s₁ : ℂ) (σ : ℝ) :
    Continuous (fam H f s₁ (σ : ℂ)) :=
  (fam_cont hH hf s₁).comp (f := fun g : G D p => ((σ, g) : ℝ × G D p)) (by fun_prop)

theorem fam_at (H : G D p → ℝ≥0) (f : G D p → ℂ) : fam H f ((p : ℂ) / 2) (((p : ℝ) / 2 : ℝ) : ℂ) = f := by
  funext g
  have : ((((p : ℝ) / 2 : ℝ) : ℂ)) - (p : ℂ) / 2 = 0 := by push_cast; ring
  simp [fam, this]

theorem res_leftInv {H : G D p → ℝ≥0} (hH : IsHt H) {f : G D p → ℂ} (hf : IsRho f) (σ : ℝ) :
    LeftInv (GF D p) (res H f σ) := fun γ hγ g => by
  simp only [res, eisS]
  rw [leftInv_cosetSum (law_ratInv (fam_law_real hH hf σ)) γ hγ g]

theorem eis_right (s : G D p → ℂ) (x : G D p) : eisS s x = eisS (fun g => s (g * x)) 1 := by
  simp only [eisS]
  rw [cosetSum_mul_right, one_mul]

theorem res_equi (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f : G D p → ℂ} (hf : IsRho f) (x : G D p) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x' in 𝓝 x, ∀ σ ∈ Ioc ((p : ℝ) / 2) (p / 2 + 1), ‖res H f σ x' - res H f σ x‖ ≤ ε := by
  obtain ⟨B, hB0, hB⟩ := eis_bound hS hp hH (isCompact_singleton (x := (1 : G D p)))
  have hK : IsCompact (Icc ((p : ℝ) / 2) (p / 2 + 1) ×ˢ C) := isCompact_Icc.prod hC
  have hε' : 0 < ε / (2 * (B + 1)) := by positivity
  have hfc := fam_cont hH hf.1 ((p : ℂ) / 2)
  have hev : ∀ᶠ x' in 𝓝 x, ∀ y ∈ Icc ((p : ℝ) / 2) (p / 2 + 1) ×ˢ C,
      ‖fam H f ((p : ℂ) / 2) (y.1 : ℂ) (y.2 * x') - fam H f ((p : ℂ) / 2) (y.1 : ℂ) (y.2 * x)‖ <
        ε / (2 * (B + 1)) * (H y.2 : ℝ) ^ (y.1 + p / 2) := by
    refine hK.eventually_forall_of_forall_eventually fun y _ => ?_
    have c1 : Continuous fun u : G D p × (ℝ × G D p) => fam H f ((p : ℂ) / 2) (u.2.1 : ℂ) (u.2.2 * u.1) :=
      hfc.comp (f := fun u : G D p × (ℝ × G D p) => ((u.2.1, u.2.2 * u.1) : ℝ × G D p)) (by fun_prop)
    have c2 : Continuous fun u : G D p × (ℝ × G D p) => fam H f ((p : ℂ) / 2) (u.2.1 : ℂ) (u.2.2 * x) :=
      hfc.comp (f := fun u : G D p × (ℝ × G D p) => ((u.2.1, u.2.2 * x) : ℝ × G D p)) (by fun_prop)
    have c3 : Continuous fun u : G D p × (ℝ × G D p) => ε / (2 * (B + 1)) * (H u.2.2 : ℝ) ^ (u.2.1 + p / 2) :=
      continuous_const.mul ((NNReal.continuous_coe.comp (hH.1.comp (continuous_snd.comp continuous_snd))).rpow
        ((continuous_fst.comp continuous_snd).add continuous_const) fun u => Or.inl (NNReal.coe_pos.2 (hH.2.1 _)).ne')
    refine ((c1.sub c2).norm.continuousAt.eventually_lt c3.continuousAt ?_)
    simp only [Pi.sub_apply, sub_self, norm_zero]
    exact mul_pos hε' (Real.rpow_pos_of_pos (NNReal.coe_pos.2 (hH.2.1 _)) _)
  filter_upwards [hev] with x' hx' σ hσ
  have hI' : σ ∈ Icc ((p : ℝ) / 2) (p / 2 + 1) := ⟨hσ.1.le, hσ.2⟩
  have hl := fam_law_real hH hf σ
  have hc := fam_cont_at hH hf.1 ((p : ℂ) / 2) σ
  have hct : ∀ y : G D p, Continuous fun g => fam H f ((p : ℂ) / 2) (σ : ℂ) (g * y) := fun y =>
    hc.comp (continuous_id.mul continuous_const)
  have hb := law_bound hH hcov (law_sub (law_right hl x') (law_right hl x)) (δ := ε / (2 * (B + 1))) (fun c hc =>
    (hx' (σ, c) ⟨hI', hc⟩).le)
  have hf' := (hB σ hσ 1 rfl _ _ hb).2
  rw [eis_sub (conv_of_section hS hp hH hC hcov hσ (hct x') (law_right hl x') 1)
    (conv_of_section hS hp hH hC hcov hσ (hct x) (law_right hl x) 1), ← eis_right, ← eis_right] at hf'
  have e : res H f σ x' - res H f σ x =
      ((σ - p / 2 : ℝ) : ℂ) * (eisS (fam H f ((p : ℂ) / 2) (σ : ℂ)) x' - eisS (fam H f ((p : ℂ) / 2) (σ : ℂ)) x) := by
    simp only [res]; ring
  rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith [hσ.1])]
  have : ε / (2 * (B + 1)) * B ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  linarith

theorem res_cont (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f : G D p → ℂ} (hf : IsRho f) {σ : ℝ}
    (hσ : σ ∈ Ioc ((p : ℝ) / 2) (p / 2 + 1)) : Continuous (res H f σ) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [res_equi hS hp hH hC hcov hf x (half_pos hε)] with x' hx'
  rw [dist_eq_norm]
  linarith [hx' σ hσ]

theorem resA_near (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f : G D p → ℂ} (hf : IsRho f) (x : G D p) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x' in 𝓝 x, ‖resA H f x' - resA H f x‖ ≤ ε := by
  filter_upwards [res_equi hS hp hH hC hcov hf x hε] with x' hx'
  have h1 := ((res_tendsto hS hp hH hC hcov hf x').sub (res_tendsto hS hp hH hC hcov hf x)).norm
  refine le_of_tendsto h1 ?_
  refine ufil_le p ?_
  filter_upwards [ev_Ioc p] with σ hσ using hx' σ hσ

theorem resA_cont (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f : G D p → ℂ} (hf : IsRho f) : Continuous (resA H f) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [resA_near hS hp hH hC hcov hf x (half_pos hε)] with x' hx'
  rw [dist_eq_norm]
  linarith

theorem resA_leftInv (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f : G D p → ℂ} (hf : IsRho f) : LeftInv (GF D p) (resA H f) := fun γ hγ g => by
  refine tendsto_nhds_unique (res_tendsto hS hp hH hC hcov hf (γ * g)) ?_
  have := res_tendsto hS hp hH hC hcov hf g
  refine this.congr fun σ => ?_
  rw [res_leftInv hH hf σ γ hγ g]

theorem resA_unif (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f : G D p → ℂ} (hf : IsRho f) {C' : Set (G D p)} (hC' : IsCompact C')
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ σ in ((ufil p : Ultrafilter ℝ) : Filter ℝ), ∀ c ∈ C', ‖res H f σ c - resA H f c‖ ≤ ε := by
  refine hC'.induction_on (p := fun S => ∀ᶠ σ in ((ufil p : Ultrafilter ℝ) : Filter ℝ), ∀ c ∈ S, ‖res H f σ c - resA H f c‖ ≤ ε)
    (by simp) (fun s t hst h => h.mono fun σ hσ c hc => hσ c (hst hc))
    (fun s t hs ht => by
      filter_upwards [hs, ht] with σ h1 h2 c hc
      exact hc.elim (h1 c) (h2 c)) fun x _ => ?_
  have hε3 : 0 < ε / 3 := by positivity
  refine ⟨_, mem_nhdsWithin_of_mem_nhds ((res_equi hS hp hH hC hcov hf x hε3).and (resA_near hS hp hH hC hcov hf x hε3)), ?_⟩
  have h1 : ∀ᶠ σ in ((ufil p : Ultrafilter ℝ) : Filter ℝ), ‖res H f σ x - resA H f x‖ < ε / 3 := by
    have := (res_tendsto hS hp hH hC hcov hf x)
    rw [Metric.tendsto_nhds] at this
    filter_upwards [this _ hε3] with σ hσ
    rwa [dist_eq_norm] at hσ
  filter_upwards [h1, ufil_le p (ev_Ioc p)] with σ hσ hI c hc
  have a1 := hc.1 σ hI
  have a2 := hc.2
  calc ‖res H f σ c - resA H f c‖ = ‖(res H f σ c - res H f σ x) + (res H f σ x - resA H f x) - (resA H f c - resA H f x)‖ := by
        congr 1; ring
    _ ≤ ‖res H f σ c - res H f σ x‖ + ‖res H f σ x - resA H f x‖ + ‖resA H f c - resA H f x‖ :=
        (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ ε := by linarith

theorem resA_translate (hS : SphBound) (hp : 1 ≤ p) {H : G D p → ℝ≥0} (hH : IsHt H) {C : Set (G D p)} (hC : IsCompact C)
    (hcov : ∀ g, ∃ q ∈ P D p, ∃ c ∈ C, g = q * c) {f : G D p → ℂ} (hf : IsRho f) (x : G D p) :
    resA H f x = resA H (fun g => f (g * x)) 1 := by
  have hfx := rho_right hf x
  have hd := tendsto_diff hS hp hH hC hcov
    (S := fun σ g => fam H f ((p : ℂ) / 2) (σ : ℂ) (g * x)) (S' := fun σ => fam H (fun g => f (g * x)) ((p : ℂ) / 2) (σ : ℂ))
    ((fam_cont hH hf.1 _).comp (f := fun u : ℝ × G D p => ((u.1, u.2 * x) : ℝ × G D p)) (by fun_prop)).continuousOn
    (fam_cont hH hfx.1 _).continuousOn
    (fun σ _ => law_right (fam_law_real hH hf σ) x) (fun σ _ => fam_law_real hH hfx σ)
    (by simp only [fam_at])
  have h1 := (hd.mono_left (ufil_le p)).add (res_tendsto hS hp hH hC hcov hfx 1)
  rw [zero_add] at h1
  refine tendsto_nhds_unique (res_tendsto hS hp hH hC hcov hf x) (h1.congr fun σ => ?_)
  simp only [res]
  rw [eis_right (fam H f ((p : ℂ) / 2) (σ : ℂ)) x]
  ring

end GlobalTheory.CompanionTheory.ResMu
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentProductJacquetShuffleCount
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.FineProd

theorem sum_map_filter {β : Type*} (p : β → Prop) [DecidablePred p] (f : β → ℕ) (l : List β) :
    ((l.filter fun a => decide (p a)).map f).sum = (l.map fun j => if p j then f j else 0).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases hp : p a
    · simp [List.filter_cons, hp, ih]
    · simp [List.filter_cons, hp, ih]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem deg_sub {h : ℕ} (W : List (IrrGL (k := k))) (c : Fin W.length → Fin h) (i : Fin h) :
    ((sub W c i).map Sigma.fst).sum = ∑ j, if c j = i then (W.get j).1 else 0 := by
  show ((List.map W.get (List.filter (fun p => decide (c p = i)) (List.finRange W.length))).map
    Sigma.fst).sum = _
  rw [List.map_map, Fin.sum_univ_def]
  exact sum_map_filter (fun p => c p = i) (fun p => (W.get p).1) (List.finRange W.length)

theorem deg_decWord (Γ : Segment k) : ((decWord Γ).map Sigma.fst).sum = Γ.deg := by
  have h : ∀ a, (Γ.term a).1 = Γ.d := fun a => rfl
  show ((List.ofFn Γ.term).reverse.map Sigma.fst).sum = Γ.len * Γ.d
  rw [List.map_reverse, List.sum_reverse, List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_def, h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

def colourMat {h : ℕ} (W : List (IrrGL (k := k))) (c : Fin W.length → Fin h) (i : Fin h) (j : Fin W.length) : ℕ :=
  if c j = i then (W.get j).1 else 0

theorem sum_colourMat {h : ℕ} (W : List (IrrGL (k := k))) (c : Fin W.length → Fin h) (j : Fin W.length) :
    ∑ i, colourMat W c i j = (W.get j).1 := by
  simp [colourMat]

end GlobalTheory.CompanionTheory.FineProd


open GlobalTheory.CompanionTheory.FineProd in
theorem GlobalTheory.CompanionTheory.FineProd.jmL_prodIrr : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → LSegJacquet k → ∀ {h N : ℕ} (Γ : Fin h → Segment k) (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), (∀ i, IsLSeg (Γ i) (x i).rep) → ∀ W : List (IrrGL (k := k)), (∀ w ∈ W, w.IsCusp) → jmL W (prodIrr x hd) = (shuffleCount W (fun i => decWord (Γ i)) : ℕ∞) := by
  intro k _ _ _ _ hA hJ h N Γ x hd hΓ W hW
  classical
  have hΓd : ∀ i, ((decWord (Γ i)).map Sigma.fst).sum = (x i).1 := fun i =>
    (deg_decWord _).trans (hΓ i).deg_eq
  let S : Finset (Fin W.length → Fin h) := Finset.univ.filter fun c => ∀ i, sub W c i = decWord (Γ i)
  have hcount : shuffleCount W (fun i => decWord (Γ i)) = S.card := by
    unfold shuffleCount
    congr
  have hrowS : ∀ c ∈ S, ∀ i, ∑ j, colourMat W c i j = (x i).1 := fun c hc i => by
    have h1 := (Finset.mem_filter.1 hc).2 i
    have h2 := deg_sub W c i
    rw [h1, hΓd] at h2
    exact h2.symm
  have hSdeg : ∀ c ∈ S, ∑ a, (W.get a).1 = N := fun c hc => by
    rw [← hd, ← Finset.sum_congr rfl fun i _ => hrowS c hc i, Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => (sum_colourMat W c j).symm
  have hpos : ∀ j, 0 < (W.get j).1 := fun j => (hW _ (List.get_mem _ _)).1
  rw [hcount]
  by_cases hWd : ∑ a, (W.get a).1 = N
  swap
  · have hSe : S = ∅ := Finset.eq_empty_of_forall_notMem fun c hc => hWd (hSdeg c hc)
    rw [hSe, jmL, dite_eq_right hWd]
    simp
  let m : Fin h → Type := fun i => Fin (x i).1
  let m' : Fin W.length → Type := fun j => Fin (W.get j).1
  haveI : Fintype (SizeMatrix m m') := Fintype.ofFinite _
  have hr : ∀ (b : SizeMatrix m m') i, ∑ j, b.1 i j = (x i).1 := fun b i => by
    simpa [m] using b.2.1 i
  have hc : ∀ (b : SizeMatrix m m') j, ∑ i, b.1 i j = (W.get j).1 := fun b j => by
    simpa [m'] using b.2.2 j
  have hτ : (piTensor fun j => (W.get j).rep).IsIrreducible :=
    _root_.GlobalTheory.ExtTensorIrr.piTensor_isIrreducible GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k _ _ fun j => (W.get j).2.rep
  have key := ((GlobalTheory.CompanionTheory.GeoLink.geometricLemma k).1).jhMult_eq (m := m) (m' := m')
    (stdBlocks (fun a => (x a).1) hd) (stdBlocks (fun a => (W.get a).1) hWd)
    (isSmooth_piTensor fun i => (x i).2.rep.smooth)
    (fun b i => stdBlocks (b.1 i) (hr b i)) (fun b j => stdBlocks (fun i => b.1 i j) (hc b j)) hτ
  have hF : ∀ b : SizeMatrix m m', jhMult (piTensor fun j => (W.get j).rep)
      (cellFunctor (c := fun i j => Fin (b.1 i j)) (fun i => stdBlocks (b.1 i) (hr b i))
        (fun j => stdBlocks (fun i => b.1 i j) (hc b j)) (piTensor fun i => (x i).rep)) =
      if ∃ c ∈ S, b.1 = colourMat W c then 1 else 0 := by
    intro b
    split_ifs with hb
    · obtain ⟨c, hcS, hbc⟩ := hb
      rw [GlobalTheory.T.cuspidal_cell_multiplicity_of_colouring x W b.1 (hr b) (hc b) c (fun i j => by rw [hbc]; rfl)]
      refine Finset.prod_eq_one fun i _ => ?_
      refine ((GlobalTheory.T.segment_rep_jacquet_word_multiplicity hA hJ (Γ i) (x i).rep (hΓ i) (sub W c i) fun w hw => ?_).1
        ((Finset.mem_filter.1 hcS).2 i))
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 hw
      exact hW _ (List.get_mem _ _)
    · by_cases hm : ∃ (j : Fin W.length) (i i' : Fin h), i ≠ i' ∧ b.1 i j ≠ 0 ∧ b.1 i' j ≠ 0
      · obtain ⟨j, i, i', hii, h1, h2⟩ := hm
        exact GlobalTheory.T.cuspidal_cell_multiplicity_zero_of_split_column hA x (fun j => W.get j) (fun j => hW _ (List.get_mem _ _)) b.1 (hr b) (hc b) j i i' hii h1 h2
      · push_neg at hm
        have hex : ∀ j, ∃ i, b.1 i j ≠ 0 := fun j => by
          by_contra hne
          push_neg at hne
          have := hc b j
          rw [Finset.sum_eq_zero fun i _ => hne i] at this
          exact (hpos j).ne this
        choose c hcj using hex
        have hzero : ∀ i j, c j ≠ i → b.1 i j = 0 := fun i j hij => by
          by_contra hne
          exact hne (hm j (c j) i hij (hcj j))
        have hbc : b.1 = colourMat W c := by
          funext i j
          unfold colourMat
          split_ifs with hij
          · subst hij
            rw [← hc b j]
            exact (Finset.sum_eq_single (c j) (fun i _ hi => hzero i j (Ne.symm hi)) (by simp)).symm
          · exact hzero i j hij
        have hcS : c ∉ S := fun hcS => hb ⟨c, hcS, hbc⟩
        have hex2 : ∃ i, sub W c i ≠ decWord (Γ i) := by
          by_contra hne
          push_neg at hne
          exact hcS (Finset.mem_filter.2 ⟨Finset.mem_univ _, hne⟩)
        obtain ⟨i, hi⟩ := hex2
        rw [GlobalTheory.T.cuspidal_cell_multiplicity_of_colouring x W b.1 (hr b) (hc b) c (fun i j => by rw [hbc]; rfl)]
        refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
        refine (GlobalTheory.T.segment_rep_jacquet_word_multiplicity hA hJ (Γ i) (x i).rep (hΓ i) (sub W c i) (fun w hw => ?_)).2 hi
        obtain ⟨p, -, rfl⟩ := List.mem_map.1 hw
        exact hW _ (List.get_mem _ _)
  rw [jmL, dite_eq_left hWd]
  refine Eq.trans key ?_
  have hcard : (Finset.univ.filter fun b : SizeMatrix m m' => ∃ c ∈ S, b.1 = colourMat W c).card = S.card := by
    symm
    let mk : ∀ c, c ∈ S → SizeMatrix m m' := fun c hc =>
      ⟨colourMat W c, fun i => by simpa [m] using hrowS c hc i, fun j => by simpa [m'] using sum_colourMat W c j⟩
    refine Finset.card_bij mk (fun c hc => Finset.mem_filter.2 ⟨Finset.mem_univ _, c, hc, rfl⟩) ?_ ?_
    · intro c hc c' hc' he
      funext j
      have h1 : colourMat W c (c j) j = colourMat W c' (c j) j :=
        congrFun (congrFun (congrArg Subtype.val he) (c j)) j
      by_contra hne
      have h2 : c' j ≠ c j := fun e => hne e.symm
      simp only [colourMat, if_true, if_neg h2] at h1
      exact (hpos j).ne' h1
    · intro b hb
      obtain ⟨c, hc, hbc⟩ := (Finset.mem_filter.1 hb).2
      exact ⟨c, hc, Subtype.ext hbc.symm⟩
  rw [Finset.sum_congr rfl fun b _ => hF b, Finset.sum_boole, hcard]
end
end

