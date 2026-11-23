module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.EisensteinMeromorphy.Strong
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0012
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0043
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0013
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.KFiniteVectors.ExistsAtPlace
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0044
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKkfinTDer
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.OppositeUnipotentWeylConj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0032
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0045
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.StepNB
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.DenseW

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKheadStrong
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.SiegelWeilFormula
open GlobalTheory.Cont
namespace PositivityTheory.SiegelWeilFormula.Khead
theorem eisStrong_of_k : _root_.GlobalTheory.ThK.Dbl.EisBL_k → _root_.PositivityTheory.SiegelWeilFormula.EisStrong_k := by
  intro hBL F E _ _ _ _ _ σ d hS s₁ f hf s₀
  obtain ⟨r', s', hY⟩ := hS
  obtain ⟨Ê, ⟨t, hsum, hdiff⟩, hw⟩ := hBL F E σ d.B d.n d.Y r' s' d.ok.good d.ok.hn hY d.χ d.ok.hecke d.m d.ok.res d.b d.K d.a
    d.ok.frame d.ok.stdK d.ok.hgt s₁ f hf
  have hp : ∀ s₀ : ℂ, ∃ (k : ℕ) (H : ℂ → d.G → ℂ), An.Reg (fun x : d.G => (ht2 x : ℝ)) H s₀ ∧
      ∀ᶠ s in 𝓝[≠] s₀, ∀ x, H s x = (s - s₀) ^ k * Ê s x := by
    intro s₀
    obtain ⟨k, U, H, hU, he, hd⟩ := hw s₀
    refine ⟨k, fun s => (H s).1, reg_of_weak hU hd, ?_⟩
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hU, self_mem_nhdsWithin] with s hs hne
    exact he s hs hne
  have hr : ∀ s : ℂ, t < s.re → An.Reg (fun x : d.G => (ht2 x : ℝ)) Ê s := fun s hs => by
    obtain ⟨k, H, a, e⟩ := hp s
    exact a.remove one_le_height_GL2 e ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs) hdiff
  obtain ⟨U, p, G, hUo, hUr, hs₀, hp0, hreg, heq⟩ := strip one_le_height_GL2 hp hr s₀
  obtain ⟨hGd, hGc⟩ := diff_cont_of_reg hreg
  obtain ⟨t2, hmaj⟩ := _root_.PositivityTheory.SiegelWeilFormula.Khead.majorant_k d ⟨r', s', hY⟩ hf
  have hinv := _root_.GlobalTheory.T.eisenstein_series_moderate_growth F E σ d.B d.n d.Y r' s' d.ok.good d.ok.hn hY d.b d.K d.a d.ok.frame d.ok.stdK d.ok.hgt d.χ s₁ f hf
    d.ok.hecke t Ê hsum
  have hfl : ∀ z, (fun y => ((d.Ht y : ℝ) : ℂ) ^ (z - s₁) * f y) = flat d.a f s₁ z := fun z => funext fun y => by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.Ht, flat]
    rw [Real.coe_toNNReal _ (hgt_nonneg d.ok.hgt y)]
  have Heisenberg₂ : ∀ z : ℂ, t < z.re → ∀ g, d.eis f s₁ z g = Ê z g := fun z hz g => by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.eis]
    rw [hfl z]
    exact (hsum z hz g).tsum_eq
  refine ⟨U, p, G, max t t2, hUo, hUr, hs₀, hp0, hGd, hGc, ?_, fun z hz =>
    ⟨hmaj z (lt_of_le_of_lt (le_max_right _ _) hz), fun g => ?_⟩⟩
  · intro z hz γ hγ g
    obtain ⟨τ, hτ⟩ := hUr.1
    have han : ∀ x, AnalyticOnNhd ℂ (G · x) U := fun x => (hGd x).analyticOnNhd hUo
    have hz₀ : (((max τ t + 1 : ℝ)) : ℂ) ∈ rightOf (max τ t) := by simp
    refine (han (γ * g)).eqOn_of_preconnected_of_eventuallyEq (han g) hUr.isPreconnected
      (hτ (rightOf_subset (le_max_left _ _) hz₀)) ?_ hz
    filter_upwards [(isOpen_rightOf _).mem_nhds hz₀] with w hw
    have hw' : t < w.re := lt_of_le_of_lt (le_max_right _ _) hw
    rw [heq w hw', heq w hw', hinv w hw' γ hγ g]
  · have hz1 : t < z.re := lt_of_le_of_lt (le_max_left _ _) hz
    rw [heq z hz1, Heisenberg₂ z hz1]
end PositivityTheory.SiegelWeilFormula.Khead
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKkfinVarB
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KK
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
open Matrix
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem exists_at_place_k (w : InfinitePlace F) (V : Matrix (Fin d.m) (Fin d.n) ℂ) :
    ∃ V' : Mx F E d.m d.n, At (evI F) V' ∧ ∀ w', d.cw w' V' = if w' = w then V else 0 := by
  have h := d.ok.good.cm
  choose x hx hz using fun i j => GlobalTheory.CompanionTheory.RealPlaceAdele.exists_adele_piInf σ h d.B.emb fun w' =>
    if w' = w then V i j else 0
  refine ⟨Matrix.of x, fun c hc => Matrix.ext fun i j => hx i j c hc, fun w' => ?_⟩
  ext i j
  show piInf (d.B.emb w') (x i j) = _
  rw [hz i j w']
  split_ifs <;> rfl
theorem mZ_place_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (tA : Matrix (Fin d.n) (Fin d.n) (AE F E)) (htA : _root_.PositivityTheory.SiegelWeilFormula.KK.firstFrameColumns d = _root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d * tA)
    {V' : Mx F E d.m d.n} {V : Matrix (Fin d.m) (Fin d.n) ℂ} (hV : ∀ w', d.cw w' V' = if w' = w then V else 0)
    (X : Mx F E d.m d.n) :
    _root_.PositivityTheory.SiegelWeilFormula.KK.mZ_k d (V' * tAᵀ) X = -(2 * ((((R.ε : ℤ) : ℂ)) * trace ((d.cw w X)ᵀ * d.A.J.map (d.B.emb w).1 * V.map star)).re) := by
  have e1 : V' * tAᵀ * (_root_.PositivityTheory.SiegelWeilFormula.KK.dg_k d)ᵀ = V' * (_root_.PositivityTheory.SiegelWeilFormula.KK.firstFrameColumns d)ᵀ := by rw [htA, Matrix.transpose_mul, Matrix.mul_assoc]
  rw [_root_.PositivityTheory.SiegelWeilFormula.KK.mZ_k, e1, _root_.PositivityTheory.SiegelWeilFormula.KK.trace_sp_k, Finset.sum_eq_single w]
  · congr 3
    have hX : (X * (_root_.PositivityTheory.SiegelWeilFormula.KK.secondFrameColumns d)ᵀ).map (piInf (d.B.emb w)) = d.cw w X * ((d.b.1.map (d.B.emb w).1).toCols₂)ᵀ := by
      rw [_root_.PositivityTheory.SiegelWeilFormula.KK.map_mul_incM_T_k]; rfl
    have hVb : (V' * (_root_.PositivityTheory.SiegelWeilFormula.KK.firstFrameColumns d)ᵀ).map (piInf (d.B.emb w)) = V * ((d.b.1.map (d.B.emb w).1).toCols₁)ᵀ := by
      rw [_root_.PositivityTheory.SiegelWeilFormula.KK.map_mul_incM_T_k]
      have := hV w
      rw [if_pos rfl] at this
      rw [show V'.map (piInf (d.B.emb w)) = d.cw w V' from rfl, this]
      rfl
    rw [hX, hVb]
    exact trace_form_sign_eq (_root_.PositivityTheory.SiegelWeilFormula.KK.frame_form_k R w) (d.cw w X) V
  · intro w' _ hw'
    have hVb : (V' * (_root_.PositivityTheory.SiegelWeilFormula.KK.firstFrameColumns d)ᵀ).map (piInf (d.B.emb w')) = 0 := by
      rw [_root_.PositivityTheory.SiegelWeilFormula.KK.map_mul_incM_T_k]
      have := hV w'
      rw [if_neg hw'] at this
      rw [show V'.map (piInf (d.B.emb w')) = d.cw w' V' from rfl, this, Matrix.zero_mul]
    rw [hVb]
    simp
  · intro h; exact absurd (Finset.mem_univ w) h
theorem var_span'_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (k : Fin d.m × Fin d.n × Bool) :
    ∃ (Z₁ Z₂ : Mx F E d.m d.n) (c₁ c₂ : ℂ), At (evI F) Z₁ ∧ At (evI F) Z₂ ∧
      ∀ X, evX (MvPolynomial.X k) (R.loc w X) = c₁ * (_root_.PositivityTheory.SiegelWeilFormula.KK.mZ_k d Z₁ X : ℂ) + c₂ * (_root_.PositivityTheory.SiegelWeilFormula.KK.mZ_k d Z₂ X : ℂ) := by
  obtain ⟨tA, htA⟩ := _root_.PositivityTheory.SiegelWeilFormula.KK.firstColumns_eq_diag_mul (d := d)
  set τ := d.B.emb w
  set fr := (R.fr w).1
  set fi := ((R.fr w)⁻¹).1
  set A := d.A.J.map τ.1
  set e : ℂ := ((R.ε : ℤ) : ℂ)
  have he : e * e = 1 := by rcases Int.units_eq_one_or R.ε with h | h <;> simp [e, h]
  have hes : star e = e := by simp [e]
  have hz : star R.ζ * R.ζ = 1 := by rcases R.hζ with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> simp [Complex.ext_iff]
  have hfi : fr * fi = 1 := by simp only [fr, fi]; rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hif : fi * fr = 1 := by simp only [fr, fi]; rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  set P := (((R.sg w : ℤ) : ℂ) * R.ζ) • (fr.map star * frᵀ)
  have hAP : A * P = 1 := by
    have hA := A_eq hfi hz (R.hfr w)
    rw [show d.A.J.map (d.B.emb w).1 = A from rfl] at hA
    rw [hA]
    simp only [P, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have t1 : fiᵀ * fi.map star * (fr.map star * frᵀ) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (fi.map star), ← mapStar_mul, hif]
      rw [show (1 : Matrix (Fin d.m) (Fin d.m) ℂ).map star = 1 from Matrix.map_one star (star_zero _) (star_one _)]
      rw [Matrix.one_mul, ← transpose_mul, hfi, transpose_one]
    rw [t1]
    have hs2 : ((R.sg w : ℤ) : ℂ) * R.ζ * (((R.sg w : ℤ) : ℂ) * star R.ζ) = 1 := by
      calc _ = (((R.sg w : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ)) * (star R.ζ * R.ζ) := by ring
        _ = 1 := by rw [hz, mul_one]; rcases Int.units_eq_one_or (R.sg w) with h | h <;> simp [h]
    rw [hs2, one_smul]
  have key : ∀ M : Matrix (Fin d.m) (Fin d.n) ℂ, ∃ Z : Mx F E d.m d.n, At (evI F) Z ∧
      ∀ X, (_root_.PositivityTheory.SiegelWeilFormula.KK.mZ_k d Z X : ℂ) = -(2 * e) * ((trace ((d.cw w X)ᵀ * M)).re : ℂ) := by
    intro M
    obtain ⟨V', hV'a, hV'⟩ := _root_.PositivityTheory.SiegelWeilFormula.KK.exists_at_place_k (d := d) w ((P * M).map star)
    refine ⟨V' * tAᵀ, at_mul hV'a _, fun X => ?_⟩
    rw [_root_.PositivityTheory.SiegelWeilFormula.KK.mZ_place_k R w tA htA hV' X]
    have : (d.cw w X)ᵀ * A * ((P * M).map star).map star = (d.cw w X)ᵀ * M := by
      rw [show ((P * M).map star).map star = P * M by ext i j; simp only [Matrix.map_apply, star_star], ← Matrix.mul_assoc, Matrix.mul_assoc _ A, hAP,
        Matrix.mul_one]
    rw [show d.A.J.map (d.B.emb w).1 = A from rfl, this]
    have hre : (e * trace ((d.cw w X)ᵀ * M)).re = e.re * (trace ((d.cw w X)ᵀ * M)).re := by
      rcases Int.units_eq_one_or R.ε with h | h <;> simp [e, h]
    rw [hre]
    rcases Int.units_eq_one_or R.ε with h | h <;> simp [e, h] <;> ring
  have hM : ∀ (c : ℂ) (x : Matrix (Fin d.m) (Fin d.n) ℂ),
      trace (xᵀ * Matrix.of fun b j => if j = k.2.1 then c * fi k.1 b else 0) = c * (fi * x) k.1 k.2.1 := fun c x => by
    simp only [trace, diag_apply, Matrix.mul_apply, transpose_apply, of_apply, mul_ite, mul_zero]
    rw [Finset.sum_eq_single k.2.1 (fun j _ hj => by simp [hj]) (by simp)]
    simp only [if_pos rfl, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by simp only [if_true]; ring
  obtain ⟨Z₁, h1, e1⟩ := key (Matrix.of fun b j => if j = k.2.1 then 1 * fi k.1 b else 0)
  obtain ⟨Z₂, h2, e2⟩ := key (Matrix.of fun b j => if j = k.2.1 then (-Complex.I) * fi k.1 b else 0)
  have hl : ∀ X, evX (MvPolynomial.X k) (R.loc w X) =
      if k.2.2 then (fi * d.cw w X) k.1 k.2.1 else star ((fi * d.cw w X) k.1 k.2.1) := fun X => by
    simp only [evX, MvPolynomial.eval_X, _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc, Matrix.map_apply]
    split_ifs <;> (try simp only [star_star]) <;> rfl
  have hsplit : ∀ z : ℂ, z = (z.re : ℂ) + Complex.I * ((-Complex.I * z).re : ℂ) := fun z => by
    apply Complex.ext <;> simp
  have hsplit' : ∀ z : ℂ, star z = (z.re : ℂ) - Complex.I * ((-Complex.I * z).re : ℂ) := fun z => by
    apply Complex.ext <;> simp
  refine ⟨Z₁, Z₂, -(e / 2) * (if k.2.2 then 1 else 1), -(e / 2) * (if k.2.2 then Complex.I else -Complex.I), h1, h2,
    fun X => ?_⟩
  rw [hl X, e1 X, e2 X, hM, hM, one_mul]
  have hinv : -(e / 2) * (-(2 * e)) = 1 := by linear_combination he
  split_ifs
  · conv_lhs => rw [hsplit ((fi * d.cw w X) k.1 k.2.1)]
    linear_combination (-(((fi * d.cw w X) k.1 k.2.1).re : ℂ) - Complex.I * ((-Complex.I * (fi * d.cw w X) k.1 k.2.1).re : ℂ)) * hinv
  · rw [hsplit' ((fi * d.cw w X) k.1 k.2.1)]
    linear_combination (-(((fi * d.cw w X) k.1 k.2.1).re : ℂ) + Complex.I * ((-Complex.I * (fi * d.cw w X) k.1 k.2.1).re : ℂ)) * hinv
end PositivityTheory.SiegelWeilFormula.KK
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopRelPf
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace RD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F)
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.w_four_pf {ε : ℤˣ} {w₀ : d.G} (h : d.IsW ε w₀) : w₀ * w₀ * w₀ * w₀ = 1 := by
  apply d.inFrame_inj
  have hW : inFrame d.b w₀ = wM d.n ((ε : ℤ) : AE F E) := h
  rw [d.inFrame_mul, d.inFrame_mul, d.inFrame_mul, hW, d.inFrame_one, wM_four _ (intUnit_sq ε)]
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.cw_iota_pf (y : GR d.n) : d.cw w (inFrame d.b (R.ι w y)) = dZ d.n R.ζ⁻¹ * mR y * dZ d.n R.ζ := by
  have hζ0 : R.ζ ≠ 0 := Krd.zeta_ne R.hζ
  calc d.cw w (inFrame d.b (R.ι w y)) = dZ d.n R.ζ⁻¹ * (dZ d.n R.ζ * d.cw w (inFrame d.b (R.ι w y))) := by
        rw [← Matrix.mul_assoc, Krd.dZ_inv_mul hζ0, Matrix.one_mul]
    _ = dZ d.n R.ζ⁻¹ * mR y * dZ d.n R.ζ := by rw [R.at_w w y, Matrix.mul_assoc]
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.cw_wM {ε : ℤˣ} {w₀ : d.G} (h : d.IsW ε w₀) (w' : InfinitePlace F) :
    d.cw w' (inFrame d.b w₀) = wM d.n ((ε : ℤ) : ℂ) := by
  have hW : inFrame d.b w₀ = wM d.n ((ε : ℤ) : AE F E) := h
  rw [hW]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, wM, Matrix.one_apply] <;> split_ifs <;> simp
def _root_.PositivityTheory.SiegelWeilFormula.RD_k.nUpt (x : Matrix (Fin d.n) (Fin d.n) ℂ) (hx : xᴴ = x) : GR d.n :=
  ⟨⟨nU x, nU (-x), by simp [nU, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one],
    by simp [nU, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]⟩,
    by
      show InG (nU x)
      simp [InG, nU, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hx]⟩
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.nbar_conj_pf {ε : ℤˣ} {w₀ : d.G} (h : d.IsW ε w₀) : ∀ (y : GR d.n) (c : Matrix (Fin d.n) (Fin d.n) ℂ), cᴴ = c →
    mR y = nbLoc c → ∃ (y' : GR d.n) (x : Matrix (Fin d.n) (Fin d.n) ℂ), xᴴ = x ∧ mR y' = nU x ∧
      R.ι w y = w₀ * w₀ * w₀ * R.ι w y' * w₀ := by
  intro y c hc hy
  have hζ0 : R.ζ ≠ 0 := Krd.zeta_ne R.hζ
  have he : ((ε : ℤ) : ℂ) * ((ε : ℤ) : ℂ) = 1 := intUnit_sq ε
  have hs : star (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) = ((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹ := by
    rcases R.hζ with ⟨-, hz⟩ | ⟨-, hz⟩
    · rw [hz]; simp
    · rw [hz]; simp [Complex.inv_I]
  set x : Matrix (Fin d.n) (Fin d.n) ℂ := (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c with hxdef
  have hx : xᴴ = x := by rw [hxdef, Matrix.conjTranspose_smul, hc, hs]
  refine ⟨_root_.PositivityTheory.SiegelWeilFormula.RD_k.nUpt x hx, x, hx, rfl, ?_⟩
  apply d.inFrame_inj
  simp only [d.inFrame_mul]
  apply _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d
  · intro w'
    simp only [_root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k d, _root_.PositivityTheory.SiegelWeilFormula.RD_k.cw_wM h]
    by_cases hw : w' = w
    · rw [hw, R.cw_iota_pf w y, R.cw_iota_pf w (_root_.PositivityTheory.SiegelWeilFormula.RD_k.nUpt x hx), hy]
      have e1 : mR (_root_.PositivityTheory.SiegelWeilFormula.RD_k.nUpt x hx) = nU x := rfl
      rw [e1, dZ_conj_nb hζ0, dZ_conj_nU hζ0, weyl_cube_conj_unipotent _ he]
      congr 1
      rw [hxdef, smul_smul, smul_smul]
      congr 1
      calc R.ζ⁻¹ = (((ε : ℤ) : ℂ) * ((ε : ℤ) : ℂ)) * (R.ζ * R.ζ⁻¹) * R.ζ⁻¹ := by
            rw [he, mul_inv_cancel₀ hζ0]; ring
        _ = _ := by ring
    · rw [R.off_w w w' y hw, R.off_w w w' _ hw, Matrix.mul_one, wM_four _ he]
  · have hW : inFrame d.b w₀ = wM d.n ((ε : ℤ) : AE F E) := h
    rw [R.off_f w y]
    simp only [Krd.fin_mul, R.off_f w]
    simp only [← Krd.fin_mul, Matrix.mul_one, hW, wM_four _ (intUnit_sq ε)]
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.oppositeUnipotent_weylConj {ε : ℤˣ} {w₀ : d.G} (h : d.IsW ε w₀) : ∀ (y : GR d.n) (c : Matrix (Fin d.n) (Fin d.n) ℂ), cᴴ = c →
    mR y = nbLoc c → ∃ y' : GR d.n, mR y' = nU ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c) ∧
      R.ι w y = w₀ * w₀ * w₀ * R.ι w y' * w₀ := by
  intro y c hc hy
  have hζ0 : R.ζ ≠ 0 := Krd.zeta_ne R.hζ
  have he : ((ε : ℤ) : ℂ) * ((ε : ℤ) : ℂ) = 1 := intUnit_sq ε
  have hs : star (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) = ((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹ := by
    rcases R.hζ with ⟨-, hz⟩ | ⟨-, hz⟩
    · rw [hz]; simp
    · rw [hz]; simp [Complex.inv_I]
  set x : Matrix (Fin d.n) (Fin d.n) ℂ := (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c with hxdef
  have hx : xᴴ = x := by rw [hxdef, Matrix.conjTranspose_smul, hc, hs]
  refine ⟨_root_.PositivityTheory.SiegelWeilFormula.RD_k.nUpt x hx, rfl, ?_⟩
  apply d.inFrame_inj
  simp only [d.inFrame_mul]
  apply _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d
  · intro w'
    simp only [_root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k d, _root_.PositivityTheory.SiegelWeilFormula.RD_k.cw_wM h]
    by_cases hw : w' = w
    · rw [hw, R.cw_iota_pf w y, R.cw_iota_pf w (_root_.PositivityTheory.SiegelWeilFormula.RD_k.nUpt x hx), hy]
      have e1 : mR (_root_.PositivityTheory.SiegelWeilFormula.RD_k.nUpt x hx) = nU x := rfl
      rw [e1, dZ_conj_nb hζ0, dZ_conj_nU hζ0, weyl_cube_conj_unipotent _ he]
      congr 1
      rw [hxdef, smul_smul, smul_smul]
      congr 1
      calc R.ζ⁻¹ = (((ε : ℤ) : ℂ) * ((ε : ℤ) : ℂ)) * (R.ζ * R.ζ⁻¹) * R.ζ⁻¹ := by
            rw [he, mul_inv_cancel₀ hζ0]; ring
        _ = _ := by ring
    · rw [R.off_w w w' y hw, R.off_w w w' _ hw, Matrix.mul_one, wM_four _ he]
  · have hW : inFrame d.b w₀ = wM d.n ((ε : ℤ) : AE F E) := h
    rw [R.off_f w y]
    simp only [Krd.fin_mul, R.off_f w]
    simp only [← Krd.fin_mul, Matrix.mul_one, hW, wM_four _ (intUnit_sq ε)]
end RD
end PositivityTheory.SiegelWeilFormula
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopStepNB
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace RD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F)
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.cw_mulR {p q r : Type} [Fintype q] (w' : InfinitePlace F) (A : Matrix p q (AE F E)) (B : Matrix q r (AE F E)) :
    d.cw w' (A * B) = d.cw w' A * d.cw w' B :=
  Matrix.map_mul (f := piInf (d.B.emb w'))
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.cw_loc (X : Mx F E d.m d.n) : d.cw w X = (R.fr w).1 * (Matrix.of (R.loc w X)).map star := by
  have e : (Matrix.of (R.loc w X)).map star = ((R.fr w)⁻¹).1 * d.cw w X := by
    ext i j
    exact star_star _
  rw [e, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.cw_gram (X : Mx F E d.m d.n) :
    d.cw w (d.gram X X) = (R.ζ⁻¹ * ((R.sg w : ℤ) : ℂ)) • ((Matrix.of (R.loc w X))ᴴ * Matrix.of (R.loc w X)) := by
  have hζ0 : R.ζ ≠ 0 := Krd.zeta_ne R.hζ
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram]
  rw [_root_.PositivityTheory.SiegelWeilFormula.RD_k.cw_mulR, _root_.PositivityTheory.SiegelWeilFormula.RD_k.cw_mulR, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_transpose_k d, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_incM_k d, _root_.PositivityTheory.SiegelWeilFormula.Place.cw_cA_k d, R.cw_loc w X]
  exact gram_loc _ _ _ _ hζ0 (R.hfr w) _
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.psi_nU (b : Matrix (Fin d.n) (Fin d.n) ℂ) (hb : bᴴ = b) (β : Matrix (Fin d.n) (Fin d.n) (AE F E))
    (hβw : d.cw w β = R.ζ • b) (hβo : ∀ w', w' ≠ w → d.cw w' β = 0) (hβf : finOne F • β = 0) (X : Mx F E d.m d.n) :
    d.B.ψ (-(⅟(2 : AF F) * d.tt (β * d.gram X X))) = Complex.exp (2 * Real.pi * Complex.I * ((R.sg w : ℤ) : ℂ) *
      Matrix.trace (b * ((Matrix.of (R.loc w X))ᴴ * Matrix.of (R.loc w X)))) := by
  have hζ0 : R.ζ ≠ 0 := Krd.zeta_ne R.hζ
  set z : AE F E := (-(⅟(2 : AF F))) • (β * d.gram X X).trace with hz
  have e1 : -(⅟(2 : AF F) * d.tt (β * d.gram X X)) = Algebra.trace (AF F) (AE F E) z := by
    rw [hz, LinearMap.map_smul, smul_eq_mul, neg_mul]
    rfl
  have hpi : ∀ w', piInf (d.B.emb w') z = -(1 / 2) * (d.cw w' β * d.cw w' (d.gram X X)).trace := by
    intro w'
    rw [hz, Algebra.smul_def, map_mul, map_neg, map_neg, piInf_half, ← _root_.PositivityTheory.SiegelWeilFormula.RD_k.cw_mulR]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.trace, _root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, Matrix.map_apply, Matrix.diag, map_sum]
  have hf : finOne F • z = 0 := by
    rw [hz, smul_comm, ← Matrix.trace_smul, ← Matrix.smul_mul, hβf, Matrix.zero_mul, Matrix.trace_zero, smul_zero]
  have ho : ∀ u, u ≠ w → piInf (d.B.emb u) z = 0 := by
    intro u hu
    rw [hpi, hβo u hu, Matrix.zero_mul, Matrix.trace_zero, mul_zero]
  rw [e1, Place.psi_trace_at d.std d.cm d.B.emb w z hf ho, hpi, hβw, R.cw_gram w X]
  set T := (b * ((Matrix.of (R.loc w X))ᴴ * Matrix.of (R.loc w X))).trace with hT
  have hreal : ((T.re : ℝ) : ℂ) = T := trace_herm_real _ _ hb (by rw [Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose])
  have e2 : (R.ζ • b * (R.ζ⁻¹ * ((R.sg w : ℤ) : ℂ)) • ((Matrix.of (R.loc w X))ᴴ * Matrix.of (R.loc w X))).trace = ((R.sg w : ℤ) : ℂ) * T := by
    rw [smul_mul_smul_comm, Matrix.trace_smul, hT, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hζ0, one_mul]
  rw [e2]
  rw [← hreal]
  congr 1
  push_cast
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, Complex.intCast_re,
    Complex.intCast_im, mul_zero, sub_zero, Complex.div_ofNat_re, Complex.one_re, Complex.neg_im, Complex.div_ofNat_im,
    Complex.one_im, zero_mul]
  push_cast
  ring
end RD
end PositivityTheory.SiegelWeilFormula
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdDenseW
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Krd.DM
open PositivityTheory.SiegelWeilFormula.Krd.DC
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem dblJ_det_k {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = QR E d.n ε) : (dbl d.Y.J).det ≠ 0 := by
  intro h0
  have := congrArg Matrix.det hε
  rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero, zero_mul] at this
  exact QR_det_ne E ε this.symm
def bX_k (X : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E :=
  d.b.1 * X * (d.b⁻¹).1
theorem bX_unitary_k {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = QR E d.n ε)
    {X : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E} (hX : Xᵀ * QR E d.n ε * X.map σ = QR E d.n ε) :
    (_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.bX_k d X)ᵀ * dbl d.Y.J * (_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.bX_k d X).map σ = dbl d.Y.J :=
  conj_unitE (σ : E →+* E) d.b.1 (d.b⁻¹).1 X (dbl d.Y.J) (QR E d.n ε) (Units.mul_inv d.b) hε hX
def ratG_k {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = QR E d.n ε)
    (X : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) (hX : Xᵀ * QR E d.n ε * X.map σ = QR E d.n ε) : d.G :=
  ⟨Matrix.GeneralLinearGroup.map (inclR (F := F) (AF F))
    (Matrix.nonsingInvUnit (_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.bX_k d X) (isUnit_iff_ne_zero.2 (det_ne_of (σ : E →+* E) (_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.bX_unitary_k d hε hX) (_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.dblJ_det_k d hε)))),
    by
      show (incM F (_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.bX_k d X))ᵀ * dbl (incM F d.Y.J) * (incM F (_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.bX_k d X)).map (cA σ) = dbl (incM F d.Y.J)
      rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.dbl_incM_k d, incM_cA, incM_alt_bis, ← incM_mul, ← incM_mul, _root_.PositivityTheory.SiegelWeilFormula.Krd.DM.bX_unitary_k d hε hX]⟩
theorem ratG_mem_k {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = QR E d.n ε)
    (X : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) (hX : Xᵀ * QR E d.n ε * X.map σ = QR E d.n ε) :
    _root_.PositivityTheory.SiegelWeilFormula.Krd.DM.ratG_k d hε X hX ∈ rat2 σ d.Y :=
  Subgroup.mem_subgroupOf.2 ⟨_, rfl⟩
theorem inFrame_ratG_k {ε : ℤˣ} (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = QR E d.n ε)
    (X : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) (hX : Xᵀ * QR E d.n ε * X.map σ = QR E d.n ε) :
    inFrame d.b (_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.ratG_k d hε X hX) = incM F X := by
  show incM F (d.b⁻¹).1 * incM F (_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.bX_k d X) * incM F d.b.1 = incM F X
  rw [← incM_mul, ← incM_mul]
  congr 1
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.bX_k, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
theorem inFrame_mul_k (x z : d.G) : inFrame d.b (x * z) = inFrame d.b x * inFrame d.b z := by
  show incM F (d.b⁻¹).1 * (mat2 x * mat2 z) * incM F d.b.1 =
    (incM F (d.b⁻¹).1 * mat2 x * incM F d.b.1) * (incM F (d.b⁻¹).1 * mat2 z * incM F d.b.1)
  calc incM F (d.b⁻¹).1 * (mat2 x * mat2 z) * incM F d.b.1 =
      incM F (d.b⁻¹).1 * mat2 x * (incM F d.b.1 * incM F (d.b⁻¹).1) * mat2 z * incM F d.b.1 := by
        rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.bb_k d, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]
theorem inFrame_inj_k {x z : d.G} (h : inFrame d.b x = inFrame d.b z) : x = z := by
  have e : ∀ u : d.G, mat2 u = incM F d.b.1 * inFrame d.b u * incM F (d.b⁻¹).1 := fun u => by
    simp only [inFrame, ← Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.Krd.bb_k d, Matrix.one_mul]
    rw [Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.Krd.bb_k d, Matrix.mul_one]
  apply Subtype.ext
  apply Units.ext
  show mat2 x = mat2 z
  rw [e x, e z, h]
end PositivityTheory.SiegelWeilFormula.Krd.DM
open PositivityTheory.SiegelWeilFormula.Krd PositivityTheory.SiegelWeilFormula.Krd.DM PositivityTheory.SiegelWeilFormula.Krd.DC in
theorem PositivityTheory.SiegelWeilFormula.Krd.denseW_k : _root_.PositivityTheory.SiegelWeilFormula.DenseW_k := by
  intro F E _ _ _ _ _ σ d R w y O hO hy
  have h0 := zeta_ne R.hζ
  have hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = QR E d.n R.ε := R.hε
  obtain ⟨X, hXU, hXO⟩ := exists_rat d.cm (d.B.emb w).1 R.hζ hO hy
  have hX := rat_unitary d.cm (d.B.emb w).1 R.ε X hXU
  refine ⟨_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.ratG_k d hε X hX, _root_.PositivityTheory.SiegelWeilFormula.Krd.DM.ratG_mem_k d hε X hX, _, hXO, _root_.PositivityTheory.SiegelWeilFormula.Krd.DM.ratG_k d hε X hX * (R.ι w (Phi R.hζ ⟨_, hXU⟩))⁻¹,
    (inv_mul_cancel_right _ _).symm, fun y'' => ?_⟩
  set y' := Phi R.hζ ⟨X.map (d.B.emb w).1, hXU⟩ with hy'
  set A := inFrame d.b (_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.ratG_k d hε X hX * (R.ι w y')⁻¹) with hA
  have hAC : A * inFrame d.b (R.ι w y') = incM F X := by
    rw [hA, ← _root_.PositivityTheory.SiegelWeilFormula.Krd.DM.inFrame_mul_k, inv_mul_cancel_right, _root_.PositivityTheory.SiegelWeilFormula.Krd.DM.inFrame_ratG_k]
  have hC : d.cw w (inFrame d.b (R.ι w y')) = X.map (d.B.emb w).1 := by
    have e := R.at_w w y'
    rw [show mR y' = dZ d.n R.ζ * X.map (d.B.emb w).1 * dZ d.n R.ζ⁻¹ from rfl, Matrix.mul_assoc _ (dZ _ R.ζ⁻¹),
      dZ_inv_mul h0, Matrix.mul_one] at e
    have := congrArg (fun M => dZ d.n R.ζ⁻¹ * M) e
    simpa only [← Matrix.mul_assoc, dZ_inv_mul h0, Matrix.one_mul] using this
  have hdet := det_of_inU hXU
  have hAw : d.cw w A = 1 := by
    have e : d.cw w A * X.map (d.B.emb w).1 = X.map (d.B.emb w).1 := by
      have := congrArg (d.cw w) hAC
      rwa [_root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, hC, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_incM_k] at this
    calc d.cw w A = d.cw w A * X.map (d.B.emb w).1 * (X.map (d.B.emb w).1)⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
      _ = 1 := by rw [e, Matrix.mul_nonsing_inv _ hdet]
  apply _root_.PositivityTheory.SiegelWeilFormula.Krd.DM.inFrame_inj_k d
  rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.DM.inFrame_mul_k d _ (R.ι w y''), _root_.PositivityTheory.SiegelWeilFormula.Krd.DM.inFrame_mul_k d (R.ι w y''), ← hA]
  refine _root_.PositivityTheory.SiegelWeilFormula.Place.cw_ext_k d (fun w' => ?_) ?_
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Krd.cw_mul_k]
    by_cases hw : w' = w
    · subst hw; rw [hAw, Matrix.one_mul, Matrix.mul_one]
    · rw [R.off_w w w' y'' hw, Matrix.one_mul, Matrix.mul_one]
  · rw [fin_mul, fin_mul, R.off_f w y'', ← fin_mul, ← fin_mul, Matrix.mul_one, Matrix.one_mul]
end
end
end

