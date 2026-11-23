module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0250
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0382
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0370
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0396
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0356
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0360
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0361
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0383
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0390
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0336
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0381
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0393
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0404
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0405
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0313

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoHodgeJumpOfGoodJumpMultiset
section
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.NoJumpMult

open Module TensorProduct

section Gen
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem filV_anti (a : ℤ) : Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := V) (a + 1) ≤ Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := V) a := by
  have h := PD.Fil_anti a
  unfold Formalism.WeaklyAdmissibleFiltrations.FilV
  have : AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) ((PD.Fil (a + 1)).restrictScalars Qp).subtype =
      (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) ((PD.Fil a).restrictScalars Qp).subtype).comp
        (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
          (Submodule.inclusion (show (PD.Fil (a + 1)).restrictScalars Qp ≤ (PD.Fil a).restrictScalars Qp from h))) := by
    ext x y; rfl
  rw [this]
  exact LinearMap.range_comp_le_range _ _

theorem fildR_anti (τ : K →ₐ[Qp] LL) (a : ℤ) : Formalism.WeaklyAdmissibleFiltrations.FildR PD ρ τ (a + 1) ≤ Formalism.WeaklyAdmissibleFiltrations.FildR PD ρ τ a :=
  inf_le_inf_left _ (filV_anti PD a)

theorem fildR_le (τ : K →ₐ[Qp] LL) (a : ℤ) : Formalism.WeaklyAdmissibleFiltrations.FildR PD ρ τ a ≤ Formalism.WeaklyAdmissibleFiltrations.DdR PD ρ :=
  inf_le_left.trans inf_le_left

theorem multV_ne_zero (τ : K →ₐ[Qp] LL) (a : ℤ) (hpos : 0 < finrank LL ↥(Formalism.WeaklyAdmissibleFiltrations.DdR PD ρ))
    (hj : Formalism.WeaklyAdmissibleFiltrations.IsJumpV PD ρ τ a) : Formalism.WeaklyAdmissibleFiltrations.multV PD ρ τ a ≠ 0 := by
  have : FiniteDimensional LL ↥(Formalism.WeaklyAdmissibleFiltrations.DdR PD ρ) := Module.finite_of_finrank_pos hpos
  have : FiniteDimensional LL ↥(Formalism.WeaklyAdmissibleFiltrations.FildR PD ρ τ a) := Submodule.finiteDimensional_of_le (fildR_le PD ρ τ a)
  have hlt : Formalism.WeaklyAdmissibleFiltrations.FildR PD ρ τ (a + 1) < Formalism.WeaklyAdmissibleFiltrations.FildR PD ρ τ a := lt_of_le_of_ne (fildR_anti PD ρ τ a) hj
  have := Submodule.finrank_lt_finrank_of_lt hlt
  unfold Formalism.WeaklyAdmissibleFiltrations.multV
  omega
end Gen

end GlobalTheory.NoJumpMult

namespace GlobalTheory.NoJumpMult

theorem r_pos (D : D7) : 0 < D.R.r := by
  have h1 := D.R.two_le_m; have h2 := D.R.m_add_three_le_k
  unfold Formalism.BasicNotions.Ranks.r; omega

theorem noJump_of_jumps : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), ∀ (ι : FractionRing (D.ntw.O0 i) →+* ℂ) (J : (D.host.E →+* ℂ) → Multiset ℤ), HodgeL bkP i s → JumpsAre bkP i s ι J → GoodJ D J → NoJump bkP i s := by
  set_option synthInstance.maxHeartbeats 200000 in
    intro D bkP i s ι J hH hJ hG v hv τ a ha
    obtain ⟨τc, hτc, -⟩ := GlobalTheory.ReadEmbEx.exists_readEmb D bkP i ι v hv τ
    have hdR := (hH v hv (Tgl i s) (Set.mem_insert_of_mem _ rfl)).1
    have hK : 0 < Module.finrank ℚ_[D.ntw.l i] ↥(bkP.br i v hv).Kw.1 := by
      have := (bkP.br i v hv).Kw.2
      exact Module.finrank_pos
    have hpos : 0 < Module.finrank ↥(bkP.br i v hv).LL.1
        ↥(Formalism.WeaklyAdmissibleFiltrations.DdR (PDv bkP i v hv) (repV bkP i v hv (Tgl i s))) := by
      have : Module.finrank ↥(bkP.br i v hv).LL.1
        ↥(Formalism.WeaklyAdmissibleFiltrations.DdR (PDv bkP i v hv) (repV bkP i v hv (Tgl i s))) =
          Module.finrank ℚ_[D.ntw.l i] ↥(bkP.br i v hv).Kw.1 * D.R.r := hdR
      rw [this]; exact Nat.mul_pos hK (r_pos D)
    have hm := multV_ne_zero _ _ τ a hpos ha
    rw [hJ v hv τ τc hτc a] at hm
    have hmem : a ∈ J τc := by
      by_contra hn
      exact hm (by simp [Multiset.count_eq_zero.mpr hn])
    exact (hG τc).2.2 a hmem

end GlobalTheory.NoJumpMult
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoInvAwayOfPure
section
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.PurityInvariants

theorem isRoot_of_eigen {R K : Type} [CommRing R] [Field K] (f : R →+* K) (ι : K →+* ℂ) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (c : K) (x : Fin n → K) (hx : x ≠ 0)
    (h : (M.map f).mulVec x = c • x) : (M.charpoly.map (ι.comp f)).IsRoot (ι c) := by
  classical
  have hdet : (Matrix.scalar (Fin n) c - M.map f).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨x, hx, ?_⟩
    rw [Matrix.sub_mulVec, h]
    ext j
    simp [Matrix.scalar_apply]
  have hroot : ((M.map f).charpoly).eval c = 0 := by
    rw [Matrix.eval_charpoly]
    exact hdet
  unfold Polynomial.IsRoot
  rw [← Polynomial.map_map, ← Matrix.charpoly_map, Polynomial.eval_map, Polynomial.eval₂_hom,
    hroot, map_zero]

theorem eigen_of_dual {R K : Type} [CommRing R] [Field K] (f : R →+* K) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (hM : IsUnit M.det) (c : R) (x : Fin n → K)
    (h : ((c • M⁻¹.transpose).map f).mulVec x = x) : (M.transpose.map f).mulVec x = f c • x := by
  have key : M.transpose * (c • M⁻¹.transpose) = c • (1 : Matrix (Fin n) (Fin n) R) := by
    rw [Matrix.mul_smul, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hM, Matrix.transpose_one]
  calc (M.transpose.map f).mulVec x
      = (M.transpose.map f).mulVec (((c • M⁻¹.transpose).map f).mulVec x) := by rw [h]
    _ = ((M.transpose * (c • M⁻¹.transpose)).map f).mulVec x := by
        rw [Matrix.mulVec_mulVec, Matrix.map_mul]
    _ = f c • x := by
        rw [key]
        ext j
        simp [Matrix.mulVec, dotProduct, Matrix.one_apply, apply_ite f, ite_mul, Finset.sum_ite_eq]

theorem one_lt_norm {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) :
    (1 : ℝ) < ((normV v : ℕ) : ℝ) := by
  have h1 : normV v = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  have hne1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  have hne0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have : 1 < normV v := by omega
  exact_mod_cast this

end GlobalTheory.PurityInvariants
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyBreuilKisinDatum
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem wq_map_injective {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {O : Type} [CommRing O] [IsDomain O]
    [CharZero O] (w : Wq l a →+* O) : Function.Injective w := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  obtain ⟨n, u, rfl⟩ := WittVector.exists_eq_pow_p_mul' x h0
  rw [map_mul, map_pow, map_natCast] at hx
  rcases mul_eq_zero.1 hx with h | h
  · exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h
  · exact (u.isUnit.map w).ne_zero h

theorem nonempty_bk_of_finExt : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), Nonempty (BK K) := by
  intro l hl K
  obtain ⟨hdvr, hfin, hunit⟩ := _root_.GlobalTheory.IntDvr.main l K
  obtain ⟨a, ha, w, hK, hw, hres⟩ := _root_.GlobalTheory.BSP.Res.exists_witt_residue l K
  letI : Algebra (Wq l a) ↥(OL K) := w.toRingHom.toAlgebra
  have halg : ∀ c, algebraMap (Wq l a) ↥(OL K) c = w c := fun _ => rfl
  haveI : IsScalarTower ℤ_[l] (Wq l a) ↥(OL K) :=
    IsScalarTower.of_algebraMap_eq fun z => (w.commutes z).symm
  haveI : Module.Finite (Wq l a) ↥(OL K) := Module.Finite.of_restrictScalars_finite ℤ_[l] _ _
  obtain ⟨π, Ep, hπ, hE, hne, hmin⟩ :=
    _root_.GlobalTheory.EisShift.exists_uniformiser l a ↥(OL K) (wq_map_injective _) hres
  obtain ⟨str, hstr⟩ := _root_.GlobalTheory.bkStr_quotient_equiv l a ↥(OL K) π Ep hE hmin
  obtain ⟨hδ, hc⟩ := _root_.GlobalTheory.BKReal.eisPoly_distinguished_complete l a Ep hE
  obtain ⟨fl, ev, hfl, hX, hC, hφ⟩ :=
    _root_.GlobalTheory.BKReal.exists_ev_of_root l a (intToOC K π) (fun h => hπ.not_isUnit ((hunit π).2 h))
  have hpoly : ∀ f : Polynomial (Wq l a),
      Per.θ l (ev (f : (Wq l a)⟦X⟧)) = intToOC K (Polynomial.aeval π f) := by
    intro f
    have : ((Per.θ l).comp ev).comp Polynomial.coeToPowerSeries.ringHom =
        (intToOC K).comp (Polynomial.aeval π : Polynomial (Wq l a) →ₐ[Wq l a] ↥(OL K)).toRingHom := by
      refine Polynomial.ringHom_ext (fun c => ?_) ?_
      · change Per.θ l (ev ((Polynomial.C c : Polynomial (Wq l a)) : (Wq l a)⟦X⟧)) =
          intToOC K (Polynomial.aeval π (Polynomial.C c))
        rw [Polynomial.coe_C, hC, Polynomial.aeval_C, halg, hw]
      · change Per.θ l (ev ((Polynomial.X : Polynomial (Wq l a)) : (Wq l a)⟦X⟧)) =
          intToOC K (Polynomial.aeval π (Polynomial.X : Polynomial (Wq l a)))
        rw [Polynomial.coe_X, hX, Polynomial.aeval_X, hfl]
    exact congrArg (fun φ : Polynomial (Wq l a) →+* OC l => φ f) this
  have hE0 : Per.θ l (ev (Ep : (Wq l a)⟦X⟧)) = 0 := by rw [hpoly, hmin.1, map_zero]
  refine ⟨{
    a := a, Ep := Ep, monic := hE.1, deg_pos := hE.2.1, dvd_coeff := hE.2.2.1, coeff_zero := hE.2.2.2
    not_expand := hne, str := str, isUnit_δ := hδ, complete := hc, flat := fl, ev := ev, ev_X := hX
    ev_C := hC, ev_frob := hφ
    span_ev := _root_.GlobalTheory.BSP.span_eq_ker_theta_of_distinguished l _ hE0 ?_
    θ_ev := fun r x h => ?_
    gal_w := fun g c => gal_wA l a
      (fun x hx => (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 x (hK hx)) c }⟩
  · rw [← (deltaS l a).map_δ_of_map_φ (ainfDelta l) ainf_torsionFree ev hφ]
    exact hδ.map ev
  · obtain ⟨f, rfl⟩ := hmin.2.1 r
    rw [hstr, Ideal.Quotient.eq, Ideal.mem_span_singleton'] at h
    obtain ⟨y, hy⟩ := h
    rw [← hpoly, ← sub_eq_zero, ← map_sub, ← map_sub, ← hy, map_mul, map_mul, hE0, mul_zero]

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormTeichmullerTiltMinusOneLe
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.BK

variable {l : ℕ} [Fact l.Prime] {K : FinExt l}

theorem norm_iA_mu_le : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (e : OCb l), IsEps e →
    ‖bk.iA (mu e)‖ ≤ (l : ℝ)⁻¹ ∧ (l = 2 → ‖bk.iA (mu e)‖ ≤ (4 : ℝ)⁻¹) := by
  intro l _ K bk e he
  have hker := (_root_.GlobalTheory.BSP.RhoZeroNormBounds.seed_norms l K bk).2.2
  have hθmu : Per.θ l (mu e) = 0 := by
    simp only [mu, map_sub, map_one]
    simp [he.1]
  refine ⟨hker _ hθmu, ?_⟩
  rintro rfl
  set δ := (frobeniusEquiv (Per.Fl 2) 2).symm e with hδ
  have hδ2 : δ ^ 2 = e := by
    rw [hδ]; exact frobenius_apply_frobeniusEquiv_symm (Per.Fl 2) 2 e
  have hu : δ.untilt ^ 2 = 1 := by
    rw [← map_pow, hδ2, he.1]
  have hu' : δ.untilt = -1 := by
    have h1 : (δ.untilt - 1) * (δ.untilt + 1) = 0 := by linear_combination hu
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd (sub_eq_zero.1 h) he.2
    · linear_combination h
  have hθa : Per.θ 2 (Per.tm δ + 1) = 0 := by
    simp [hu']
  have ha := hker _ hθa
  have hfac : mu e = (Per.tm δ + 1) * ((Per.tm δ + 1) - 2) := by
    simp only [mu]
    rw [← hδ2]
    show WittVector.teichmuller 2 (δ ^ 2) - 1 = _
    rw [map_pow]
    ring
  have h2 : ‖bk.iA ((Per.tm δ + 1) - 2)‖ ≤ (2 : ℝ)⁻¹ := by
    rw [map_sub]
    have hn2 : ‖bk.iA 2‖ ≤ (2 : ℝ)⁻¹ := by
      have := DiscBasic.norm_l_disc_le 2 (bk.ev X) bk.ρ₀
      rw [map_ofNat]; simpa using this
    rw [sub_eq_add_neg]
    refine (DiscBasic.norm_add_le_max_disc 2 (bk.ev X) bk.ρ₀ _ _).trans (max_le ?_ ?_)
    · simpa using ha
    · rw [norm_neg]; exact hn2
  rw [hfac, map_mul]
  refine (norm_mul_le _ _).trans ?_
  have : ((2 : ℕ) : ℝ)⁻¹ * (2 : ℝ)⁻¹ = (4 : ℝ)⁻¹ := by norm_num
  rw [← this]
  exact mul_le_mul ha h2 (norm_nonneg _) (by positivity)

end GlobalTheory.BSP.BK
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiKernelKillingElement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
open GlobalTheory.HodgeAt

noncomputable section
namespace GlobalTheory.HodgeAt

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (σ : GQ l) (L : FinExt l)

theorem phiS_map_emb (u : ↥L.1 ⊗[ℚ_[l]] ↥L.1) :
    phiS P σ L (Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥L.1) (emb P σ L) u) =
      emb P σ L (Algebra.TensorProduct.lift (AlgHom.id ℚ_[l] ↥L.1) (AlgHom.id ℚ_[l] ↥L.1)
        (fun _ _ => Commute.all _ _) u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul c d => simp [phiS, map_mul]

theorem key_emb (t : ↥L.1 ⊗[ℚ_[l]] ↥L.1)
    (ht : ∀ c : ↥L.1, ((1 : ↥L.1) ⊗ₜ[ℚ_[l]] c) * t = (AlgHom.id ℚ_[l] ↥L.1) c • t) (c : ↥L.1) :
    ((1 : ↥L.1) ⊗ₜ[ℚ_[l]] emb P σ L c) * Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥L.1) (emb P σ L) t =
      (c ⊗ₜ[ℚ_[l]] (1 : P.R.BdR)) * Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥L.1) (emb P σ L) t := by
  have h := congrArg (Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥L.1) (emb P σ L)) (ht c)
  rw [map_mul, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply] at h
  rw [h, Algebra.smul_def, map_mul]
  congr 1
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul]
  simp

theorem mul_eq_mul_phiS (e : ↥L.1 ⊗[ℚ_[l]] P.R.BdR)
    (hkey : ∀ c : ↥L.1, ((1 : ↥L.1) ⊗ₜ[ℚ_[l]] emb P σ L c) * e = (c ⊗ₜ[ℚ_[l]] (1 : P.R.BdR)) * e)
    (s : ↥L.1 ⊗[ℚ_[l]] P.R.BdR) : e * s = e * ((1 : ↥L.1) ⊗ₜ[ℚ_[l]] phiS P σ L s) := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [mul_add, hx, hy, map_add (f := _), TensorProduct.tmul_add, mul_add]
  | tmul c b =>
    calc e * (c ⊗ₜ[ℚ_[l]] b) = ((c ⊗ₜ[ℚ_[l]] (1 : P.R.BdR)) * e) * ((1 : ↥L.1) ⊗ₜ[ℚ_[l]] b) := by
          rw [mul_comm (c ⊗ₜ[ℚ_[l]] (1 : P.R.BdR)) e, mul_assoc, Algebra.TensorProduct.tmul_mul_tmul,
            mul_one, one_mul]
      _ = (((1 : ↥L.1) ⊗ₜ[ℚ_[l]] emb P σ L c) * e) * ((1 : ↥L.1) ⊗ₜ[ℚ_[l]] b) := by rw [hkey]
      _ = e * ((1 : ↥L.1) ⊗ₜ[ℚ_[l]] phiS P σ L (c ⊗ₜ[ℚ_[l]] b)) := by
          rw [mul_comm ((1 : ↥L.1) ⊗ₜ[ℚ_[l]] emb P σ L c) e, mul_assoc, Algebra.TensorProduct.tmul_mul_tmul,
            one_mul, phiS_tmul, emb_apply]

theorem sm_eq_zero_of_PhiS (a : ℕ) (e : ↥L.1 ⊗[ℚ_[l]] P.R.BdR)
    (hmul : ∀ s : ↥L.1 ⊗[ℚ_[l]] P.R.BdR, e * s = e * ((1 : ↥L.1) ⊗ₜ[ℚ_[l]] phiS P σ L s))
    (x : (Fin a → ↥L.1) ⊗[ℚ_[l]] P.R.BdR) (hx : PhiS P σ L a x = 0) :
    GlobalTheory.DRFil.sm ℚ_[l] P.R.BdR ↥L.1 (Fin a → ↥L.1) e x = 0 := by
  have hc : ∀ i, phiS P σ L (GlobalTheory.DRFil.ext ℚ_[l] P.R.BdR ((Pi.basisFun ↥L.1 (Fin a)).coord i) x) = 0 := by
    intro i
    have : (Pi.basisFun ↥L.1 (Fin a)).coord i = (LinearMap.proj i : (Fin a → ↥L.1) →ₗ[↥L.1] ↥L.1) := by
      ext v; simp
    rw [this]
    exact congrFun hx i
  have hsum := GlobalTheory.DRFil.eq_sum_basis (Qp := ℚ_[l]) (F := P.R.BdR) (Pi.basisFun ↥L.1 (Fin a)) x
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hsum, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← GlobalTheory.DRFil.sm_mul, hmul, hc i, TensorProduct.tmul_zero, mul_zero]
  simp

end GlobalTheory.HodgeAt

theorem GlobalTheory.HodgeAt.exists_idem_phiS_ker : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (σ : GQ l) (L : FinExt l) [FiniteDimensional ℚ_[l] ↥L.1] (a : ℕ), ∃ e : ↥L.1 ⊗[ℚ_[l]] P.R.BdR, phiS P σ L e = 1 ∧ ∀ x : (Fin a → ↥L.1) ⊗[ℚ_[l]] P.R.BdR, PhiS P σ L a x = 0 → GlobalTheory.DRFil.sm ℚ_[l] P.R.BdR ↥L.1 (Fin a → ↥L.1) e x = 0 := by
  intro l _ P σ L _ a
  obtain ⟨t, ht1, ht2⟩ := GlobalTheory.DRFil.exists_idem (Qp := ℚ_[l]) (AlgHom.id ℚ_[l] ↥L.1)
  refine ⟨Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥L.1) (emb P σ L) t, ?_, ?_⟩
  · rw [phiS_map_emb, ht1, map_one]
  · exact sm_eq_zero_of_PhiS P σ L a _ (mul_eq_mul_phiS P σ L _ (key_emb P σ L t ht2))
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismHomMapIdealEqStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prism_hom_map_ideal_eq : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B B' : Obj l R) (f : Hom B B'), B.I.map f.f = B'.I := by
  first | exact @GlobalTheory.Prism.Rigid.map_I_eq | exact GlobalTheory.Prism.Rigid.map_I_eq | (intros; apply GlobalTheory.Prism.Rigid.map_I_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RatioIntegral
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.RatioTransport

open GlobalTheory.PMon.Gauss

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)

theorem lift_phi {b : P.R.B} {y : Formalism.Per.Acris l}
    (h : T.eB b = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) y) :
    T.eB (P.φB b) = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) (φc l y) := by
  rw [T.frob, h, (GlobalTheory.PMon.Trans.acris_bcris l).2.1]

theorem lift_iter {b : P.R.B} {y : Formalism.Per.Acris l}
    (h : T.eB b = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) y) (j : ℕ) :
    T.eB (P.φB^[j] b) = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) ((φc l)^[j] y) := by
  induction j with
  | zero => exact h
  | succ j ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply']; exact lift_phi T ih

theorem iter_lpow (m j : ℕ) (x : P.R.B) :
    P.φB^[m] ((l : P.R.B) ^ j * x) = (l : P.R.B) ^ j * P.φB^[m] x := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_mul, map_pow, map_natCast]

theorem isUnit_lpow (m : ℕ) : IsUnit ((l : P.R.B) ^ m) := by
  have h : IsUnit (l : ℚ_[l]) := (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero : (l : ℚ_[l]) ≠ 0).isUnit
  have h2 := h.map (algebraMap ℚ_[l] P.R.B)
  rw [map_natCast] at h2
  exact h2.pow m

theorem ratio_integral {h s : ℕ} (hs : s < h) {b b' : P.R.B} {y y' : Formalism.Per.Acris l}
    (hb : T.eB b = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) y)
    (hb' : T.eB b' = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) y')
    (he : P.φB^[h] b = (l : P.R.B) ^ s * b) (he' : P.φB^[h] b' = (l : P.R.B) ^ s * b')
    (h0 : b' ≠ 0) (hr : P.φB b * b' = b * P.φB b') : ∃ c : ℚ_[l], b = c • b' := by
  obtain ⟨hinj, -, hz⟩ := GlobalTheory.PMon.Trans.acris_bcris l
  have e1 : (φc l)^[h] y = (l : Formalism.Per.Acris l) ^ s * y := by
    apply hinj
    rw [← lift_iter T hb, he, map_mul, map_pow, map_natCast, hb, map_mul, map_pow, map_natCast]
  have e2 : (φc l)^[h] y' = (l : Formalism.Per.Acris l) ^ s * y' := by
    apply hinj
    rw [← lift_iter T hb', he', map_mul, map_pow, map_natCast, hb', map_mul, map_pow, map_natCast]
  have e3 : y' ≠ 0 := by
    rintro rfl
    apply h0
    apply T.eB.injective
    rw [hb', map_zero, map_zero]
  have e4 : φc l y * y' = y * φc l y' := by
    apply hinj
    rw [map_mul, map_mul, ← lift_phi T hb, ← lift_phi T hb', ← hb, ← hb', ← map_mul, ← map_mul, hr]
  obtain ⟨c, d, hc, hcd⟩ := ratio_proportional_target l h s hs y y' e1 e2 e3 e4
  have e5 : algebraMap ℚ_[l] P.R.B (c : ℚ_[l]) * b = algebraMap ℚ_[l] P.R.B (d : ℚ_[l]) * b' := by
    apply T.eB.injective
    rw [map_mul, map_mul, T.zB, T.zB, hb, hb', ← hz, ← hz, ← map_mul, ← map_mul, hcd]
  have hc' : (c : ℚ_[l]) ≠ 0 := fun e => hc (Subtype.ext e)
  refine ⟨(c : ℚ_[l])⁻¹ * d, ?_⟩
  rw [Algebra.smul_def, map_mul, mul_assoc, ← e5, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc', map_one, one_mul]

theorem ratio_of_acris : Ratio := by
  intro l _ P AI T h s hs ω ω' hω hω' he he' h0 hr
  obtain ⟨N, x, hx⟩ := hω
  obtain ⟨M, x', hx'⟩ := hω'
  have hb : T.eB ((l : P.R.B) ^ (N + M) * ω) =
      algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) ((l : Formalism.Per.Acris l) ^ M * x) := by
    have e : (l : P.R.B) ^ (N + M) * ω = (l : P.R.B) ^ M * ((l : P.R.B) ^ N * ω) := by ring
    rw [e, map_mul T.eB ((l : P.R.B) ^ M), hx]
    simp only [map_mul, map_pow, map_natCast]
  have hb' : T.eB ((l : P.R.B) ^ (N + M) * ω') =
      algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) ((l : Formalism.Per.Acris l) ^ N * x') := by
    have e : (l : P.R.B) ^ (N + M) * ω' = (l : P.R.B) ^ N * ((l : P.R.B) ^ M * ω') := by ring
    rw [e, map_mul T.eB ((l : P.R.B) ^ N), hx']
    simp only [map_mul, map_pow, map_natCast]
  have hu := isUnit_lpow (P := P) (N + M)
  obtain ⟨c, hc⟩ := ratio_integral T hs hb hb'
    (by rw [iter_lpow, he]; ring) (by rw [iter_lpow, he']; ring)
    (fun e => h0 ((hu.mul_right_eq_zero).1 e))
    (by
      simp only [map_mul, map_pow, map_natCast]
      linear_combination ((l : P.R.B) ^ (N + M)) ^ 2 * hr)
  refine ⟨c, hu.mul_left_cancel ?_⟩
  rw [hc, Algebra.smul_def, Algebra.smul_def]
  ring

end GlobalTheory.PMon.RatioTransport
end

