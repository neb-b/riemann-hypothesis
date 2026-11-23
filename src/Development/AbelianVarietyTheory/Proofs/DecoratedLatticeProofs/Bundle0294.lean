module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StrongApproximationDecomposition
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntSubIsLattice
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1206
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsHermitianAuxiliaryVectorSystemBesselVectors
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0162

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicTranslateOneEqStandardLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.MovesOne

theorem finM_one {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) : finM V hn (1 : GA D V) = 1 := by
  subst hn
  unfold finM Formalism.L2.Theta.mt
  rw [map_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  simp

theorem moves_one : ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n) (N : Submodule (𝓞 D.host.E) (Fin n → D.host.E)),
    Moves V hn 1 N → N = Formalism.L2.Col.stdLat D.host.E n := by
  intro D V n hn N h
  ext x
  rw [h x, inv_one, finM_one, Matrix.one_mulVec]
  simp only [GlobalTheory.SplitDec.rat_int_iff]
  exact ⟨fun hx i _ => hx i, fun hx i => hx i trivial⟩

end GlobalTheory.AdForm.MovesOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicTranslateStandardLatticeIsSelfDual
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.StdMove
variable {D : D7}

theorem moves_exists (V : HSp D) (g : GA D V) : ∃ N, Moves V rfl g N := by
  obtain ⟨Λ, hΛ, -, -, -⟩ := GlobalTheory.AdLat.exists_lattice_latOf D.host.F D.host.E V.rank (GlobalTheory.SplitMove.intSub D V.rank)
    (finHom V g) (GlobalTheory.SplitMove.intSub_fg _) (GlobalTheory.SplitMove.intSub_span _)
  have inv : ∀ y, (finHom V g⁻¹).1 *ᵥ ((finHom V g).1 *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, map_inv, Units.inv_mul, Matrix.one_mulVec]
  have inv' : ∀ y, (finHom V g).1 *ᵥ ((finHom V g⁻¹).1 *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, map_inv, Units.mul_inv, Matrix.one_mulVec]
  have ent : ∀ (x : Fin V.rank → D.host.E) i,
      Algebra.TensorProduct.comm D.host.F (Formalism.L2.Herm.Af D.host.F) D.host.E
        (((finHom V g⁻¹).1 *ᵥ GlobalTheory.AdLat.fv D.host.F x) i) =
      (finM V rfl g⁻¹ *ᵥ fun j => eToEAf D (x j)) i := by
    intro x i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [GlobalTheory.AdForm.finM, Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.reindex_apply,
      finCongr_refl, Equiv.refl_symm, Equiv.coe_refl, Matrix.submatrix_id_id]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
  refine ⟨Λ, fun x => ?_⟩
  rw [← SetLike.mem_coe, hΛ, GlobalTheory.SplitMove.coe_intSub]
  change GlobalTheory.AdLat.fv D.host.F x ∈ (finHom V g).1.mulVec '' _ ↔ _
  constructor
  · rintro ⟨y, hy, hxy⟩ i
    rw [← ent, ← hxy, inv]
    exact (GlobalTheory.SplitMove.hat_intVec_iff D V.rank y).1 hy i
  · intro hx
    refine ⟨(finHom V g⁻¹).1 *ᵥ GlobalTheory.AdLat.fv D.host.F x, (GlobalTheory.SplitMove.hat_intVec_iff D V.rank _).2 fun i => ?_, inv' _⟩
    rw [ent]; exact hx i

theorem isSdLat_of (V : HSp D) (hV : V.gram = 1) (N : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (h : IsSelfDualC V N) : Formalism.L2.Col.IsSdLat N := by
  refine ⟨h.1, ?_⟩
  ext x
  rw [h.2 x]
  simp only [Formalism.HermitianLatticesTheory.IsUnimodular, Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply, Submodule.mem_one]
  refine forall_congr' fun y => imp_congr_right fun _ => ?_
  have e : Formalism.L2.Col.hStd D.host.E V.rank y x = ∑ i, ∑ j, star (y i) * V.gram i j * x j := by
    rw [hV]
    simp [Formalism.L2.Col.hStd, Matrix.one_apply]
  rw [e]

theorem std_moved_lattice : ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n), V.gram = 1 → (∀ g : GA D V, ∃ N, Moves V hn g N) ∧ ∀ (g : GA D V) N, Moves V hn g N → Formalism.L2.Col.IsSdLat N ∧ ∃ Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E), (Λ : Set (Fin V.rank → D.host.E)) = latFr V hn N ∧ IsSelfDualC V Λ := by
  intro D V n hn hV
  subst hn
  refine ⟨fun g => moves_exists V g, fun g N hN => ?_⟩
  have hsd := GlobalTheory.SplitMove.selfDual_move V hV g N hN
  refine ⟨isSdLat_of V hV N hsd, N, ?_, hsd⟩
  ext x
  first | exact Iff.rfl | simp [GlobalTheory.AdForm.latFr]

end GlobalTheory.StdMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AlVEmbHEqNegOneZpow
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SemiTrace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem tauE_star (D : D7) (τ : D.what₂.Tau) (x : D.host.E) :
    tauE D τ (star x) = starRingEnd ℂ (tauE D τ x) :=
  D.sp.cm.cmUnram.2.1 _ x

theorem sum_two_re_tauE (D : D7) (e : D.host.E) :
    ∑ t, (((2 * (tauE D t e).re : ℝ)) : ℂ) = ((Algebra.trace ℚ D.host.E e : ℚ) : ℂ) := by
  classical
  have h1 : ((Algebra.trace ℚ D.host.E e : ℚ) : ℂ) = ∑ σ : D.host.E →+* ℂ, σ e := by
    have := trace_eq_sum_embeddings (K := ℚ) (L := D.host.E) ℂ (x := e)
    rw [eq_ratCast] at this
    rw [this]
    exact (Fintype.sum_equiv (RingHom.equivRatAlgHom D.host.E ℂ) _ _ fun _ => rfl).symm
  have hi := GlobalTheory.StdRat.tauE_injective D
  have hcm := GlobalTheory.StdRat.tauE_cm D
  have hb : Function.Bijective (Sum.elim (tauE D) fun t => ComplexEmbedding.conjugate (tauE D t)) := by
    have hc : ∀ σ : D.host.E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ :=
      fun σ => star_star σ
    constructor
    · rintro (a | a) (b | b) h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
      · rw [hi h]
      · exact absurd ⟨a, h⟩ ((hcm (tauE D b)).1 ⟨b, rfl⟩)
      · exact absurd ⟨b, h.symm⟩ ((hcm (tauE D a)).1 ⟨a, rfl⟩)
      · have := congrArg ComplexEmbedding.conjugate h
        rw [hc, hc] at this
        rw [hi this]
    · intro σ
      by_cases h : ∃ t, tauE D t = ComplexEmbedding.conjugate σ
      · obtain ⟨t, ht⟩ := h
        exact ⟨Sum.inr t, by simp only [Sum.elim_inr]; rw [ht, hc]⟩
      · obtain ⟨t, ht⟩ := (hcm σ).2 h
        exact ⟨Sum.inl t, ht⟩
  have h4 := hb.sum_comp fun σ : D.host.E →+* ℂ => σ e
  rw [Fintype.sum_sum_type, ← h1] at h4
  simp only [Sum.elim_inl, Sum.elim_inr, ComplexEmbedding.conjugate_coe_eq] at h4
  rw [← h4, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Complex.add_conj]

theorem re_xi_mul_sq (u : ℝ) (hu : 0 < u) :
    (Complex.I * ((u⁻¹ : ℝ) : ℂ) * ((1 + Complex.I * (u : ℂ)) / 2) ^ 2).re = -1 / 2 := by
  have h : Complex.I * ((u⁻¹ : ℝ) : ℂ) * ((1 + Complex.I * (u : ℂ)) / 2) ^ 2
      = ((-1 / 2 : ℝ) : ℂ) + Complex.I * (((1 - u ^ 2) / (4 * u) : ℝ) : ℂ) := by
    have hu' : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hu.ne'
    push_cast
    field_simp
    ring_nf
    rw [Complex.I_sq, Complex.I_pow_three]
    ring
  rw [h]
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

end GlobalTheory.SemiTrace

namespace GlobalTheory.SemiTrace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem alV_embH_eq_neg_one_zpow : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (y : Formalism.L2.Col.HomE D.host.E a b) (k : ℤ), (k : ℚ) = Algebra.trace ℚ D.host.E (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 * GlobalTheory.LatVac.hRat S T ((LinearMap.toMatrix' (y)).reindex (finCongr hT.symm) (finCongr hS.symm)) ((LinearMap.toMatrix' (y)).reindex (finCongr hT.symm) (finCongr hS.symm))) → alV D.host.d sc (embH (tauE D) δ y) = (-1 : ℂ) ^ k := by
  intro D ψ θ S T a b hS hT δ sc hP y k hk
  subst hS hT
  have hd : 0 < Real.sqrt D.host.d :=
    Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero D.host.hyp.2.1.ne_zero))
  set M := (LinearMap.toMatrix' y).reindex (finCongr (rfl : T.rank = T.rank).symm) (finCongr (rfl : S.rank = S.rank).symm) with hMdef
  have hMij : ∀ i j, M i j = y (Pi.single j 1) i := by
    intro i j; simp [M, LinearMap.toMatrix'_apply]
  set s : D.what₂.Tau → ℝ := fun τ => ∑ i, ∑ j, Complex.normSq (tauE D τ (M i j)) with hs
  have hh : ∀ τ, tauE D τ (GlobalTheory.LatVac.hRat S T M M) = ((s τ : ℝ) : ℂ) := by
    intro τ
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [GlobalTheory.LatVac.hRat, hP.gS, hP.gT, inv_one, Matrix.one_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_sum, map_mul, tauE_star, hs]
    simp only [apply_ite (⇑(tauE D τ)), map_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, map_mul, tauE_star]
    push_cast
    rw [Finset.sum_comm]
    calc _ = ∑ j, ∑ i, ((Complex.normSq (tauE D τ (M i j)) : ℝ) : ℂ) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_comm]
          simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Complex.normSq_eq_conj_mul_self]
      _ = _ := Finset.sum_comm
  have hτ : ∀ τ, (tauE D τ (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 * GlobalTheory.LatVac.hRat S T M M)).re = -(s τ) / 2 := by
    intro τ
    rw [map_mul, map_mul, map_pow, map_div₀, map_add (f := _), map_one, map_ofNat, hh, hP.xi, Formalism.L2.Theta.tauE_sqrtMinusD,
      Complex.re_mul_ofReal, re_xi_mul_sq _ hd]
    ring
  have hk' : (k : ℂ) = ((-(∑ τ, s τ) : ℝ) : ℂ) := by
    have e1 := sum_two_re_tauE D (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 * GlobalTheory.LatVac.hRat S T M M)
    rw [← hk] at e1
    push_cast at e1
    rw [← e1]
    simp only [hτ]
    push_cast
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    ring
  have hsc : sc * Complex.normSq δ = 2 * (Real.sqrt D.host.d)⁻¹ := by
    rw [← Complex.sq_norm]; exact hP.scale
  have hq : Formalism.L2.Th1.H.qOf (Real.sqrt D.host.d / 2) (HV sc) (embH (tauE D) δ y) = ∑ τ, s τ := by
    simp only [Formalism.L2.Th1.H.qOf, HV, LinearMap.mk₂'ₛₗ_apply, embH, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Complex.mul_conj]
    rw [show ((sc : ℂ) * ∑ x, ∑ x_1, ∑ x_2, ((Complex.normSq (δ * tauE D x (y (Pi.single x_2 1) x_1)) : ℝ) : ℂ)) =
        ((sc * ∑ x, ∑ x_1, ∑ x_2, Complex.normSq (δ * tauE D x (y (Pi.single x_2 1) x_1)) : ℝ) : ℂ) by push_cast; rfl,
      Complex.ofReal_re]
    simp_rw [Complex.normSq_mul, ← Finset.mul_sum]
    simp only [hs, hMij]
    rw [← mul_assoc sc, hsc]
    field_simp
  have hsum : ((∑ τ, s τ : ℝ) : ℂ) = -(k : ℂ) := by rw [hk']; push_cast; ring
  rw [alV, Formalism.L2.Th1.H.alphaQ, hq, hsum,
    show (Real.pi : ℂ) * Complex.I * -(k : ℂ) = ((-k : ℤ) : ℂ) * ((Real.pi : ℂ) * Complex.I) by push_cast; ring,
    Complex.exp_int_mul, Complex.exp_pi_mul_I, _root_.zpow_neg, ← _root_.inv_zpow, inv_neg, inv_one]
end GlobalTheory.SemiTrace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselCharacterLocalElementEqSimpleEntrySum
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LocBesChar
open GlobalTheory.LocFrame (hA hQ besselAuxiliaryVectors IsHermitianAuxiliaryVectorSystem ent colN)
open Finset (range)

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

theorem psiE_ι {ψ : AddChar (AF D.host.F) ℂ} {ψk : AddChar k Circle} (h : p.IsChar ψ ψk) (y : k) :
    psiE ψ (p.ι y) = ψk (y / p.xi) := by
  rw [h]
  congr 1
  have : p.ι y = p.ι (p.π (incA D D.host.xi0 * p.ι (y / p.xi))) := by
    rw [RingHom.map_mul, p.π_ι]
    change _ = p.ι (p.xi * _)
    rw [mul_div_cancel₀ _ (Witness.xi_ne p)]
  rw [this, p.ι_π, mul_left_comm, Witness.e_ι]

theorem psiE_cA (ψ : AddChar (AF D.host.F) ℂ) (x : AE D) : psiE ψ (cA D x) = psiE ψ x := by
  rw [psiE, psiE, GlobalTheory.DualPairCheck.trace_cA]

theorem psiE_supp {ψ : AddChar (AF D.host.F) ℂ} {ψk : AddChar k Circle} (h : p.IsChar ψ ψk) {u : AE D}
    (hu : (p.e + cA D p.e) * u = u) : psiE ψ u = ψk ((p.π u + p.π (cA D u)) / p.xi) := by
  have e : u = p.ι (p.π u) + cA D (p.ι (p.π (cA D u))) := by
    rw [p.ι_π, p.ι_π, RingHom.map_mul, GlobalTheory.DualPairCheck.cA_cA, ← add_mul, hu]
  conv_lhs => rw [e]
  rw [psiE_add, psiE_cA, psiE_ι p h, psiE_ι p h, add_div, AddChar.map_add_eq_mul, Circle.coe_mul]

theorem hA_supp {V : HSp D} {e : AE D} {g : GA D V} (hg : SuppAt e V g) {x y : Fin V.rank → D.host.E} (h : hQ V x y = 0) :
    (e + cA D e) * hA V g x y = hA V g x y := by
  have e1 : hA V g x y = (ratV (star y) ᵥ* gA V) ⬝ᵥ (mt V g - 1) *ᵥ ratV x := by
    rw [← dotProduct_mulVec, mulVec_mulVec, mul_sub, sub_mulVec, dotProduct_sub, ← mt_one V, ← hA, ← hA,
      ← GlobalTheory.LocFrame.incA_hQ, h, map_zero, sub_zero]
  rw [e1]
  simp only [dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have := hg i j
  linear_combination ((ratV (star y) ᵥ* gA V) i * ratV x j) * this

theorem π_hA (V : HSp D) (g : GA D V) (x y : Fin V.rank → D.host.E) :
    p.π (hA V g x y) = (Witness.prH p ∘ (star y ᵥ* V.gram)) ⬝ᵥ (mt V g).map p.π *ᵥ (Witness.prH p ∘ x) := by
  have h1 : ratV (star y) ᵥ* gA V = ratV (star y ᵥ* V.gram) := funext fun i => (RingHom.map_vecMul (incA D) _ _ i).symm
  rw [hA, ← mulVec_mulVec, dotProduct_mulVec, h1, GlobalTheory.LocFrame.map_dot]
  rfl

variable {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem map_mt_inv {V : HSp D} {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k V.rank Y) {g : GA D V} {q : GL Y k}
    (h : (mt V g).map p.π = F.β * q.val * F.γ) : (mt V g⁻¹).map p.π = F.β * (q⁻¹).val * F.γ := by
  have h1 : (mt V g⁻¹).map p.π * (mt V g).map p.π = 1 := by
    rw [← Matrix.map_mul, mt_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : (F.β * q.val * F.γ) * (F.β * (q⁻¹).val * F.γ) = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc F.β (q⁻¹).val, ← Matrix.mul_assoc F.γ, F.γβ, Matrix.one_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc q.val, Units.mul_inv, Matrix.one_mul, F.βγ]
  rw [← Matrix.mul_one ((mt V g⁻¹).map p.π), ← h2, ← Matrix.mul_assoc, ← h, h1, Matrix.one_mul]

theorem col_ne_zero {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k N Y) (j : Y) {t : k} {x : Fin N → k}
    (h : ∀ r, F.β r j = t * x r) : t ≠ 0 := fun e => by
  have h1 := congrFun (congrFun F.γβ j) j
  simp [Matrix.mul_apply, h, e] at h1

section Coef
variable {V X : HSp D} {jX : Matrix (Fin V.rank) (Fin X.rank) D.host.E} {a : ℕ → Fin V.rank → D.host.E}
  {κ : ℕ → D.host.E} {t : ℕ → k} (H : IsHermitianAuxiliaryVectorSystem c V X jX a κ) {M : Matrix (Fin X.rank) n k} {F : Frame k V.rank (n ⊕ Fin c)}
  (hl : ∀ r b, F.β r (Sum.inl b) = (jX.map p.pr * M) r b) (hr : ∀ (i : Fin c) r, F.β r (Sum.inr i) = t i * p.pr (a i r))
include H hl hr

theorem π_coef {g : GA D V} {q : GL (n ⊕ Fin c) k} (h : (mt V g).map p.π = F.β * q.val * F.γ) (i j : Fin c) :
    t j * p.π (hA V g (a j) (a (c - 1 - i))) = p.pr (κ i) * t i * q.val (.inr i) (.inr j) := by
  set u := Witness.prH p ∘ (star (a (c - 1 - i)) ᵥ* V.gram) with hu
  have e1 : t j • (Witness.prH p ∘ a j) = F.β *ᵥ Pi.single (.inr j) 1 := by
    rw [mulVec_single_one]
    exact funext fun r => (hr j r).symm
  have e2 (b : n) : (u ᵥ* F.β) (.inl b) = 0 := by
    have : (u ᵥ* (jX.map (Witness.prH p) * M)) b = 0 := by
      rw [← vecMul_vecMul, show u ᵥ* jX.map (Witness.prH p) = 0 from funext fun s => by
        rw [hu, ← RingHom.map_vecMul, H.perp _ (by omega), Pi.zero_apply, map_zero, Pi.zero_apply], zero_vecMul, Pi.zero_apply]
    rw [← this]
    change ∑ r, u r * F.β r (.inl b) = ∑ r, u r * (jX.map p.pr * M) r b
    exact Finset.sum_congr rfl fun r _ => congrArg (u r * ·) (hl r b)
  have e3 (l : Fin c) : (u ᵥ* F.β) (.inr l) = if l = i then p.pr (κ i) * t i else 0 := by
    have h3 : (u ᵥ* F.β) (.inr l) = t l * Witness.prH p (hQ V (a l) (a (c - 1 - i))) := by
      rw [hQ, dotProduct_mulVec, RingHom.map_dotProduct, dotProduct, Finset.mul_sum]
      change ∑ r, u r * F.β r (.inr l) = _
      refine Finset.sum_congr rfl fun r _ => ?_
      change u r * F.β r (.inr l) = t l * (u r * p.pr (a l r))
      rw [hr]; ring
    rw [h3, H.pair i i.2 l l.2]
    by_cases e : l = i
    · subst e; rw [if_pos rfl, if_pos rfl, mul_comm]; rfl
    · rw [if_neg (fun e' => e (Fin.ext e')), if_neg e, map_zero, mul_zero]
  rw [π_hA, h, ← smul_eq_mul, ← dotProduct_smul, ← mulVec_smul, e1, mulVec_mulVec, Matrix.mul_assoc, F.γβ, Matrix.mul_one,
    ← mulVec_mulVec, dotProduct_mulVec, mulVec_single_one, dotProduct, Fintype.sum_sum_type]
  simp [← hu, e2, e3]

theorem π_simple {g : GA D V} {q : GL (n ⊕ Fin c) k} (h : (mt V g).map p.π = F.β * q.val * F.γ) {i : ℕ} (hi : i + 1 < c)
    {x : k} (hx : p.pr (κ i) * t i = x * t (i + 1)) : p.π (hA V g (a (i + 1)) (a (c - 1 - i))) = x * ent q i := by
  have h1 := π_coef p H hl hr h ⟨i, by omega⟩ ⟨i + 1, hi⟩
  have h2 : t (i + 1) ≠ 0 := col_ne_zero F _ (hr ⟨i + 1, hi⟩)
  rw [ent, dite_eq_left hi]
  refine mul_left_cancel₀ h2 (h1.trans ?_)
  simp only [hx]
  ring

end Coef

def scal {ρ : ℕ} (B : BesLev D ρ) (s : k) (i : ℕ) : k :=
  if i < ρ then s * p.xi ^ (ρ - i) else if i = ρ then s else s * (-p.hz B / p.xi) * (-1 / p.xi) ^ (ρ - 1 - (2 * ρ - i))

theorem scal_lo {ρ : ℕ} (B : BesLev D ρ) (s : k) {i : ℕ} (hi : i < ρ) :
    p.pr (if i = ρ then hQ B.L B.ζ B.ζ else 1) * scal p B s i = p.xi * scal p B s (i + 1) := by
  rw [if_neg hi.ne, show p.pr 1 = 1 from (Witness.prH p).map_one, scal, scal, if_pos hi]
  split_ifs with h1 h2
  · rw [show ρ - i = ρ - (i + 1) + 1 by omega]; ring
  · rw [show ρ - i = 1 by omega]; ring
  · omega

theorem scal_hi {ρ : ℕ} (B : BesLev D ρ) (s : k) {i : ℕ} (hi : ρ ≤ i) (hi' : i < 2 * ρ) :
    p.pr (if i = ρ then hQ B.L B.ζ B.ζ else 1) * scal p B s i = -p.xi * scal p B s (i + 1) := by
  have hx := Witness.xi_ne p
  rw [scal, scal, if_neg (show ¬ i < ρ by omega), if_neg (show ¬ i + 1 < ρ by omega), if_neg (show ¬ i + 1 = ρ by omega)]
  split_ifs with h1
  · rw [show ρ - 1 - (2 * ρ - (i + 1)) = 0 by omega]
    change p.hz B * s = _
    field_simp
  · rw [show ρ - 1 - (2 * ρ - (i + 1)) = ρ - 1 - (2 * ρ - i) + 1 by omega, show p.pr 1 = 1 from (Witness.prH p).map_one, pow_succ]
    field_simp

theorem col_eq {ρ : ℕ} {B : BesLev D ρ} {s : k} {FA : Frame k B.A.rank n} {FV : Frame k B.V.rank (n ⊕ Fin c)}
    (h : p.IsBesFrame B s FA FV) (i : Fin c) (r) :
    FV.β r (Sum.inr i) = scal p B s i * p.pr (besselAuxiliaryVectors B.d (vecB B.o B.ζ) i r) := by
  obtain ⟨hc, -, h1, h2, h3⟩ := h
  have := i.2
  unfold scal besselAuxiliaryVectors
  split_ifs with e1 e2
  · rw [h1 ⟨i, e1⟩ i rfl r, colN, dite_eq_left e1]
  · exact h2 i e2 r
  · have e3 : 2 * ρ - i < ρ := by omega
    rw [h3 ⟨2 * ρ - i, e3⟩ i (by simp only; omega) r, colN, dite_eq_left e3]

theorem psiBes_isLoc : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (σ : ℕ) (B : BesLev D σ) (s : k) (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (FA : Frame k B.A.rank n) (FV : Frame k B.V.rank (n ⊕ Fin c)), p.IsBesFrame B s FA FV → ∀ (g : GA D B.V) (q : GL (n ⊕ Fin c) k), q ∈ N k n c (σ + 1) → p.IsLoc FV g q → psiBes ψ B.d 1 (vecB B.o B.ζ) g = (ψk (GlobalTheory.RootEx.simpleSum q) : ℂ) := by
  intro D k _ _ _ _ p ψ ψk hψ σ B s n _ _ c FA FV hF g q hq hg
  obtain rfl := hF.1
  have H : IsHermitianAuxiliaryVectorSystem (2 * σ + 1) B.V B.A (B.d.i₀ * B.o.iA)
      (besselAuxiliaryVectors B.d (vecB B.o B.ζ)) (fun i => if i = σ then hQ B.L B.ζ B.ζ else 1) := by
    open GlobalTheory.LocFrame in
    exact {
  iso := by
    rw [conjTranspose_mul, Matrix.mul_assoc B.o.iAᴴ, Matrix.mul_assoc B.o.iAᴴ, ← Matrix.mul_assoc _ B.d.i₀, B.d.iso,
      ← Matrix.mul_assoc, B.o.isoA]
  perp := by
    intro i hi
    unfold besselAuxiliaryVectors
    split_ifs with h1 h2
    · rw [colN_eq_mulVec _ h1, ← vecMul_vecMul, perp_of_gram B.d.i₀e, zero_vecMul]
    · rw [vecB, mulVec_mulVec]
      refine perp_of_gram ?_ _
      rw [conjTranspose_mul, Matrix.mul_assoc B.o.iAᴴ, Matrix.mul_assoc B.o.iAᴴ, ← Matrix.mul_assoc _ B.d.i₀, B.d.iso,
        ← Matrix.mul_assoc, B.o.orth']
    · rw [colN_eq_mulVec _ (show 2 * σ - i < σ by omega), ← vecMul_vecMul, perp_of_gram B.d.i₀e', zero_vecMul]
  pair := by
    intro i hi l hl
    unfold besselAuxiliaryVectors
    rcases lt_trichotomy l σ with h | h | h <;> rcases lt_trichotomy i σ with h' | h' | h'
    · rw [if_pos h, if_neg (by omega), if_neg (by omega), hQ_XY B.d h (by omega), if_neg h'.ne]
      exact if_congr (by omega) rfl rfl
    · rw [if_pos h, if_neg (by omega), if_pos (by omega), wittDecomposition_hermitian_e_anisotropicPart B.d h, if_neg (by omega)]
    · rw [if_pos h, if_pos (by omega), hQ_XX B.d h (by omega), if_neg (by omega)]
    · rw [if_neg (by omega), if_pos h, if_neg (by omega), if_neg (by omega), hQ_0Y B.d (by omega), if_neg (by omega)]
    · rw [if_neg (by omega), if_pos h, if_neg (by omega), if_pos (by omega), hQ_vecB B.d B.o, if_pos (by omega), if_pos h']
    · rw [if_neg (by omega), if_pos h, if_pos (by omega), hQ_0X B.d (by omega), if_neg (by omega)]
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), hQ_YY B.d (by omega) (by omega),
        if_neg (by omega)]
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega), wittDecomposition_hermitian_dual_anisotropicPart B.d (by omega),
        if_neg (by omega)]
    · rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), hQ_YX B.d (by omega) (by omega), if_neg h'.ne']
      exact if_congr (by omega) rfl rfl
  ne := by
    intro i _
    split_ifs
    exacts [B.line.2, one_ne_zero]
  card := by have := B.d.rank_add; have := B.o.rank_add; have := B.line.1; omega
    }
  have hx := Witness.xi_ne p
  rw [psiBes, map_one, one_mul, GlobalTheory.LocFrame.simpleSum_eq_sum_hA, psiE_supp p hψ, GlobalTheory.LocFrame.simpleSum_eq_sum_ent]
  · congr 2
    set_option synthInstance.maxHeartbeats 100000 in
      rw [div_eq_iff hx, show 2 * σ + 1 - 1 = σ + σ by omega, Finset.sum_range_add, add_mul, map_sum, map_sum, map_sum,
      Finset.sum_mul, ← Finset.sum_range_reflect (fun i => ent q (σ + i)), Finset.sum_mul]
    congr 1
    · refine Finset.sum_congr rfl fun i hi => ?_
      have hi' := Finset.mem_range.1 hi
      have h1 := π_simple p H hF.2.1 (col_eq p hF) hg.2 (i := i) (by omega) (scal_lo p B s hi')
      rw [show σ + σ - i = 2 * σ + 1 - 1 - i by omega, h1, mul_comm]
    · refine Finset.sum_congr rfl fun i hi => ?_
      have hi' := Finset.mem_range.1 hi
      have h1 := π_simple p H hF.2.1 (col_eq p hF) (map_mt_inv p FV hg.2) (i := σ + (σ - 1 - i)) (by omega)
        (scal_hi p B s (by omega) (by omega))
      rw [show 2 * σ + 1 - 1 - (σ + (σ - 1 - i)) = i + 1 by omega, show σ + (σ - 1 - i) + 1 = σ + σ - i by omega,
        GlobalTheory.LocFrame.ent_inv hq] at h1
      rw [GlobalTheory.LocFrame.cA_hA, h1]
      ring
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => hA_supp hg.1 ?_
    have hi' := Finset.mem_range.1 hi
    rw [H.pair i (by omega) _ (by omega), if_neg (by omega)]

end GlobalTheory.LocBesChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmulMemPerOOfMemHalfBO
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfBCMul

theorem cmul_mem_perO_of_mem_halfBO : ∀ (D : D7) (a b : ℕ) (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (c : ℕ), 0 < c → ∀ y ∈ halfBO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, (c : D.host.E) • y ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' := by
  intro D a b N N' SS c hc y hy
  have h1 := GlobalTheory.CommonReps.natsmul_mem_twO _ c (expS SS) (fun _ => 0) (fun Q => by
    unfold expS; split_ifs <;> omega) hy
  rw [GlobalTheory.CommonReps.mem_twO_zero] at h1
  have e : ((c : 𝓞 D.host.E) • y) = (c : D.host.E) • y := by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  rwa [e] at h1

end GlobalTheory.HalfBCMul
end

