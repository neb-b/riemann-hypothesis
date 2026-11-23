module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0672
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0673
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0686
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0664
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0661
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0682
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0709
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0674
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0689
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0659
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0081
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelLossDegreeBounds
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Formalism.LocalRingCardinality.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0715
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNilpotentOfIsNilDP
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer.TaylorCore

open GlobalTheory.PeriodFamily GlobalTheory.CatCoh

theorem isNilpotent_of_isNilDP {D : Type} [CommRing D] {J : Ideal D} {κ : DividedPowers J} (h : IsNilDP κ) : IsNilpotent J := by
  obtain ⟨N, hN⟩ := h
  have key : ∀ (n : ℕ) (l : List D), (∀ x ∈ l, x ∈ J) → N ≤ l.length + n → ∀ y ∈ J ^ n, l.prod * y = 0 := by
    intro n
    induction n with
    | zero =>
      intro l hl hn y _
      have := hN (l.map fun x => (1, x)) (by simpa using hl) (by simpa [Function.comp_def] using hn)
      rw [List.map_map, List.map_congr_left (f := (fun p : ℕ × D ↦ κ.dpow p.1 p.2) ∘ fun x ↦ (1, x)) (g := id)
        fun x hx => κ.dpow_one (hl x hx), List.map_id] at this
      rw [this, zero_mul]
    | succ n ih =>
      intro l hl hn y hy
      rw [pow_succ'] at hy
      refine Submodule.mul_induction_on hy (fun a ha b hb => ?_) fun a b ha hb => by rw [mul_add, ha, hb, add_zero]
      have := ih (a :: l) (by simpa [ha] using hl) (by simp; omega) b hb
      rw [List.prod_cons] at this
      linear_combination this
  exact ⟨N, eq_bot_iff.2 fun y hy => by simpa using key N [] (by simp) (by simp) y hy⟩

def tayHom {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D)
    (ht : ∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) {V : Opens (I → ℂ)} (h0 : (0 : I → ℂ) ∈ V) : Hol V →+* D where
  toFun f := PeriodFamily.taylor N t f.fn
  map_one' := by
    rw [(taylor_formal_properties N t).2.2.2.1 _ (fun _ => 1) (by
      filter_upwards [V.isOpen.mem_nhds h0] with z hz using by rw [← Hol.ev_apply z hz, map_one]),
      (taylor_formal_properties N t).2.2.1, map_one]
  map_zero' := by
    rw [(taylor_formal_properties N t).2.2.2.1 _ (fun _ => 0) (by
      filter_upwards [V.isOpen.mem_nhds h0] with z hz using by rw [← Hol.ev_apply z hz, map_zero]),
      (taylor_formal_properties N t).2.2.1, map_zero]
  map_mul' f f' := by
    rw [(taylor_formal_properties N t).2.2.2.1 _ (fun z => f.fn z * f'.fn z) (by
      filter_upwards [V.isOpen.mem_nhds h0] with z hz using Hol.fn_mul _ _ hz),
      taylor_mul_of_prod_eq_zero N t ht _ _ (f.analytic _ h0) (f'.analytic _ h0)]
  map_add' f f' := by
    rw [(taylor_formal_properties N t).2.2.2.1 _ (fun z => f.fn z + f'.fn z) (by
      filter_upwards [V.isOpen.mem_nhds h0] with z hz using Hol.fn_add _ _ hz),
      (taylor_formal_properties N t).1 _ _ (f.analytic _ h0) (f'.analytic _ h0)]

theorem ev_red {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {W : Opens E} {D : Type} [CommRing D] [Algebra ℂ D]
    (π : D →ₐ[ℂ] ℂ) (p : E) (hp : p ∈ W) (x : D ⊗[ℂ] Hol W) :
    Hol.ev p hp (Algebra.TensorProduct.lift ((Algebra.ofId ℂ (Hol W)).comp π) (AlgHom.id ℂ (Hol W))
      (fun _ _ ↦ Commute.all _ _) x) =
    π (Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul d c =>
    simp only [Algebra.TensorProduct.lift_tmul, map_mul, AlgHom.comp_apply, AlgHom.id_apply, Algebra.ofId_apply,
      AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]

theorem main : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {F₀ : Fam Empty g Λ} {B : Type} [CommRing B] {X X₀ : Scheme.{0}} {s : X ⟶ Sp B} {s₀ : X₀ ⟶ Sp ℂ} {σ : B →+* Hol F.V} (e : Unif F s σ) (e₀ : Unif F₀ s₀ (algebraMap ℂ (Hol F₀.V))), X.IsSeparated → X₀.IsSeparated → (0 : I → ℂ) ∈ F.V → (∃ z, z ∈ F₀.V) → (∀ l z, F₀.τ l z = F.τ l 0) → ∀ (φ₀ : X₀ ⟶ X), (∀ p : Tot Empty g, p.1 ∈ F₀.V → e₀.E p ≫ φ₀ = e.E (0, p.2)) → ∀ (D : Type) [CommRing D] [Algebra ℂ D] (π : D →+* ℂ) (κ : DividedPowers (RingHom.ker π)), IsNilDP κ → (∀ a : ℂ, π (algebraMap ℂ D a) = a) → ∀ (N : ℕ) (t : I → D), (∀ i, π (t i) = 0) → (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ (j : B →+* D), (∀ b, j b = GlobalTheory.PeriodFamily.taylor N t (σ b).fn) → ∀ (s' : X₀ ⟶ Sp D), s' = s₀ ≫ spMap π → ∀ (n : IsMor (dp0 B) s κ s' j φ₀) (φ : X₀ ⟶ X₀), φ = 𝟙 X₀ → ∀ (k : IsMor (dp0 ℂ) s₀ κ s' (algebraMap ℂ D) φ) (c : FirstDeRham s) (per : Λ →+ Hol F.V), IsPeriod e c per → ∀ (m : ℕ) (d : Fin m → D) (cs : Fin m → FirstDeRham s₀) (p : Fin m → Λ → ℂ) (ps : Fin m → Λ →+ Hol F₀.V), (∀ i l, ps i l = algebraMap ℂ _ (p i l)) → (∀ i, IsPeriod e₀ (cs i) (ps i)) → n.pull1 c = ∑ i, d i • k.pull1 (cs i) → ∀ l, ∑ i, d i * algebraMap ℂ D (p i l) = GlobalTheory.PeriodFamily.taylor N t (per l).fn := by
  intro I _ _ g Λ _ F F₀ B _ X X₀ s s₀ σ e e₀ hX hX₀ h0 hV₀ hτ φ₀ hφ₀ D _ _ π κ hκ hπ N t ht htN j hj s' hs' n φ hφ k c per hper
    m d cs p ps hps hcs hdec l
  let πa : D →ₐ[ℂ] ℂ := { π with commutes' := hπ }
  obtain ⟨D', _, _, io, π', nn, hio, hpio, hnil, hn0, hn2, hnt⟩ := SquareZeroSum.exists_sum_sq_zero N D πa t
    (isNilpotent_of_isNilDP hκ) ht htN
  obtain ⟨M, hM⟩ := id hnil
  have hJ : ∀ s : Fin (N + M + 1) → D', (∀ a, s a ∈ RingHom.ker π') → ∏ a, s a = 0 := fun s hs => by
    have h1 : ∏ a, s a ∈ ∏ _a : Fin (N + M + 1), RingHom.ker π' := Ideal.prod_mem_prod fun a _ => hs a
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
    have h2 := Ideal.pow_le_pow_right (show M ≤ N + M + 1 by omega) h1
    rwa [hM, Ideal.zero_eq_bot, Ideal.mem_bot] at h2
  have ht0 : ∀ i, π' (io (t i)) = 0 := fun i => (hpio _).trans (ht i)
  have ht' : ∀ s : Fin (N + M + 1) → I, ∏ a, io (t (s a)) = 0 := fun s => hJ _ fun a => ht0 _
  have hT : ∀ f, PeriodFamily.taylor (N + M) (fun i => io (t i)) f = io (PeriodFamily.taylor N t f) := fun f => by
    rw [← (taylor_formal_properties (N + M) t).2.2.2.2.1 D' io f, taylor_eq_of_le N t htN _ (Nat.le_add_right _ _)]
  have hred : ∀ f, π' (PeriodFamily.taylor (N + M) (fun i => io (t i)) f) = f 0 := fun f => by
    have h1 : PeriodFamily.taylor (N + M) (fun i => io (t i)) f - algebraMap ℂ D' (f 0) ∈ RingHom.ker π' :=
      (Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact ht0 i)) ((taylor_formal_properties (N + M) _).2.2.2.2.2 f)
    rw [RingHom.mem_ker, map_sub, sub_eq_zero, AlgHom.commutes] at h1
    exact h1
  obtain ⟨K₀, K, ν, hrich, hK₀, hK, hW, hν⟩ := ChartPair.exists_pair e₀ e (fun _ => 0) analyticOnNhd_const (fun _ _ => h0)
    LinearMap.id (AddMonoidHom.id Λ) fun l z _ => (hτ l z).symm
  obtain ⟨r₀, hr₀, -⟩ := exists_real_isFor e₀ hX₀ K₀ hK₀
  obtain ⟨r, hr, -⟩ := exists_real_isFor e hX K hK
  choose Ta hTa hTd using fun k => TaylorHom.exists_taylor_algHom (N + M) (fun i => io (t i)) ht' (K.W (ν k)) (K₀.W k) (hW k)
  let τV : Hol F.V →+* D' := tayHom (N + M) (fun i => io (t i)) ht' h0
  have hfam := TenFam.main π' r₀ rfl κ hs' (io : D →+* D') hpio hnil K r ν hν Ta τV
    (fun k f => tensor_hol_ext_of_values _ _ _ _ fun q hq => by
      rw [hTa k _ q hq, Algebra.TensorProduct.lift_tmul, map_one, _root_.mul_one]
      refine (taylor_formal_properties _ _).2.2.2.1 _ _ ?_
      have hc : Continuous fun z : I → ℂ => ((z, q.2) : Tot I g) := by fun_prop
      filter_upwards [hc.continuousAt.preimage_mem_nhds ((K.W (ν k)).isOpen.mem_nhds (hW k q hq))] with z hz
      exact K.fn_cst _ f hz)
    hTd (fun l k' k h₀ => close_paramTaylor_shift F F₀ h0 hτ _ (N + M) hJ _ N nn hn0 hn2 hnt K K₀ l _ _ k k' (hν l k' k h₀) h₀
      (hW k') (Ta k) (Ta k') (hTa k) (hTa k')) φ₀
    (fun k => point_hol_ext_of_isSeparated _ hX _ _ fun q hq => by
      rw [← Category.assoc, ← Category.assoc, hr₀ k q hq, hφ₀ q (K₀.base k q hq), ← hr (ν k) (0, q.2) (hW k q hq),
        ← Cris.spMap_comp]
      refine congrArg (fun ψ => spMap ψ ≫ r.x (ν k)) (RingHom.ext fun h => ?_)
      refine (ev_red π' q hq (Ta k h)).trans ?_
      rw [hTa k h q hq, hred]
      exact (Hol.ev_apply _ _ _).symm)
    j n (fun b => (congrArg io (hj b)).trans (hT _).symm) c per (τV.toAddMonoidHom.comp per) (fun _ => rfl) (hper K r hr)
  obtain ⟨z₀, hz₀⟩ := hV₀
  let q : Fin m → Λ →+ D' := fun i => ((algebraMap ℂ D').comp (Hol.ev z₀ hz₀).toRingHom).toAddMonoidHom.comp (ps i)
  have hq : ∀ i l, q i l = algebraMap ℂ D' (p i l) := fun i l =>
    congrArg (algebraMap ℂ D') ((congrArg (Hol.ev z₀ hz₀) (hps i l)).trans ((Hol.ev z₀ hz₀).commutes _))
  have hfib := fun i => TenFib.ten_fib π' r₀ rfl κ hs' (io : D →+* D') hpio hnil (algebraMap ℂ D) φ hφ k io.commutes (cs i) (p i)
    (ps i) (q i) (hps i) (hq i) (hcs i K₀ r₀ hr₀)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hdec, map_sum] at hfam
  simp only [LinearMap.map_smulₛₗ, hfib] at hfam
  have hz : K₀.tenZ (∑ i, io (d i) • q i - τV.toAddMonoidHom.comp per) =
      ∑ i, io (d i) • K₀.tenZ (q i) - K₀.tenZ (τV.toAddMonoidHom.comp per) := by
    let Z : (Λ →+ D') →ₗ[D'] Z1 (K₀.Ten D') :=
      { toFun := K₀.tenZ
        map_add' := fun a b => Subtype.ext (by funext T T' f; exact map_add (algebraMap D' (T'.ten D')) _ _)
        map_smul' := fun a b => Subtype.ext (by
          funext T T' f
          exact (map_mul (algebraMap D' (T'.ten D')) _ _).trans (Algebra.smul_def _ _).symm) }
    change Z _ = ∑ i, io (d i) • Z _ - Z _
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub, map_sum, map_smul]
  have := Charts.tenZ_eq_zero K₀ hrich ⟨z₀, hz₀⟩ (∑ i, io (d i) • q i - τV.toAddMonoidHom.comp per) (by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hz, map_sub, ← hfam, map_sum]
    simp only [map_smul]
    exact sub_self _)
  have h1 := DFunLike.congr_fun (sub_eq_zero.1 this) l
  refine hio ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hT, map_sum]
  refine Eq.trans ?_ h1
  change _ = (AddMonoidHom.eval l) (∑ i, io (d i) • q i)
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by
    change io (d i * algebraMap ℂ D (p i l)) = (io (d i) • q i) l
    rw [map_mul, io.commutes, AddMonoidHom.smul_apply, hq, smul_eq_mul]

end GlobalTheory.AnPer.TaylorCore
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitNormOne
section
noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace GlobalTheory.PlaneNorm

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def gram2E (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x z : Fin M → E) : E :=
  hE σ J x x * hE σ J z z - hE σ J x z * hE σ J z x

def gram2R (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (a b : Fin M → R ⊗[F] E) : R ⊗[F] E :=
  hR R σ J a a * hR R σ J b b - hR R σ J a b * hR R σ J b a

def IsUnitNorm (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (a : R ⊗[F] E) : Prop :=
  ∃ s : R ⊗[F] E, IsUnit s ∧ s * sigR R σ s = a

theorem IsUnitNorm.isUnit {R : Type} [CommRing R] [Algebra F R] {σ : E →ₐ[F] E} {a : R ⊗[F] E}
    (h : IsUnitNorm R σ a) : IsUnit a := by
  obtain ⟨s, hs, rfl⟩ := h
  exact hs.mul (hs.map (sigR R σ))

end GlobalTheory.PlaneNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetOperatorCharacterScaledTable
section
open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.JetCharScale

variable {K : Type} [Field K]

def scaleVar {σ : Type} (u : σ → K) : MvPolynomial σ K →ₐ[K] MvPolynomial σ K := aeval fun v => C (u v) * X v

theorem scaleVar_monomial {σ : Type} (u : σ → K) (m : σ →₀ ℕ) (c : K) :
    scaleVar u (monomial m c) = (m.prod fun v e => u v ^ e) • monomial m c := by
  rw [scaleVar, aeval_monomial, smul_eq_C_mul, monomial_eq]
  simp only [mul_pow, Finsupp.prod, Finset.prod_mul_distrib, map_prod, map_pow, algebraMap_eq]
  ring

variable {ι : Type} {a b : ℕ}

theorem jetLin_monomial (J : (DVar ι a b →₀ ℕ) → K) (m : (ι × Fin b × Fin b) ⊕ DVar ι a b →₀ ℕ) :
    jetLin J (monomial m 1) = monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn)
      (J (m.comapDomain Sum.inr Sum.inr_injective.injOn)) := by
  have := (basisMonomials ((ι × Fin b × Fin b) ⊕ DVar ι a b) K).constr_basis K (fun m =>
    (monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn) (J (m.comapDomain Sum.inr Sum.inr_injective.injOn)) : Pol K ι b)) m
  rw [coe_basisMonomials] at this
  exact this

theorem subD_scale (w : ι → K) (P : Pol K ι a) :
    scaleVar (Sum.elim (fun _ => 1) fun k => w k.1) (subD K ι a b P) =
      scaleVar (Sum.elim (fun v => w v.1) fun _ => 1) (subD K ι a b P) := by
  refine AlgHom.congr_fun (φ₁ := (scaleVar _).comp (subD K ι a b)) (φ₂ := (scaleVar _).comp (subD K ι a b))
    (MvPolynomial.algHom_ext fun v => ?_) P
  simp only [AlgHom.comp_apply, subD, aeval_X]
  split_ifs with h
  · set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, scaleVar, aeval_X, Sum.elim_inl, Sum.elim_inr, map_one]
    refine Finset.sum_congr rfl fun β _ => ?_
    ring
  · simp

variable [Fintype ι]

theorem jetLin_right (J : (DVar ι a b →₀ ℕ) → K) (w : ι → K) (c : K)
    (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) :
    jetLin (fun m => c * ((m.prod fun v e => w v.1 ^ e) * J m)) Q =
      c • jetLin J (scaleVar (Sum.elim (fun _ => 1) fun k => w k.1) Q) := by
  refine LinearMap.congr_fun (g := c • (jetLin J ∘ₗ (scaleVar (Sum.elim (fun _ => 1) fun k => w k.1)).toLinearMap))
    ((basisMonomials _ K).ext fun m => ?_) Q
  rw [coe_basisMonomials]
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  rw [scaleVar_monomial, map_smul, jetLin_monomial, jetLin_monomial, smul_monomial, smul_monomial, smul_eq_mul, smul_eq_mul,
    Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp), Fintype.prod_sum_type]
  simp

theorem jetLin_left (J : (DVar ι a b →₀ ℕ) → K) (w : ι → K)
    (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) :
    jetLin J (scaleVar (Sum.elim (fun v => w v.1) fun _ => 1) Q) = scaleVar (fun v => w v.1) (jetLin J Q) := by
  induction Q using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | monomial m c =>
    have e : (monomial m c : MvPolynomial _ K) = c • monomial m 1 := by rw [smul_monomial, smul_eq_mul, mul_one]
    rw [e, map_smul, map_smul, map_smul, map_smul, scaleVar_monomial, map_smul, jetLin_monomial, scaleVar_monomial,
      Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp), Fintype.prod_sum_type]
    simp

theorem jetMap_scale (J : (DVar ι a b →₀ ℕ) → K) (w : ι → K) (c : K) (n : ι → ℕ) (P : Pol K ι a) :
    jetMap (fun m => c * ((m.prod fun v e => w v.1 ^ e) * J m)) n P = c • scaleVar (fun v => w v.1) (jetMap J n P) := by
  simp only [jetMap, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  rw [jetLin_right, subD_scale, jetLin_left]

theorem scaleVar_hom [DecidableEq ι] (w : ι → K) (d : ι → ℕ) {Q : Pol K ι b}
    (hQ : ∀ τ, IsWeightedHomogeneous (GlobalTheory.JetDeg.posW b τ) Q (d τ)) :
    scaleVar (fun v => w v.1) Q = (∏ τ, w τ ^ d τ) • Q := by
  conv_lhs => rw [Q.as_sum]
  conv_rhs => rw [Q.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [scaleVar_monomial, Finsupp.prod_fintype _ _ (by simp), Fintype.prod_prod_type]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  have h := hQ τ (mem_support_iff.mp hm)
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_prod_type, Finset.sum_eq_single τ] at h
  · rw [← h]
    simp [GlobalTheory.JetDeg.posW, Finset.prod_pow_eq_pow_sum]
  · intro x _ hx
    simp [GlobalTheory.JetDeg.posW, hx]
  · simp

theorem jetOp_scale : ∀ {ι : Type} [Fintype ι] {a b : ℕ} (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (n : ι → ℕ)
    (J : (Formalism.L2.Ker.DVar ι a b →₀ ℕ) → ℂ) (w : ι → ℂ) (c : ℂ), Formalism.L2.Ker.JetInVV ℂ lam lam' n →
    Formalism.L2.Ker.jetOp lam lam' (fun m => c * ((m.prod fun v e => w v.1 ^ e) * J m)) n =
      (c * ∏ τ, w τ ^ (∑ i, (lam' τ).natW i)) • Formalism.L2.Ker.jetOp lam lam' J n := by
  classical
  intro ι _ a b lam lam' n J w c hV
  refine LinearMap.ext fun P => ?_
  simp only [jetOp, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.subtype_apply]
  rw [jetMap_scale, scaleVar_hom w _ fun τ => GlobalTheory.JetDeg.VV_hom lam' τ (hV J P P.2), smul_smul, map_smul]

end GlobalTheory.JetCharScale

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviRestrictionVanishingPreservedByOperator
section
open NumberField MeasureTheory GlobalTheory.CuspRep

noncomputable section

namespace GlobalTheory.LeviDeriv

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a r : ℕ}

theorem block_mul {R : Type} [CommRing R] {M N : Matrix (Fin a) (Fin a) R}
    (hM : ∀ i j : Fin a, ((i : ℕ) < r ↔ (j : ℕ) < r) ∨ M i j = 0)
    (hN : ∀ i j : Fin a, ((i : ℕ) < r ↔ (j : ℕ) < r) ∨ N i j = 0) :
    ∀ i j : Fin a, ((i : ℕ) < r ↔ (j : ℕ) < r) ∨ (M * N) i j = 0 := by
  intro i j
  by_cases h : ((i : ℕ) < r ↔ (j : ℕ) < r)
  · exact Or.inl h
  · right
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases hM i k with h1 | h1
    · rcases hN k j with h2 | h2
      · exact absurd (h1.trans h2) h
      · rw [h2, mul_zero]
    · rw [h1, zero_mul]

theorem block_infGL (y : GL (Fin a) (Cinf E))
    (hy : ∀ i j : Fin a, ((i : ℕ) < r ↔ (j : ℕ) < r) ∨ (y : Matrix (Fin a) (Fin a) (Cinf E)) i j = 0) :
    ∀ i j : Fin a, ((i : ℕ) < r ↔ (j : ℕ) < r) ∨ (infGL E a y : Matrix (Fin a) (Fin a) (Ad E)) i j = 0 := by
  intro i j
  by_cases h' : ((i : ℕ) < r ↔ (j : ℕ) < r)
  · exact Or.inl h'
  · right
    have h := (hy i j).resolve_left h'
    have hij : i ≠ j := fun e => h' (by rw [e])
    change (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sInf E ((1 : Matrix (Fin a) (Fin a) (Cinf E)) i j) +
      sInf E ((y : Matrix (Fin a) (Fin a) (Cinf E)) i j) = 0
    rw [h, Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, map_zero, sub_zero, zero_add]

theorem lieD_single_blkGL (hr : r ≤ a) (f : Sm E a)
    (hf : ∀ (m₁ : GA E r) (m₂ : GA E (a - r)), f.1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)) = 0)
    (i j : Fin a) (hij : (i : ℕ) < r ↔ (j : ℕ) < r) (x : Cinf E) (m₁ : GA E r) (m₂ : GA E (a - r)) :
    lieD (toL (Matrix.single i j x)) f.1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)) = 0 := by
  set m := GlobalTheory.LeviGA.blkGL hr (m₁, m₂)
  set X : Lie E a := toL (Matrix.single i j x)
  have hz : ∀ t : ℝ, chart f.1 m (oneL E a + t • X) = 0 := by
    intro t
    unfold chart
    split_ifs with hu
    · have hyb : ∀ k l : Fin a, ((k : ℕ) < r ↔ (l : ℕ) < r) ∨
          ((hu.unit : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) k l = 0 := by
        intro k l
        rw [hu.unit_spec]
        by_cases hkl : ((k : ℕ) < r ↔ (l : ℕ) < r)
        · exact Or.inl hkl
        · right
          have hne : k ≠ l := fun e => hkl (by rw [e])
          have hs : Matrix.single i j x k l = 0 := by
            rw [Matrix.single_apply]
            rw [if_neg]
            rintro ⟨e1, e2⟩
            exact hkl (by rw [← e1, ← e2]; exact hij)
          change (1 : Matrix (Fin a) (Fin a) (Cinf E)) k l + t • Matrix.single i j x k l = 0
          rw [hs, Matrix.one_apply_ne hne, smul_zero, add_zero]
      obtain ⟨p, hp⟩ := GlobalTheory.LeviGA.exists_blkGL hr (m * infGL E a hu.unit)
        (by rw [Units.val_mul]; exact block_mul (GlobalTheory.LeviGA.blkGL_block hr _) (block_infGL _ hyb))
      rw [← hp]
      exact hf p.1 p.2
    · rfl
  have hline : HasDerivAt (fun t : ℝ => oneL E a + t • X) X 0 := by
    have := ((hasDerivAt_id' (0 : ℝ)).smul_const X).const_add (oneL E a)
    rwa [one_smul] at this
  have hd : HasFDerivAt (chart f.1 m) (fderiv ℝ (chart f.1 m) (oneL E a)) (oneL E a + (0 : ℝ) • X) := by
    rw [zero_smul, add_zero]
    exact (differentiableAt_chart f.2 m).hasFDerivAt
  have h1 := hd.comp_hasDerivAt (0 : ℝ) hline
  have h2 : HasDerivAt (chart f.1 m ∘ fun t : ℝ => oneL E a + t • X) 0 0 := by
    have e : (chart f.1 m ∘ fun t : ℝ => oneL E a + t • X) = fun _ => 0 := funext hz
    rw [e]
    exact hasDerivAt_const _ _
  exact h1.unique h2

theorem Eop_blkGL_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) (hr : r ≤ a)
    (f : Sm E a), (∀ (m₁ : GA E r) (m₂ : GA E (a - r)), f.1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)) = 0) →
    ∀ (τ : E →+* ℂ) (i j : Fin a), ((i : ℕ) < r ↔ (j : ℕ) < r) → ∀ (m₁ : GA E r) (m₂ : GA E (a - r)),
      (Eop τ i j f).1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)) = 0 := by
  intro E _ _ _ a r hr f hf τ i j hij m₁ m₂
  have k := fun x => lieD_single_blkGL hr f hf i j hij x m₁ m₂
  change (1 / 2 : ℂ) * ((lieS E a i j (atEmb τ 1) f).1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂)) -
    Complex.I * (lieS E a i j (atEmb τ Complex.I) f).1 (GlobalTheory.LeviGA.blkGL hr (m₁, m₂))) = 0
  rw [lieS_apply, lieS_apply, lie_apply, lie_apply, k, k]
  simp

end GlobalTheory.LeviDeriv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LossBoundNonneg
section
noncomputable section

namespace GlobalTheory.LossItemsCompare

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.HCEntries

section Programme

variable {l d : ℕ} [NeZero d]

end Programme

section Point

variable {D : D7} {L : SizeData₂ D} {X : ErrX D} {K : Consts} {c : ErrC}

theorem cube_le_eta (P : ParameterChoice' D L) : 4 * (D.R.N D.R.m : ℝ) ^ 3 + 6 ≤ L.etaSz := by
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by have := D.R.two_le_m; omega : 1 ≤ D.R.m)
  have a1 := P.h0_ge.2.2.2.2.1
  have a2 : LevelStarExponents.h0 L ≤ L.etaSz := div_le_self L.etaSz_pos.le hm
  linarith [one_le_letterBlockLength D]

end Point

section Family

variable {eps : ℝ} (Fm : FamP eps)

end Family

end GlobalTheory.LossItemsCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotMemHalfLatticeOfOddMultiplier
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology ComplexConjugate

namespace GlobalTheory.CMModel

theorem mem_lattice_of_even_kerReps :
    ∀ (L : PeriodPair) (α a : ℂ) (S : Finset ℂ), α ≠ 0 → MulStable L α → IsKerReps L α S →
      Even S.card → α * a ∈ L.lattice → 2 * a ∈ L.lattice → a ∈ L.lattice := by
  intro L α a S hα hst hS hev h1 h2
  obtain ⟨m, hm⟩ := hev
  have hc := kerRepsCard L α S hα hst hS
  obtain ⟨t, n, ht, -, -⟩ := mulStableIntegral L α hst
  have hN : α * conj α = 2 * (m : ℂ) + 1 := by
    rw [Complex.mul_conj, ← hc, hm]
    push_cast
    ring
  have key : a = t • (α * a) - α * (α * a) - m • (2 * a) := by
    rw [zsmul_eq_mul, nsmul_eq_mul, ← ht]
    linear_combination (-a) * hN
  rw [key]
  exact sub_mem (sub_mem (zsmul_mem h1 t) (hst _ h1)) (nsmul_mem h2 m)

end GlobalTheory.CMModel
end

