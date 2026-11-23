module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeAlgebraMapOC
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0232
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0236
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0233
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0239

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisOfSubmodule
section
noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

namespace GlobalTheory.Cyc.LatBasis

variable {l : ℕ} [Fact l.Prime]

theorem exists_basis_of_submodule {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V]
    [IsScalarTower ℤ_[l] ℚ_[l] V] (S : Submodule ℤ_[l] V) [Module.Free ℤ_[l] S]
    [Module.Finite ℤ_[l] S] (hS : ∀ x : V, ∃ y : ℤ_[l], y ≠ 0 ∧ y • x ∈ S) :
    ∃ (n : ℕ) (w : Module.Basis (Fin n) ℚ_[l] V), ∀ x : V, x ∈ S ↔ ∀ i, ‖w.repr x i‖ ≤ 1 := by
  let b := Module.finBasis ℤ_[l] S
  have hli : LinearIndependent ℤ_[l] (fun i => (b i : V)) :=
    b.linearIndependent.map' S.subtype (Submodule.ker_subtype S)
  have hli' : LinearIndependent ℚ_[l] (fun i => (b i : V)) :=
    (LinearIndependent.iff_fractionRing ℤ_[l] ℚ_[l]).1 hli
  have hsum : ∀ t : S, (t : V) = ∑ i, ((b.repr t i : ℤ_[l]) : ℚ_[l]) • (b i : V) := by
    intro t
    conv_lhs => rw [← b.sum_repr t]
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, ← algebraMap_smul ℚ_[l]]
    rfl
  have hsp : ⊤ ≤ Submodule.span ℚ_[l] (Set.range fun i => (b i : V)) := by
    intro x _
    obtain ⟨y, hy, hx⟩ := hS x
    have hy' : algebraMap ℤ_[l] ℚ_[l] y ≠ 0 := by
      simpa using hy
    have h1 : y • x ∈ Submodule.span ℚ_[l] (Set.range fun i => (b i : V)) := by
      have := hsum ⟨_, hx⟩
      change y • x = _ at this
      rw [this]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    rw [← algebraMap_smul ℚ_[l]] at h1
    exact (Submodule.smul_mem_iff _ hy').1 h1
  let w := Module.Basis.mk hli' hsp
  have hw : ∀ i, w i = (b i : V) := fun i => Module.Basis.mk_apply _ _ i
  refine ⟨_, w, fun x => ⟨fun hx i => ?_, fun hx => ?_⟩⟩
  · have := hsum ⟨x, hx⟩
    change x = _ at this
    simp only [← hw] at this
    have h2 : w.repr x i = ((b.repr ⟨x, hx⟩ i : ℤ_[l]) : ℚ_[l]) := by
      conv_lhs => rw [this]
      exact congrFun (w.repr_sum_self _) i
    rw [h2]
    exact PadicInt.norm_le_one _
  · rw [← w.sum_repr x]
    refine S.sum_mem fun i _ => ?_
    obtain ⟨z, h3⟩ : ∃ z : ℤ_[l], w.repr x i = algebraMap ℤ_[l] ℚ_[l] z := ⟨⟨_, hx i⟩, rfl⟩
    rw [h3, algebraMap_smul, hw]
    exact S.smul_mem _ (b i).2

theorem continuous_coord {L V : Type} [Field L] [Algebra ℚ_[l] L] [TopologicalSpace L]
    [IsTopologicalRing L] [T2Space L] (hc : Continuous (algebraMap ℚ_[l] L))
    [AddCommGroup V] [Module L V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] L V] [TopologicalSpace V]
    [IsModuleTopology L V] [FiniteDimensional L V] {n : ℕ} (w : Module.Basis (Fin n) ℚ_[l] V) :
    Continuous w.equivFun ∧ Continuous w.equivFun.symm := by
  haveI : IsTopologicalAddGroup V := IsModuleTopology.topologicalAddGroup L V
  haveI : ContinuousSMul L V := IsModuleTopology.toContinuousSMul L V
  haveI : T2Space V := by
    let c := Module.finBasis L V
    have h1 : Continuous c.equivFun :=
      IsModuleTopology.continuous_of_linearMap c.equivFun.toLinearMap
    exact T2Space.of_injective_continuous c.equivFun.injective h1
  haveI : ContinuousSMul ℚ_[l] V := ⟨by
    have h : (fun p : ℚ_[l] × V => p.1 • p.2) = fun p => algebraMap ℚ_[l] L p.1 • p.2 := by
      funext p; rw [algebraMap_smul]
    rw [h]
    exact (hc.comp continuous_fst).smul continuous_snd⟩
  exact ⟨w.equivFunL.continuous, w.equivFunL.symm.continuous⟩

theorem exists_basis_lattice {L O V : Type} [Field L] [Algebra ℚ_[l] L] [CommRing O] [Algebra O L]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
    (hcomp : ∀ a : ℤ_[l], algebraMap O L (algebraMap ℤ_[l] O a) = algebraMap ℚ_[l] L (a : ℚ_[l]))
    (hL : ∀ a : L, ∃ y : ℤ_[l], y ≠ 0 ∧ ∃ o : O, algebraMap O L o = algebraMap ℚ_[l] L y * a)
    [AddCommGroup V] [Module L V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] L V] [Module O V]
    [IsScalarTower O L V] (S : Submodule O V) (hfg : S.FG) (hfree : Module.Free O S)
    (hspan : Submodule.span L (S : Set V) = ⊤) :
    ∃ (n : ℕ) (w : Module.Basis (Fin n) ℚ_[l] V), ∀ x : V, x ∈ S ↔ ∀ i, ‖w.repr x i‖ ≤ 1 := by
  first
  | (rename_i h_1 h_5 h_6 h_7 h_8 h_9 h_10 h_11 h_14 h_15 h_16 h_17 h_18 h_19; revert l h_1 L O V h_5 h_6 h_7 h_8 h_9 h_10 h_11 hcomp hL h_14 h_15 h_16 h_17 h_18 h_19 S hfg hfree hspan; exact @_root_.GlobalTheory.UnitBallBasis.exists_basis_mem_iff_norm_le_one)
  | exact @_root_.GlobalTheory.UnitBallBasis.exists_basis_mem_iff_norm_le_one
  | exact _root_.GlobalTheory.UnitBallBasis.exists_basis_mem_iff_norm_le_one
  | (apply _root_.GlobalTheory.UnitBallBasis.exists_basis_mem_iff_norm_le_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnitBallBasis.exists_basis_mem_iff_norm_le_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnitBallBasis.exists_basis_mem_iff_norm_le_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnitBallBasis.exists_basis_mem_iff_norm_le_one ..)

theorem exists_mul_mem (LL : FinExt l) (a : ↥LL.1) :
    ∃ y : ℤ_[l], y ≠ 0 ∧ ∃ o : ↥(OL LL),
      algebraMap ↥(OL LL) ↥LL.1 o = algebraMap ℚ_[l] ↥LL.1 y * a := by
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have h1 : IsAlgebraic ℚ_[l] a := Algebra.IsAlgebraic.isAlgebraic a
  have h2 : IsAlgebraic ℤ_[l] a := (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] ↥LL.1).2 h1
  obtain ⟨y, hy, hi⟩ := h2.exists_integral_multiple
  refine ⟨y, hy, ⟨_, hi⟩, ?_⟩
  change y • a = _
  rw [Algebra.smul_def]
  rfl

theorem continuous_algebraMap_ext (LL : FinExt l) : Continuous (algebraMap ℚ_[l] ↥LL.1) :=
  continuous_induced_rng.2 (continuous_algebraMap ℚ_[l] (Om l))


set_option synthInstance.maxHeartbeats 400000 in
theorem exists_basis (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G]
    (LL : FinExt l) (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) :
    ∃ (n : ℕ) (w : Module.Basis (Fin n) ℚ_[l] T.V),
      (∀ x : T.V, x ∈ T.L.T ↔ ∀ i, ‖w.repr x i‖ ≤ 1) ∧
        Continuous w.equivFun ∧ Continuous w.equivFun.symm := by
  haveI := Decomp.freeOL LL
  haveI := Decomp.finiteOL LL
  obtain ⟨n, w, hw⟩ := exists_basis_lattice (l := l) (L := ↥LL.1) (O := ↥(OL LL)) (fun _ => rfl)
    (exists_mul_mem LL) T.L.T T.L.fg T.L.free T.L.span
  exact ⟨n, w, hw, continuous_coord (continuous_algebraMap_ext LL) w⟩

end GlobalTheory.Cyc.LatBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsComplexReadingLocalEmbedding
section
noncomputable section

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.ReadEmbEx

theorem exists_read {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
    {O : Type} [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [TopologicalSpace O] (B : LocBridge l E Ω Gw O)
    (ι : FractionRing O →+* ℂ) :
    ∃ φ : ↥B.LL.1 →+* ℂ, ∀ a : O, φ (B.toLL a) = ι (algebraMap O (FractionRing O) a) := by
  have hinj : Function.Injective B.toLL := fun _ _ h => B.eO.injective (Subtype.ext h)
  let f : FractionRing O →+* ↥B.LL.1 := IsFractionRing.lift (g := B.toLL) hinj
  have hf : ∀ a : O, f (algebraMap O (FractionRing O) a) = B.toLL a := fun a =>
    IsFractionRing.lift_algebraMap _ a
  have hb : Function.Bijective f := by
    refine ⟨f.injective, fun y => ?_⟩
    have hint (x : Om l) : IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
      have hx : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
      rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic hx)]
      constructor
      · intro h n
        rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
        exact ((minpoly ℤ_[l] x).coeff n).2
      · intro h
        have hl : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
          rw [Polynomial.lifts_iff_coeff_lifts]
          exact fun n => ⟨⟨_, h n⟩, rfl⟩
        obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl (minpoly.monic hx)
        refine ⟨q, hqm, ?_⟩
        rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]
    have hmem (x : ↥B.LL.1) : x ∈ OL B.LL ↔ ‖(x : Om l)‖ ≤ 1 := by
      rw [← hint, OL, mem_integralClosure_iff]
      exact (isIntegral_algHom_iff (B.LL.1.val.restrictScalars ℤ_[l]) B.LL.1.val.toRingHom.injective).symm
    have hnorm (x : ↥B.LL.1) : ‖(x : Om l)‖ ≤ 1 → ∃ n : O, x = B.toLL n := by
      intro hx
      refine ⟨B.eO.symm ⟨x, (hmem x).2 hx⟩, ?_⟩
      simp [LocBridge.toLL]
    have hfrac (y : ↥B.LL.1) : ∃ n d : O, d ≠ 0 ∧ B.toLL d * y = B.toLL n := by
      by_cases h : ‖(y : Om l)‖ ≤ 1
      · obtain ⟨n, hn⟩ := hnorm y h
        refine ⟨n, 1, fun h1 => ?_, by simp [hn]⟩
        have := congrArg B.toLL h1
        simp at this
      · have hy : y ≠ 0 := by
          rintro rfl
          simp at h
        have h' : ‖((y⁻¹ : ↥B.LL.1) : Om l)‖ ≤ 1 := by
          rw [IntermediateField.coe_inv, norm_inv]
          exact inv_le_one_of_one_le₀ (not_le.1 h).le
        obtain ⟨d, hd⟩ := hnorm _ h'
        refine ⟨1, d, fun h1 => ?_, by rw [← hd, map_one, inv_mul_cancel₀ hy]⟩
        rw [h1, map_zero] at hd
        exact hy (inv_eq_zero.1 hd)
    obtain ⟨n, d, hd, e⟩ := hfrac y
    have hd' : B.toLL d ≠ 0 := fun h0 => hd (hinj (h0.trans (map_zero _).symm))
    refine ⟨algebraMap O _ n / algebraMap O _ d, ?_⟩
    rw [map_div₀, hf, hf, ← e, mul_div_cancel_left₀ _ hd']
  let e := RingEquiv.ofBijective f hb
  refine ⟨ι.comp e.symm.toRingHom, fun a => ?_⟩
  rw [← hf]
  exact congrArg ι (e.symm_apply_apply _)

theorem exists_readEmb : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (ι : FractionRing (D.ntw.O0 i) →+* ℂ) (v : HeightOneSpectrum (𝓞 D.host.E)) (hv : v ∈ placesOver D.host.E (D.ntw.l i)) (τ : EmbV bkP i v hv), ∃ τc : D.host.E →+* ℂ, ReadEmb bkP i ι v hv τ τc ∧ ∀ (v' : HeightOneSpectrum (𝓞 D.host.E)) (hv' : v' ∈ placesOver D.host.E (D.ntw.l i)) (τ' : EmbV bkP i v' hv'), IsConjEmb bkP i v v' hv hv' τ τ' → ReadEmb bkP i ι v' hv' τ' (τc.comp (cj D)) := by
  intro D bkP i ι v hv τ
  obtain ⟨φ, hφ⟩ := exists_read (bkP.br i v hv) ι
  let c : D.host.E →+* ↥(bkP.br i v hv).Kw.1 :=
    ((bkP.br i v hv).j.comp (algebraMap D.host.E D.nd.Om)).codRestrict (bkP.br i v hv).Kw.1 (bkP.br i v hv).j_E
  have h : ReadEmb bkP i ι v hv τ ((φ.comp (AlgHom.toRingHom τ)).comp c) := by
    intro x n d hx
    have := congrArg φ hx.2
    rw [map_mul, hφ, hφ] at this
    exact this
  exact ⟨_, h, fun v' hv' τ' hc x n d hx => h _ n d ((hc x n d).1 hx)⟩

end GlobalTheory.ReadEmbEx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFontaineThetaFrobeniusInverseShift
section
noncomputable section

namespace GlobalTheory.Cyc.Decomp

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

variable {l : ℕ} [Fact l.Prime]

theorem ringHom_padicInt_OC_ext (f g : ℤ_[l] →+* OC l) (x : ℤ_[l]) : f x = g x := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hn : ‖((l : ℕ) : PadicComplex l)‖ = (l : ℝ)⁻¹ := by
    have h := norm_zC ((l : ℕ) : ℤ_[l])
    rw [PadicInt.norm_p] at h
    rw [← h]
    simp [zC]
  have key : ∀ k : ℕ, ‖((f x - g x : OC l) : PadicComplex l)‖ ≤ ((l : ℝ)⁻¹) ^ k := by
    intro k
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec k x)
    have hx : x = (x.appr k : ℤ_[l]) + y * (l : ℤ_[l]) ^ k := by rw [hy]; ring
    have h1 : f x - g x = (f y - g y) * ((l : ℕ) : OC l) ^ k := by
      conv_lhs => rw [hx]
      simp only [map_add (f := _), map_mul, map_pow, map_natCast]
      ring
    have h2 : ((f x - g x : OC l) : PadicComplex l) =
        ((f y - g y : OC l) : PadicComplex l) * ((l : ℕ) : PadicComplex l) ^ k := by
      rw [h1]; push_cast; rfl
    rw [h2, norm_mul, norm_pow, hn]
    exact mul_le_of_le_one_left (by positivity) ((mem_OC _).1 (f y - g y).2)
  have h0 : ‖((f x - g x : OC l) : PadicComplex l)‖ ≤ 0 :=
    ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
      (inv_lt_one_of_one_lt₀ hl)) key
  have h3 : f x - g x = 0 := Subtype.ext (norm_le_zero_iff.1 h0)
  exact sub_eq_zero.1 h3

theorem map_frobeniusEquiv_symm_OCb (e : OCb l →+* OCb l) (x : OCb l) :
    e ((frobeniusEquiv (OCb l) l).symm x) = (frobeniusEquiv (OCb l) l).symm (e x) := by
  apply (frobeniusEquiv (OCb l) l).injective
  rw [RingEquiv.apply_symm_apply, frobeniusEquiv_apply, frobenius_def, ← map_pow,
    frobeniusEquiv_symm_pow_p]

theorem exists_thetaShift_ringHom {P : LocPrime l} (AI : LocAinf l P) (n : ℕ) :
    ∃ θ : Ainf l →+* OC l,
      (∀ (g : GQ l) (a : Ainf l), ((θ (AI.actW g a) : OC l) : PadicComplex l) =
        AI.actC g ((θ a : OC l) : PadicComplex l)) ∧
      ∀ j : ℕ, θ (WittVector.teichmuller l (AI.εroot j)) = AI.ζ (j + n) := by
  induction n with
  | zero =>
    obtain ⟨θ, -, -, h1, -, h2⟩ := exists_isTheta l P AI
    exact ⟨θ, h1, h2⟩
  | succ n ih =>
    obtain ⟨θ, h1, h2⟩ := ih
    refine ⟨θ.comp (WittVector.map (frobeniusEquiv (OCb l) l).symm.toRingHom), fun g a => ?_,
      fun j => ?_⟩
    · have e : WittVector.map (frobeniusEquiv (OCb l) l).symm.toRingHom (AI.actW g a) =
          AI.actW g (WittVector.map (frobeniusEquiv (OCb l) l).symm.toRingHom a) :=
        WittVector.ext fun k =>
          (map_frobeniusEquiv_symm_OCb (AI.actT g).toRingHom (a.coeff k)).symm
      rw [RingHom.comp_apply, RingHom.comp_apply, e, h1]
    · have e : (frobeniusEquiv (OCb l) l).symm.toRingHom (AI.εroot j) = AI.εroot (j + 1) := by
        rw [LocAinf.εroot, LocAinf.εroot, Function.iterate_succ_apply']
        rfl
      rw [RingHom.comp_apply, WittVector.map_teichmuller, e, h2, add_assoc, add_comm 1 n]

theorem exists_isThetaShift : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (n : ℕ),
    ∃ θ : Ainf l →ₐ[ℤ_[l]] OC l, IsThetaShift AI n θ := by
  intro l _ P AI n
  obtain ⟨θ, h1, h2⟩ := exists_thetaShift_ringHom AI n
  exact ⟨{ toRingHom := θ
           commutes' := fun x => ringHom_padicInt_OC_ext (θ.comp (algebraMap ℤ_[l] (Ainf l)))
             (algebraMap ℤ_[l] (OC l)) x }, fun g a => h1 g a, h2⟩

end GlobalTheory.Cyc.Decomp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisRepTwist
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.HalfTwist

theorem eta_char (D : D7) (w : PlE D.host) :
    D.naut.lpChar (D.naut.locG D.naut.etaT w) (D.naut.locG D.naut.etaTinv w) = D.naut.lpUnr w {1} := by
  have hu := D.naut.etaT_unr w
  have hinv := D.naut.etaTinv_def w
  have hd1 : D.naut.lpDim (D.naut.locG D.naut.etaTinv w) = 1 := D.naut.locG_dim _ _
  have hcard : Multiset.card (D.naut.frobEig (D.naut.locG D.naut.etaT w)) = 1 := by
    rw [D.naut.frobEig_card _ hu, D.naut.locG_dim]
  obtain ⟨b, hb⟩ := Multiset.card_eq_one.1 hcard
  have hb0 : b ≠ 0 := by
    have h0 := D.naut.frobEig_ne_zero _ hu
    rw [hb] at h0
    intro hb'
    exact h0 (by simp [hb'])
  have hinvb : D.naut.frobEig (D.naut.locG D.naut.etaTinv w) = {b⁻¹} := by
    rw [hinv.2, hb, Multiset.map_singleton]
  have hunr := D.naut.unr_char _ _ hd1 hu hinv.1
  have hf := D.naut.frobEig_char _ _ b⁻¹ hu hinv.1 hd1 hinvb
  rw [D.naut.unr_eq_lpUnr _ hunr, hf, hb, Multiset.map_singleton, mul_inv_cancel₀ hb0]

theorem eta_inf (D : D7) (hA : SumRepresentations.At.TieAut D.nd D.naut) (τ : D.host.E →+* ℂ) :
    ∃ h : ℂ, D.naut.infG D.naut.etaT τ = {h} ∧ D.naut.infG D.naut.etaTinv τ = {-h} ∧
      (h = 1 / 2 ∨ h = -(1 / 2)) := by
  obtain ⟨h1, h2⟩ := hA.2.1 τ
  rcases h1 with h1 | h1
  · exact ⟨1 / 2, h1, by rw [h2, h1, Multiset.map_singleton], Or.inl rfl⟩
  · exact ⟨-(1 / 2), h1, by rw [h2, h1, Multiset.map_singleton], Or.inr rfl⟩

end GlobalTheory.HalfTwist

end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntWeightsCompatibleRootsOfUnityLevels
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

namespace GlobalTheory.LevelSums

theorem sum_class {R : Type*} [CommRing R] (x : R) (m k n : ℕ) (hm : 0 < m) :
    ∑ a ∈ Finset.range (m * k), (if a % m = n % m then x ^ a else 0) =
      x ^ (n % m) * ∑ i ∈ Finset.range k, (x ^ m) ^ i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ, mul_add]
    congr 1
    rw [Finset.sum_eq_single (n % m)]
    · rw [if_pos (by simp), pow_add, pow_mul, mul_comm]
    · intro b hb hne
      rw [if_neg]
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (Finset.mem_range.1 hb)]
      exact hne
    · intro h
      exact absurd (Finset.mem_range.2 (Nat.mod_lt _ hm)) h


open Classical in
theorem sum_ind {R : Type*} [CommRing R] [IsDomain R] (l : ℕ) (hl : 0 < l) (x : R) (s j n : ℕ)
    (hj : 1 ≤ j) (hjs : j ≤ s) (hn : ¬ l ∣ n) (hx : x ^ l ^ s = 1) :
    ∑ a ∈ primeTo l s, (((if a % l ^ j = n % l ^ j then 1 else 0 : ℤ)) : R) * x ^ a =
      if x ^ l ^ j = 1 then (l : R) ^ (s - j) * x ^ n else 0 := by
  have hs : l ^ s = l ^ j * l ^ (s - j) := by rw [← pow_add]; congr 1; omega
  have h1 : ∑ a ∈ primeTo l s, (((if a % l ^ j = n % l ^ j then 1 else 0 : ℤ)) : R) * x ^ a =
      ∑ a ∈ Finset.range (l ^ j * l ^ (s - j)), (if a % l ^ j = n % l ^ j then x ^ a else 0) := by
    rw [← hs]
    unfold primeTo
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h : a % l ^ j = n % l ^ j
    · have : ¬ l ∣ a := by
        intro ha
        have hd : l ∣ l ^ j := dvd_pow_self l (by omega)
        exact hn (((Nat.ModEq.of_dvd hd h).dvd_iff dvd_rfl).1 ha)
      simp [h, this]
    · simp [h]
  rw [h1, sum_class x _ _ n (pow_pos hl j)]
  split_ifs with h
  · rw [h, ← pow_eq_pow_mod n h]
    simp [mul_comm]
  · have h2 : (x ^ l ^ j) ^ l ^ (s - j) = 1 := by rw [← pow_mul, ← hs, hx]
    have h3 := mul_geom_sum (x ^ l ^ j) (l ^ (s - j))
    rw [h2, sub_self] at h3
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact absurd (sub_eq_zero.1 h4) h
    · rw [h4, mul_zero]

theorem pow_shift {M : Type*} [Monoid M] (l : ℕ) (ζ : ℕ → M) (h : ∀ j, ζ (j + 1) ^ l = ζ j)
    (i j : ℕ) : ζ (i + j) ^ l ^ j = ζ i := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ', pow_mul, ← add_assoc, h, ih]

theorem pow_eq_one_iff_le {M : Type*} [Monoid M] (l : ℕ) (ζ : ℕ → M) (h0 : ζ 0 = 1) (h1 : ζ 1 ≠ 1)
    (h : ∀ j, ζ (j + 1) ^ l = ζ j) (i j : ℕ) : ζ i ^ l ^ j = 1 ↔ i ≤ j := by
  constructor
  · intro hij
    by_contra hlt
    obtain ⟨d, rfl⟩ : ∃ d, i = 1 + (j + d) := ⟨i - 1 - j, by omega⟩
    apply h1
    rw [← pow_shift l ζ h 1 (j + d), pow_add, pow_mul, hij, one_pow]
  · intro hij
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
    have := pow_shift l ζ h 0 i
    rw [zero_add] at this
    rw [pow_add, pow_mul, this, h0, one_pow]

theorem exists_weights : ∀ (l : ℕ) [Fact l.Prime] (ζ : ℕ → Om l), ζ 0 = 1 → ζ 1 ≠ 1 → (∀ j, ζ (j + 1) ^ l = ζ j) → ∀ s j n : ℕ, 1 ≤ j → j ≤ s → ¬ l ∣ n → ∃ lam : ℕ → ℤ, (∑ a ∈ primeTo l s, lam a = if j = 1 then (l : ℤ) ^ (s - 1) else 0) ∧ ∀ i, 1 ≤ i → i ≤ s → ∑ a ∈ primeTo l s, (lam a : Om l) * ζ i ^ a = if i = j then (l : Om l) ^ (if j = 1 then s - 1 else s - j + 1) * ζ j ^ n else 0 := by
  intro l hl ζ h0 h1 h s j n hj hjs hn
  have hl0 : 0 < l := hl.out.pos
  have hz : ∀ j, 1 ≤ j → j ≤ s →
      ∑ a ∈ primeTo l s, (if a % l ^ j = n % l ^ j then 1 else 0 : ℤ) = (l : ℤ) ^ (s - j) := by
    intro j hj hjs
    simpa using sum_ind l hl0 (1 : ℤ) s j n hj hjs hn (one_pow _)
  have hv : ∀ i, i ≤ s → ∀ j, 1 ≤ j → j ≤ s →
      ∑ a ∈ primeTo l s, (((if a % l ^ j = n % l ^ j then 1 else 0 : ℤ)) : Om l) * ζ i ^ a =
        if i ≤ j then (l : Om l) ^ (s - j) * ζ i ^ n else 0 := by
    intro i hi j hj hjs
    rw [sum_ind l hl0 (ζ i) s j n hj hjs hn ((pow_eq_one_iff_le l ζ h0 h1 h i s).2 hi)]
    simp only [pow_eq_one_iff_le l ζ h0 h1 h]
  by_cases hj1 : j = 1
  · subst hj1
    refine ⟨fun a => if a % l ^ 1 = n % l ^ 1 then 1 else 0, ?_, fun i hi his => ?_⟩
    · rw [hz 1 le_rfl hjs, if_pos rfl]
    · rw [hv i his 1 le_rfl hjs]
      by_cases e : i = 1
      · subst e; simp
      · rw [if_neg (by omega), if_neg e]
  · have hsj : s - (j - 1) = s - j + 1 := by omega
    refine ⟨fun a => l * (if a % l ^ j = n % l ^ j then 1 else 0) -
      (if a % l ^ (j - 1) = n % l ^ (j - 1) then 1 else 0), ?_, fun i hi his => ?_⟩
    · rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hz j hj hjs, hz (j - 1) (by omega) (by omega),
        if_neg hj1, hsj]
      ring
    · simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, sub_mul, mul_assoc]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hv i his j hj hjs,
        hv i his (j - 1) (by omega) (by omega), if_neg hj1, hsj]
      rcases lt_trichotomy i j with e | e | e
      · rw [if_pos e.le, if_pos (by omega), if_neg e.ne]; ring
      · subst e
        rw [if_pos le_rfl, if_neg (by omega), if_pos rfl]; ring
      · rw [if_neg (by omega), if_neg (by omega), if_neg e.ne']; ring

end GlobalTheory.LevelSums
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitCharacterOfGaloisStableLineCLTateStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitCharacter_of_galoisStable_line_cLTate : ∀ (l : ℕ) [Fact l.Prime] (y : ℂ_[l]), y ≠ 0 → (∀ g : GQ l, ∃ x : ℚ_[l], Per.σC g y = algebraMap ℚ_[l] ℂ_[l] x * y) → ∃ η : GQ l →* ℤ_[l]ˣ, ∀ g : GQ l, Per.σC g y = algebraMap ℚ_[l] ℂ_[l] ((η g : ℤ_[l]) : ℚ_[l]) * y := by
  first | exact @GlobalTheory.Per.exists_unit_character_of_stable_line | exact GlobalTheory.Per.exists_unit_character_of_stable_line | (intros; apply GlobalTheory.Per.exists_unit_character_of_stable_line <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfRestrictGaloisDescentStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDeRham_of_restrict_galois_descent : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K K' LL : FinExt l) (hle : GK K' ≤ GK K), K.1 ≤ K'.1 → (∀ g ∈ GK K, ∀ x ∈ K'.1, g x ∈ K'.1) → ∀ (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsDR (P.PD K') (V := V) (ρ.comp (Subgroup.inclusion hle)) → IsDR (P.PD K) ρ := by
  first | exact @GlobalTheory.DeRhamDescent.isDR_of_restrict | exact GlobalTheory.DeRhamDescent.isDR_of_restrict | (intros; apply GlobalTheory.DeRhamDescent.isDR_of_restrict <;> assumption)
end

