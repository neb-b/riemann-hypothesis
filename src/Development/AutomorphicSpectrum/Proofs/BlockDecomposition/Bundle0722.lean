module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.DictKAOfParts
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
public import Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.SiegelWeilUnitarySchrodingerLit
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262
public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0714
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0519
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0390
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0428
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0416
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0451
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0404
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0711
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0410
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0426
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0408
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0414
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0362
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0341
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0549
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0708
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0716

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockSplittingMaximalCompact
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.PfSWUS.FockSplit

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

section Box

open NumberField IsDedekindDomain

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}

theorem isPureFin_box (b : Module.Basis (Fin d) F E) {n M : ℕ}
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hA : ∀ v, IsCompact (A v) ∧ IsOpen (A v))
    (hS : ∀ v, v ∉ S → A v = HeckeCharacterZeroLocus.SiegelWeilU.latV b v) :
    HeckeCharacterZeroLocus.SiegelWeilU.IsPureFin b ((GlobalTheory.CompanionTheory.WhitFree.boxF A).indicator (fun _ => (1 : ℂ)))
      (fun v => (A v).indicator 1) := by
  classical
  refine ⟨fun v => ?_, ?_, fun X => ?_⟩
  · haveI : T2Space (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) :=
      (GlobalTheory.CompanionTheory.SW.TopK.coordHomeo (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) b).isEmbedding.t2Space
    have hcl : IsClopen (A v) := ⟨(hA v).1.isClosed, (hA v).2⟩
    refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ?_,
      HasCompactSupport.intro (hA v).1 fun x hx => Set.indicator_of_notMem hx _⟩
    by_cases hx : x ∈ A v
    · exact ⟨A v, (hA v).2, hx, fun y hy => by
        beta_reduce
        rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy]
        rfl⟩
    · exact ⟨(A v)ᶜ, hcl.compl.isOpen, hx, fun y hy => by
        beta_reduce
        rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]⟩
  · refine Filter.eventually_cofinite.2 (S.finite_toSet.subset fun v hv => ?_)
    by_contra h
    refine hv ?_
    show (A v).indicator 1 = _
    rw [hS v h]
  · by_cases hX : X ∈ GlobalTheory.CompanionTheory.WhitFree.boxF A
    · rw [Set.indicator_of_mem hX]
      exact (finprod_eq_one_of_forall_eq_one fun v => Set.indicator_of_mem (hX v) _).symm
    · rw [Set.indicator_of_notMem hX]
      obtain ⟨v₀, hv₀⟩ : ∃ v, HeckeCharacterZeroLocus.SiegelWeilU.projV v X ∉ A v := by
        by_contra h
        push_neg at h
        exact hX h
      refine (finprod_eq_zero _ v₀ (Set.indicator_of_notMem hv₀ _) ?_).symm
      have hfin := Filter.eventually_cofinite.1 (GlobalTheory.CompanionTheory.SW.MeasProj.eventually_mem_latV b X)
      refine (hfin.union S.finite_toSet).subset fun v hv => ?_
      by_contra h
      simp only [Set.mem_union, not_or, Set.mem_setOf_eq, not_not, Finset.mem_coe] at h
      apply hv
      show (A v).indicator 1 (HeckeCharacterZeroLocus.SiegelWeilU.projV v X) = 1
      rw [hS v h.2]
      exact Set.indicator_of_mem h.1 _

end Box

theorem exists_fin_sum {M : Type*} [AddCommGroup M] [Module ℂ M] {P : M → Prop}
    (hs : ∀ (a : ℂ) (x : M), P x → P (a • x)) {x : M} (hx : x ∈ Submodule.span ℂ {y | P y}) :
    ∃ (N : ℕ) (f : Fin N → M), x = ∑ j, f j ∧ ∀ j, P (f j) := by
  induction hx using Submodule.span_induction with
  | mem x h => exact ⟨1, fun _ => x, by simp, fun _ => h⟩
  | zero => exact ⟨0, Fin.elim0, by simp, fun j => j.elim0⟩
  | add x y _ _ hx hy =>
    obtain ⟨N, f, rfl, hf⟩ := hx
    obtain ⟨N', f', rfl, hf'⟩ := hy
    refine ⟨N + N', Fin.append f f', by simp [Fin.sum_univ_add, Fin.append_left, Fin.append_right], fun j => ?_⟩
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simpa [Fin.append_left] using hf i
    · simpa [Fin.append_right] using hf' i
  | smul a x _ hx =>
    obtain ⟨N, f, rfl, hf⟩ := hx
    exact ⟨N, fun j => a • f j, by rw [Finset.smul_sum], fun j => hs a _ (hf j)⟩

variable {D : D7} {n : ℕ}

theorem evalPoly_monomial_mul {m : ℕ} (e : D.what₂.Tau × Fin m × Fin n × Bool →₀ ℕ) (a c : ℂ)
    (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) :
    evalPoly (MvPolynomial.monomial e (a * c)) z = a * evalPoly (MvPolynomial.monomial e c) z := by
  simp only [evalPoly, MvPolynomial.eval_monomial, mul_assoc]

theorem isMonoFock_smul {θ : InfFam D} {V : HSp D} {l : D.what₂.Tau → ℝ}
    {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {φ : Mx D V.rank n → ℂ} (a : ℂ)
    (h : IsMonoFock θ V l s φ) : IsMonoFock θ V l s (a • φ) := by
  obtain ⟨e, c, g, d, bs, gv, hp, rfl⟩ := h
  refine ⟨e, a * c, g, d, bs, gv, hp, funext fun x => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, evalPoly_monomial_mul, mul_assoc]

theorem gen_mem_span (θ : InfFam D) (V : HSp D) (l : D.what₂.Tau → ℝ)
    (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (p : MvPolynomial (D.what₂.Tau × Fin V.rank × Fin n × Bool) ℂ)
    (g : (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E)) :
    (fun x : Mx D V.rank n => evalPoly p (fun τ => compAt θ τ x) * gauss V l s (fun τ => compAt θ τ x) *
      g (fun i j => finPart D (x i j))) ∈ Submodule.span ℂ {φ | IsMonoFock θ V l s φ} := by
  classical
  haveI : FiniteDimensional D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  let b := Module.finBasis D.host.F D.host.E
  let tr : (Fin n → Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) ≃ₜ
      (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) :=
    { toFun := fun X i j => X j i
      invFun := fun Z j i => Z i j
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := continuous_pi fun i => continuous_pi fun j =>
        (continuous_apply i).comp (continuous_apply j)
      continuous_invFun := continuous_pi fun j => continuous_pi fun i =>
        (continuous_apply j).comp (continuous_apply i) }
  let g' : (Fin n → Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ := fun X => g (tr X)
  have hg' : IsSB g' := ⟨hg.1.comp_continuous tr.continuous, hg.2.comp_homeomorph tr⟩
  obtain ⟨t, A, S, hA, hS, hdec⟩ := Box.exists_box_combN b g' hg'
  let ind : (Fin n → Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) →
      (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ :=
    fun a Z => (GlobalTheory.CompanionTheory.WhitFree.boxF (A a)).indicator (fun _ => (1 : ℂ)) (fun j i => Z i j)
  have hpure : ∀ a ∈ t, HeckeCharacterZeroLocus.SiegelWeilU.IsPureFin b (fun X => ind a fun i j => X j i)
      (fun v => (A a v).indicator 1) := fun a ha => isPureFin_box b (A a) S (hA a) (hS a ha)
  have hφ : (fun x : Mx D V.rank n => evalPoly p (fun τ => compAt θ τ x) * gauss V l s (fun τ => compAt θ τ x) *
      g (fun i j => finPart D (x i j))) =
      ∑ e ∈ p.support, ∑ a ∈ t, g' a • (fun x : Mx D V.rank n =>
        evalPoly (MvPolynomial.monomial e (p.coeff e)) (fun τ => compAt θ τ x) *
          gauss V l s (fun τ => compAt θ τ x) * ind a (fun i j => finPart D (x i j))) := by
    funext x
    have hp : evalPoly p (fun τ => compAt θ τ x) =
        ∑ e ∈ p.support, evalPoly (MvPolynomial.monomial e (p.coeff e)) (fun τ => compAt θ τ x) := by
      calc evalPoly p (fun τ => compAt θ τ x)
          = evalPoly (∑ e ∈ p.support, MvPolynomial.monomial e (p.coeff e)) (fun τ => compAt θ τ x) := by
            rw [← p.as_sum]
        _ = _ := by simp only [evalPoly, map_sum]
    have hgx : g (fun i j => finPart D (x i j)) =
        ∑ a ∈ t, g' a * ind a (fun i j => finPart D (x i j)) :=
      hdec (fun j i => finPart D (x i j))
    rw [hp, hgx, Finset.sum_mul, Finset.sum_mul, Finset.sum_apply]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.mul_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hφ]
  refine Submodule.sum_mem _ fun e _ => Submodule.sum_mem _ fun a ha => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span ⟨e, p.coeff e, ind a, _, b, _, hpure a ha, rfl⟩

theorem fockA_le_span (θ : InfFam D) (V : HSp D) (l : D.what₂.Tau → ℝ)
    (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    fockA θ V n l s ≤ Submodule.span ℂ {φ | IsMonoFock θ V l s φ} := by
  refine Submodule.span_le.2 ?_
  rintro φ ⟨p, g, hg, rfl⟩
  exact gen_mem_span θ V l s p g hg

end GlobalTheory.CompanionTheory.PfSWUS.FockSplit

namespace GlobalTheory.CompanionTheory.PfSWUS

theorem fockSplitK : PositivityTheory.PfSWUS.FockSplitK := by
  intro D n V ψ χ θ μ ω H l s ν Φ hStd _ k hk
  exact FockSplit.exists_fin_sum (fun a _ h => FockSplit.isMonoFock_smul a h)
    (FockSplit.fockA_le_span θ V l s (fockKStable D n V ψ χ θ μ ω H l s ν Φ hStd k hk))

end GlobalTheory.CompanionTheory.PfSWUS

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedVanishingOnCompact
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer

theorem exists_hpg_mid_levi (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ) (p : Mir k (i + t)) :
    ∃ h ∈ HPG k i t, ∃ κ ∈ GlobalTheory.SplitWeil.KO k (Fin (i + t)), ∃ v : Fin t → k,
      p = h * (uM k (i + t) (midV k i t v) * levi k (i + t) κ) := by
  obtain ⟨y, hy⟩ := GlobalTheory.CompanionTheory.BZPsiPG.exists_uM_of_mem k (i + t)
    (GlobalTheory.CompanionTheory.BZMirAdj.mem_of_mirProj_eq_one k (i + t)
      (p * (GlobalTheory.BZMir.levi k (i + t) (GlobalTheory.BZMir.mirabolicProjection k (i + t) p))⁻¹)
      (by rw [map_mul, map_inv, GlobalTheory.CompanionTheory.BZMirAdj.mirProj_levi, mul_inv_cancel]))
  have hp : p = GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) y *
      GlobalTheory.BZMir.levi k (i + t) (GlobalTheory.BZMir.mirabolicProjection k (i + t) p) := by
    rw [← hy, inv_mul_cancel_right]
  obtain ⟨q, κ, hκ, hgq⟩ := _root_.GlobalTheory.CompanionTheory.BZPsiPG.exists_Qp_mul_KO k i t (GlobalTheory.BZMir.mirabolicProjection k (i + t) p)
  obtain ⟨x, v, hxv⟩ := GlobalTheory.CompanionTheory.BZPsiPG.exists_top_mid k i t
    ((((q : GL (Fin (i + t)) k)⁻¹ : GL (Fin (i + t)) k) : Matrix (Fin (i + t)) (Fin (i + t)) k) *ᵥ y)
  obtain ⟨hq, -⟩ := _root_.GlobalTheory.CompanionTheory.BZPsiPG.levi_Qp_mem_pgProj k i t q
  obtain ⟨hx, -⟩ := _root_.GlobalTheory.CompanionTheory.BZPsiPG.TopCol.main k i t x
  refine ⟨GlobalTheory.BZMir.levi k (i + t) q * GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) (GlobalTheory.CompanionTheory.BZPsiPG.topV k i t x),
    mul_mem hq hx, κ, hκ, v, ?_⟩
  have key : GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) y * GlobalTheory.BZMir.levi k (i + t) q =
      GlobalTheory.BZMir.levi k (i + t) q * GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t)
        ((((q : GL (Fin (i + t)) k)⁻¹ : GL (Fin (i + t)) k) : Matrix (Fin (i + t)) (Fin (i + t)) k) *ᵥ y) := by
    rw [GlobalTheory.CompanionTheory.BZPsiPG.levi_mul_uM, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.one_mulVec]
  rw [hp, hgq, map_mul, ← mul_assoc (GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) y), key, hxv,
    GlobalTheory.CompanionTheory.BZPsiPG.uM_add]
  simp only [mul_assoc]

theorem eq_zero_of_fibV_eq_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W)
    (a : cIndSpace (HPG k i t) (hRep τ σ)),
    (∀ κ ∈ GlobalTheory.SplitWeil.KO k (Fin (i + t)), fibV a κ = 0) → a = 0 := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ a ha
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext p
  obtain ⟨h, hh, κ, hκ, v, rfl⟩ := GlobalTheory.CompanionTheory.BZPsiPG.FibKer.exists_hpg_mid_levi k i t p
  have hfe : a.1.1.1 (h * (GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) (GlobalTheory.CompanionTheory.BZPsiPG.midV k i t v) *
      GlobalTheory.BZMir.levi k (i + t) κ)) =
      GlobalTheory.CompanionTheory.BZPsiPG.hRep τ σ ⟨h, hh⟩ (a.1.1.1 (GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t)
        (GlobalTheory.CompanionTheory.BZPsiPG.midV k i t v) * GlobalTheory.BZMir.levi k (i + t) κ)) :=
    a.1.1.2 ⟨h, hh⟩ _
  have hz : a.1.1.1 (GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) (GlobalTheory.CompanionTheory.BZPsiPG.midV k i t v) *
      GlobalTheory.BZMir.levi k (i + t) κ) = 0 := congrFun (ha κ hκ) v
  show a.1.1.1 _ = (0 : V ⊗[ℂ] W)
  rw [hfe, hz, map_zero]

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralCosetIndicatorSum
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer.SmSum

theorem measure_cosetSet_eq {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (t : ℕ) [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)]
    (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure] (c : k) (a : Fin t → k) :
    μ (cosetSet t c a) = μ (cosetSet t c 0) := by
  have h : cosetSet t c a = (fun v => (-a) + v) ⁻¹' cosetSet t c 0 := by
    ext v
    have e : v - a = (-a) + v - 0 := by abel
    show Multiplicative.ofAdd (v - a) ∈ Lc t c ↔ Multiplicative.ofAdd ((-a) + v - 0) ∈ Lc t c
    rw [e]
  rw [h]
  exact MeasureTheory.measure_preimage_add μ (-a) _

theorem smInt_sum_coset : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) {Z : Type} [AddCommGroup Z] [Module ℂ Z] [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure] (c : k), c ≠ 0 → ∀ (A : Finset (Fin t → k)) (z : (Fin t → k) → Z), smInt μ (fun v => ∑ a ∈ A, (cosetSet t c a).indicator (fun _ => z a) v) = (((μ (cosetSet t c 0)).toReal : ℝ) : ℂ) • ∑ a ∈ A, z a := by
  intro k _ _ _ _ t Z _ _ _ _ μ _ c hc A z
  classical
  have hmem : ∀ B : Finset (Fin t → k),
      (fun v => ∑ a ∈ B, (cosetSet t c a).indicator (fun _ => z a) v) ∈ fibM (Fin t → k) Z := by
    intro B
    have h := Submodule.sum_mem (fibM (Fin t → k) Z) (t := B)
      (f := fun a => (cosetSet t c a).indicator (fun _ => z a))
      (fun a _ => (cosetFn t hc a (z a)).2)
    have e : (fun v => ∑ a ∈ B, (cosetSet t c a).indicator (fun _ => z a) v) =
        ∑ a ∈ B, (cosetSet t c a).indicator (fun _ => z a) := by
      funext v
      rw [Finset.sum_apply]
    rw [e]
    exact h
  refine Finset.induction_on A ?_ ?_
  · have h := GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_indicator μ (∅ : Set (Fin t → k)) (0 : Z)
    simpa using h
  · intro a B ha ih
    have e : (fun v => ∑ b ∈ insert a B, (cosetSet t c b).indicator (fun _ => z b) v) =
        (cosetSet t c a).indicator (fun _ => z a) +
          fun v => ∑ b ∈ B, (cosetSet t c b).indicator (fun _ => z b) v := by
      funext v
      rw [Finset.sum_insert ha]
      rfl
    have l₁ : IsLocallyConstant ((cosetSet t c a).indicator fun _ => z a) := (cosetFn t hc a (z a)).2.1
    have c₁ : HasCompactSupport ((cosetSet t c a).indicator fun _ => z a) := (cosetFn t hc a (z a)).2.2
    rw [e, GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_add μ l₁ c₁ (hmem B).1 (hmem B).2, ih, GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_indicator,
      measure_cosetSet_eq t μ c a, Finset.sum_insert ha, smul_add]

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer.SmSum

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetKernelLatticeConjCompact
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer.IntTwist

open ValuativeRel in
theorem mulH_inv_mem_Lc {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} {c : k} {κ : GL (Fin n) k}
    (hκ : κ ∈ GlobalTheory.SplitWeil.KO k (Fin n)) {l : Multiplicative (Fin n → k)} (hl : l ∈ Lc n c) :
    mulH κ⁻¹ l ∈ Lc n c := by
  obtain ⟨g, rfl⟩ := hκ
  have hl' : ∀ i, c * l.toAdd i ∈ 𝒪[k] := hl
  have hent : ∀ a b, (((Matrix.GeneralLinearGroup.map (n := Fin n) (algebraMap 𝒪[k] k) g)⁻¹ :
      GL (Fin n) k) : Matrix (Fin n) (Fin n) k) a b ∈ 𝒪[k] := by
    intro a b
    rw [← map_inv]
    exact (((g⁻¹ : GL (Fin n) 𝒪[k]) : Matrix (Fin n) (Fin n) 𝒪[k]) a b).2
  show ∀ j, c * ((((Matrix.GeneralLinearGroup.map (n := Fin n) (algebraMap 𝒪[k] k) g)⁻¹ :
      GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ l.toAdd) j ∈ 𝒪[k]
  intro j
  rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine sum_mem fun i _ => ?_
  rw [mul_left_comm]
  exact mul_mem (hent j i) (hl' i)

theorem mulH_mulH_inv {k : Type} [Field k] {n : ℕ} (κ : GL (Fin n) k)
    (l : Multiplicative (Fin n → k)) : mulH κ (mulH κ⁻¹ l) = l := by
  show Multiplicative.ofAdd ((κ : Matrix (Fin n) (Fin n) k).mulVec
    (((κ⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec l.toAdd)) = l
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  rfl

theorem twKer_Lc_le_twist : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) {X : Type} [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ (Multiplicative (Fin n → k)) X) (c : k) (κ : GL (Fin n) k), κ ∈ GlobalTheory.SplitWeil.KO k (Fin n) → ∀ x, x ∈ twKer ρ (Lc n c) 1 → x ∈ twKer (MonoidHom.comp ρ (mulH κ)) (Lc n c) 1 := by
  intro k _ _ _ _ n X _ _ ρ c κ hκ x hx
  unfold GlobalTheory.PRep.twKer at hx ⊢
  refine Submodule.span_le.2 ?_ hx
  rintro w ⟨m, v, rfl⟩
  apply Submodule.subset_span
  refine ⟨⟨mulH κ⁻¹ m, mulH_inv_mem_Lc hκ m.2⟩, v, ?_⟩
  simp [mulH_mulH_inv]

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer.IntTwist
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureGLRightScaling
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ColumnSplitting.Cov

theorem map_two {γ δ : Type} [MeasurableSpace γ] [MeasurableSpace δ] (c : Measure γ) (e : Measure δ)
    [SFinite c] [SFinite e] (f : γ → γ) (h : δ → δ) (hf : Measurable f) (hh : Measurable h) (r s : ℝ≥0)
    (h1 : c.map f = r • c) (h2 : e.map h = s • e) :
    (c.prod e).map (Prod.map f h) = (r * s) • c.prod e := by
  rw [← Measure.map_prod_map c e hf hh, h1, h2]
  simp only [ENNReal.smul_def, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, ENNReal.coe_mul, smul_eq_mul]
  rw [mul_comm]

theorem map_id_prod {β γ : Type} [MeasurableSpace β] [MeasurableSpace γ] (b : Measure β) (X : Measure γ)
    [SFinite b] [SFinite X] (F : γ → γ) (hF : Measurable F) (k : ℝ≥0) (h : X.map F = k • X) :
    (b.prod X).map (Prod.map id F) = k • b.prod X := by
  rw [← Measure.map_prod_map b X measurable_id hF, h, Measure.map_id]
  simp only [ENNReal.smul_def, Measure.prod_smul_right]

theorem map_four {α β γ δ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    (a : Measure α) (b : Measure β) (c : Measure γ) (e : Measure δ) [SFinite a] [SFinite b] [SFinite c] [SFinite e]
    (f : γ → γ) (h : δ → δ) (hf : Measurable f) (hh : Measurable h) (r s : ℝ≥0)
    (h1 : c.map f = r • c) (h2 : e.map h = s • e) :
    (a.prod (b.prod (c.prod e))).map (Prod.map id (Prod.map id (Prod.map f h))) =
      (r * s) • a.prod (b.prod (c.prod e)) := by
  have hm : Measurable (Prod.map f h) := hf.prodMap hh
  exact map_id_prod a _ _ (measurable_id.prodMap hm) _
    (map_id_prod b _ _ hm _ (map_two c e f h hf hh r s h1 h2))

variable {D : D7} {n t : ℕ} {B W : HSp D}

theorem zp_tau (d : HypDec B W t) (hn : W.rank + t = n) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E)
    (g : Mx D t t) (h : GA D W) (U : Mx D t n) (y : Mx D W.rank t) :
    zp d hn x₀ (h, mm U (bl hn 1 0 0 g), mm y g) =
      ((zp d hn x₀ (h, U, y)).1, mm (zp d hn x₀ (h, U, y)).2 g) := by
  simp only [zp, first_columns_mul_block_diagonal, second_columns_mul_block_diagonal, mm, Matrix.add_mul, Matrix.mul_assoc]

theorem ac_tau (a b : ℕ) (k : GA D B) (z : Mx D B.rank a × Mx D B.rank b) (g : Mx D b b) :
    ac B k (z.1, mm z.2 g) = ((ac B k z).1, mm (ac B k z).2 g) := by
  simp only [ac, mm, Matrix.mul_assoc]

theorem measurable_right (a b : ℕ) (g : Mx D b b) : Measurable (fun y : Mx D a b => mm y g) := by
  obtain ⟨-, -, -, -, h5⟩ := top_mx (D := D) a b
  have hring := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  exact (continuous_id.matrix_mul continuous_const).measurable

theorem nuT_cov : ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n) (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ x₀ (g : GL (Fin t) (AE D)), (nuT hn I μ x₀).map (fun z => (z.1, mm z.2 g.1)) = ((absA D (Matrix.GeneralLinearGroup.det g))⁻¹ ^ (W.rank + t) : ℝ≥0) • nuT hn I μ x₀ := by
  intro D n t B W d hn I μ hμ x₀ g
  obtain ⟨G, hG⟩ := GlobalTheory.CompanionTheory.WzLevi.exists_lv hn g
  obtain ⟨-, i2, i3, i4, i5⟩ := top_mx (D := D) t n
  obtain ⟨-, j2, j3, j4, j5⟩ := top_mx (D := D) W.rank t
  obtain ⟨-, k2, k3, -, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  have hBW : BorelSpace (GA D W) := ⟨rfl⟩
  obtain ⟨𝓕, hf⟩ := I.cov₁
  have s1 := hf.1
  have s2 := I.haar
  have s3 := I.probK
  have s4 := hμ
  have hdet := GlobalTheory.CompanionTheory.WzLevi.det_lv hn g G hG
  have hsc1 := map_right t n I.μ₁ hf.1 G
  rw [hdet] at hsc1
  have hsc2 := map_right W.rank t μ hμ g
  have hm1 := measurable_right (D := D) t n G.1
  have hm2 := measurable_right (D := D) W.rank t g.1
  have hτ := map_four I.νK I.m I.μ₁ μ _ _ hm1 hm2 _ _ hsc1 hsc2
  have hτm : Measurable (Prod.map (id : I.l.K → I.l.K) (Prod.map (id : GA D W → GA D W)
      (Prod.map (fun y : Mx D t n => mm y G.1) (fun y : Mx D W.rank t => mm y g.1)))) :=
    measurable_id.prodMap (measurable_id.prodMap (hm1.prodMap hm2))
  have hπ := measurable_pi hn I x₀
  have hT : Measurable (fun z : Mx D B.rank W.rank × Mx D B.rank t => (z.1, mm z.2 g.1)) :=
    measurable_fst.prodMk ((measurable_right (D := D) B.rank t g.1).comp measurable_snd)
  have hcomp : (fun z : Mx D B.rank W.rank × Mx D B.rank t => (z.1, mm z.2 g.1)) ∘
      (fun p : I.l.K × Par D n t W => ac B ((p.1 : GA D B)⁻¹) (zp d hn x₀ p.2)) =
      (fun p : I.l.K × Par D n t W => ac B ((p.1 : GA D B)⁻¹) (zp d hn x₀ p.2)) ∘
        (Prod.map (id : I.l.K → I.l.K) (Prod.map (id : GA D W → GA D W)
          (Prod.map (fun y : Mx D t n => mm y G.1) (fun y : Mx D W.rank t => mm y g.1)))) := by
    funext ⟨k, h, U, y⟩
    simp only [Function.comp, Prod.map, id]
    rw [hG, zp_tau, ac_tau]
  unfold nuT
  rw [Measure.map_map hT hπ, hcomp, ← Measure.map_map hπ hτm]
  unfold Q0
  rw [hτ, Measure.map_smul, ← pow_add, add_comm t]
  exact hπ.aemeasurable

end GlobalTheory.CompanionTheory.ColumnSplitting.Cov

end
end

