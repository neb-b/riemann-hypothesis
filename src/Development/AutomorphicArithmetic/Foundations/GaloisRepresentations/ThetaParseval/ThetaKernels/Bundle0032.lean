module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.DoubledGroupTopologicalProperties
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.WeylElementTransposeMul
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.Bundle0001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.EisensteinMeromorphy.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0009
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0012
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.KFiniteVectors.KFinOfMem
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.KFiniteVectors.Bundle0001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.GoodAwayEx
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.Bundle0002
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfourTop
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
namespace PositivityTheory.SiegelWeilFormula.kfour
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem ratM_eq_k {σ : E →ₐ[F] E} (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : d.ratM = ratMx F E d.m d.n := rfl
end PositivityTheory.SiegelWeilFormula.kfour
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfourW
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl SiegelEisensteinSeries.Grp
namespace PositivityTheory.SiegelWeilFormula.kfour
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
theorem auxiliaryExistence_holds : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties := by
  intro F E _ _ _ _ _ σ d
  obtain ⟨ν, 𝓕, hν, h𝓕, h1⟩ := exists_cov (F := F) (E := E) d.m d.n
  obtain ⟨i1, i2, i3, i4⟩ := doubled_group_topological_properties σ d.Y
  exact ⟨⟨ν, hν, 𝓕, h𝓕, h1⟩, exists_w d.ok.frame, i1, i2, i3, i4⟩
end PositivityTheory.SiegelWeilFormula.kfour
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpLrho
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
abbrev spf_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (a b : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) : AF F :=
  symp (R := AF F) (cA σ) (-1) (incM F d.A.J) (dbl (incM F d.Y.J)) a b
end PositivityTheory.SiegelWeilFormula.KFP
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKheadHead
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.SiegelWeilFormula
open GlobalTheory.Cont
namespace PositivityTheory.SiegelWeilFormula.Khead
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {Y : Spc F E n}
def basis2_k {B : Base F E} (h : _root_.UpperTheory.TP.W.GoodK σ B) : Module.Basis (Fin 2) F E :=
  have h2 : Module.finrank F E = 2 := h.cm.2.2.1
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  Module.finBasisOfFinrankEq F E h2
def mkSD_k {B : Base F E} {m : ℕ} {A : Spc F E m} {r s r' s' : ℕ} {χ : Chr F E} {κ : Type} [Fintype κ]
    {dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (dbl (incM F Y.J))) κ}
    {om : G2 σ Y →* Module.End ℂ ((κ → AF F) → ℂ)} {S : UA σ A.J →* Module.End ℂ ((κ → AF F) → ℂ)}
    {l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ} {b : GL (Fin n ⊕ Fin n) E} {K : Subgroup (G2 σ Y)} {a : G2 σ Y → ℝ}
    {μ : Measure (UA σ A.J)} {D : Set (UA σ A.J)} {Φ : (κ → AF F) → ℂ}
    (H : _root_.PositivityTheory.SiegelWeilFormula.Std_k (σ := σ) B A Y r s r' s' χ κ dd om S l b K a μ D Φ) : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ where
  B := B
  m := m
  n := n
  A := A
  Y := Y
  r := r
  s := s
  χ := χ
  κ := κ
  dd := dd
  om := om
  S := S
  l := l
  b := b
  K := K
  a := a
  μ := μ
  D := D
  bs := _root_.PositivityTheory.SiegelWeilFormula.Khead.basis2_k H.good
  ok := ⟨H.good, H.hm, H.hn, H.aniso, H.sign.imp (fun h => ⟨h.1, h.2.skew⟩) (fun h => ⟨h.1, h.2.herm⟩), H.hecke, H.res, H.dbl,
    H.frame, H.stdK, H.hgt, H.haar, H.dom⟩
theorem headOf_k : _root_.PositivityTheory.SiegelWeilFormula.HeadOf_k := by
  intro hBL hSec hStrong hMain F E _ _ _ _ _ σ B m n A Y r s r' s' χ κ _ dd om S l b K a μ D Φ H
  set d := _root_.PositivityTheory.SiegelWeilFormula.Khead.mkSD_k H with hd
  have hK : d.KFin Φ := ⟨H.sch, H.fin⟩
  have hY : Y.IsHerm σ B r' s' ∨ Y.IsSkew σ B r' s' := H.sign.elim (fun h => .inr h.2) (fun h => .inl h.2)
  obtain ⟨Ê, ⟨t, hsum, -⟩, hw⟩ := hBL F E σ B n Y r' s' H.good H.hn hY χ H.hecke m H.res b K a H.frame H.stdK H.hgt
    (s0 m n) (d.sec0 Φ) (hSec F E σ d Φ hK)
  intro x
  have hfl : ∀ z, (fun y => ((d.Ht y : ℝ) : ℂ) ^ (z - s0 m n) * d.sec0 Φ y) = flat a (d.sec0 Φ) (s0 m n) z := fun z =>
    funext fun y => by
      simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.Ht, flat]
      rw [Real.coe_toNNReal _ (hgt_nonneg d.ok.hgt y)]
      rfl
  have Heisenberg₂ : ∀ z : ℂ, t < z.re → d.eis (d.sec0 Φ) (s0 m n) z x = Ê z x := fun z hz => by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.eis]
    rw [hfl z]
    exact (hsum z hz x).tsum_eq
  have hmer := meromorphicOn_of_weak hw x
  have hext : IsExtAt (fun z => d.eis (d.sec0 Φ) (s0 d.m d.n) z x) (s0 d.m d.n) (Ê · x) :=
    ⟨Set.univ, trivial, isRightDomain_univ, hmer, t, fun z hz => (Heisenberg₂ z hz).symm⟩
  have hEA : d.EisAll := fun Φ' hΦ' => hStrong F E σ d ⟨r', s', hY⟩ _ _ (hSec F E σ d Φ' hΦ')
  obtain ⟨H', hext', han, hval⟩ := hMain F E σ d H.hnm hEA Φ hK x
  have hev := hext'.eventuallyEq hext
  have hloc : Function.update (Ê · x) (s0 m n) (d.I Φ x) =ᶠ[𝓝 (s0 m n)] H' := by
    filter_upwards [eventually_nhdsWithin_iff.1 hev] with z hz
    by_cases e : z = s0 m n
    · subst e; rw [Function.update_self]; exact hval.symm
    · rw [Function.update_of_ne e]; exact (hz e).symm
  refine ⟨Function.update (Ê · x) (s0 m n) (d.I Φ x), fun z _ => (hmer z trivial).update _ _, ⟨max t (s0 m n).re, fun z hz => ?_⟩,
    han.congr hloc.symm, Function.update_self _ _ _⟩
  have hz1 : t < z.re := lt_of_le_of_lt (le_max_left _ _) hz
  have hz2 : z ≠ s0 m n := fun e => by subst e; exact lt_irrefl _ (lt_of_le_of_lt (le_max_right _ _) hz)
  rw [Function.update_of_ne hz2]
  exact hsum z hz1 x
end PositivityTheory.SiegelWeilFormula.Khead
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKheadSecK
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.SiegelWeilFormula
namespace PositivityTheory.SiegelWeilFormula.Khead
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem secK_k : _root_.PositivityTheory.SiegelWeilFormula.SecK_k := by
  intro F E _ _ _ _ _ σ d Φ hΦ
  obtain ⟨c1, c2⟩ := sec_cont_law d.ok.dbl hΦ.1
  refine ⟨c1, fun p t x hp => ?_, ?_⟩
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.sec0, s0]
    exact c2 p t x hp
  · have := hΦ.2
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k : d.K => d.om k.1 Φ)).map
      (LinearMap.pi fun x => d.l ∘ₗ d.om x)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨k, rfl⟩, funext fun x => by simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.sec0, map_mul]⟩
end PositivityTheory.SiegelWeilFormula.Khead
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKkfinBase
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KK
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
def kfS_k : Submodule ℂ d.Fn where
  carrier := {Φ | ∃ N : Submodule ℂ d.Fn, FiniteDimensional ℂ N ∧ N ≤ d.sch ∧ Φ ∈ N ∧ ∀ k ∈ d.K, ∀ Ψ ∈ N, d.om k Ψ ∈ N}
  zero_mem' := ⟨⊥, inferInstance, bot_le, zero_mem _, fun k _ g hg => by rw [(Submodule.mem_bot ℂ).1 hg, map_zero]; exact zero_mem _⟩
  add_mem' := by
    rintro f g ⟨N, _, h0, h1, h2⟩ ⟨N', _, h0', h1', h2'⟩
    refine ⟨N ⊔ N', inferInstance, sup_le h0 h0', Submodule.add_mem_sup h1 h1', fun k hk g hg => ?_⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hg
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (h2 k hk x hx) (h2' k hk y hy)
  smul_mem' := fun c _ ⟨N, h, h0, h1, h2⟩ => ⟨N, h, h0, N.smul_mem c h1, h2⟩
variable {d}
theorem kFin_of_mem_k {Φ : d.Fn} (h : Φ ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.kfS_k d) : d.KFin Φ := by
  obtain ⟨N, _, h0, h1, h2⟩ := h
  refine ⟨h0 h1, Submodule.finiteDimensional_of_le (S₂ := N) (Submodule.span_le.2 ?_)⟩
  rintro _ ⟨k, rfl⟩
  exact h2 k.1 k.2 Φ h1
theorem mem_sch_k {Φ : d.Fn} (h : Φ ∈ _root_.PositivityTheory.SiegelWeilFormula.KK.kfS_k d) : Φ ∈ d.sch := by
  obtain ⟨N, _, h0, h1, -⟩ := h
  exact h0 h1
end PositivityTheory.SiegelWeilFormula.KK
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKkfinCpt
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
attribute [local instance] GlobalTheory.ThK.Dbl.St.ae_ring GlobalTheory.ThK.Dbl.St.ae_t2 GlobalTheory.ThK.Dbl.St.ae_smul
open scoped TensorProduct NNReal Matrix SchwartzMap Classical Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KK
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem isCompact_K_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : IsCompact (d.K : Set d.G) := by
  have hB := d.ok.good
  have hK := d.ok.stdK
  obtain ⟨Φ, hΦ, eΦ⟩ := GlobalTheory.ThK.Dbl.St.exists_section hB.cm d.B.emb
  have hI : IsCompact (intHat F E : Set (AE F E)) := SiegelEisensteinSeries.BRoad.isCompact_intHat
  have hfe : finOne F = GlobalTheory.ThK.Dbl.St.eF F := rfl
  set T : Set (AE F E) := Φ '' Set.univ.pi (fun _ => Metric.closedBall (0 : ℂ) 1) + (intHat F E : Set (AE F E))
    with hTdef
  have hT : IsCompact T := ((isCompact_univ_pi fun _ => isCompact_closedBall _ _).image hΦ).add hI
  have hentry : ∀ k ∈ d.K, ∀ i j, inFrame d.b k i j ∈ T := by
    intro k hk i j
    obtain ⟨h1, h2⟩ := (hK k).1 hk
    rw [eΦ (inFrame d.b k i j)]
    refine Set.add_mem_add ⟨_, fun w _ => ?_, rfl⟩ ?_
    · rw [mem_closedBall_zero_iff]
      have hu : (inFrame d.b k).map (piInf (d.B.emb w)) ∈ Matrix.unitaryGroup (Fin d.n ⊕ Fin d.n) ℂ :=
        Matrix.mem_unitaryGroup_iff.2 (by rw [Matrix.star_eq_conjTranspose]; exact h1 w)
      exact entry_norm_bound_of_unitary hu i j
    · rw [← hfe]
      exact h2 k (Set.mem_insert _ _) i j
  set S : Set (Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) :=
    (fun M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) => incM F d.b.1 * M * incM F (d.b⁻¹).1) ''
      Set.univ.pi (fun _ => Set.univ.pi fun _ => T) with hSdef
  have hS : IsCompact S :=
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hT).image
      ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)
  have hmat : ∀ k ∈ d.K, mat2 k ∈ S := fun k hk => ⟨inFrame d.b k, fun i _ j _ => hentry k hk i j, by
    show incM F d.b.1 * (incM F (d.b⁻¹).1 * mat2 k * incM F d.b.1) * incM F (d.b⁻¹).1 = mat2 k
    simp only [Matrix.mul_assoc, GlobalTheory.EisBL.DoubledParabolic.incM_mul_inv, Matrix.mul_one]
    rw [← Matrix.mul_assoc, GlobalTheory.EisBL.DoubledParabolic.incM_mul_inv, Matrix.one_mul]⟩
  have hp : ∀ w, Continuous (piInf (d.B.emb w)) := fun w => GlobalTheory.Grow.continuous_infEmb_compInf F w (d.B.emb w)
  have hIc := hI.isClosed
  have hfr := GlobalTheory.EisBL.DoubledParabolic.continuous_inFrame (σ := σ) (Y := d.Y) d.b
  have hKset : (d.K : Set d.G) =
      (⋂ w, {k | (inFrame d.b k).map (piInf (d.B.emb w)) * ((inFrame d.b k).map (piInf (d.B.emb w)))ᴴ = 1}) ∩
        ((⋂ i, ⋂ j, {k : d.G | finOne F • inFrame d.b k i j ∈ intHat F E}) ∩
          (⋂ i, ⋂ j, {k : d.G | finOne F • inFrame d.b k⁻¹ i j ∈ intHat F E})) := by
    ext k
    simp only [SetLike.mem_coe, hK k, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq, Set.forall_mem_insert,
      Set.mem_singleton_iff, forall_eq]
  have hKc : IsClosed (d.K : Set d.G) := by
    rw [hKset]
    refine (isClosed_iInter fun w => isClosed_eq ?_ continuous_const).inter
      ((isClosed_iInter fun i => isClosed_iInter fun j => hIc.preimage ?_).inter
        (isClosed_iInter fun i => isClosed_iInter fun j => hIc.preimage ?_))
    · exact (hfr.matrix_map (hp w)).matrix_mul (hfr.matrix_map (hp w)).matrix_conjTranspose
    · exact (hfr.matrix_elem i j).const_smul (finOne F)
    · exact ((hfr.comp continuous_inv).matrix_elem i j).const_smul (finOne F)
  exact GlobalTheory.ThK.Dbl.St.isCompact_of_units (UG (cA σ) (dbl (incM F d.Y.J))) (GlobalTheory.EisBL.DoubledGroupTopology.isClosed_doubled_group σ d.Y) d.K hKc S hS
    fun k hk => ⟨hmat k hk, hmat k⁻¹ (d.K.inv_mem hk)⟩
end PositivityTheory.SiegelWeilFormula.KK
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKkfinKc
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KK
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def thB_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (ε : ℤˣ) (w : InfinitePlace F) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) ℂ :=
  d.b.1.map (d.B.emb w).1 * (jE d.n ε)ᵀ * (d.b⁻¹).1.map (d.B.emb w).1
def thA_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) : Matrix (Fin d.m) (Fin d.m) ℂ :=
  (-(Complex.I * ((((R.ε : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ)) * R.ζ))) • 1
theorem commute_thB_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {k : d.G} (hk : k ∈ d.K) (w : InfinitePlace F) :
    Commute ((mat2 k).map (piInf (d.B.emb w))) (_root_.PositivityTheory.SiegelWeilFormula.KK.thB_k d R.ε w) := by
  have h := d.ok.good.cm
  have e1 : d.b.1.map (d.B.emb w).1 * (d.b⁻¹).1.map (d.B.emb w).1 = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  have e2 : (d.b⁻¹).1.map (d.B.emb w).1 * d.b.1.map (d.B.emb w).1 = 1 := by
    rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  have hMk : (inFrame d.b k).map (piInf (d.B.emb w)) =
      (d.b⁻¹).1.map (d.B.emb w).1 * (mat2 k).map (piInf (d.B.emb w)) * d.b.1.map (d.B.emb w).1 := by
    rw [inFrame, Matrix.map_mul, Matrix.map_mul, map_incM', map_incM']
  have hu := ((d.ok.stdK k).1 hk).1 w
  have cst : ∀ x : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E, (x.map σ).map (d.B.emb w).1 =
      (x.map (d.B.emb w).1).map star := fun x => by
    ext i j; exact h.2.2.2 (d.B.emb w).1 (x i j)
  have cstA : ∀ x : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E),
      (x.map (cA σ)).map (piInf (d.B.emb w)) = (x.map (piInf (d.B.emb w))).map star :=
    fun x => by ext i j; exact GlobalTheory.ThK.Dbl.Dense.piInf_cA h (d.B.emb w) (x i j)
  have hDw : (dbl (incM F d.Y.J)).map (piInf (d.B.emb w)) = (dbl d.Y.J).map (d.B.emb w).1 := by
    rw [← map_incM']
    congr 1
    ext (i | i) (j | j) <;> simp [dbl, incM, Matrix.fromBlocks]
  have hJ : (d.b.1.map (d.B.emb w).1)ᵀ * (dbl (incM F d.Y.J)).map (piInf (d.B.emb w)) *
      (d.b.1.map (d.B.emb w).1).map star = jE d.n R.ε := by
    have := congrArg (fun x => x.map (d.B.emb w).1) R.hε
    simp only [Matrix.map_mul, Matrix.transpose_map, cst] at this
    rw [hDw, this]
    ext (i | i) (j | j) <;> by_cases hij : i = j <;> simp [jE, Matrix.fromBlocks, Matrix.smul_apply, Matrix.one_apply, hij]
  have hk2 : ((mat2 k).map (piInf (d.B.emb w)))ᵀ * (dbl (incM F d.Y.J)).map (piInf (d.B.emb w)) *
      ((mat2 k).map (piInf (d.B.emb w))).map star = (dbl (incM F d.Y.J)).map (piInf (d.B.emb w)) := by
    have hk0 : (k.1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E))ᵀ * dbl (incM F d.Y.J) *
        (k.1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)).map (cA σ) = dbl (incM F d.Y.J) := k.2
    have := congrArg (fun x => x.map (piInf (d.B.emb w))) hk0
    simp only [Matrix.map_mul, Matrix.transpose_map, cstA] at this
    exact this
  exact commute_of_unitary_conjugate e1 e2 hMk hu hJ hk2
end PositivityTheory.SiegelWeilFormula.KK
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopAway
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped Matrix Classical
open NumberField MeasureTheory GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def SD_k.IsAwayW (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (w : InfinitePlace F) (Ψ : Mx F E d.m d.n → ℂ) : Prop :=
  ∀ X Z, (∀ w', w' ≠ w → d.cw w' Z = 0) → finOne F • Z = 0 → Ψ (X + Z) = Ψ X
namespace RD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d)
def _root_.PositivityTheory.SiegelWeilFormula.RD_k.GoodAway (w : InfinitePlace F) (Ψ : Mx F E d.m d.n → ℂ) : Prop :=
  d.IsAwayW w Ψ ∧ Ψ ≠ 0 ∧ ∀ f, IsSw f → R.tens w f Ψ ∈ d.schM
end RD
def GoodAwayEx_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
  (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F), ∃ Ψ, R.GoodAway w Ψ
end PositivityTheory.SiegelWeilFormula
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopRelA
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
namespace SD
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem _root_.PositivityTheory.SiegelWeilFormula.SD_k.bb1 : incM F d.b.1 * incM F (d.b⁻¹).1 = 1 := by
  rw [← incM_mul', ← Units.val_mul, mul_inv_cancel, Units.val_one, incM_one']
theorem _root_.PositivityTheory.SiegelWeilFormula.SD_k.bb2 : incM F (d.b⁻¹).1 * incM F d.b.1 = 1 := by
  rw [← incM_mul', ← Units.val_mul, inv_mul_cancel, Units.val_one, incM_one']
theorem _root_.PositivityTheory.SiegelWeilFormula.SD_k.inFrame_mul (x y : d.G) : inFrame d.b (x * y) = inFrame d.b x * inFrame d.b y := by
  have hmul : mat2 (x * y) = mat2 x * mat2 y := rfl
  simp only [inFrame, hmul]
  calc incM F (d.b⁻¹).1 * (mat2 x * mat2 y) * incM F d.b.1
      = incM F (d.b⁻¹).1 * mat2 x * (incM F d.b.1 * incM F (d.b⁻¹).1) * mat2 y * incM F d.b.1 := by
        rw [d.bb1]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]
theorem _root_.PositivityTheory.SiegelWeilFormula.SD_k.inFrame_one : inFrame d.b (1 : d.G) = 1 := by
  change incM F (d.b⁻¹).1 * 1 * incM F d.b.1 = 1
  simpa only [Matrix.mul_one] using d.bb2
theorem _root_.PositivityTheory.SiegelWeilFormula.SD_k.inFrame_inj {x y : d.G} (h : inFrame d.b x = inFrame d.b y) : x = y := by
  have hx : mat2 x = incM F d.b.1 * inFrame d.b x * incM F (d.b⁻¹).1 := by
    simp only [inFrame, ← Matrix.mul_assoc, d.bb1, Matrix.one_mul]
    rw [Matrix.mul_assoc, d.bb1, Matrix.mul_one]
  have hy : mat2 y = incM F d.b.1 * inFrame d.b y * incM F (d.b⁻¹).1 := by
    simp only [inFrame, ← Matrix.mul_assoc, d.bb1, Matrix.one_mul]
    rw [Matrix.mul_assoc, d.bb1, Matrix.mul_one]
  have : mat2 x = mat2 y := by rw [hx, hy, h]
  exact Subtype.ext (Units.ext this)
end SD
end PositivityTheory.SiegelWeilFormula
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdPlace
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
namespace PositivityTheory.SiegelWeilFormula.Place
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem _root_.PositivityTheory.SiegelWeilFormula.SD_k.cm (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : IsCMExt F E σ := d.ok.good.cm
theorem _root_.PositivityTheory.SiegelWeilFormula.SD_k.std (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : IsStd d.B.ψ := d.ok.good.std
theorem continuous_cw_k (w : InfinitePlace F) {p q : Type} : Continuous (fun X : Matrix p q (AE F E) => d.cw w X) :=
  continuous_id.matrix_map (continuous_piInf (d.B.emb w))
theorem cw_ext_k {p q : Type} {X Z : Matrix p q (AE F E)} (h1 : ∀ w, d.cw w X = d.cw w Z) (h2 : finOne F • X = finOne F • Z) :
    X = Z :=
  mat_ext d.cm d.B.emb h1 h2
theorem cw_cA_k (w : InfinitePlace F) {p q : Type} (X : Matrix p q (AE F E)) : d.cw w (X.map (cA σ)) = (d.cw w X).map star :=
  map_cA d.cm _ X
end PositivityTheory.SiegelWeilFormula.Place
end
end
end

