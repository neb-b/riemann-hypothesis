module

public import Formalism.LocalToGlobal.GlobalTheory.GL4.LowerSlopeInequalityFamily
public import Mathlib
public import Formalism.GL3MeanSquares.Bundle0001
public import Formalism.LocalToGlobal.Columns.Bundle0016
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL4.BcBasisApply
section
open Module NumberField

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions.flipTwoThree

section Fun

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {u : D.what₂.Word} (CV : ColVal D u)

theorem bc_sum_repr (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) (z : (D.sp.X 0).V) :
    CV.bc c τ z = ∑ i, CV.rho τ ((D.sp.X 0).frame.repr z i) • CV.bc c τ ((D.sp.X 0).frame i) := by
  conv_lhs => rw [← (D.sp.X 0).frame.sum_repr z]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => CV.bc_smul c τ _ _

theorem span_bc_frame (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) :
    ⊤ ≤ Submodule.span D.what₂.LL (Set.range fun i => CV.bc c τ ((D.sp.X 0).frame i)) := by
  rw [← (CV.Q_good c τ).2.2]
  refine Submodule.span_le.2 ?_
  intro x hx
  have hx' : x ∈ (Submodule.span D.what₂.LL (Set.range fun i => CV.bc c τ ((D.sp.X 0).frame i))).restrictScalars (𝓞 D.what₂.LL) := by
    rw [CV.bc_L c τ] at hx
    refine (Submodule.span_le.2 ?_) hx
    rintro _ ⟨z, -, rfl⟩
    rw [SetLike.mem_coe, Submodule.restrictScalars_mem, bc_sum_repr CV c τ z]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  exact hx'

theorem card_frame_eq (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) :
    Fintype.card (Fin (D.sp.X 0).rank) = finrank D.what₂.LL (CV.Q c τ).V := by
  rw [Fintype.card_fin, finrank_eq_card_basis (CV.Q c τ).b, Fintype.card_congr (CV.eQ c τ), Fintype.card_fin, D.sp.rank0, Ranks.N_zero]

def bcBasis (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) : Basis (Fin (D.sp.X 0).rank) D.what₂.LL (CV.Q c τ).V :=
  basisOfTopLeSpanOfCardEqFinrank (fun i => CV.bc c τ ((D.sp.X 0).frame i)) (span_bc_frame CV c τ) (card_frame_eq CV c τ)

theorem bcBasis_apply (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) (i : Fin (D.sp.X 0).rank) :
    bcBasis CV c τ i = CV.bc c τ ((D.sp.X 0).frame i) := by
  unfold bcBasis
  rw [coe_basisOfTopLeSpanOfCardEqFinrank]

def bcFun (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) (y : (D.sp.X 0).V) : (CV.Q c τ).V →ₗ[D.what₂.LL] D.what₂.LL :=
  (bcBasis CV c τ).constr D.what₂.LL fun i => CV.rho τ ((D.sp.X 0).hT y ((D.sp.X 0).frame i))

theorem bcFun_bc (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) (y z : (D.sp.X 0).V) :
    bcFun CV c τ y (CV.bc c τ z) = CV.rho τ ((D.sp.X 0).hT y z) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [bc_sum_repr CV c τ z, map_sum]
  simp_rw [map_smul]
  have h1 : ∀ i, bcFun CV c τ y (CV.bc c τ ((D.sp.X 0).frame i)) = CV.rho τ ((D.sp.X 0).hT y ((D.sp.X 0).frame i)) := fun i => by
    unfold bcFun
    rw [← bcBasis_apply CV c τ i, Basis.constr_basis]
  simp_rw [h1, smul_eq_mul, ← map_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum]
  congr 1
  conv_rhs => rw [← (D.sp.X 0).frame.sum_repr z]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]

theorem bcFun_int (c : (D.mem u).C.cls 0) (τ : D.what₂.Tau) {y : (D.sp.X 0).V}
    (hy : y ∈ dualSub (D.sp.X 0) (D.clsLat u 0 c)) {x : (CV.Q c τ).V} (hx : x ∈ (CV.Q c τ).L) :
    IsIntegral ℤ (bcFun CV c τ y x) := by
  rw [CV.bc_L c τ] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    rw [bcFun_bc]
    obtain ⟨o, ho⟩ := hy z hz
    have e : (D.sp.X 0).hT y z = starRingEnd D.host.E ((D.sp.X 0).hT z y) := ((D.sp.X 0).herm.eq z y).symm
    rw [e, ← ho]
    exact ((o.isIntegral_coe.map (starRingEnd D.host.E).toIntAlgHom).map (CV.rho τ).toIntAlgHom)
  | zero => rw [map_zero]; exact isIntegral_zero
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact hx.add hy
  | smul a x _ hx =>
    rw [← algebraMap_smul D.what₂.LL a x, map_smul, smul_eq_mul]
    exact a.isIntegral_coe.mul hx

end Fun

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL4.ShortAtMeanLog
section
open NumberField

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.MainNotions.flipTwoThree Formalism.HN

theorem trace_re_sum (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (z : E) :
    ((Algebra.trace ℚ E z : ℚ) : ℝ) = ∑ w : InfinitePlace E, 2 * (w.embedding z).re := by
  classical
  have h1 : ((Algebra.trace ℚ E z : ℚ) : ℂ) = ∑ φ : E →+* ℂ, φ z := by
    have h : algebraMap ℚ ℂ (Algebra.trace ℚ E z) = ∑ σ : E →ₐ[ℚ] ℂ, σ z :=
      trace_eq_sum_embeddings ℂ (x := z)
    rw [show ((Algebra.trace ℚ E z : ℚ) : ℂ) = algebraMap ℚ ℂ (Algebra.trace ℚ E z) from
      (eq_ratCast _ _).symm, h]
    exact (Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) (fun φ : E →+* ℂ => φ z)
      (fun σ : E →ₐ[ℚ] ℂ => σ z) (fun _ => rfl)).symm
  have h2 : ((Algebra.trace ℚ E z : ℚ) : ℝ) = ∑ φ : E →+* ℂ, (φ z).re := by
    rw [← Complex.re_sum, ← h1, Complex.ratCast_re]
  rw [h2, ← Finset.sum_fiberwise Finset.univ (fun φ : E →+* ℂ => InfinitePlace.mk φ)
    (fun φ : E →+* ℂ => (φ z).re)]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hfib : ∀ φ ∈ Finset.univ.filter (fun φ : E →+* ℂ => InfinitePlace.mk φ = w),
      (φ z).re = (w.embedding z).re := by
    intro φ hφ
    have hw := (Finset.mem_filter.mp hφ).2
    subst hw
    rcases InfinitePlace.embedding_mk_eq φ with h | h
    · rw [h]
    · rw [h, ComplexEmbedding.conjugate_coe_eq, Complex.conj_re]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, InfinitePlace.card_filter_mk_eq, nsmul_eq_mul]
  have hm : w.mult = 2 := InfinitePlace.mult_isComplex ⟨w, IsTotallyComplex.isComplex w⟩
  rw [hm]
  norm_num

theorem two_nPl (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] : 2 * nPl E = Module.finrank ℚ E := by
  classical
  rw [← InfinitePlace.sum_mult_eq]
  have h : ∀ w : InfinitePlace E, w.mult = 2 := fun w =>
    InfinitePlace.mult_isComplex ⟨w, IsTotallyComplex.isComplex w⟩
  simp only [h, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  unfold nPl
  ring

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private lemma sum_log_le_card_mul_log_mean_of_pos {ι : Type*} [Fintype ι] (S : ι → ℝ) (hS : ∀ i, 0 < S i)
    (hn : 0 < (Fintype.card ι : ℝ)) :
    ∑ i, Real.log (S i) ≤ (Fintype.card ι : ℝ) * Real.log ((∑ i, S i) / Fintype.card ι) := by
  have hT : 0 < ∑ i, S i := by
    have : Nonempty ι := Fintype.card_pos_iff.mp (by exact_mod_cast hn)
    exact Finset.sum_pos (fun i _ => hS i) Finset.univ_nonempty
  set M := (∑ i, S i) / (Fintype.card ι : ℝ) with hM
  have hMpos : 0 < M := div_pos hT hn
  have h1 : ∀ i, Real.log (S i) - Real.log M ≤ S i / M - 1 := by
    intro i
    rw [← Real.log_div (hS i).ne' hMpos.ne']
    exact Real.log_le_sub_one_of_pos (div_pos (hS i) hMpos)
  have h2 : ∑ i, (Real.log (S i) - Real.log M) ≤ ∑ i, (S i / M - 1) :=
    Finset.sum_le_sum fun i _ => h1 i
  have h3 : (∑ i, S i) / M = (Fintype.card ι : ℝ) := by
    have := hT.ne'
    have := hn.ne'
    rw [hM]
    field_simp
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_div, h3, Finset.sum_const,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul, mul_one] at h2
  linarith

theorem shortAt_mean_log (D : D7) (u : D.what₂.Word) (c : (D.mem u).C.cls 0) [IsTotallyComplex D.host.E]
    (y : Fin (D.R.N 0) → (D.sp.X 0).V) (hy : Formalism.MainNotions.flipTwoThree.ShortAt D u c y)
    (hpos : ∀ (w : InfinitePlace D.host.E) a, 0 < (w.embedding ((D.sp.X 0).hT (y a) (y a))).re) :
    (∑ w : InfinitePlace D.host.E, Real.log (∑ a, (w.embedding ((D.sp.X 0).hT (y a) (y a))).re)) / (nPl D.host.E : ℝ) ≤
      Real.log ((D.R.k : ℝ) ^ 3 * (2 * D.host.v) ^ 2) := by
  classical
  obtain ⟨-, -, htr⟩ := hy
  have hk : D.R.N 0 = D.R.k := Formalism.BasicNotions.Ranks.N_zero D.R
  have hfin := Formalism.MainNotions.flipTwoThree.b_finrank_host D
  have hnf : nPl D.host.E = D.R.f := by
    have h2 := two_nPl D.host.E
    rw [hfin] at h2
    omega
  have hfo : D.R.f = 2 * D.R.ord := Formalism.BasicNotions.Ranks.f_eq_ord D.R
  have hf : 0 < D.R.f := by
    have := D.R.m_le_f
    have := D.R.two_le_m
    omega
  have hfR : (0 : ℝ) < D.R.f := by exact_mod_cast hf
  have hbound : ∀ a, ∑ w : InfinitePlace D.host.E, (w.embedding ((D.sp.X 0).hT (y a) (y a))).re ≤
      (D.R.f : ℝ) * ((D.R.k : ℝ) ^ 2 * (2 * D.host.v) ^ 2) := by
    intro a
    have h := htr a
    rw [trace_re_sum, div_le_iff₀ (by linarith), ← Finset.mul_sum] at h
    nlinarith [h]
  have hS : ∀ w : InfinitePlace D.host.E, 0 < ∑ a, (w.embedding ((D.sp.X 0).hT (y a) (y a))).re := by
    intro w
    have hne : (Finset.univ : Finset (Fin (D.R.N 0))).Nonempty := by
      refine ⟨⟨0, ?_⟩, Finset.mem_univ _⟩
      rw [hk]
      have := D.R.m_add_three_le_k
      omega
    exact Finset.sum_pos (fun a _ => hpos w a) hne
  have htot : ∑ w : InfinitePlace D.host.E, ∑ a, (w.embedding ((D.sp.X 0).hT (y a) (y a))).re ≤
      (D.R.k : ℝ) * ((D.R.f : ℝ) * ((D.R.k : ℝ) ^ 2 * (2 * D.host.v) ^ 2)) := by
    rw [Finset.sum_comm]
    calc _ ≤ ∑ _a : Fin (D.R.N 0), (D.R.f : ℝ) * ((D.R.k : ℝ) ^ 2 * (2 * D.host.v) ^ 2) :=
          Finset.sum_le_sum fun a _ => hbound a
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hk, nsmul_eq_mul]
  have hcard : (nPl D.host.E : ℝ) = (Fintype.card (InfinitePlace D.host.E) : ℝ) := rfl
  have hcf : (Fintype.card (InfinitePlace D.host.E) : ℝ) = D.R.f := by
    rw [← hcard]
    exact_mod_cast hnf
  have hnpos : (0 : ℝ) < (Fintype.card (InfinitePlace D.host.E) : ℝ) := by rw [hcf]; exact hfR
  have key := sum_log_le_card_mul_log_mean_of_pos _ hS hnpos
  have hTpos : 0 < ∑ w : InfinitePlace D.host.E, ∑ a, (w.embedding ((D.sp.X 0).hT (y a) (y a))).re :=
    Finset.sum_pos (fun w _ => hS w)
      (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp (by exact_mod_cast hnpos)))
  rw [hcard, div_le_iff₀ hnpos]
  refine key.trans ?_
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ hnpos.le
  apply Real.log_le_log (div_pos hTpos hnpos)
  rw [div_le_iff₀ hnpos, hcf]
  nlinarith [htot]

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.GL4.ThirdPropositionOfClass
section
open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.HN Formalism.MainNotions.flipTwoThree Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps

theorem hTV0 (D : D7) (u : D.what₂.Word) : TSpan D.what₂.LL ((D.fm u).lam 0) = VV D.what₂.LL ((D.fm u).lam 0) :=
  translate_span_eq D.what₂.LL D.what₂.Tau (D.R.N 0) ((D.fm u).lam 0)

section Orth

variable {D : D7} {u : D.what₂.Word} (CV : ColVal D u)


open Classical in
def prjC (c : (D.mem u).C.cls 0) : ((D.fm u).lat 0).V →ₗ[D.what₂.LL] ((D.fm u).lat 0).V :=
  ((coE CV (hTV0 D u)).symm : ((D.mem u).C.cls 0 → VV D.what₂.LL ((D.fm u).lam 0)) →ₗ[D.what₂.LL] ((D.fm u).lat 0).V) ∘ₗ
    (LinearMap.single D.what₂.LL (fun _ : (D.mem u).C.cls 0 => VV D.what₂.LL ((D.fm u).lam 0)) c ∘ₗ
      (LinearMap.proj c ∘ₗ (coE CV (hTV0 D u) : ((D.fm u).lat 0).V →ₗ[D.what₂.LL] ((D.mem u).C.cls 0 → VV D.what₂.LL ((D.fm u).lam 0)))))

open Classical in
theorem co_prjC (c c' : (D.mem u).C.cls 0) (x : ((D.fm u).lat 0).V) :
    CV.co (prjC CV c x) c' = if c' = c then CV.co x c else 0 := by
  have hE : ∀ (y : ((D.fm u).lat 0).V) (c'' : (D.mem u).C.cls 0),
      CV.co y c'' = ((coE CV (hTV0 D u) y c'' : VV D.what₂.LL ((D.fm u).lam 0)) : _) := fun _ _ => rfl
  have hP : coE CV (hTV0 D u) (prjC CV c x) = Pi.single c (coE CV (hTV0 D u) x c) := by
    simp [prjC]
  rw [hE, hP, hE x c]
  by_cases h : c' = c
  · subst h
    simp
  · simp [h]

private theorem coE_prjC_self (c : (D.mem u).C.cls 0) (x : ((D.fm u).lat 0).V) :
    coE CV (hTV0 D u) (prjC CV c x) c = coE CV (hTV0 D u) x c := by
  classical
  simp [prjC]

private theorem coE_prjC_of_ne_eq_zero (c c' : (D.mem u).C.cls 0) (x : ((D.fm u).lat 0).V) (h : c' ≠ c) :
    coE CV (hTV0 D u) (prjC CV c x) c' = 0 := by
  classical
  simp [prjC, h]

theorem prjC_sum (x : ((D.fm u).lat 0).V) : ∑ c, prjC CV c x = x := by
  apply (coE CV (hTV0 D u)).injective
  funext c'
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_apply, Finset.sum_eq_single c']
  · exact coE_prjC_self CV c' x
  · intro b _ hb
    exact coE_prjC_of_ne_eq_zero CV b c' x (Ne.symm hb)
  · intro h
    exact absurd (Finset.mem_univ _) h

def NC (c : (D.mem u).C.cls 0) : Submodule (𝓞 D.what₂.LL) ((D.fm u).lat 0).V :=
  ((D.fm u).lat 0).L.map ((prjC CV c).restrictScalars (𝓞 D.what₂.LL))

theorem prjC_mem (c : (D.mem u).C.cls 0) {x : ((D.fm u).lat 0).V} (hx : x ∈ ((D.fm u).lat 0).L) :
    prjC CV c x ∈ ((D.fm u).lat 0).L := by
  refine Formalism.L2.Ker.mem_of_forall_locP _ fun Q => ?_
  obtain ⟨w, rfl⟩ : ∃ w, D.plEq w = Q := ⟨D.plEq.symm Q, D.plEq.apply_symm_apply Q⟩
  rw [mem_localization_iff_localizationAtPlace]
  have hγ : ∀ c τ, ∃ γ, LocBasis D w (CV.Q c τ) (CV.eQ c τ) γ := fun c τ =>
    exists_locBasis w (CV.Q c τ) (CV.Q_good c τ) (CV.eQ c τ)
  choose γ hγ using hγ
  have hxw : x ∈ locW D.what₂.places w ((D.fm u).lat 0).L := Submodule.subset_span hx
  rw [CV.fin w γ hγ] at hxw
  rw [CV.fin w γ hγ]
  intro c'
  rw [co_prjC]
  split_ifs with h
  · subst h
    exact hxw c'
  · have e : actAll ((D.fm u).lam 0) (fun τ => (γ c' τ)⁻¹) (0 : MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) D.what₂.LL) = 0 := by
      simp [actAll]
    rw [e]
    exact zero_mem _

theorem iSup_NC : (⨆ c, NC CV c) = ((D.fm u).lat 0).L := by
  apply le_antisymm
  · refine iSup_le fun c => ?_
    rintro _ ⟨x, hx, rfl⟩
    exact prjC_mem CV c hx
  · intro x hx
    rw [← prjC_sum CV x]
    exact Submodule.sum_mem _ fun c _ => Submodule.mem_iSup_of_mem c ⟨x, hx, rfl⟩

theorem tcAt_eq_zero {v : InfinitePlace D.what₂.LL} {c : (D.mem u).C.cls 0} {x : ((D.fm u).lat 0).V} (h : CV.co x c = 0) :
    tcAt CV v c x = 0 := by
  simp [tcAt, h]

theorem NC_orth (c c' : (D.mem u).C.cls 0) (hcc : c ≠ c') :
    ∀ x ∈ NC CV c, ∀ y ∈ NC CV c', ∀ v, majAt ((D.fm u).lat 0).b ((D.fm u).lat 0).X v x y = 0 := by
  rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩ v
  simp only [LinearMap.restrictScalars_apply]
  rw [majorant_lattice_eq_sum CV]
  refine Finset.sum_eq_zero fun c'' _ => ?_
  by_cases h : c'' = c
  · subst h
    have : tcAt CV v c'' (prjC CV c' y) = 0 := tcAt_eq_zero CV (by rw [co_prjC, if_neg hcc])
    rw [this, nfAll_zero_left]
  · have : tcAt CV v c'' (prjC CV c x) = 0 := tcAt_eq_zero CV (by rw [co_prjC, if_neg h])
    rw [this, nfAll_zero_right]

theorem injOn_NC (c : (D.mem u).C.cls 0) {W : Type} [AddCommGroup W] [Module D.what₂.LL W]
    (ψ : VV D.what₂.LL ((D.fm u).lam 0) →ₗ[D.what₂.LL] W) (hψ : Function.Injective ψ) :
    Set.InjOn (ψ ∘ₗ (LinearMap.proj c ∘ₗ (coE CV (hTV0 D u) : ((D.fm u).lat 0).V →ₗ[D.what₂.LL]
      ((D.mem u).C.cls 0 → VV D.what₂.LL ((D.fm u).lam 0))))) (NC CV c) := by
  rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩ hxy
  have h := hψ hxy
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe,
    LinearMap.coe_proj, Function.eval] at h ⊢
  apply (coE CV (hTV0 D u)).injective
  funext c'
  by_cases hc : c' = c
  · subst hc
    exact h
  · rw [coE_prjC_of_ne_eq_zero CV c c' x hc, coE_prjC_of_ne_eq_zero CV c c' y hc]

end Orth

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.HN Formalism.MainNotions.flipTwoThree Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps

section Rank

variable {D : D7} {u : D.what₂.Word} (CV : ColVal D u)

theorem vv_finite_pos (D : D7) (u : D.what₂.Word) :
    Module.Finite D.what₂.LL (VV D.what₂.LL ((D.fm u).lam 0)) ∧ 0 < finrank D.what₂.LL (VV D.what₂.LL ((D.fm u).lam 0)) := by
  obtain ⟨Z, -, hne, -, -⟩ := standard_basis_z D.what₂.Tau (D.R.N 0) ((D.fm u).lam 0)
  have := Z.fin
  exact ⟨Module.Finite.of_basis (Z.basis D.what₂.LL), by rw [Module.finrank_eq_card_basis (Z.basis D.what₂.LL)]; exact Fintype.card_pos⟩

theorem range_prjC (c : (D.mem u).C.cls 0) :
    finrank D.what₂.LL (LinearMap.range (prjC CV c)) = finrank D.what₂.LL (VV D.what₂.LL ((D.fm u).lam 0)) := by
  classical
  have hsurj : LinearMap.range (LinearMap.proj c ∘ₗ (coE CV (hTV0 D u) : ((D.fm u).lat 0).V →ₗ[D.what₂.LL]
      ((D.mem u).C.cls 0 → VV D.what₂.LL ((D.fm u).lam 0)))) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro z
    refine ⟨(coE CV (hTV0 D u)).symm (Pi.single c z), ?_⟩
    simp
  unfold prjC
  rw [← LinearMap.comp_assoc, LinearMap.range_comp_of_range_eq_top _ hsurj]
  apply LinearMap.finrank_range_of_inj
  rw [LinearMap.coe_comp]
  exact (coE CV (hTV0 D u)).symm.injective.comp (by simpa using Pi.single_injective c)

theorem rk_NC (c : (D.mem u).C.cls 0) : rkK (NC CV c) = finrank D.what₂.LL (VV D.what₂.LL ((D.fm u).lam 0)) := by
  unfold Formalism.HN.rkK NC
  rw [Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, ((D.fm u).lat_good 0).2.2, Submodule.map_top]
  exact range_prjC CV c

theorem rank_lattice_level_zero (CV : ColVal D u) : rkK ((D.fm u).lat 0).L =
    Fintype.card ((D.mem u).C.cls 0) * finrank D.what₂.LL (VV D.what₂.LL ((D.fm u).lam 0)) := by
  obtain ⟨hfin, -⟩ := vv_finite_pos D u
  unfold Formalism.HN.rkK
  rw [((D.fm u).lat_good 0).2.2, finrank_top, LinearEquiv.finrank_eq (coE CV (hTV0 D u)), Module.finrank_pi_fintype,
    Finset.sum_const, Finset.card_univ, smul_eq_mul]

theorem NC_ne_bot (c : (D.mem u).C.cls 0) : NC CV c ≠ ⊥ := by
  intro h0
  have h1 := rk_NC CV c
  rw [h0] at h1
  have h2 : Formalism.HN.rkK (⊥ : Submodule (𝓞 D.what₂.LL) ((D.fm u).lat 0).V) = 0 := by
    unfold Formalism.HN.rkK
    rw [Submodule.bot_coe, Submodule.span_zero_singleton, finrank_bot]
  have := (vv_finite_pos D u).2
  omega

theorem muMax_le_class : ∃ c, ((D.fm u).lat 0).muMax ≤ (withL ((D.fm u).lat 0) (NC CV c)).muMax := by
  classical
  have : Nonempty ((D.mem u).C.cls 0) := CV.ne
  have key := Formalism.L2.Col.hlat_orth_sum (A := (D.fm u).lat 0) (NC CV) ((D.fm u).lat_good 0).1
    (fun c => ((D.fm u).lat_good 0).2.1.map _) (NC_ne_bot CV) (NC_orth CV)
    (finrank D.what₂.LL (VV D.what₂.LL ((D.fm u).lam 0))) (vv_finite_pos D u).2 (rk_NC CV)
    (by rw [iSup_NC CV]; exact rank_lattice_level_zero CV)
  obtain ⟨c, hc⟩ := key.2
  rw [iSup_NC CV] at hc
  exact ⟨c, hc⟩

end Rank

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def SlopeMaxClass (D : D7) : Prop :=
  ∀ u (CV : ColVal D u) (c : (D.mem u).C.cls 0), (∃ y : Fin (D.R.N 0) → (D.sp.X 0).V, Formalism.MainNotions.flipTwoThree.ShortAt D u c y) →
    (withL ((D.fm u).lat 0) (NC CV c)).muMax ≤
      ∑ τ, (colAbsP D u τ * Real.log (4 * (D.R.k : ℝ) ^ 4 * D.host.v ^ 2) +
        Real.log (cNu ((D.fm u).lam 0 τ).natW) - (lamCol D u τ (D.R.k - 1) : ℝ) * Real.log (Tu D u))

theorem slopeMaxGiven_of_class (D : D7) (h : SlopeMaxClass D) : SlopeMaxGiven D := by
  intro u CV hs
  obtain ⟨c, hc⟩ := muMax_le_class CV
  exact hc.trans (h u CV c (hs c))

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

