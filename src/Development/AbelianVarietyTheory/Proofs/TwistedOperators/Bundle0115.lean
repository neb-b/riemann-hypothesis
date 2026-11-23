module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0760
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelExistsUniqueGLn
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0330
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0543
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0513
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsDetOnStableSubspaceExpSmul
section
open Matrix

namespace GlobalTheory.FlagMeas

theorem detOn_exp_smul : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (V : Submodule ℂ (Fin n → ℂ)),
    (∀ y ∈ V, A *ᵥ y ∈ V) → ∃ c : ℝ, ∀ t : ℝ,
      GlobalTheory.FlagMeas.detOn (NormedSpace.exp (t • A)) V = Real.exp (t * c) := by
  intro n A V hA
  have hA' : ∀ y ∈ V, Matrix.toLin' A y ∈ V := fun y hy => by
    rw [Matrix.toLin'_apply]; exact hA y hy
  set f : V →ₗ[ℂ] V := (Matrix.toLin' A).restrict hA' with hf
  set b := Module.finBasis ℂ V with hb
  set B := LinearMap.toMatrixAlgEquiv b f with hB
  refine ⟨(B.trace).re, fun t => ?_⟩
  have hts : t • A = (t : ℂ) • A := by ext i j; simp [Complex.real_smul]
  rw [hts]
  set s : ℂ := (t : ℂ) with hs
  have hpowA : ∀ (k : ℕ) (v : V), (s • A) ^ k *ᵥ (v : Fin n → ℂ) = (((s • f) ^ k) v : Fin n → ℂ) := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      rw [pow_succ', pow_succ', ← Matrix.mulVec_mulVec, ih, Module.End.mul_apply]
      simp [hf, LinearMap.restrict_apply, Matrix.toLin'_apply, Matrix.smul_mulVec]
  have hpowB : ∀ k : ℕ, Matrix.toLinAlgEquiv b ((s • B) ^ k) = (s • f) ^ k := by
    intro k
    rw [map_pow, map_smul, hB, Matrix.toLinAlgEquiv_toMatrixAlgEquiv]
  have key : ∀ v : V, NormedSpace.exp (s • A) *ᵥ (v : Fin n → ℂ) =
      ((Matrix.toLinAlgEquiv b (NormedSpace.exp (s • B))) v : Fin n → ℂ) := by
    intro v
    open scoped Matrix.Norms.Operator in
    have h1 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (s • A)
    open scoped Matrix.Norms.Operator in
    have h2 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (s • B)
    let g1 : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (Fin n → ℂ) :=
      LinearMap.applyₗ (v : Fin n → ℂ) ∘ₗ Matrix.toLin'.toLinearMap
    let g2 : Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ →ₗ[ℂ] (Fin n → ℂ) :=
      V.subtype ∘ₗ LinearMap.applyₗ v ∘ₗ (Matrix.toLinAlgEquiv b).toLinearMap
    have h1' := h1.map g1 (LinearMap.continuous_of_finiteDimensional g1)
    have h2' := h2.map g2 (LinearMap.continuous_of_finiteDimensional g2)
    have heq : (g1 ∘ fun k : ℕ => ((k.factorial : ℂ)⁻¹) • (s • A) ^ k) =
        (g2 ∘ fun k : ℕ => ((k.factorial : ℂ)⁻¹) • (s • B) ^ k) := by
      funext k
      simp only [Function.comp_apply, map_smul, g1, g2, LinearMap.comp_apply, LinearMap.applyₗ_apply_apply,
        LinearEquiv.coe_coe, Matrix.toLin'_apply, AlgEquiv.toLinearMap_apply, Submodule.subtype_apply]
      rw [hpowA, hpowB]
    rw [heq] at h1'
    exact h1'.unique h2'
  have hstab : ∀ y ∈ V, Matrix.toLin' (NormedSpace.exp (s • A)) y ∈ V := fun y hy => by
    rw [Matrix.toLin'_apply, key ⟨y, hy⟩]; exact Submodule.coe_mem _
  have hres : (Matrix.toLin' (NormedSpace.exp (s • A))).restrict hstab =
      Matrix.toLinAlgEquiv b (NormedSpace.exp (s • B)) := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    simp only [LinearMap.restrict_coe_apply, Matrix.toLin'_apply]
    exact key v
  rw [detOn, dite_eq_left hstab, hres]
  show ‖LinearMap.det (Matrix.toLin b b (NormedSpace.exp (s • B)))‖ = _
  rw [LinearMap.det_toLin, GlobalTheory.SUVol.det_exp, Matrix.trace_smul, smul_eq_mul, Complex.norm_exp, hs,
    Complex.re_ofReal_mul]

end GlobalTheory.FlagMeas
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGenericSeriesSquarefreeLabels
section
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.BadShare GlobalTheory.BadShare.Basic
open scoped Classical

namespace GlobalTheory.GLq.SqSeries

variable {g : ℕ} [Fact g.Prime]

theorem isClass_of_isChar {G : Type} [Group G] {χ : G → ℂ} (h : IsChar χ) : IsClass χ := by
  obtain ⟨V, hV⟩ := h
  intro x y
  rw [← hV, ← hV, FDRep.char_conj]

theorem wh_one_zero (ψ : AddChar (ZMod g) ℂ) : wh ψ (fun _ : Gn g 0 => (1 : ℂ)) = 1 := by
  haveI : Subsingleton (Gn g 0) := ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
  unfold wh tr
  rw [Fintype.sum_subsingleton _ 1, eU, coeff_eDat, mul_one]
  have hU : ∀ u : Gn g 0, IsUniUp u.val := fun u a => a.elim0
  have hc : Nat.card {u : GG g 0 // IsUniUp u.val} = 1 := by
    haveI : Nonempty {u : GG g 0 // IsUniUp u.val} := ⟨⟨1, hU 1⟩⟩
    exact Nat.card_unique
  unfold eps
  rw [if_pos (hU 1), hc]
  simp

theorem wh_const_mul (ψ : AddChar (ZMod g) ℂ) {n : ℕ} (c : ℂ) (χ : Gn g n → ℂ) :
    wh ψ (fun x => c * χ x) = c * wh ψ χ := by
  unfold wh tr
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem wh_hcL (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) (L : List (Pc g))
    (h : ∀ p ∈ L, IsCusp p.2 ∧ p.2 1 = ∏ i ∈ Finset.Ico 1 p.1, ((g : ℂ) ^ i - 1)) :
    wh ψ (hcL L (degL L)) = 1 := by
  induction L with
  | nil => exact wh_one_zero ψ
  | cons p L ih =>
    have hp := h p List.mem_cons_self
    have hL := fun q hq => h q (List.mem_cons_of_mem p hq)
    have hch : ∀ q : Pc g, IsCusp q.2 → IsChar q.2 := fun q hq => by
      obtain ⟨V, -, hV⟩ := hq.2.1
      exact ⟨V, hV⟩
    have c1 := isClass_of_isChar (hch p hp.1)
    have c2 := isClass_of_isChar (_root_.GlobalTheory.gl_list_product_perm_char g L L _ rfl fun q hq => hch q (hL q hq).1).1
    rw [hcL_cons, hc, _root_.GlobalTheory.GLq.WhMul.wh_hcT g ψ hψ p.1 (degL L) _ (by simp [degL]) _
      (fun y a b => by simp only [c1 a b]) (fun x a b => by simp only [c2 a b])]
    simp only [wh_const_mul, ih hL, mul_one]
    exact _root_.GlobalTheory.GLq.wh_cusp_eq_one g ψ hψ _ _ hp.1 hp.2

theorem isGeneric_of_wh (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) {n : ℕ} (hn : 0 < n) (V : FDRep ℂ (GG g n))
    (h : wh ψ V.character ≠ 0) : IsGeneric V.ρ := by
  have hk : 0 + 0 < n := hn
  refine ⟨levOfChar ψ hψ n false 0 0 hk, rfl, ?_⟩
  have h1 : op V.ρ (levOfChar ψ hψ n false 0 0 hk).e ≠ 0 := by
    intro h0
    apply h
    have := congrArg (LinearMap.trace ℂ V) h0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zero, op, map_sum] at this
    rw [← this]
    unfold wh tr
    refine Finset.sum_congr (by congr) fun x _ => ?_
    rw [coeff_eU ψ hψ 0 0 hk, map_smul, smul_eq_mul]
    rfl
  obtain ⟨y, hy⟩ : ∃ y, op V.ρ (levOfChar ψ hψ n false 0 0 hk).e y ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h1 (LinearMap.ext hc)
  refine ⟨_, hy, fun u hu => ?_⟩
  exact (GlobalTheory.BadShare.EpsProj.mem_range_iff V.ρ (mem_one _) (fun _ _ => mem_mul _) (chi_one _) (fun _ _ => chi_mul _) _).1
    ⟨y, rfl⟩ u ⟨hu, fun hs => absurd hs (by simp [levOfChar])⟩

theorem deg_hcL (L : List (Pc g)) (n : ℕ) (hn : n = degL L)
    (h : ∀ p ∈ L, 0 < p.1 ∧ p.2 1 = ∏ i ∈ Finset.Ico 1 p.1, ((g : ℂ) ^ i - 1)) :
    hcL L n 1 * (L.map fun p => ((g : ℂ) ^ p.1 - 1)).prod = ∏ i ∈ Finset.range n, ((g : ℂ) ^ (i + 1) - 1) := by
  have H := _root_.GlobalTheory.GLq.HcDeg.hc_degree g L n hn
  have e1 : (L.map fun p => ∏ i ∈ Finset.Icc 1 p.1, ((g : ℂ) ^ i - 1)).prod =
      (L.map fun p => ((g : ℂ) ^ p.1 - 1)).prod * (L.map fun p => p.2 1).prod := by
    rw [← List.prod_map_mul]
    congr 1
    refine List.map_congr_left fun p hp => ?_
    rw [(h p hp).2, ← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_succ_top (h p hp).1, mul_comm]
  have e2 : (L.map fun p => p.2 1).prod ≠ 0 := by
    refine List.prod_ne_zero fun h0 => ?_
    obtain ⟨p, hp, h1⟩ := List.mem_map.1 h0
    rw [(h p hp).2, Finset.prod_eq_zero_iff] at h1
    obtain ⟨i, hi, h2⟩ := h1
    have h3 : g ^ i = 1 := by exact_mod_cast sub_eq_zero.1 h2
    have h4 := (Fact.out : g.Prime).one_lt
    have h5 := (Finset.mem_Ico.1 hi).1
    have := Nat.one_lt_pow (n := i) (by omega) h4
    omega
  rw [e1, ← mul_assoc] at H
  rw [mul_right_cancel₀ e2 H, ← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range]
  simp [add_comm]

theorem exists_series : GlobalTheory.GLq.Green → ∀ (g : ℕ) [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) (n : ℕ), 5 ≤ g → 0 < n → ∃ τ : (ZMod g)[X] → GlobalTheory.BadShare.GG g n → ℂ, GlobalTheory.BadShare.IsSeries τ ∧ ∀ f ∈ GlobalTheory.BadShare.sqSet g n, ∀ x, (GlobalTheory.GLq.eSerC L n f).coeff x = GlobalTheory.BadShare.zc (τ f) x := by
  intro hG g _ L n hg hn
  obtain ⟨H1, -, H3⟩ := _root_.GlobalTheory.GLq.Label.label_main g L hg hG n
  have H4 := fun (f : (ZMod g)[X]) (hf : f ∈ sqSet g n) =>
    H3 f (mem_sqSet.1 hf).1 (mem_sqSet.1 hf).2.1 (mem_sqSet.1 hf).2.2.2 (mem_sqSet.1 hf).2.2.1
  choose! Q Q1 Q2 Q3 Q4 using H4
  have hmem : ∀ f ∈ sqSet g n, IsIrr (hcL ((Q f).map Prod.snd) n) ∧ HasLabel L (hcL ((Q f).map Prod.snd) n) f := by
    intro f hf
    have : hcL ((Q f).map Prod.snd) n ∈ {χ : Gn g n → ℂ | IsIrr χ ∧ HasLabel L χ f} := by
      rw [Q4 f hf]; rfl
    exact this
  refine ⟨fun f => hcL ((Q f).map Prod.snd) n, ⟨fun f hf f' hf' h => ?_, fun f hf => ?_⟩, fun f hf x => ?_⟩
  · have a := hmem f hf
    have b := (hmem f' hf').2
    have h' : hcL ((Q f).map Prod.snd) n = hcL ((Q f').map Prod.snd) n := h
    rw [← h'] at b
    exact (H1 _ a.1).unique a.2 b
  · obtain ⟨V, hs, hV⟩ := (hmem f hf).1
    have hV' : V.character = hcL ((Q f).map Prod.snd) n := funext hV
    have hc : ∀ p ∈ (Q f).map Prod.snd, IsCusp p.2 ∧ p.2 1 = ∏ i ∈ Finset.Ico 1 p.1, ((g : ℂ) ^ i - 1) := by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      exact ⟨(Q1 f hf q hq).1.2.1, (Q1 f hf q hq).2⟩
    refine ⟨V, hs, hV', ?_, ?_⟩
    · have hψ := (levStandard g n false 0 0 hn).hψ
      refine isGeneric_of_wh _ hψ hn V ?_
      have h1 := wh_hcL _ hψ _ hc
      rw [Q3 f hf] at h1
      rw [hV', h1]
      exact one_ne_zero
    · have h1 := deg_hcL _ n (Q3 f hf).symm fun p hp => ⟨(hc p hp).1.1, (hc p hp).2⟩
      have hpos : ∀ i, 1 ≤ g ^ i := fun i => Nat.one_le_pow _ _ (by omega)
      have h2 : (torusCard g f : ℂ) = (((Q f).map Prod.snd).map fun p => ((g : ℂ) ^ p.1 - 1)).prod := by
        rw [torusCard, degType, ← Q2 f hf]
        simp only [Multiset.map_coe, Multiset.prod_coe, List.map_map, Nat.cast_list_prod]
        congr 1
        refine List.map_congr_left fun q hq => ?_
        simp only [Function.comp]
        rw [(Q1 f hf q hq).1.1.2.2.2, Nat.cast_sub (hpos _)]
        simp
      rw [← hV', FDRep.char_one, ← h2] at h1
      apply Nat.cast_injective (R := ℂ)
      rw [Nat.cast_mul, h1, Nat.cast_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Nat.cast_sub (hpos _)]
      simp
  · rw [eSerC, Q4 f hf, finsum_mem_singleton]
    exact coeff_alg (zc _) x

end GlobalTheory.GLq.SqSeries
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteAlgebraAdelicLatticeProof
section
open GlobalTheory.RegSS

open Formalism.UG NumberField Topology
open scoped TensorProduct

namespace GlobalTheory.RegSSLattice

open NumberField Topology in
open scoped TensorProduct in
private lemma finite_setOf_algebraMap_mem_of_isCompact (F : Type) [Field F] [NumberField F]
    {K : Set (AdeleRing (𝓞 F) F)} (hK : IsCompact K) :
    {c : F | algebraMap F (AdeleRing (𝓞 F) F) c ∈ K}.Finite := by
  obtain ⟨U, hU, hUF⟩ := _root_.GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F
  have hsub : Filter.Tendsto (fun p : AdeleRing (𝓞 F) F × AdeleRing (𝓞 F) F => p.1 - p.2)
      (𝓝 (0, 0)) (𝓝 0) :=
    (continuous_fst.sub continuous_snd).tendsto' _ _ (by simp)
  have hpre : (fun p : AdeleRing (𝓞 F) F × AdeleRing (𝓞 F) F => p.1 - p.2) ⁻¹' U ∈
      𝓝 ((0 : AdeleRing (𝓞 F) F), (0 : AdeleRing (𝓞 F) F)) := hsub hU
  rw [nhds_prod_eq] at hpre
  obtain ⟨V, hV, W, hW, hVW⟩ := Filter.mem_prod_iff.mp hpre
  have hVU : ∀ v ∈ V ∩ W, ∀ w ∈ V ∩ W, v - w ∈ U := fun v hv w hw =>
    hVW (Set.mk_mem_prod hv.1 hw.2)
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun k => {y | y - k ∈ V ∩ W}) fun k _ =>
    (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds
      (by simpa using Filter.inter_mem hV hW)
  refine (t.finite_toSet.biUnion
    (t := fun k => {c : F | algebraMap F (AdeleRing (𝓞 F) F) c - k ∈ V ∩ W})
    fun k _ => ?_).subset fun c hc => ?_
  · refine Set.Subsingleton.finite fun c hc c' hc' => ?_
    have := hUF (c - c') (by simpa [map_sub] using hVU _ hc _ hc')
    exact sub_eq_zero.mp this
  · simpa using ht hc


open NumberField Topology in
open scoped TensorProduct in
theorem _root_.GlobalTheory.RegSSLattice.tensorLattice : _root_.GlobalTheory.RegSS.TensorLattice := by
  unfold _root_.GlobalTheory.RegSS.TensorLattice
  intro F B _ _ _ _ _
  haveI := _root_.GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := _root_.GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI := _root_.GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  obtain ⟨U, hU, hUF⟩ := _root_.GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero F
  haveI : Nontrivial (AdeleRing (𝓞 F) F) := ⟨⟨0, 1, fun h01 => one_ne_zero
    (hUF 1 (by rw [map_one, ← h01]; exact mem_of_mem_nhds hU))⟩⟩
  letI : Algebra (AdeleRing (𝓞 F) F) (B ⊗[F] AdeleRing (𝓞 F) F) :=
    Algebra.TensorProduct.rightAlgebra
  letI : TopologicalSpace (B ⊗[F] AdeleRing (𝓞 F) F) := _root_.Formalism.BasicNotions.tensTopL (AdeleRing (𝓞 F) F)
  haveI : IsModuleTopology (AdeleRing (𝓞 F) F) (B ⊗[F] AdeleRing (𝓞 F) F) := ⟨rfl⟩
  haveI : ContinuousAdd (B ⊗[F] AdeleRing (𝓞 F) F) :=
    IsModuleTopology.toContinuousAdd (AdeleRing (𝓞 F) F) _
  let b := Module.finBasis F B
  let c : B ⊗[F] AdeleRing (𝓞 F) F ≃ₗ[AdeleRing (𝓞 F) F] AdeleRing (𝓞 F) F ⊗[F] B :=
    { TensorProduct.comm F B (AdeleRing (𝓞 F) F) with
      map_smul' := fun a t => by
        induction t using TensorProduct.induction_on with
        | zero => simp
        | tmul x y =>
          change TensorProduct.comm F B _ (a • (x ⊗ₜ y)) = a • TensorProduct.comm F B _ (x ⊗ₜ y)
          rw [Algebra.smul_def]
          simp [Algebra.TensorProduct.right_algebraMap_apply, TensorProduct.smul_tmul', mul_comm]
        | add x y hx hy => simp_all [smul_add] }
  let e := c.trans (Algebra.TensorProduct.basis (AdeleRing (𝓞 F) F) b).equivFun
  haveI : Module.Finite (AdeleRing (𝓞 F) F) (B ⊗[F] AdeleRing (𝓞 F) F) :=
    Module.Finite.of_basis ((Algebra.TensorProduct.basis (AdeleRing (𝓞 F) F) b).map c.symm)
  let h : B ⊗[F] AdeleRing (𝓞 F) F ≃L[AdeleRing (𝓞 F) F]
      (Fin (Module.finrank F B) → AdeleRing (𝓞 F) F) :=
    { e with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }
  have he : ∀ β : B, h (_root_.Formalism.UG.inclE (AdeleRing (𝓞 F) F) β) =
      fun i => algebraMap F (AdeleRing (𝓞 F) F) (b.equivFun β i) := by
    intro β
    ext i
    show e (β ⊗ₜ 1) i = _
    simp [e, c, Algebra.TensorProduct.basis_repr_tmul]
  refine ⟨IsModuleTopology.isTopologicalRing (AdeleRing (𝓞 F) F) _,
    h.toHomeomorph.isClosedEmbedding.locallyCompactSpace, h.toHomeomorph.isEmbedding.t2Space,
    h.toHomeomorph.secondCountableTopology, _root_.Formalism.UG.P.inclE_injective F B (AdeleRing (𝓞 F) F), ?_, ?_⟩
  · intro D hD
    have hD' : IsCompact (h '' D) := hD.image h.continuous
    refine ((Set.Finite.pi (t := fun i => {x : F | algebraMap F (AdeleRing (𝓞 F) F) x ∈
      (fun y => y i) '' (h '' D)}) fun i => finite_setOf_algebraMap_mem_of_isCompact F
        (hD'.image (continuous_apply i))).preimage b.equivFun.injective.injOn).subset ?_
    intro β hβ
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_setOf_eq]
    intro i
    exact ⟨h (_root_.Formalism.UG.inclE (AdeleRing (𝓞 F) F) β), ⟨_, hβ, rfl⟩, by rw [he]⟩
  · obtain ⟨K, hK, hKF⟩ := _root_.GlobalTheory.AdeleCocompact.exists_compact_adele F
    refine ⟨h.symm '' Set.univ.pi fun _ => K,
      (isCompact_univ_pi fun _ => hK).image h.symm.continuous, fun x => ?_⟩
    choose y hy using fun i => hKF (h x i)
    refine ⟨b.equivFun.symm y, h (x - _root_.Formalism.UG.inclE (AdeleRing (𝓞 F) F) (b.equivFun.symm y)), ?_,
      by simp⟩
    intro i _
    rw [map_sub, he, LinearEquiv.apply_symm_apply]
    simpa using hy i

end GlobalTheory.RegSSLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply
section
noncomputable section

namespace GlobalTheory.ModuLR

open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

section Gen

variable {S : Type} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] {κ : Type} [Fintype κ] [DecidableEq κ]

def mulVecCE (M : Matrix κ κ S) (hM : IsUnit M.det) : (κ → S) ≃ₜ+ (κ → S) where
  toFun x := M *ᵥ x
  invFun x := M⁻¹ *ᵥ x
  left_inv x := by simp [mulVec_mulVec, nonsing_inv_mul M hM]
  right_inv x := by simp [mulVec_mulVec, mul_nonsing_inv M hM]
  map_add' x y := mulVec_add M x y
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

theorem mulVecCE_apply (M : Matrix κ κ S) (hM : IsUnit M.det) (x : κ → S) : mulVecCE M hM x = M *ᵥ x := rfl

end Gen

def prodCE {G₁ G₂ : Type} [AddCommGroup G₁] [TopologicalSpace G₁] [AddCommGroup G₂] [TopologicalSpace G₂]
    (e₁ : G₁ ≃ₜ+ G₁) (e₂ : G₂ ≃ₜ+ G₂) : (G₁ × G₂) ≃ₜ+ (G₁ × G₂) :=
  { AddEquiv.prodCongr e₁.toAddEquiv e₂.toAddEquiv with
    continuous_toFun := e₁.continuous.prodMap e₂.continuous
    continuous_invFun := e₁.symm.continuous.prodMap e₂.symm.continuous }

theorem prodCE_apply {G₁ G₂ : Type} [AddCommGroup G₁] [TopologicalSpace G₁] [AddCommGroup G₂]
    [TopologicalSpace G₂] (e₁ : G₁ ≃ₜ+ G₁) (e₂ : G₂ ≃ₜ+ G₂) (x : G₁ × G₂) : prodCE e₁ e₂ x = (e₁ x.1, e₂ x.2) := rfl

def lrCE {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {m n : ℕ} (g : GL (Fin m) R)
    (a : GL (Fin n) R) : Matrix (Fin m) (Fin n) R ≃ₜ+ Matrix (Fin m) (Fin n) R where
  toFun u := (g : Matrix (Fin m) (Fin m) R) * u * (a : Matrix (Fin n) (Fin n) R)
  invFun u := ((g⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) * u * ((a⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)
  left_inv u := by
    simp only [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  right_inv u := by
    simp only [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
    rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  map_add' u v := by rw [Matrix.mul_add, Matrix.add_mul]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

theorem lrCE_apply {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {m n : ℕ} (g : GL (Fin m) R)
    (a : GL (Fin n) R) (u : Matrix (Fin m) (Fin n) R) :
    lrCE g a u = (g : Matrix (Fin m) (Fin m) R) * u * (a : Matrix (Fin n) (Fin n) R) := rfl

def zipHom (κ X Y : Type) [AddCommGroup X] [AddCommGroup Y] : (κ → X) × (κ → Y) →+ (κ → X × Y) where
  toFun p i := (p.1 i, p.2 i)
  map_zero' := rfl
  map_add' _ _ := rfl

section Places

variable (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))

abbrev SPart : Type := ∀ v : S, Fv F v.1

abbrev OPart : Type := ∀ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, v.1.adicCompletionIntegers F


open Classical in
def jS : SPart F S × OPart F S →+* Af F where
  toFun p := ⟨fun v => if h : v ∈ S then p.1 ⟨v, h⟩ else (p.2 ⟨v, h⟩ : Fv F v),
    Filter.eventually_cofinite.2 (S.finite_toSet.subset fun v hv => by
      by_contra h
      exact hv (by simp only [dif_neg (show v ∉ S from h)]; exact (p.2 ⟨v, h⟩).2))⟩
  map_one' := Subtype.ext (funext fun v => by
    show dite (v ∈ S) _ _ = 1
    split_ifs <;> rfl)
  map_mul' p q := Subtype.ext (funext fun v => by
    show dite (v ∈ S) _ _ = dite (v ∈ S) _ _ * dite (v ∈ S) _ _
    split_ifs <;> rfl)
  map_zero' := Subtype.ext (funext fun v => by
    show dite (v ∈ S) _ _ = 0
    split_ifs <;> rfl)
  map_add' p q := Subtype.ext (funext fun v => by
    show dite (v ∈ S) _ _ = dite (v ∈ S) _ _ + dite (v ∈ S) _ _
    split_ifs <;> rfl)

open Classical in
theorem evalV_jS (p : SPart F S × OPart F S) (v : HeightOneSpectrum (𝓞 F)) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (jS F S p) = if h : v ∈ S then p.1 ⟨v, h⟩ else (p.2 ⟨v, h⟩ : Fv F v) := rfl

end Places

end GlobalTheory.ModuLR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SuppInd
section
noncomputable section

open Classical

namespace GlobalTheory.LevelVecNorm

def locH {E : Type} [Field E] [NumberField E] (Pg : Finset (Formalism.L2.DIV.Pl E)) {r : ℕ}
    (Hl : ∀ PP : ↥Pg, Subgroup (GL (Fin r) (Formalism.L2.DIV.kP PP.1))) (PP : Formalism.L2.DIV.Pl E) :
    Subgroup (GL (Fin r) (Formalism.L2.DIV.kP PP)) :=
  if h : PP ∈ Pg then Hl ⟨PP, h⟩ else ⊤


open Classical in
def suppInd {k : Type} [CommRing k] (r : ℕ) {b a : ℕ} (H : Subgroup (GL (Fin r) k)) (z : Matrix (Fin b) (Fin a) k) : ℝ :=
  if Formalism.IndefR.Datum.LowZero r z ∧ ∃ g ∈ H, ((g : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) = Formalism.IndefR.Datum.topL r z then 1 else 0

end GlobalTheory.LevelVecNorm

end
end

