module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0017
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0267
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0276
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicUnitaryHaarBiInvariant
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0067
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0170
public import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0004
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvalVCutIdemOfNotMem
section
noncomputable section

namespace GlobalTheory.LevelClosure

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU Filter Topology

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


open Classical in
def cutIdem (T : Finset (HeightOneSpectrum (𝓞 F))) : Af F :=
  ⟨fun v => if v ∈ T then 1 else 0, Eventually.of_forall fun v => by
    by_cases h : v ∈ T
    · simp only [h, if_true]; exact one_mem _
    · simp only [h, if_false]; exact zero_mem _⟩

theorem evalV_cutIdem_of_mem {T : Finset (HeightOneSpectrum (𝓞 F))} {v : HeightOneSpectrum (𝓞 F)} (h : v ∈ T) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (cutIdem T) = 1 := by
  classical
  exact if_pos h

theorem evalV_cutIdem_of_notMem {T : Finset (HeightOneSpectrum (𝓞 F))} {v : HeightOneSpectrum (𝓞 F)} (h : v ∉ T) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (cutIdem T) = 0 := by
  classical
  exact if_neg h

theorem tendsto_cutIdem_mul (a : Af F) :
    Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) => cutIdem T * a) atTop (𝓝 a) := by
  let S : Set (HeightOneSpectrum (𝓞 F)) := {v | a v ∈ v.adicCompletionIntegers F}
  have hle : (cofinite : Filter (HeightOneSpectrum (𝓞 F))) ≤ principal S := by
    rw [le_principal_iff]; exact a.2
  let P := RestrictedProduct (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
      (fun w => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) (principal S)
  let f : Finset (HeightOneSpectrum (𝓞 F)) → P := fun T =>
    ⟨fun v => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (cutIdem T) * a v, by
      rw [eventually_principal]
      intro w hw
      by_cases h : w ∈ T
      · simp only [evalV_cutIdem_of_mem h, one_mul]; exact hw
      · simp only [evalV_cutIdem_of_notMem h, zero_mul]; exact zero_mem _⟩
  let a' : P := ⟨fun v => a v, by rw [eventually_principal]; exact fun w hw => hw⟩
  have hf : Tendsto f atTop (𝓝 a') := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.tendsto_nhds_iff, tendsto_pi_nhds]
    intro v
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ({v} : Finset _)] with T hT
    have : v ∈ T := hT (Finset.mem_singleton_self v)
    change a v = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (cutIdem T) * a v
    rw [evalV_cutIdem_of_mem this, one_mul]
  exact ((RestrictedProduct.continuous_inclusion hle).tendsto a').comp hf

theorem tendsto_cutIdem_smul (z : Af F ⊗[F] E) :
    Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) => (cutIdem T : Af F) • z) atTop (𝓝 z) := by
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (Af F ⊗[F] E) := IsModuleTopology.toContinuousAdd (Af F) _
  induction z using TensorProduct.induction_on with
  | zero => simpa using tendsto_const_nhds
  | add x y hx hy => simpa only [smul_add] using hx.add hy
  | tmul a x =>
    have h := (tendsto_cutIdem_mul a).smul_const ((1 : Af F) ⊗ₜ[F] x)
    simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using h

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

def cutPt (T : Finset (HeightOneSpectrum (𝓞 F))) : GAd σ J →* GAd σ J := (embAt σ J T).comp (projAt σ J T)

omit [NumberField E] in
theorem map_smul_cut (v : HeightOneSpectrum (𝓞 F)) (c : Af F) (z : Af F ⊗[F] E) :
    Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) (c • z) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v c • Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]
  | tmul a x => simp [TensorProduct.smul_tmul']

omit [NumberField E] in
theorem cutPt_entry (T : Finset (HeightOneSpectrum (𝓞 F))) (g : GAd σ J) (i j : Fin n) :
    (matHom _ σ J (projFin σ J (cutPt σ J T g))).1 i j =
      (cutIdem T : Af F) • ((matHom _ σ J (projFin σ J g)).1 i j - (1 : Matrix (Fin n) (Fin n) _) i j) +
        (1 : Matrix (Fin n) (Fin n) _) i j := by
  refine GlobalTheory.LatticeLocalGlobal.ext_components _ _ fun v => ?_
  have e : ∀ g : GAd σ J, Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E)
      ((matHom _ σ J (projFin σ J g)).1 i j) = (matHom _ σ J (proj σ J v g)).1 i j := fun g => by
    rw [← projFinLoc_projFin]; rfl
  have e1 : Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E)
      ((1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) i j) = (1 : Matrix (Fin n) (Fin n) _) i j := by
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  change Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) _ =
    Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) _
  rw [map_add (f := _), map_smul_cut, map_sub, e, e, e1]
  by_cases hv : v ∈ T
  · have : proj σ J v (cutPt σ J T g) = proj σ J v g := proj_embAt σ J T _ ⟨v, hv⟩
    rw [this, evalV_cutIdem_of_mem hv, one_smul, sub_add_cancel]
  · have : proj σ J v (cutPt σ J T g) = 1 := (mem_atPts.1 (embAt_mem σ J T _)).2 v hv
    rw [this, evalV_cutIdem_of_notMem hv, zero_smul, zero_add, map_one, Units.val_one]

theorem tendsto_projFin_cutPt (g : GAd σ J) :
    Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) => projFin σ J (cutPt σ J T g)) atTop (𝓝 (projFin σ J g)) := by
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (Af F ⊗[F] E) := IsModuleTopology.toContinuousAdd (Af F) _
  have h : ∀ g : GAd σ J, Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) =>
      (matHom _ σ J (projFin σ J (cutPt σ J T g))).1) atTop (𝓝 (matHom _ σ J (projFin σ J g)).1) := fun g => by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    simp only [cutPt_entry]
    have := (tendsto_cutIdem_smul ((matHom _ σ J (projFin σ J g)).1 i j -
      (1 : Matrix (Fin n) (Fin n) _) i j)).add_const ((1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) i j)
    rwa [sub_add_cancel] at this
  rw [(isEmbedding_matHom _ σ J).tendsto_nhds_iff, Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  refine (h g).prodMk_nhds ?_
  refine (MulOpposite.continuous_op.tendsto _).comp ?_
  have h2 := h g⁻¹
  simp only [map_inv] at h2
  exact h2

theorem tendsto_cutPt {g : GAd σ J} (hg : g ∈ finPts σ J) :
    Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 F)) => cutPt σ J T g) atTop (𝓝 g) := by
  have e : ∀ g ∈ finPts σ J, ofFin σ J (projFin σ J g) = g := fun g hg =>
    ext_inf_fin σ J (by simp [mem_finPts.1 hg]) (by simp)
  have h := ((continuous_ofFin σ J).tendsto _).comp (tendsto_projFin_cutPt σ J g)
  rw [e g hg] at h
  exact h.congr fun T => e _ (mem_atPts.1 (embAt_mem σ J T _)).1

theorem mem_of_isClosed {H : Subgroup (GAd σ J)} (hH : IsClosed (H : Set (GAd σ J))) {g : GAd σ J}
    (hg : g ∈ finPts σ J) (h : ∀ v, emb σ J v (proj σ J v g) ∈ H) : g ∈ H :=
  hH.mem_of_tendsto (tendsto_cutPt σ J hg) (Eventually.of_forall fun T =>
    Subgroup.noncommProd_mem H (f := fun v : T => emb σ J v (proj σ J v g))
      (fun _ _ _ _ h => commute_emb σ J _ (proj_emb_ne σ J (fun e => h (Subtype.ext e)) _)) fun v _ => h v)

end General

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.WeilParts
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem ksph_le_of_isClosed : ∀ (D : D7) (V : HSp D) (Z : Finset (HeightOneSpectrum (𝓞 D.host.F))) (H : Subgroup (GA D V)), IsClosed (H : Set (GA D V)) → (∀ v, v ∉ Z → ∀ ε, IsPlaceIdem D v ε → ∀ g ∈ KsphC V ∅, SuppPl ε V g → g ∈ H) → ∀ k ∈ KsphC V Z, k ∈ H := by
  intro D V Z H hH h k hk
  rw [KsphC_eq] at hk
  obtain ⟨h1, h2, h3⟩ := mem_levelOff.1 hk
  refine mem_of_isClosed D.sp.cm.sig V.gram hH h1 fun v => ?_
  by_cases hv : v ∈ Z
  · rw [h2 v hv, map_one]; exact one_mem _
  · have hε : IsPlaceIdem D v (pairA D.host.F 0 (singleFin v 1)) :=
      ⟨_, rfl, evalV_singleFin_self v 1, fun _ hu => evalV_singleFin_ne hu 1⟩
    exact h v hv _ hε _ ((Model.emb_mem_KsphC_iff V v _).2 (h3 v hv)) ((Model.suppF_iff V hε _).2 ⟨_, rfl⟩)

end GlobalTheory.LevelClosure

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCountData
section
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev GlobalTheory.RowLev.Inhab NumberField Matrix
open scoped InnerProductSpace ComplexOrder Classical

namespace GlobalTheory.Mem.RowsBundle

section Infl

variable {I : AutInst} {g : ℕ} {Q : Type} [Group Q] (ρ : Red I g Q)

theorem fibre_eq (q : Q) :
    ∃ t : I.Gf, {x | x ∈ I.Kset ∧ ρ.toFun x = q} = (fun y => t * y) ⁻¹' I.Kg g := by
  obtain ⟨t, ht, rfl⟩ := ρ.surj q
  have ht' : t⁻¹ ∈ I.Kset := (Ksub I).inv_mem ht
  refine ⟨t⁻¹, Set.ext fun x => ⟨fun h => ?_, fun h => ?_⟩⟩
  · refine (ρ.ker _ ((Ksub I).mul_mem ht' h.1)).1 ?_
    rw [ρ.map_mul _ ht' _ h.1, ρ.map_inv ht, h.2, inv_mul_cancel]
  · have h1 : t⁻¹ * x ∈ I.Kset := h.1
    have hx : x ∈ I.Kset := ((Ksub I).mul_mem_cancel_left ht').1 h1
    have h2 := (ρ.ker _ h1).2 h
    rw [ρ.map_mul _ ht' _ hx, ρ.map_inv ht, inv_mul_eq_one] at h2
    exact ⟨hx, h2.symm⟩

theorem integral_inflate [Fintype Q] (μf : Measure I.Gf) [μf.IsHaarMeasure] (hg : 1 ≤ g) (F : Q → ℂ) :
    Integrable (fun x => if x ∈ I.Kset then F (ρ.toFun x) else 0) μf ∧
      ∫ x, (if x ∈ I.Kset then F (ρ.toFun x) else 0) ∂μf = ((μf (I.Kg g)).toReal : ℂ) * ∑ q, F q := by
  have hU : IsOpen (I.Kg g) := I.topf_open g hg
  have hfin : μf (I.Kg g) ≠ ⊤ :=
    ((measure_mono (show I.Kg g ⊆ I.Kset from fun x hx => hx.1)).trans_lt
      (GlobalTheory.adelicStab_isCompact_isOpen I).1.measure_lt_top).ne
  have hm : ∀ q, MeasurableSet {x | x ∈ I.Kset ∧ ρ.toFun x = q} ∧
      μf {x | x ∈ I.Kset ∧ ρ.toFun x = q} = μf (I.Kg g) := fun q => by
    obtain ⟨t, ht⟩ := fibre_eq ρ q
    rw [ht]
    exact ⟨(hU.preimage (by fun_prop)).measurableSet, measure_preimage_mul μf t _⟩
  have e : (fun x => if x ∈ I.Kset then F (ρ.toFun x) else 0) =
      fun x => ∑ q, {x | x ∈ I.Kset ∧ ρ.toFun x = q}.indicator (fun _ => F q) x := by
    funext x
    by_cases hx : x ∈ I.Kset
    · rw [if_pos hx, Finset.sum_eq_single (ρ.toFun x)]
      · rw [Set.indicator_of_mem]
        exact ⟨hx, rfl⟩
      · exact fun q _ hq => Set.indicator_of_notMem (by exact fun h => hq h.2.symm) _
      · exact fun h => absurd (Finset.mem_univ _) h
    · rw [if_neg hx]
      exact (Finset.sum_eq_zero fun q _ => Set.indicator_of_notMem (by exact fun h => hx h.1) _).symm
  have hi : ∀ q, Integrable ({x | x ∈ I.Kset ∧ ρ.toFun x = q}.indicator (fun _ => F q)) μf := fun q =>
    (integrable_indicator_iff (hm q).1).2 (integrableOn_const ((hm q).2 ▸ hfin))
  rw [e]
  refine ⟨integrable_finsetSum _ fun q _ => hi q, ?_⟩
  rw [integral_finsetSum _ fun q _ => hi q, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [integral_indicator_const _ (hm q).1, Measure.real, (hm q).2, Complex.real_smul]

theorem integrable_lift [Finite Q] (μf : Measure I.Gf) [μf.IsHaarMeasure] (hg : 1 ≤ g) (a : MonoidAlgebra ℂ Q) :
    Integrable (ρ.lift μf a) μf := by
  letI := Fintype.ofFinite Q
  exact (integral_inflate ρ μf hg fun q => a.coeff q / ((μf (I.Kg g)).toReal : ℂ)).1

theorem lift_biinv (μf : Measure I.Gf) (a : MonoidAlgebra ℂ Q) (x : I.Gf) (k : I.Gf) (hk : k ∈ I.Kg g)
    (k' : I.Gf) (hk' : k' ∈ I.Kg g) : ρ.lift μf a (k * x * k') = ρ.lift μf a x := by
  by_cases hx : x ∈ I.Kset
  · have h1 : k * x ∈ I.Kset := (Ksub I).mul_mem hk.1 hx
    rw [ρ.lift_of_mem μf a hx, ρ.lift_of_mem μf a ((Ksub I).mul_mem h1 hk'.1), ρ.map_mul _ h1 _ hk'.1,
      ρ.map_mul _ hk.1 _ hx, (ρ.ker _ hk.1).2 hk, (ρ.ker _ hk'.1).2 hk', one_mul, mul_one]
  · rw [ρ.lift_of_notMem μf a hx, ρ.lift_of_notMem μf a fun h => hx
      (((Ksub I).mul_mem_cancel_left hk.1).1 (((Ksub I).mul_mem_cancel_right hk'.1).1 h))]

end Infl

section Tens

variable {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)]

end Tens

end GlobalTheory.Mem.RowsBundle
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsImNeZeroOfTotallyComplex
section
open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField GlobalTheory.Mem.SJ
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ

theorem exists_im_ne_zero_of_totallyComplex {K : Type} [Field K] [_root_.NumberField.IsTotallyComplex K] (σ : K →+* ℂ) :
    ∃ a, (σ a).im ≠ 0 := by
  by_contra h
  push Not at h
  refine IsTotallyComplex.complexEmbedding_not_isReal σ ?_
  rw [ComplexEmbedding.isReal_iff]
  ext a
  exact Complex.conj_eq_iff_im.2 (h a)

theorem lin_single_cpt {K : Type} [Field K] (σ : K →+* ℂ) {d : ℕ} {V W : Type} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module ℂ W] (e : (Fin d → K) ≃ₗ[K] V) (j : V →ₛₗ[σ] W) (x : Fin d → K) :
    lin (fun k => j (e (Pi.single k 1))) (cpt σ x) = j (e x) := by
  rw [lin_apply]
  conv_rhs => rw [pi_eq_sum_univ' x]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, map_smulₛₗ, cpt]

theorem rows_eq_rows_level : ∀ (D : D7) (Bs : DefBase D.what₂.LL) (A : DefAmb Bs) (X : CxData A) (fc : DefSub A → DefFace Bs) (s : Bool) (R : Read D X fc s) (cr : Crd A fc) (M : Seam R cr) (eV : ∀ t, (Fin ((fc X.zs).Df1.nV t) → D.what₂.LL) →ₗ[D.what₂.LL] A.FR t), CxFacts X cr eV → R.RRTie cr → (∀ F, M.eR F ∈ X.EEl true) ∧ (∀ e ∈ X.EEl true, ∃ F, M.eR F = e) ∧ ∀ F, ‖M.eR F‖ = Real.sqrt (X.nP true) * ‖F‖ := by
  intro D Bs A X fc s R cr M eV hX hT
  obtain ⟨L, hT⟩ := hT
  have hn : 0 < X.nP true := hX.pos.2.2 true
  let g := lin (fun k => D.jEE (R.eRR (Pi.single k 1)))
  have hg : ∀ x, g (cpt D.what₂.embLL x) = D.jEE (R.eRR x) := lin_single_cpt _ R.eRR D.jEE
  have hsurj : Function.Surjective g := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← D.jEE_basis.2, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨cpt D.what₂.embLL (R.eRR.symm (D.div.RR.b i)), by rw [hg, R.eRR.apply_symm_apply]⟩
  have key : ∀ z, M.eR (g z) = X.iC cr true Bs.μ0 (cjv s z) := by
    intro z
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← lin_basis (X.iC cr true Bs.μ0), lin_apply, lin_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smulₛₗ, M.eR_eq]
    congr 2
    funext i
    by_cases h : i = k <;> simp [cpt, h]
  have hcc : ∀ z : Fin ((lv (fc X.zs) true).dQ Bs.μ0) → ℂ, cjv s (cjv s z) = z := by
    intro z
    funext i
    cases s <;> simp [cjv, cj]
  refine ⟨fun F => ?_, fun e he => ?_, fun F => ?_⟩
  · obtain ⟨z, rfl⟩ := hsurj F
    rw [key, ← hX.h2.2.2]
    exact ⟨_, rfl⟩
  · rw [← hX.h2.2.2] at he
    obtain ⟨z, rfl⟩ := he
    exact ⟨g (cjv s z), by rw [key, hcc]⟩
  · obtain ⟨z, rfl⟩ := hsurj F
    rw [key]
    have hd : DenseRange (cpt D.what₂.embLL : (Fin ((lv (fc X.zs) true).dQ Bs.μ0) → D.what₂.LL) → _) :=
      DenseRange.piMap (fun _ => denseRange_of_im_ne_zero D.what₂.embLL (exists_im_ne_zero_of_totallyComplex _))
    have hcj : Continuous (cj s) := by
      cases s
      · exact continuous_id
      · exact Complex.continuous_conj
    have hcv : Continuous fun z : Fin ((lv (fc X.zs) true).dQ Bs.μ0) → ℂ => cjv s z :=
      continuous_pi fun i => hcj.comp (continuous_apply i)
    have h1 : Continuous fun z => ‖X.iC cr true Bs.μ0 (cjv s z)‖ :=
      ((LinearMap.continuous_of_finiteDimensional (X.iC cr true Bs.μ0)).comp hcv).norm
    have h2 : Continuous fun z => Real.sqrt (X.nP true) * ‖g z‖ :=
      continuous_const.mul (LinearMap.continuous_of_finiteDimensional g).norm
    refine hd.induction_on z (isClosed_eq h1 h2) fun x => ?_
    have hv : cjv s (cpt D.what₂.embLL x) = cpt Bs.v0.embedding x := by
      funext i
      simp [cjv, cpt, R.twist]
    have hXE : X.XE cr true Bs.v0 = frameOf (X.gramE cr true) := by
      simp [CxData.XE, rowXE, rowFrame, spliceFrame]
    have hli : LinearIndependent ℂ fun i => X.iC cr true Bs.μ0 (Pi.single i 1) :=
      li_of_lin_injective (by rw [lin_basis]; exact hX.h2.1)
    have hm := majAt_gram_smul (X.XE cr true) Bs.v0 _ hli _ (inv_pos.2 hn) hXE x x
    rw [lin_basis] at hm
    rw [hv, hg, ← D.jEE_norm, ← R.v0, normAt_sq_eq_majAt_re, hT.metric, hm, inner_self_eq_norm_sq_to_K,
      ← Real.sqrt_mul hn.le]
    erw [show ((((X.nP true)⁻¹ : ℝ) : ℂ) * ((‖X.iC cr true Bs.μ0 (cpt Bs.v0.embedding x)‖ : ℝ) : ℂ) ^ 2).re =
      (X.nP true)⁻¹ * ‖X.iC cr true Bs.μ0 (cpt Bs.v0.embedding x)‖ ^ 2 by norm_cast]
    rw [mul_inv_cancel_left₀ hn.ne', Real.sqrt_sq (norm_nonneg _)]

end GlobalTheory.Mem.SJ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowEqUnitOfContinuousComplexRoot
section
open Polynomial

namespace GlobalTheory.ContRoot

open GlobalTheory.AffinePoints

theorem nonempty_algHom (B : Type) [CommRing B] [Nontrivial B] [Algebra ℂ B]
    [Algebra.FiniteType ℂ B] : Nonempty (B →ₐ[ℂ] ℂ) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  let _ := Ideal.Quotient.field m
  have : Module.Finite ℂ (B ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℂ (B ⧸ m)
  exact ⟨(IsAlgClosed.lift : (B ⧸ m) →ₐ[ℂ] ℂ).comp (Ideal.Quotient.mkₐ ℂ m)⟩

theorem exists_monic_prime_dvd (B : Type) [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    {n : ℕ} (hn : 0 < n) (u : B) :
    ∃ P : B[X], P.Monic ∧ Prime P ∧ 0 < P.natDegree ∧ P ∣ X ^ n - C u := by
  let L := AlgebraicClosure (FractionRing B)
  have hinj : Function.Injective (algebraMap B L) := by
    rw [IsScalarTower.algebraMap_eq B (FractionRing B) L]
    exact (algebraMap (FractionRing B) L).injective.comp (IsFractionRing.injective B _)
  have : FaithfulSMul B L := (faithfulSMul_iff_algebraMap_injective B L).2 hinj
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap B L u) hn
  have h0 : aeval β (X ^ n - C u : B[X]) = 0 := by simp [hβ]
  have hint : IsIntegral B β := ⟨_, monic_X_pow_sub_C u hn.ne', h0⟩
  exact ⟨minpoly B β, minpoly.monic hint, minpoly.prime_of_isIntegrallyClosed hint,
    minpoly.natDegree_pos hint, minpoly.isIntegrallyClosed_dvd hint h0⟩

theorem exists_pow_eq_of_continuous_root : ∀ (B : Type) [CommRing B] [IsDomain B] [Algebra ℂ B] [Algebra.Smooth ℂ B] (n : ℕ) (u : Bˣ) (ρ : (B →ₐ[ℂ] ℂ) → ℂ), 0 < n → (∀ (m : ℕ) (V : Set (Fin m → ℂ)) (s : (Fin m → ℂ) → (B →ₐ[ℂ] ℂ)), IsOpen V → (∀ a : B, DifferentiableOn ℂ (fun p => s p a) V) → ContinuousOn (fun p => ρ (s p)) V) → (∀ ψ : B →ₐ[ℂ] ℂ, ρ ψ ^ n = ψ (u : B)) → ∃ b : B, b ^ n = u := by
  intro B _ _ _ _ n u ρ hn hc hρ
  have hρc : Continuous ρ := GlobalTheory.RootConst.continuous_of_holomorphic_families B ρ hc
  have := GlobalTheory.isIntegrallyClosed_of_smooth ℂ B
  obtain ⟨P, hm, hp, hd, hdvd⟩ := exists_monic_prime_dvd B hn (u : B)
  have hdom : IsDomain (AdjoinRoot P) := AdjoinRoot.isDomain_of_prime hp
  have hft : Algebra.FiniteType ℂ (AdjoinRoot P) :=
    Algebra.FiniteType.trans (S := B) inferInstance inferInstance
  have hconn := GlobalTheory.RootConst.preconnectedSpace_algHom (AdjoinRoot P)
  let φ : B →ₐ[ℂ] AdjoinRoot P := IsScalarTower.toAlgHom ℂ B (AdjoinRoot P)
  have hroot : AdjoinRoot.root P ^ n = φ u := by
    have h := (AdjoinRoot.mk_eq_zero (f := P)).2 hdvd
    rw [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, sub_eq_zero] at h
    exact h
  have hu : ∀ ψ : B →ₐ[ℂ] ℂ, ψ u ≠ 0 := fun ψ => (u.isUnit.map ψ).ne_zero
  have hρ0 : ∀ ψ, ρ ψ ≠ 0 := fun ψ h => hu ψ (by rw [← hρ, h, zero_pow hn.ne'])
  have hcont : Continuous fun χ : AdjoinRoot P →ₐ[ℂ] ℂ =>
      χ (AdjoinRoot.root P) / ρ (comap φ χ) :=
    (continuous_eval _).div (hρc.comp (continuous_comap φ)) fun _ => hρ0 _
  have hconst := GlobalTheory.RootConst.eq_of_pow_eq_one hcont hn fun χ => by
    rw [div_pow, ← map_pow, hroot, hρ, comap_apply]
    exact div_self (hu (comap φ χ))
  obtain ⟨ψ⟩ := nonempty_algHom B
  have key : ∀ z, (P.map (ψ : B →+* ℂ)).IsRoot z → ∃ χ : AdjoinRoot P →ₐ[ℂ] ℂ,
      comap φ χ = ψ ∧ χ (AdjoinRoot.root P) = z := by
    intro z hz
    have hz' : P.eval₂ (ψ : B →+* ℂ) z = 0 := by rw [← eval_map]; exact hz
    refine ⟨AdjoinRoot.liftAlgHom P ψ z hz', ?_, by simp⟩
    ext b
    simp [φ]
  have huniq : ∀ z w, (P.map (ψ : B →+* ℂ)).IsRoot z → (P.map (ψ : B →+* ℂ)).IsRoot w →
      z = w := by
    intro z w hz hw
    obtain ⟨χ, h1, h2⟩ := key z hz
    obtain ⟨χ', h1', h2'⟩ := key w hw
    have h := hconst χ χ'
    simp only [h1, h1', h2, h2'] at h
    exact (div_left_inj' (hρ0 ψ)).1 h
  have hsep : (P.map (ψ : B →+* ℂ)).Separable := by
    refine (separable_X_pow_sub_C (n := n) (ψ u) (Nat.cast_ne_zero.2 hn.ne') (hu ψ)).of_dvd ?_
    simpa using Polynomial.map_dvd (ψ : B →+* ℂ) hdvd
  have hne : P.map (ψ : B →+* ℂ) ≠ 0 := (hm.map _).ne_zero
  have hdeg : P.natDegree ≤ 1 := by
    rw [← hm.natDegree_map (ψ : B →+* ℂ),
      (IsAlgClosed.splits (P.map (ψ : B →+* ℂ))).natDegree_eq_card_roots,
      ← Multiset.toFinset_card_of_nodup (nodup_roots hsep)]
    refine Finset.card_le_one.2 fun a ha b hb => huniq a b ?_ ?_
    · exact (mem_roots hne).1 (Multiset.mem_toFinset.1 ha)
    · exact (mem_roots hne).1 (Multiset.mem_toFinset.1 hb)
  have h1 : P = X + C (P.coeff 0) := hm.eq_X_add_C (le_antisymm hdeg hd)
  refine ⟨-P.coeff 0, ?_⟩
  have h2 : P.eval (-P.coeff 0) = 0 := by
    rw [congrArg (eval (-P.coeff 0)) h1]; simp
  have h3 := eval_eq_zero_of_dvd_of_eval_eq_zero hdvd h2
  simpa [sub_eq_zero] using h3

end GlobalTheory.ContRoot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorsOfSmoothThetaStable
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum

namespace GlobalTheory.FockTheta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem ptStable : ∀ D : D7, Formalism.IndefR.Fin.PtStable D := by
  intro D ψ θ hψ hθ S T sS sT BS BT f P hf
  exact (GlobalTheory.OrientedHeis.pureTensorL_intertwine (IsThetaFunO ψ S T) GlobalTheory.OrientedHeis.theta_zero
    (fun _ _ => GlobalTheory.OrientedHeis.theta_add) (fun c _ => GlobalTheory.OrientedHeis.theta_smul c) _
    (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT) 1
    (fun k _ hg => ⟨GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.OrientedHeis.theta_sub
      (GlobalTheory.OrientedHeis.theta_dRho hθ hψ k.1 _ hg)
      (GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.OrientedHeis.theta_dRho hθ hψ k.1 _ hg))), rfl⟩) f hf P).1

end GlobalTheory.FockTheta

end
end

