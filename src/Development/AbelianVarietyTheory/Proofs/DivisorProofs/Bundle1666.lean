module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1520
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1548
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1543
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1648
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1588
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1545
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1611
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0923
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1646
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1617
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1619
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0974
public import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0828
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0989
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0901
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1647
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1266
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1283
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1267
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1653
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1547
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1630

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePlaceVacuumAnyDarbouxCoordinates
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.VacAny

private theorem supported_sum {F : Type} [Field F] [NumberField F]
    {v : HeightOneSpectrum (𝓞 F)} {ι : Type} (s : Finset ι) {f : ι → AF F}
    (h : ∀ i ∈ s, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (f i)) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (∑ i ∈ s, f i) := by
  intro u hu
  rw [Finset.smul_sum]
  exact Finset.sum_eq_zero fun i hi => h i hi u hu

private theorem supported_neg {F : Type} [Field F] [NumberField F]
    {v : HeightOneSpectrum (𝓞 F)} {x : AF F}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) x) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (-x) := by
  intro u hu
  rw [smul_neg, h u hu, neg_zero]

private theorem supported_atPlace {F : Type} [Field F] [NumberField F]
    {v : HeightOneSpectrum (𝓞 F)} (t : Fv F v) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (GlobalTheory.EmbChart.atPlace v t) := by
  intro u hu
  rw [smul_eq_mul, mul_comm, GlobalTheory.EmbChart.atPlace_mul_right, hu, mul_zero, map_zero]

private theorem supported_mul_right {F : Type} [Field F] [NumberField F]
    {v : HeightOneSpectrum (𝓞 F)} {x : AF F}
    (hx : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) x) (y : AF F) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (x * y) := by
  intro u hu
  rw [smul_eq_mul, ← mul_assoc, show u * x = 0 from hx u hu, zero_mul]

private theorem supported_mul_left {F : Type} [Field F] [NumberField F]
    {v : HeightOneSpectrum (𝓞 F)} (x : AF F) {y : AF F}
    (hy : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) y) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (x * y) := by
  rw [mul_comm]
  exact supported_mul_right hy x

private theorem supported_sub {F : Type} [Field F] [NumberField F]
    {v : HeightOneSpectrum (𝓞 F)} {x y : AF F}
    (hx : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) x)
    (hy : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) y) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (x - y) := by
  intro u hu
  rw [smul_sub, hx u hu, hy u hu, sub_self]

private theorem evFin_invOf_two_local {F : Type} [Field F] [NumberField F]
    {v : HeightOneSpectrum (𝓞 F)} :
    GlobalTheory.AdelicU.evFin F v (⅟(2 : AF F)) = ⅟(2 : Fv F v) := by
  refine (invOf_eq_right_inv ?_).symm
  have h : GlobalTheory.AdelicU.evFin F v (2 * ⅟(2 : AF F)) = 1 := by
    rw [mul_invOf_self, map_one]
  rwa [map_mul, map_ofNat] at h

theorem exists_isVac_any_darboux : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E), B.IsGood σ → ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → Y.IsSkew σ B r' s' → ∀ (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J)) (Fin n × Fin d)) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)),
    ∃ φ, Model.IsVac (Model.mk (σ := σ) (X := X) (W := Y) co (fun _ => 0) 0 ∅) B.ψ v φ := by
  intro F E _ _ _ _ _ σ B hB n d X Y r s r' s' hX hY co v
  obtain ⟨θ, hθ⟩ := GlobalTheory.exists_int_add_conj_eq_one_of_base_good B hB
  obtain ⟨M, _, g, hΓ⟩ := GlobalTheory.T.tensorLatticeAtFinitePlace_eq_integral_span_generators X Y hX.lat.toIsLattice hY.lat.toIsLattice v
  let γf : (M → v.adicCompletionIntegers F) → Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
    fun a => ∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m)
  let u : M → (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) := fun m =>
    (fun i => GlobalTheory.AdelicU.evFin F v ((co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m))).1 i),
     fun i => GlobalTheory.AdelicU.evFin F v ((co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m))).2 i))
  let χ : (M → v.adicCompletionIntegers F) → ℂ := fun a => B.ψ (⅟(2 : AF F) *
    GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) (θ : E)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) (γf a) (γf a))
  have he : ∀ a, co.e (γf a) =
      ∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) • co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m)) := by
    intro a
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [γf, map_sum, map_smul]
  have hcomp : ∀ a i, (co.e (γf a)).1 i =
      ∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) * (co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m))).1 i ∧
      (co.e (γf a)).2 i =
      ∑ m, GlobalTheory.EmbChart.atPlace v (a m : Fv F v) * (co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g m))).2 i := by
    intro a i
    rw [he]
    simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, smul_eq_mul]
  have hAt : ∀ a i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) ((co.e (γf a)).1 i) ∧
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) ((co.e (γf a)).2 i) := by
    intro a i
    rw [(hcomp a i).1, (hcomp a i).2]
    exact ⟨supported_sum _ fun m _ => supported_mul_right (supported_atPlace _) _,
      supported_sum _ fun m _ => supported_mul_right (supported_atPlace _) _⟩
  have hev : ∀ a, ((fun i => GlobalTheory.AdelicU.evFin F v ((co.e (γf a)).1 i)),
      (fun i => GlobalTheory.AdelicU.evFin F v ((co.e (γf a)).2 i))) = ∑ m, (a m : Fv F v) • u m := by
    intro a
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    set_option synthInstance.maxHeartbeats 100000 in
      · simp [(hcomp a i).1, map_sum, map_mul, GlobalTheory.EmbChart.evFin_atPlace, Prod.fst_sum, Finset.sum_apply, u]
    set_option synthInstance.maxHeartbeats 100000 in
      · simp [(hcomp a i).2, map_sum, map_mul, GlobalTheory.EmbChart.evFin_atPlace, Prod.snd_sum, Finset.sum_apply, u]
  have hψ : ∀ z : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) z →
      B.ψ z = GlobalTheory.VacAny.psiV B.ψ v (GlobalTheory.AdelicU.evFin F v z) := fun z hz => by
    rw [GlobalTheory.VacAny.psiV_apply, ← GlobalTheory.T.eq_adeleSupportedAtFinitePlace_of_supportedAt v z hz]
  have hzero : ∀ a, ∑ m, (a m : Fv F v) • u m = 0 → γf a = 0 := by
    intro a h
    rw [← hev a] at h
    have h1 : co.e (γf a) = 0 := by
      refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
      · rw [GlobalTheory.T.eq_adeleSupportedAtFinitePlace_of_supportedAt v _ (hAt a i).1, show GlobalTheory.AdelicU.evFin F v ((co.e (γf a)).1 i) = 0 from
          congrFun (congrArg Prod.fst h) i, map_zero]
        rfl
      · rw [GlobalTheory.T.eq_adeleSupportedAtFinitePlace_of_supportedAt v _ (hAt a i).2, show GlobalTheory.AdelicU.evFin F v ((co.e (γf a)).2 i) = 0 from
          congrFun (congrArg Prod.snd h) i, map_zero]
        rfl
    exact co.e.map_eq_zero_iff.1 h1
  have hker : ∀ a, ∑ m, (a m : Fv F v) • u m = 0 → χ a = 1 := by
    intro a h
    simp only [χ, hzero a h]
    simp [GlobalTheory.WeilM.symp, GlobalTheory.WeilM.hTens]
  have hadd : ∀ a b, γf (a + b) = γf a + γf b := by
    intro a b
    simp only [γf]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [show (((a + b) m : v.adicCompletionIntegers F) : Fv F v) = (a m : Fv F v) + b m from rfl, map_add (f := _), add_smul]
  have hmem : ∀ a, γf a ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v := fun a => (hΓ _).2 ⟨a, rfl⟩
  have hdot : ∀ a b, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) ((co.e (γf a)).1 ⬝ᵥ (co.e (γf b)).2) ∧
      GlobalTheory.AdelicU.evFin F v ((co.e (γf a)).1 ⬝ᵥ (co.e (γf b)).2) =
        (∑ m, (a m : Fv F v) • u m).1 ⬝ᵥ (∑ m, (b m : Fv F v) • u m).2 := by
    intro a b
    refine ⟨supported_sum _ fun i _ => supported_mul_right (hAt a i).1 _, ?_⟩
    rw [← hev a, ← hev b]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, map_sum, map_mul]
  have hcoc : ∀ a b, χ (a + b) = χ a * χ b * GlobalTheory.VacAny.psiV B.ψ v
      (-(⅟(2 : Fv F v) * ((∑ m, (a m : Fv F v) • u m).1 ⬝ᵥ (∑ m, (b m : Fv F v) • u m).2 -
        (∑ m, (b m : Fv F v) • u m).1 ⬝ᵥ (∑ m, (a m : Fv F v) • u m).2))) := by
    intro a b
    simp only [χ]
    rw [hadd, GlobalTheory.T.addChar_halfTrace_tensorLattice_heisenbergCocycle B hB X Y r s r' s' hX hY θ hθ v _ (hmem a) _ (hmem b), co.form]
    congr 1
    have hz := supported_neg (supported_mul_left (⅟(2 : AF F))
      (supported_sub (hdot a b).1 (hdot b a).1))
    rw [hψ _ hz, map_neg, map_mul, map_sub, (hdot a b).2, (hdot b a).2, evFin_invOf_two_local]
  obtain ⟨φ, hφSB, hφ0, hφ⟩ := GlobalTheory.T.exists_schroedinger_eigenvector_compact_cocycle v (GlobalTheory.VacAny.psiV B.ψ v) (GlobalTheory.VacAny.continuous_psiV hB.std.1 v)
    (GlobalTheory.T.standardTraceAdelicAddChar_localComponent_ne_one B.ψ hB.std v) u χ (GlobalTheory.T.continuous_addChar_symplecticSelfPairing_placeCoordinates σ B.ψ hB.std.1 X.J Y.J (θ : E) v g) hker hcoc
  refine ⟨φ, hφSB, hφ0, θ, hθ, ?_⟩
  intro γ hγ
  obtain ⟨a, rfl⟩ := (hΓ γ).1 hγ
  intro rr hrr
  show GlobalTheory.WeilM.schr B.ψ (co.e (γf a)) _ = _
  rw [GlobalTheory.T.adelicSchrodinger_tensor_eq_local_of_supportedAt B.ψ v (co.e (γf a)) (fun i => (hAt a i).1) (fun i => (hAt a i).2) φ rr hrr.1, hev a, hφ a]

end GlobalTheory.VacAny
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteUnitaryPointSelfDualToOrthonormal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefTransfer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefTransfer.LatMove

open scoped Matrix

theorem mem_hat_stdLat_iff {D : D7} {n : ℕ} (z : Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    z ∈ GlobalTheory.AdLat.hat D.host.F (Formalism.L2.Pj.stdLat D.host.E n : Set (Fin n → D.host.E)) ↔ IntVec z := by
  constructor
  · intro h i
    induction h using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      obtain ⟨r, hr⟩ := Submodule.mem_one.1 (hx i trivial)
      exact AddSubgroup.subset_closure ⟨a, ha, r, congrArg (fun t => a ⊗ₜ[D.host.F] t) hr.symm⟩
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | neg y _ hy => exact neg_mem hy
  · intro h
    rw [← Finset.univ_sum_single z]
    refine sum_mem fun i _ => ?_
    have hi := h i
    generalize z i = c at hi
    induction hi using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, rfl⟩ := hy
      refine AddSubgroup.subset_closure ⟨a, ha, Pi.single i (x : D.host.E), fun j _ => ?_, funext fun j => ?_⟩
      · rw [Pi.single_apply]
        split_ifs
        exacts [Submodule.mem_one.2 ⟨x, rfl⟩, zero_mem _]
      · rw [Pi.single_apply, Pi.single_apply]
        split_ifs
        exacts [rfl, (TensorProduct.tmul_zero _ _).symm]
    | zero => rw [Pi.single_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [Pi.single_add]; exact add_mem hy hz
    | neg y _ hy => rw [Pi.single_neg]; exact neg_mem hy

theorem mem_hat_colLat_iff {D : D7} {n : ℕ} (B : GL (Fin n) D.host.E)
    (w : Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    w ∈ GlobalTheory.AdLat.hat D.host.F (Formalism.L2.DIV.colLat B : Set (Fin n → D.host.E)) ↔
      IntVec (GlobalTheory.UnRep.fm D.host.F (B⁻¹).1 *ᵥ w) := by
  have ew : GlobalTheory.UnRep.fm D.host.F B.1 *ᵥ (GlobalTheory.UnRep.fm D.host.F (B⁻¹).1 *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec, ← GlobalTheory.HatPullback.fm_mul', Units.mul_inv, GlobalTheory.HatPullback.fm_one', Matrix.one_mulVec]
  have h1 := GlobalTheory.HatPullback.main D.host.F D.host.E n B (Formalism.L2.DIV.colLat B) (GlobalTheory.UnRep.fm D.host.F (B⁻¹).1 *ᵥ w)
  rw [ew, GlobalTheory.ColStd.colLat_comap_eq_stdLat] at h1
  exact h1.trans (mem_hat_stdLat_iff _)

theorem swap_mem_hatL_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (u : Fin n → FiniteAdeleRing (𝓞 F) F ⊗[F] E) :
    (fun i => Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E (u i)) ∈ Formalism.L2.Herm.hatL (F := F) L ↔
      u ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)) := by
  rw [GlobalTheory.GenusTranslate.hatL_iff]
  simp only [AlgEquiv.symm_apply_apply]

theorem exists_move {D : D7} (V : HSp D) (B : GL (Fin V.rank) D.host.E)
    (hB : cT (D.sp.cm.sig : D.host.E →+* D.host.E) B.1 * V.gram * B.1 = 1) :
    ∃ x ∈ GfC V, ∀ w, w ∈ GlobalTheory.AdLat.hat D.host.F (Formalism.L2.DIV.colLat B : Set (Fin V.rank → D.host.E)) ↔
      (finHom V x).1 *ᵥ w ∈ GlobalTheory.AdLat.hat D.host.F (GlobalTheory.PlaceModel.latFrame V : Set (Fin V.rank → D.host.E)) := by
  obtain ⟨x, hx, h⟩ := GlobalTheory.GenusTranslate.exists_move_colLat D V B _ hB (GlobalTheory.PlaceModel.isSelfDualC_latFrame V)
  refine ⟨x, hx, fun w => ?_⟩
  have h1 := h fun i => Formalism.IndefR.Lev.swapAE D (w i)
  have h2 : (Formalism.IndefR.Lev.finE V x).1 *ᵥ (fun i => Formalism.IndefR.Lev.swapAE D (w i)) =
      fun i => Formalism.IndefR.Lev.swapAE D (((finHom V x).1 *ᵥ w) i) :=
    funext fun i => (RingHom.map_mulVec (Formalism.IndefR.Lev.swapAE D) (finHom V x).1 w i).symm
  rw [h2] at h1
  exact (swap_mem_hatL_iff _ w).symm.trans (h1.trans (swap_mem_hatL_iff _ ((finHom V x).1 *ᵥ w)))

theorem exists_finite_point : ∀ (D : D7) [IsCMField D.host.E] (V : HSp D) (M : Matrix (Fin V.rank) (Fin V.rank) D.host.E),
    cT (D.sp.cm.sig : D.host.E →+* D.host.E) M * V.gram * M = 1 →
    ∃ h₀ ∈ GfC V, ∀ y, y ∈ latHat D.host.F D.host.E (L0c D V) ↔
      IntVec (Matrix.mulVec (M⁻¹.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) (Matrix.mulVec (finMat D.sp.cm.sig V.gram h₀) y)) := by
  intro D _ V M hM
  have hu : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 (Matrix.isUnit_det_of_left_inverse hM)
  obtain ⟨B, rfl⟩ := hu
  obtain ⟨x, hx, h⟩ := exists_move V B hM
  refine ⟨x⁻¹, inv_mem hx, fun y => ?_⟩
  have hL : L0c D V = (GlobalTheory.PlaceModel.latFrame V : Set (Fin V.rank → D.host.E)) :=
    Set.ext fun z => (GlobalTheory.PlaceModel.mem_latFrame V z).symm
  have h1 := h ((finHom V x⁻¹).1 *ᵥ y)
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.one_mulVec,
    mem_hat_colLat_iff, Matrix.coe_units_inv] at h1
  rw [hL]
  exact h1.symm

end GlobalTheory.DefTransfer.LatMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFullLift
section
set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
open GlobalTheory.LiftLower GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.Survey.LevelVectorSizeBounds

namespace GlobalTheory.LowForm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem op_idem {G H : Type} [Group G] [Fintype G] [AddCommGroup H] [Module ℂ H] (ρ : Representation ℂ G H) {a : G → ℂ}
    (ha : GlobalTheory.IndefiniteRowSideFullHecke.GoodBasisCentralIdempotents.IsCentralIdem a) (u : H) :
    (∑ g, a g • ρ g : H →ₗ[ℂ] H) ((∑ g, a g • ρ g : H →ₗ[ℂ] H) u) = (∑ g, a g • ρ g : H →ₗ[ℂ] H) u := by
  set E : H →ₗ[ℂ] H := ∑ g, a g • ρ g with hE
  have h1 : E u = ∑ g, ∑ h, (a h * a (h⁻¹ * g)) • ρ g u := by
    simp only [← Finset.sum_smul, ha.2, hE, LinearMap.sum_apply, LinearMap.smul_apply]
  have h2 : E (E u) = ∑ h, ∑ g, (a h * a g) • ρ h (ρ g u) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hE, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  rw [h2, h1, Finset.sum_comm (f := fun g h => (a h * a (h⁻¹ * g)) • ρ g u)]
  refine Finset.sum_congr rfl fun h _ => Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => ?_
  simp only [Equiv.coe_mulLeft, inv_mul_cancel_left, map_mul, Module.End.mul_apply]

theorem adjoint_eq_self {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (E : H →ₗ[ℂ] H)
    (h1 : ∀ u, E (E u) = E u) (h2 : ∀ x, E x = x → ∀ y, ⟪x, E y⟫_ℂ = ⟪x, y⟫_ℂ) : LinearMap.adjoint E = E := by
  refine LinearMap.ext fun x => ext_inner_right ℂ fun y => ?_
  rw [LinearMap.adjoint_inner_left, ← h2 _ (h1 x) y, ← inner_conj_symm, ← h2 _ (h1 y) x, inner_conj_symm]

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem eC_idem_at (hr : R.grp_record) (σ : D.what₂.LL →+* ℂ) : GlobalTheory.IndefiniteRowSideFullHecke.GoodBasisCentralIdempotents.IsCentralIdem (RealDat.eC (A := A) σ) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.LiftScalarCompare.eC_idem hr
  unfold RealDat.eC at h1 h2 ⊢
  refine ⟨fun g k => congrArg σ ((sg0 D A).injective (h1 g k)), fun g => ?_⟩
  have := h2 g
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← map_mul, ← map_sum] at this ⊢
  exact congrArg σ ((sg0 D A).injective this)


open Classical in
variable (R) in
def blkChar (i : Fin D.R.m) : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ :=
  fun PP => if PP ∈ R.Pg then (R.chi ((i : ℕ) + 1) PP)⁻¹ else R.xiR A.μ0 PP

def conjChar (s : ℂ ≃+* ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ :=
  fun PP => (Units.map (s : ℂ →+* ℂ).toMonoidHom).comp (m PP)

theorem twVal_zero {E : Type} [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) (P : HeightOneSpectrum (𝓞 E)) (k : Eˣ) :
    twVal χ 0 P k = ((χ.locK P k : ℂˣ) : ℂ) := by
  unfold twVal
  simp

theorem levFn_conj {n : ℕ} (β : GL (Fin n) (Lev.EAf D)) (r : ℕ) (hr : r ≤ n) (t s' : ℕ) (Pg Q : Finset (Pl D.host.E))
    (s : ℂ ≃+* ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (x) :
    ((levFn β ⟨r, hr, t, s', Pg, Q, LevelP.triv _ _ _, fun _ => conjChar s m, conjChar s m⟩ x : ℂˣ) : ℂ) =
      s ((levFn β ⟨r, hr, t, s', Pg, Q, LevelP.triv _ _ _, fun _ => m, m⟩ x : ℂˣ) : ℂ) := by
  unfold levFn
  have e : ∀ y, ext1 (LevelP.triv Pg r ℂ).H (LevelP.triv Pg r ℂ).chi y = 1 := fun y => Lev.subgroupCharExtension_one_apply _ _
  simp only [e, one_mul, Units.val_mul, Units.coe_prod, map_mul, map_prod]
  rfl

theorem chrOf_conj (i : Fin D.R.m) (s : ℂ ≃+* ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (k : levJ R i A.μ0) :
    ((chrOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv (conjChar s m)) k : ℂˣ) : ℂ) =
      s ((chrOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q A.μ0) R.triv m) k : ℂˣ) : ℂ) :=
  levFn_conj (R.βV i) D.R.r (r_le_V i) D.R.t 1 R.Pg (R.Q A.μ0) s m (Formalism.UG.bc (Lev.swapAE D) k.1.1)

theorem hookPlus_le (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.logHookSum i (lab σ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.logHookSum i id) : hookPlus D i ≤ mainTerm D i σ := by
  have e : mainTerm D i σ = GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.logHookSum i (lab σ) := by
    unfold mainTerm GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.logHookSum
    simp only [Nat.cast_mul]
    rfl
  rw [e, h]
  unfold hookPlus GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.logHookSum
  refine Finset.sum_le_sum fun ρ _ => Real.log_le_log (Nat.cast_pos.2 (hookProd_pos _)) (Nat.cast_le.2 ?_)
  exact Nat.le_mul_of_pos_right _ (hookProd_pos _)

theorem eq_of_low_at (hW : R.models_HW) {i : Fin D.R.m} {σ : D.what₂.LL →+* ℂ} {v : (R.MW i σ).Vec} (hv : IsExtVec (R.MW i σ) v)
    {x y : (R.HW i σ).H}
    (h : ∀ w : ∀ ρ, lowT (R.MW i σ) ρ, (R.HW i σ).e x (fun ρ => w ρ) = (R.HW i σ).e y fun ρ => w ρ) : x = y := by
  have h0 : (R.HW i σ).e (x - y) v = 0 := by
    rw [LinearMap.map_sub]
    exact sub_eq_zero.2 (h fun ρ => ⟨v ρ, (hv ρ).2.1⟩)
  have h1 := (hW i σ).2.2 (x - y) (x - y)
  rw [ipAt, GlobalTheory.EvalAtUnitVector.ipM_self_eq_zero _ _ _ _ v (fun τ => (hv τ).1) h0, mul_zero] at h1
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h1)

theorem lower_of_parts {X Y ι : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (T th : X →ₗ[ℂ] Y) (e : Y →ₗ[ℂ] Y)
    (P : ι → Submodule ℂ Y) (S : ι → Prop) (a : ℝ) (h1 : LinearMap.adjoint e = e) (h2 : ∀ y, e (e y) = e y)
    (h3 : (⨆ (k) (_ : S k), P k) = ⊤)
    (h4 : ∀ k, P k ≠ ⊥ → ∃ l : ℝ, 0 < l ∧ (∀ y ∈ P k, T (LinearMap.adjoint T y) = (l : ℂ) • y) ∧ a ≤ Real.log l)
    (h5 : ∀ x, th x = e (T x)) : ∀ x ∈ (LinearMap.ker th)ᗮ, Real.exp a * ‖x‖ ^ 2 ≤ ‖th x‖ ^ 2 := by
  obtain rfl : th = e ∘ₗ T := LinearMap.ext h5
  refine GlobalTheory.mul_norm_sq_le_norm_proj_apply_sq_of_spanning_parts X Y ι T e P _ (Real.exp_pos a) h1 h2 ?_ fun k => ?_
  · exact top_le_iff.1 (h3.ge.trans (iSup₂_le fun k _ => le_iSup P k))
  · by_cases hk : P k = ⊥
    · refine ⟨_, le_rfl, fun y hy => ?_⟩
      rw [hk, Submodule.mem_bot] at hy
      simp [hy]
    · obtain ⟨l, a1, a2, a3⟩ := h4 k hk
      exact ⟨l, (Real.le_log_iff_exp_le a1).1 a3, a2⟩



end GlobalTheory.LowForm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertPlaceTransversalOfLocalCore
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.TransvChoose

theorem exists_transversal : (∀ (O : Type) [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    (∃ x : O, IsUnit (c x - x)) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) O), (∀ i j, c (J j i) = J i j) → IsUnit J.det →
    ∀ g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O, IsUnit g.det →
      gᵀ * Matrix.fromBlocks 0 J J 0 * g.map c = Matrix.fromBlocks 0 J J 0 →
      ∃ Z : Matrix (Fin n) (Fin n) O, Zᵀ * J + J * Z.map c = 0 ∧ IsUnit (g.toBlocks₂₁ * Z + g.toBlocks₂₂).det) → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n r s : ℕ) (X : Spc F E n), B.IsGood σ → X.IsHerm σ B r s →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ g ∈ GlobalTheory.DblVac.KD σ X v,
    ∃ Z : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) Z ∧ (∀ z ∈ GlobalTheory.InertSph.latAt X v, Z *ᵥ z ∈ GlobalTheory.InertSph.latAt X v) ∧
      Zᵀ * incM F X.J + incM F X.J * Z.map (cA σ) = 0 ∧
      IsUnit ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.antiCols n +
        (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD g * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * Z).det ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt X v,
        ((GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.antiCols n +
          (GlobalTheory.DblVac.antiCols (F := F) (E := E) n)ᵀ * GlobalTheory.DblVac.matD g * (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) * Z)⁻¹ *ᵥ z ∈
          GlobalTheory.InertSph.latAt X v := by
  intro core F E _ _ _ _ _ σ B n r s X hB hX v w hw g hg
  obtain ⟨O, _, c, ι, P, Q, JL, hloc, hcc, h2, hcx, hinj, hAt, hsupp, hcι, hPQ, hQP, hP, hQ, hJh, hJu, hJ, hlat⟩ :=
    GlobalTheory.T.exists_local_dictionary_inertPlace F E σ B n r s X hB hX v w hw
  haveI := hloc
  obtain ⟨hg1, hg2⟩ := hg
  have hinv : GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.matD g⁻¹ = 1 := by
    simp [GlobalTheory.DblVac.matD]
  obtain ⟨G, G', hGG, hMG⟩ := _root_.GlobalTheory.LatticeStab.matrix_in_diag_basis (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) O ι n P Q (GlobalTheory.InertSph.latAt X v : Set (Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) hinj hPQ hQP hP hQ
    (fun z => hlat z) (GlobalTheory.DblVac.matD g) (GlobalTheory.DblVac.matD g⁻¹) hinv (fun z h1 h2 => by
      obtain ⟨ha, hb⟩ := hg2 z ⟨h1, h2⟩
      exact ⟨ha.1, ha.2, hb.1, hb.2⟩)
  have hgU : (GlobalTheory.DblVac.matD g)ᵀ * Matrix.fromBlocks (incM F X.J) 0 0 (-incM F X.J) * (GlobalTheory.DblVac.matD g).map (cA σ).toRingHom =
      Matrix.fromBlocks (incM F X.J) 0 0 (-incM F X.J) := g.2
  have hU := _root_.GlobalTheory.fromBlocks_unitary_transfer (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) O ι (cA σ).toRingHom c n P (incM F X.J) JL hinj hcι hJ (GlobalTheory.DblVac.matD g) G hgU hMG
  obtain ⟨ZL, hZL1, hZL2⟩ := _root_.GlobalTheory.HermBlockChange.exists_unit_lower_block O c h2 (fun n J hJ hJd g hgd hgu => core O c hcc h2 hcx n J hJ hJd g hgd hgu)
    n JL G G' hJh hJu hGG hU
  exact GlobalTheory.T.exists_adelic_skewHermitian_correction_of_local_solution F E σ n X v O c ι P Q JL hAt hsupp hcι hPQ hQP hP hQ hJ hlat (GlobalTheory.DblVac.matD g) G ZL hg1 hMG hZL1 hZL2

end GlobalTheory.TransvChoose
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianColumnsLinearParametrisationFinitePlacStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lagrangianColumns_linear_parametrisation_finitePlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (v : Pl (F := F))
    (m : ℕ) (C : Matrix (Fin d) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), IsLagrAt σ W v C →
    d = 2 * m ∧ ∃ (N : ℕ) (j : (Fin N → Fv F v) →ₗ[Fv F v] (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v))
      (ζ : (Fin N → Fv F v) → Matrix (Fin n) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), Function.Injective j ∧
      (∀ y, At (evFin F v) (ζ y) ∧ locCo M.co v (ζ y * Cᵀ) = j y) ∧
      (∀ z : Matrix (Fin n) (Fin m) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) z → ∃ y, ζ y = z) ∧
      ∀ s : GL (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), ∃ T : GL (Fin N) (Fv F v), (∀ y, ζ (T.val *ᵥ y) = s.val * ζ y) ∧
        T.val.det = Algebra.norm (Fv F v) (compFin F E v s.val.det) ^ m := by
  first | exact @GlobalTheory.InertLagParam.param | exact GlobalTheory.InertLagParam.param | (intros; apply GlobalTheory.InertLagParam.param <;> assumption)
end

