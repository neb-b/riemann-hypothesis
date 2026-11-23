module

public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.ExistsGap
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.WdValAppend
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.NrmLCharpoly

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.KeepQ
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

section AlgExPf

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem keepQ {Q : Submodule ℂ H} {Γ : Type} {op : Γ → (H →L[ℂ] H)} {v : Γ → ℂ}
    (hQ : ∀ x, ∀ f ∈ Q, op x f ∈ Q ∧ star (op x) f ∈ Q) {y : (H →L[ℂ] H) × ℂ}
    (hy : y ∈ StarAlgebra.adjoin ℂ (Set.range fun x => (op x, v x))) :
    (∀ f ∈ Q, y.1 f ∈ Q) ∧ ∀ f ∈ Q, (star y.1) f ∈ Q := by
  induction hy using StarAlgebra.adjoin_induction with
  | mem x h =>
    obtain ⟨a, rfl⟩ := h
    exact ⟨fun f hf => (hQ a f hf).1, fun f hf => (hQ a f hf).2⟩
  | algebraMap r =>
    have h1 : (algebraMap ℂ ((H →L[ℂ] H) × ℂ) r).1 = r • (1 : H →L[ℂ] H) := by
      rw [Prod.algebraMap_apply, Algebra.algebraMap_eq_smul_one]
    rw [h1]
    refine ⟨fun f hf => ?_, fun f hf => ?_⟩
    · simpa using Q.smul_mem r hf
    · simpa [star_smul] using Q.smul_mem (star r) hf
  | add x y _ _ hx hy =>
    refine ⟨fun f hf => ?_, fun f hf => ?_⟩
    · exact Q.add_mem (hx.1 f hf) (hy.1 f hf)
    · rw [Prod.fst_add, star_add]
      exact Q.add_mem (hx.2 f hf) (hy.2 f hf)
  | mul x y _ _ hx hy =>
    refine ⟨fun f hf => ?_, fun f hf => ?_⟩
    · exact hx.1 _ (hy.1 f hf)
    · rw [Prod.fst_mul, star_mul]
      exact hy.2 _ (hx.2 f hf)
  | star x _ hx =>
    refine ⟨fun f hf => hx.2 f hf, fun f hf => ?_⟩
    have : (star (star x).1) = x.1 := by rw [Prod.fst_star, star_star]
    rw [this]
    exact hx.1 f hf

end AlgExPf

end UpperTheory.Zero.ConvolutionTheory.EB

theorem UpperTheory.Zero.ConvolutionTheory.EB.algEx :
    UpperTheory.Zero.ConvolutionTheory.EB.AlgEx := by
  intro H _ _ _ Q _ Γ op v hc hs hQ
  let s : Set ((H →L[ℂ] H) × ℂ) := Set.range fun x => (op x, v x)
  have hcomm : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact Prod.ext (hc x y).eq (mul_comm _ _)
  have hcs : ∀ a ∈ s, ∀ b ∈ s, a * star b = star b * a := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact Prod.ext (hs x y).eq (mul_comm _ _)
  letI : IsMulCommutative (StarAlgebra.adjoin ℂ s) :=
    StarAlgebra.isMulCommutative_adjoin ℂ
      (fun x hx => ⟨(hcs x hx x hx).symm⟩)
      (fun x hx y hy _ => hcomm x hx y hy)
      (fun x hx y hy _ => hcs x hx y hy)
  letI : CommRing (StarAlgebra.adjoin ℂ s) := { (inferInstance : Ring _) with
    mul_comm := fun a b => mul_comm' a b }
  have keep : ∀ y : StarAlgebra.adjoin ℂ s, (∀ f ∈ Q, y.1.1 f ∈ Q) ∧ ∀ f ∈ Q, (star y.1.1) f ∈ Q :=
    fun y => UpperTheory.Zero.ConvolutionTheory.EB.keepQ hQ y.2
  let res : StarAlgebra.adjoin ℂ s → (Q →L[ℂ] Q) := fun y =>
    (y.1.1 ∘L Q.subtypeL).codRestrict Q fun q => (keep y).1 q q.2
  let R : StarAlgebra.adjoin ℂ s →⋆ₐ[ℂ] (Q →L[ℂ] Q) :=
    { toFun := res
      map_one' := by ext q; rfl
      map_mul' := fun a b => by ext q; rfl
      map_zero' := by ext q; rfl
      map_add' := fun a b => by ext q; rfl
      commutes' := fun r => by
        ext q
        have h1 : ((algebraMap ℂ (StarAlgebra.adjoin ℂ s) r).1).1 = r • (1 : H →L[ℂ] H) := by
          show (algebraMap ℂ ((H →L[ℂ] H) × ℂ) r).1 = _
          rw [Prod.algebraMap_apply, Algebra.algebraMap_eq_smul_one]
        have h2 : algebraMap ℂ (Q →L[ℂ] Q) r = r • (1 : Q →L[ℂ] Q) :=
          Algebra.algebraMap_eq_smul_one r
        show ((algebraMap ℂ (StarAlgebra.adjoin ℂ s) r).1).1 (q : H) = _
        rw [h1, h2]
        simp
      map_star' := fun y => by
        show res (star y) = star (res y)
        rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.eq_adjoint_iff]
        intro p q
        show inner ℂ (star y.1.1 (p : H)) (q : H) = inner ℂ (p : H) (y.1.1 (q : H))
        rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left] }
  let ι : Γ → StarAlgebra.adjoin ℂ s := fun x => ⟨(op x, v x), StarAlgebra.subset_adjoin ℂ s ⟨x, rfl⟩⟩
  have all : ∀ y : StarAlgebra.adjoin ℂ s, y ∈ StarAlgebra.adjoin ℂ (Set.range ι) := by
    intro y
    induction y using StarAlgebra.adjoin_induction_subtype with
    | mem x h =>
      obtain ⟨a, rfl⟩ := h
      exact StarAlgebra.subset_adjoin ℂ _ ⟨a, rfl⟩
    | algebraMap r => exact algebraMap_mem _ r
    | add x y hx hy => exact add_mem hx hy
    | mul x y hx hy => exact mul_mem hx hy
    | star x hx => exact star_mem hx
  have top : StarAlgebra.adjoin ℂ (Set.range ι) = ⊤ := eq_top_iff.2 fun y _ => all y
  exact ⟨{ B := StarAlgebra.adjoin ℂ s
           R := R
           P := (StarAlgHom.snd ℂ (H →L[ℂ] H) ℂ).comp (StarSubalgebra.subtype _)
           F := (StarAlgHom.fst ℂ (H →L[ℂ] H) ℂ).comp (StarSubalgebra.subtype _)
           ι := ι
           hF := fun _ => rfl
           hP := fun _ => rfl
           hR := fun _ _ => rfl
           top := top }⟩
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.LvEx
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] borelG borelF borelA borelH

theorem UpperTheory.Zero.ConvolutionTheory.EB.lvEx :
    UpperTheory.Zero.ConvolutionTheory.EB.LvEx := by
  intro E _ _ _ a b Z φ h
  have key : ∀ w : Pl E, ∃ (A : Subgroup (GLw a w)) (B : Subgroup (GLw b w)),
      IsOpen (A : Set (GLw a w)) ∧ IsOpen (B : Set (GLw b w)) ∧ A ≤ KGL w (n := a) ∧ B ≤ KGL w (n := b) ∧
      (w ∉ Z → A = KGL w (n := a) ∧ B = KGL w (n := b)) ∧ (w ∈ Z → IsHecke (A.prod B) (φ w)) := by
    intro w
    by_cases hw : w ∈ Z
    · obtain ⟨K', ho, hle, hH⟩ := h w hw
      refine ⟨K'.comap (MonoidHom.inl _ _), K'.comap (MonoidHom.inr _ _), ?_, ?_, ?_, ?_,
        fun h' => absurd hw h', fun _ => ⟨hH.1, ?_⟩⟩
      · exact ho.preimage (continuous_id.prodMk continuous_const)
      · exact ho.preimage (continuous_const.prodMk continuous_id)
      · intro x hx
        exact (hle hx).1
      · intro y hy
        exact (hle hy).2
      · rintro ⟨x, y⟩ ⟨hx, hy⟩ g
        have hxy : ((x, y) : GLw a w × GLw b w) ∈ K' := by
          have := K'.mul_mem hx hy
          simpa using this
        exact hH.2 _ hxy g
    · exact ⟨KGL w (n := a), KGL w (n := b), (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).1,
        (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).1, le_rfl, le_rfl,
        fun _ => ⟨rfl, rfl⟩, fun h' => absurd h' hw⟩
  choose A B hA hB hA' hB' hoff hfix using key
  exact ⟨⟨A, B, hA, hB, hA', hB', hoff⟩, hfix⟩
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.PeakAlg
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

private lemma wdVal_map {B C Γ : Type} [CommRing B] [StarRing B] [Algebra ℂ B] [Ring C] [StarRing C] [Algebra ℂ C]
    (f : B →⋆ₐ[ℂ] C) (gen : Γ → B) (w : List (Γ × Bool)) :
    f (wdVal gen w) = wdVal (fun x => f (gen x)) w := by
  induction w with
  | nil => simp [wdVal]
  | cons p w ih =>
    simp only [wdVal, List.map_cons, List.prod_cons, map_mul] at ih ⊢
    rw [ih]
    congr 1
    split_ifs <;> simp [map_star]

theorem peakAlg : PeakAlg := by
  intro H _ _ _ Q _ Γ op v 𝔄 arch a₀ x ρ ha hv hρ hs
  let gen : {γ // arch γ} → 𝔄.B := fun γ => 𝔄.ι γ
  let A : StarSubalgebra ℂ 𝔄.B := StarAlgebra.adjoin ℂ (Set.range gen)
  have hmem : ∀ γ : {γ // arch γ}, 𝔄.ι γ ∈ A := fun γ =>
    StarAlgebra.subset_adjoin ℂ (Set.range gen) (Set.mem_range_self γ)
  let p : A →⋆ₐ[ℂ] ℂ := 𝔄.P.comp A.subtype
  let a₁ : A := ⟨𝔄.ι a₀, hmem ⟨a₀, ha⟩⟩
  obtain ⟨g, hg, hn⟩ := UpperTheory.V.Z.Tf.GlobalTraceComparison.peak 𝔄.B Q 𝔄.R A p a₁ (𝔄.ι x) ρ
    (by
      change 𝔄.P (𝔄.ι a₀) = 1
      rw [𝔄.hP, hv])
    hρ
    (fun s hb hsa => hs s hb fun γ hγ => by
      have h1 := hsa ⟨𝔄.ι γ, hmem ⟨γ, hγ⟩⟩
      have h2 : p ⟨𝔄.ι γ, hmem ⟨γ, hγ⟩⟩ = v γ := by
        change 𝔄.P (𝔄.ι γ) = v γ
        exact 𝔄.hP γ
      rw [← h2]
      exact h1)
  obtain ⟨J, hJ, c, w, L, -, hgw, -⟩ := PositivityTheory.Rg.BcB.F.adjWords _ _ gen (g : 𝔄.B) g.2
  refine ⟨J, hJ, c, w, ?_, ?_⟩
  · have hp : 𝔄.P (g : 𝔄.B) = 1 := hg
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hgw, map_sum] at hp
    rw [← hp]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, wdVal_map, smul_eq_mul]
    congr 2
    funext γ
    exact (𝔄.hP γ).symm
  · have hF : op x * ((∑ j, c j • wdVal (fun γ : {γ // arch γ} => op γ) (w j)) * op a₀) =
        𝔄.F (𝔄.ι x * ((g : 𝔄.B) * 𝔄.ι a₀)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_mul, map_mul, 𝔄.hF, 𝔄.hF, hgw, map_sum]
      congr 2
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, wdVal_map]
      congr 2
      funext γ
      exact (𝔄.hF γ).symm
    rw [hF]
    have hnorm : ‖𝔄.F (𝔄.ι x * ((g : 𝔄.B) * 𝔄.ι a₀)) ∘L Q.subtypeL‖ =
        ‖𝔄.R (𝔄.ι x * ((g : 𝔄.B) * 𝔄.ι a₀))‖ := by
      refine ContinuousLinearMap.opNorm_ext _ _ fun q => ?_
      change ‖𝔄.F _ (q : H)‖ = ‖(𝔄.R _ q)‖
      rw [← 𝔄.hR]
      rfl
    rw [hnorm]
    exact hn

end UpperTheory.Zero.ConvolutionTheory.EB
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.PowNorm
section
theorem UpperTheory.Zero.ConvolutionTheory.EB.powNorm :
    UpperTheory.Zero.ConvolutionTheory.EB.PowNorm := by
  intro H _ _ Q U ρ hQ hU k
  have hρ : 0 ≤ ρ := (norm_nonneg _).trans hU
  have hb : ∀ f ∈ Q, ‖U f‖ ≤ ρ * ‖f‖ := by
    intro f hf
    exact (U ∘L Q.subtypeL).le_of_opNorm_le hU ⟨f, hf⟩
  have key : ∀ k : ℕ, ∀ f ∈ Q, (U ^ k) f ∈ Q ∧ ‖(U ^ k) f‖ ≤ ρ ^ k * ‖f‖ := by
    intro k
    induction k with
    | zero =>
      intro f hf
      simp [hf]
    | succ k ih =>
      intro f hf
      obtain ⟨h1, h2⟩ := ih f hf
      have e : (U ^ (k + 1)) f = U ((U ^ k) f) := by
        rw [pow_succ']
        rfl
      rw [e]
      refine ⟨hQ _ h1, (hb _ h1).trans ?_⟩
      rw [pow_succ', mul_assoc]
      exact mul_le_mul_of_nonneg_left h2 hρ
  refine ⟨fun f hf => (key k f hf).1, ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (pow_nonneg hρ k) fun q => ?_
  exact (key k q q.2).2
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.SatCard
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] borelG borelF borelA borelH

theorem UpperTheory.Zero.ConvolutionTheory.EB.satCard :
    UpperTheory.Zero.ConvolutionTheory.EB.SatCard := by
  intro E _ _ _ n D w B h
  obtain ⟨b, hb, rfl⟩ := h
  rw [Multiset.card_sum]
  exact (Finset.sum_congr rfl fun i _ => (hb i).card).trans D.sum
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.TranslCharpoly
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

open PositivityTheory.Rg.Tf.Loc (twConj)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem transl_eq {u : GL (Fin n) E} (hu : IsTransl u) (d : GL (Fin n) E) (x : GA E n) :
    gFin (twConj (thetaA E n) x (ratGL E n d)) * (ratF E n u)⁻¹ =
      (GeneralLinearGroup.map (pFin E) x)⁻¹ * ratF E n (d * u⁻¹) * thF E n (GeneralLinearGroup.map (pFin E) x) := by
  have h := congrArg (GeneralLinearGroup.map (pFin E)) (adeleqof_twist translAd_holds hu d x)
  simp only [map_mul, map_inv, adeleqof_pFin_thetaGL, adeleqof_pFin_ratGL] at h
  rw [map_mul (ratF E n), map_inv]
  exact h

private theorem transl_norm {u : GL (Fin n) E} (hu : IsTransl u) (d : GL (Fin n) E) (x : GA E n) :
    (gFin (twConj (thetaA E n) x (ratGL E n d)) * (ratF E n u)⁻¹) *
        thF E n (gFin (twConj (thetaA E n) x (ratGL E n d)) * (ratF E n u)⁻¹) =
      (GeneralLinearGroup.map (pFin E) x)⁻¹ * ratF E n (nrm d) * GeneralLinearGroup.map (pFin E) x := by
  rw [transl_eq hu]
  set c := GeneralLinearGroup.map (pFin E) x
  set r := ratF E n (d * u⁻¹) with hr0
  set s := ratF E n (thE E n (d * u⁻¹)) with hs0
  have hr : thF E n r = s := by
    rw [hr0, hs0, GlobalTheory.EulerTw.Comm.thF_ratF]
  rw [← poleq_norm E n u hu d, map_mul (ratF E n), ← hr0, ← hs0, map_mul, map_mul, map_inv,
    GlobalTheory.EulerTw.Comm.thF_thF, hr]
  group

private theorem transl_charpoly (w : Pl E) {u : GL (Fin n) E} (hu : IsTransl u) (d : GL (Fin n) E) (x : GA E n) :
    (GeneralLinearGroup.map (pLoc E w) ((gFin (twConj (thetaA E n) x (ratGL E n d)) * (ratF E n u)⁻¹) *
        thF E n (gFin (twConj (thetaA E n) x (ratGL E n d)) * (ratF E n u)⁻¹))).val.charpoly =
      (nrm d).val.charpoly.map (algebraMap E (w.adicCompletion E)) := by
  rw [transl_norm hu, map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, Matrix.coe_units_inv,
    Matrix.charpoly_units_conj']
  rw [← Matrix.charpoly_map]
  rfl

private theorem sep_of {a b : ℕ} {S : Set (Pl E)} {φ₁ φ₂ : ∀ w : Pl E, LF a b w} (h₁ : IsTestP φ₁) (h₂ : IsTestP φ₂)
    {w : Pl E} (hwS : w ∈ S) (hsp : IsSplitAt w)
    (hreg : ∀ y z, φ₁ w y ≠ 0 → φ₂ w z ≠ 0 → ((y * z).1.val.charpoly * (y * z).2.val.charpoly).Separable)
    (y : Gf E a b) (hne : finFn S φ₁ φ₂ y ≠ 0) :
    (GeneralLinearGroup.map (pLoc E w) (y.1 * thF E a y.1)).val.charpoly.Separable ∧
      (GeneralLinearGroup.map (pLoc E w) (y.2 * thF E b y.2)).val.charpoly.Separable := by
  have hf := GlobalTheory.CompanionTheory.SuppFinTw.factors_ne h₁ h₂ y hne w hwS
  have hs := hreg (atW w y) (atW w (thP E a b y)) hf.1 (hf.2 hsp)
  have e₁ : (atW w y * atW w (thP E a b y)).1 = GeneralLinearGroup.map (pLoc E w) (y.1 * thF E a y.1) :=
    (map_mul _ _ _).symm
  have e₂ : (atW w y * atW w (thP E a b y)).2 = GeneralLinearGroup.map (pLoc E w) (y.2 * thF E b y.2) :=
    (map_mul _ _ _).symm
  rw [e₁, e₂] at hs
  exact ⟨Polynomial.Separable.of_mul_left hs, Polynomial.Separable.of_mul_right hs⟩

theorem _root_.UpperTheory.Zero.ConvolutionTheory.EB.regS : RegS := by
  intro E _ _ _ a b S u₁ u₂ hu₁ hu₂ φ₁ φ₂ h₁ h₂ hw
  obtain ⟨w, hwS, hsp, hreg⟩ := hw
  refine ⟨fun d x h₂' hne => ?_, fun d x h₁' hne => ?_⟩
  · have hs := (sep_of h₁ h₂ hwS hsp hreg _ hne).1
    simp only [Prod.fst_mul, Prod.fst_inv] at hs
    rw [transl_charpoly w hu₁] at hs
    exact (Polynomial.separable_map _).1 hs
  · have hs := (sep_of h₁ h₂ hwS hsp hreg _ hne).2
    simp only [Prod.snd_mul, Prod.snd_inv] at hs
    rw [transl_charpoly w hu₂] at hs
    exact (Polynomial.separable_map _).1 hs

end UpperTheory.Zero.ConvolutionTheory.EB

end
end

