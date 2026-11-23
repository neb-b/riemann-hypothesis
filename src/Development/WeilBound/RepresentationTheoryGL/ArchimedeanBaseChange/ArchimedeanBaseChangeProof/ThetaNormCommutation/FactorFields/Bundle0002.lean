module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.TensorCompl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1048
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NegOneNotSqSqrtTwo
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PGenUnit
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.GenUnitP

theorem avg_const {H : Type} [Group H] (c : ℂ) : avg (fun _ : H => c) = c := by
  have hR : rStab (fun _ : H => c) = ⊤ := by
    ext k; simp [GlobalTheory.TwOrbConj.mem_rStab]
  unfold avg
  rw [hR, Subgroup.index_top]
  haveI : Subsingleton (H ⧸ (⊤ : Subgroup H)) := QuotientGroup.subsingleton_quotient_top
  rw [finsum_eq_single _ (1 : H ⧸ (⊤ : Subgroup H)) (fun q hq => absurd (Subsingleton.elim q 1) hq)]
  simp

theorem ind_const {G : Type} [Group G] (θ : G →* G) (K : Subgroup G) (hKθ : ∀ k ∈ K, θ k ∈ K) (y x : G) :
    (fun k : K => (K : Set G).indicator (1 : G → ℂ) ((x * k)⁻¹ * y * θ (x * k))) =
      fun _ => (K : Set G).indicator (1 : G → ℂ) (x⁻¹ * y * θ x) := by
  funext k
  have e : (x * (k : G))⁻¹ * y * θ (x * k) = (k : G)⁻¹ * (x⁻¹ * y * θ x) * θ k := by
    simp only [map_mul, _root_.mul_inv_rev]; group
  rw [e]
  by_cases hm : x⁻¹ * y * θ x ∈ K
  · rw [Set.indicator_of_mem (show _ ∈ (K : Set G) from
      K.mul_mem (K.mul_mem (K.inv_mem k.2) hm) (hKθ _ k.2)), Set.indicator_of_mem (show _ ∈ (K : Set G) from hm)]
    rfl
  · rw [Set.indicator_of_notMem (show _ ∉ (K : Set G) from hm), Set.indicator_of_notMem]
    intro h
    apply hm
    have := K.mul_mem (K.mul_mem k.2 h) (K.inv_mem (hKθ _ k.2))
    simpa [mul_assoc] using this

theorem summand_eq {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G)
    (hKθ : ∀ k ∈ K, θ k ∈ K) (y x : G) :
    GlobalTheory.TwOrbConj.summand θ K y ((K : Set G).indicator 1) x =
      if x⁻¹ * y * θ x ∈ K then
        (((twCent θ y ⊓ K.map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent θ y)) : ℕ) : ℂ) else 0 := by
  unfold GlobalTheory.TwOrbConj.summand
  rw [ind_const θ K hKθ y x, avg_const]
  by_cases hm : x⁻¹ * y * θ x ∈ K
  · rw [Set.indicator_of_mem (show _ ∈ (K : Set G) from hm), if_pos hm]; simp
  · rw [Set.indicator_of_notMem (show _ ∉ (K : Set G) from hm), if_neg hm]; simp

end PositivityTheory.Rg.BcB.G3.GenUnitP

theorem PositivityTheory.Rg.BcB.G3.genUnit_pf : PositivityTheory.Rg.BcB.G3.GenUnit := by
  intro G _ _ _ θ K z hKθ hzK huniq hcptK g
  have hidx : ∀ x : G, (rStab fun k : K =>
      (K : Set G).indicator (1 : G → ℂ) ((x * k)⁻¹ * z * θ (x * k))).index ≠ 0 := by
    intro x
    rw [PositivityTheory.Rg.BcB.G3.GenUnitP.ind_const θ K hKθ z x]
    have : rStab (fun _ : K => (K : Set G).indicator (1 : G → ℂ) (x⁻¹ * z * θ x)) = ⊤ := by
      ext k; simp [GlobalTheory.TwOrbConj.mem_rStab]
    rw [this, Subgroup.index_top]
    exact one_ne_zero
  rw [GlobalTheory.TwOrbConj.twOrb_twConj G θ K z g ((K : Set G).indicator 1) hidx]
  have hcpt : cptPart (twCent θ z) ≤ twCent θ z ⊓ K :=
    le_inf ((Subgroup.closure_le _).2 fun t ht => ht.1)
      ((Subgroup.closure_le _).2 fun t ht => hcptK t ht.1 ht.2)
  have hval : GlobalTheory.TwOrbConj.summand θ K z ((K : Set G).indicator 1) 1 = 1 := by
    rw [PositivityTheory.Rg.BcB.G3.GenUnitP.summand_eq θ K hKθ z 1, if_pos (by simpa using hzK),
      GlobalTheory.TwOrbConj.map_conj_self K (K.one_mem), (Subgroup.relIndex_eq_one).2 hcpt]
    simp
  rw [GlobalTheory.TwOrbConj.twOrb_eq, finsum_eq_single _ (DoubleCoset.mk (twCent θ z) K 1)]
  · obtain ⟨t, ht, k, hk, he⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1
      (DoubleCoset.out_eq' (DoubleCoset.mk (twCent θ z) K 1)).symm
    rw [he, GlobalTheory.TwOrbConj.summand_rep θ K z _ 1 ht hk, hval]
  · intro q hq
    rw [PositivityTheory.Rg.BcB.G3.GenUnitP.summand_eq θ K hKθ z]
    split_ifs with hm
    · exfalso
      apply hq
      obtain ⟨t, ht, k, hk, he⟩ := huniq _ hm
      symm
      conv_rhs => rw [← DoubleCoset.out_eq' q]
      rw [DoubleCoset.eq]
      exact ⟨t, ht, k, hk, by rw [he]; group⟩
    · rfl
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PQuadField
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.QuadFieldP

open QuadraticAlgebra

theorem not_sq_of_real (E : Type) [Field E] [NumberField E] [IsCMField E] (s : E)
    (d : maximalRealSubfield E) (hs0 : s ≠ 0) (hs : IsCMField.complexConj E s = -s)
    (hd : algebraMap (maximalRealSubfield E) E d = s ^ 2) (K : Type) [Field K]
    [Algebra (maximalRealSubfield E) K] (τ : K →+* ℂ) (t : ℂ) (ht : starRingEnd ℂ t = t) :
    t ^ 2 ≠ τ (algebraMap (maximalRealSubfield E) K d) := by
  intro h
  let _ := (τ.comp (algebraMap (maximalRealSubfield E) K)).toAlgebra
  let φ : E →ₐ[maximalRealSubfield E] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have h1 : (φ s) ^ 2 = τ (algebraMap (maximalRealSubfield E) K d) := by
    rw [← map_pow, ← hd, φ.commutes]; rfl
  have hu : starRingEnd ℂ (φ s) = - φ s := by
    have h' := IsCMField.complexEmbedding_complexConj E φ.toRingHom s
    simpa [hs] using h'.symm
  have hu0 : φ s ≠ 0 := by
    intro h0; exact hs0 (φ.toRingHom.injective (by simpa using h0))
  rw [← h1] at h
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h with h2 | h2
  · apply hu0
    have : starRingEnd ℂ (φ s) = φ s := by rw [← h2]; exact ht
    have h3 : (2 : ℂ) * φ s = 0 := by linear_combination hu - this
    simpa using h3
  · apply hu0
    have : starRingEnd ℂ (φ s) = φ s := by
      have := congrArg Neg.neg ht
      rw [h2, map_neg, neg_neg, neg_neg] at this
      exact this
    have h3 : (2 : ℂ) * φ s = 0 := by linear_combination hu - this
    simpa using h3

end PositivityTheory.Rg.BcB.G3.QuadFieldP

namespace PositivityTheory.Rg.BcB.G3

open QuadFieldP QuadraticAlgebra in
theorem quadField_pf : QuadField := by
  intro E _ _ _ s d hs0 hs hd K _ _ _ hKr
  refine ⟨?_, ?_⟩
  · rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyReal.nrComplexPlaces_eq_zero, add_zero,
      ← IsTotallyReal.finrank, ← IsCMField.card_infinitePlace_eq_card_infinitePlace E,
      InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyReal.nrComplexPlaces_eq_zero, add_zero,
      ← IsTotallyReal.finrank, ← (letI : Module.Free (maximalRealSubfield E) K := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) K), mul_comm]
  generalize hδ : algebraMap (maximalRealSubfield E) K d = δ
  have hkey : ∀ (τ : K →+* ℂ) (t : ℂ), starRingEnd ℂ t = t → t ^ 2 ≠ τ δ := by
    intro τ t ht
    rw [← hδ]
    exact not_sq_of_real E s d hs0 hs hd K τ t ht
  have hns : ∀ r : K, r ^ 2 ≠ δ + 0 * r := by
    intro r hr
    let τ : K →+* ℂ := Classical.choice (inferInstance : Nonempty _)
    have hre := ComplexEmbedding.isReal_iff.1 (IsTotallyReal.complexEmbedding_isReal τ)
    refine hkey τ (τ r) ?_ ?_
    · rw [← ComplexEmbedding.conjugate_coe_eq, hre]
    · rw [← map_pow, hr, zero_mul, add_zero]
  have : Fact (∀ r : K, r ^ 2 ≠ δ + 0 * r) := ⟨hns⟩
  have hq := GlobalTheory.QuadSymbol.Model.isQuadratic δ
  have hnf := GlobalTheory.QuadSymbol.Model.numberField δ
  have : FiniteDimensional K (QuadraticAlgebra K δ 0) :=
    Module.Finite.of_basis (QuadraticAlgebra.basis δ 0)
  refine ⟨QuadraticAlgebra K δ 0, inferInstance, hnf, inferInstance, hq, ?_, ?_, ?_⟩
  · refine ⟨fun w => ?_⟩
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    intro hre
    let e := w.embedding
    refine hkey (e.comp (algebraMap K _)) (e (ω : QuadraticAlgebra K δ 0)) ?_ ?_
    · rw [← ComplexEmbedding.conjugate_coe_eq, hre]
    · rw [RingHom.comp_apply, ← map_pow, sq, omega_mul_omega_eq_algebraMap]; simp
  · intro x
    rw [GlobalTheory.QuadSymbol.mem_globalNorms_iff]
    have key := GlobalTheory.QuadSymbol.Model.mem_normGroup_sqrt (A := K) δ (x := x)
    rw [GlobalTheory.QuadSymbol.mem_normGroup_iff] at key
    simp only [Algebra.algebraMap_self, RingHom.id_apply] at key
    rw [← key]
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨(Algebra.TensorProduct.lid K _).symm z, ?_⟩
      rw [Algebra.norm_eq_of_algEquiv, hz]
    · rintro ⟨z, hz⟩
      refine ⟨Algebra.TensorProduct.lid K _ z, ?_⟩
      rw [Algebra.norm_eq_of_algEquiv, hz]
  · intro u x
    exact GlobalTheory.QuadSymbol.Model.mem_normGroup_sqrt δ

end PositivityTheory.Rg.BcB.G3

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PSkewEx
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3

theorem skewEx_pf : SkewEx := by
  intro E _ _ _
  obtain ⟨x, hx⟩ : ∃ x : E, IsCMField.complexConj E x ≠ x := by
    by_contra h
    push Not at h
    exact IsCMField.complexConj_ne_one (K := E) (AlgEquiv.ext h)
  have hconj : IsCMField.complexConj E (x - IsCMField.complexConj E x) = -(x - IsCMField.complexConj E x) := by
    rw [map_sub, IsCMField.complexConj_apply_apply, neg_sub]
  have hmem : (x - IsCMField.complexConj E x) ^ 2 ∈ maximalRealSubfield E := by
    rw [← IsCMField.complexConj_eq_self_iff, map_pow, hconj, neg_sq]
  exact ⟨x - IsCMField.complexConj E x, ⟨_, hmem⟩, sub_ne_zero.mpr (Ne.symm hx), hconj, rfl⟩

end PositivityTheory.Rg.BcB.G3

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PSplitSq
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3

theorem splitSq_pf (h1 : TensorCompl) : SplitSq := by
  intro E _ _ _ s d hs hcs hd w hw
  have hcm : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt (maximalRealSubfield E) E (IsCMField.complexConj E).toAlgHom :=
    ⟨inferInstance, inferInstance, Algebra.IsQuadraticExtension.finrank_eq_two _ _,
      fun τ x => IsCMField.complexEmbedding_complexConj E τ x⟩
  obtain ⟨u, hne, hu⟩ := hw
  have hv : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) (w.under (𝓞 (maximalRealSubfield E))) :=
    ⟨u, w, hne, congrArg HeightOneSpectrum.asIdeal hu, rfl⟩
  obtain ⟨τ, -⟩ := GlobalTheory.LFun.SplitChart.exists_splitPrime_eq hcm hv rfl
  refine ⟨τ s, ?_⟩
  have key : τ (algebraMap (maximalRealSubfield E) E d) = τ s * τ s := by rw [hd, pow_two, map_mul]
  exact (τ.commutes d).symm.trans key

end PositivityTheory.Rg.BcB.G3

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PTensorCompl
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.TensorComplP

variable {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
  (v : HeightOneSpectrum (𝓞 F))

theorem finite_over : {w : HeightOneSpectrum (𝓞 K) | w.under (𝓞 F) = v}.Finite := by
  have := v.isMaximal
  have h := IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 K)
  refine (h.preimage (f := HeightOneSpectrum.asIdeal)
    (fun a _ b _ hab => HeightOneSpectrum.ext hab)).subset ?_
  rintro w rfl
  exact ⟨w.isPrime, ⟨rfl⟩⟩

def phi : v.adicCompletion F ⊗[F] K →+*
    (∀ u : {u : HeightOneSpectrum (𝓞 K) // u.under (𝓞 F) = v}, u.1.adicCompletion K) :=
  RingHom.pi fun u => GlobalTheory.LFun.toCompl u.2

theorem phi_apply (y : v.adicCompletion F ⊗[F] K) (u : {u : HeightOneSpectrum (𝓞 K) // u.under (𝓞 F) = v}) :
    phi v y u = GlobalTheory.LFun.toCompl u.2 y := rfl

def extZ : v.adicCompletion F ⊗[F] K →ₗ[F] FiniteAdeleRing (𝓞 F) F ⊗[F] K :=
  LinearMap.rTensor K (GlobalTheory.AdelicU.singleFin v)

theorem map_extZ_self (y : v.adicCompletion F ⊗[F] K) :
    Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F K) (extZ v y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    simp only [extZ, LinearMap.rTensor_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rw [GlobalTheory.AdelicU.evalV_singleFin_self]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem map_extZ_ne {v' : HeightOneSpectrum (𝓞 F)} (h : v' ≠ v) (y : v.adicCompletion F ⊗[F] K) :
    Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v') (AlgHom.id F K) (extZ v y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    simp only [extZ, LinearMap.rTensor_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rw [GlobalTheory.AdelicU.evalV_singleFin_ne h, TensorProduct.zero_tmul]
  | add a b ha hb => simp only [map_add (f := _), ha, hb, add_zero]

theorem phi_injective : Function.Injective (phi (K := K) v) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro y hy
  have h0 : GlobalTheory.LFun.finAdEquiv F K (extZ v y) = 0 := by
    have hc : ∀ w : HeightOneSpectrum (𝓞 K), GlobalTheory.LFun.finAdEquiv F K (extZ v y) w = 0 := by
      intro w
      by_cases hw : w.under (𝓞 F) = v
      · rw [GlobalTheory.LFun.finAdEquiv_apply hw, map_extZ_self]
        exact (phi_apply v y ⟨w, hw⟩).symm.trans (congrFun hy ⟨w, hw⟩)
      · rw [GlobalTheory.LFun.finAdEquiv_apply rfl, map_extZ_ne v hw, map_zero]
    exact Subtype.ext (funext hc)
  have h1 : extZ v y = 0 := (map_eq_zero_iff _ (GlobalTheory.LFun.finAdEquiv F K).injective).1 h0
  rw [← map_extZ_self v y, h1, map_zero]

theorem phi_surjective : Function.Surjective (phi (K := K) v) := by
  intro z
  obtain ⟨y, hy⟩ := (GlobalTheory.LFun.finAdEquiv F K).surjective
    ⟨fun w => if h : w.under (𝓞 F) = v then z ⟨w, h⟩ else 0, by
      filter_upwards [(finite_over (K := K) v).compl_mem_cofinite] with u hu
      rw [dite_eq_right (by simpa using hu)]
      exact zero_mem _⟩
  refine ⟨Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F K) y, funext fun u => ?_⟩
  rw [phi_apply, ← GlobalTheory.LFun.finAdEquiv_apply u.2, hy]
  show (if h : u.1.under (𝓞 F) = v then z ⟨u.1, h⟩ else 0) = z u
  rw [dite_eq_left u.2]

end PositivityTheory.Rg.BcB.G3.TensorComplP

open PositivityTheory.Rg.BcB.G3.TensorComplP in
theorem PositivityTheory.Rg.BcB.G3.tensorCompl_pf : TensorCompl := by
  intro F K _ _ _ _ _ v
  refine ⟨RingEquiv.ofBijective (phi v) ⟨phi_injective v, phi_surjective v⟩, fun a u => ?_⟩
  show GlobalTheory.LFun.toCompl u.2 (1 ⊗ₜ[F] a) = _
  rw [GlobalTheory.LFun.toCompl_tmul, map_one, one_mul]

end
end

