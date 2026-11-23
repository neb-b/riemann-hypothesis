module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0030
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0018
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagLineDegree
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0031
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0032
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0029

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpVerticalPush
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

open Classical in
theorem BlowUpVerticalPush.proof (hfib : BlowUpVerticalFibre.Statement.{u}) :
    BlowUpVerticalPush.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hu' c x hx hxP a
  have hZ : (Function.support (divCycle (blowUpOf P u) (liftForm (J := J) x))).Finite :=
    DivCycleFiniteSupport.proof O (Option K) (extIdx ι J) _ _

  have hC : ∀ W' : Ideal (MRing (extIdx ι J) O), (C ϖ : MRing (extIdx ι J) O) ∈ W' ↔
      (C ϖ : MRing ι O) ∈ W'.comap (liftForm (ι := ι) (J := J) (R := O)) := by
    intro W'
    rw [Ideal.mem_comap]
    simp [liftForm]
  set g : Ideal (MRing (extIdx ι J) O) → ℤ := fun W' =>
    divCycle (blowUpOf P u) (liftForm x) W' *
      (if (C ϖ : MRing (extIdx ι J) O) ∈ W' then vNum W' (liftDegs a) else 0) with hg_def
  have hg : Function.support g ⊆ hZ.toFinset := fun W' hW' =>
    hZ.mem_toFinset.mpr (Function.support_mul_subset_left _ _ hW')

  have key : ∀ W : Ideal (MRing ι O),
      (∑ W' ∈ hZ.toFinset with W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W, g W') =
        divCycle P x W * (if (C ϖ : MRing ι O) ∈ W then vNum W a else 0) := by
    intro W
    by_cases hW : (C ϖ : MRing ι O) ∈ W
    · rw [if_pos hW, ← hfib O ϖ hϖ K ι J P n hP N u hu hu' c x hx hxP a W hW,
        finsum_eq_sum_of_support_subset _ (s := hZ.toFinset), Finset.sum_filter]
      · refine Finset.sum_congr rfl fun W' _ => ?_
        by_cases h1 : W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W
        · rw [if_pos h1, if_pos h1, hg_def]
          dsimp only
          rw [if_pos ((hC W').mpr (by rw [h1]; exact hW))]
        · rw [if_neg h1, if_neg h1]
      · intro W' hW'
        refine hZ.mem_toFinset.mpr ?_
        rw [Function.mem_support] at hW' ⊢
        intro h0
        apply hW'
        simp [h0]
    · rw [if_neg hW, mul_zero]
      refine Finset.sum_eq_zero fun W' hW' => ?_
      have h1 := (Finset.mem_filter.mp hW').2
      rw [hg_def]
      dsimp only
      rw [if_neg (fun h => hW (h1 ▸ (hC W').mp h)), mul_zero]
  unfold cycEval
  calc (∑ᶠ W', divCycle (blowUpOf P u) (liftForm x) W' *
          (if (C ϖ : MRing (extIdx ι J) O) ∈ W' then vNum W' (liftDegs a) else 0))
      = ∑ W' ∈ hZ.toFinset, g W' := finsum_eq_sum_of_support_subset g hg
    _ = ∑ᶠ W, ∑ W' ∈ hZ.toFinset with W'.comap (liftForm (ι := ι) (J := J) (R := O)) = W, g W' :=
        (finsum_sum_filter _ _ _).symm
    _ = _ := finsum_congr key

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagBundleLineBase
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace FlagBundleLineBaseProof

theorem intNum_eq_intNumL {K : Type*} [DecidableEq K] {ι : K → Type*} (F : Type*) [Field F]
    (P : Ideal (MRing ι F)) {n : ℕ} (bs : Fin n → K → ℤ) :
    intNum F P bs = intNumL F P (List.ofFn bs) := by
  unfold intNumL intNum mixedDiff
  rw [List.ofFn_get]

theorem pullDeg_some {K : Type*} (c : K → ℤ) :
    FieldNumbers.pullDeg (Function.Embedding.some : K ↪ Option K) c = liftDeg c := by
  funext o
  cases o with
  | none =>
    simp only [FieldNumbers.pullDeg, liftDeg, Option.elim]
    rw [Function.extend_apply']
    · rfl
    · rintro ⟨k, hk⟩
      exact Option.some_ne_none k hk
  | some k =>
    simp only [FieldNumbers.pullDeg, liftDeg, Option.elim]
    exact (Option.some_injective K).extend_apply c 0 k

theorem relDim_of_krull {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} (F : Type)
    [Field F] (I : Ideal (MRing ι F)) (e : ℕ)
    (h : ringKrullDim (MRing ι F ⧸ I) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    FieldNumbers.relDim I = ((e : ℕ) : WithBot (WithTop ℤ)) := by
  exact (FieldNumbers.CutRegular.relDim_eq_natCast_iff I e).2 h

theorem contractPrime_projIdeal {K : Type} {ι : K → Type} {Ω : Type} [Field Ω] {N M : ℕ}
    {E : Type} [AddCommGroup E] [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ] (F : Type)
    [Field F] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) :
    FieldNumbers.contractPrime (Function.Embedding.some : K ↪ Option K) (projIdeal F y w φ t) =
      pointIdeal (ι := fun k => bundleIdx ι M ((Function.Embedding.some : K ↪ Option K) k)) F y := by
  let ψ : MvPolynomial K Ω →+* MvPolynomial (Option K) Φ :=
    (rename (Option.some : K → Option K)).toRingHom.comp (MvPolynomial.map (algebraMap Ω Φ))
  have hψ : Function.Injective ψ :=
    (rename_injective _ (Option.some_injective K)).comp
      (MvPolynomial.map_injective _ (algebraMap Ω Φ).injective)
  unfold FieldNumbers.contractPrime projIdeal pointIdeal
  have hcomp : (eval₂Hom (C.comp ((algebraMap Ω Φ).comp (algebraMap F Ω)))
      (fun p => C (projCoord y w φ t p) * X p.1)).comp
      (rename (FieldNumbers.blockIncl (Function.Embedding.some : K ↪ Option K)
        (bundleIdx ι M))).toRingHom = ψ.comp (pointConeMap (ι := fun k => bundleIdx ι M ((Function.Embedding.some : K ↪ Option K) k))
        F y).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [ψ, pointConeMap, MvPolynomial.algebraMap_eq]
    · rintro ⟨k, i⟩
      simp [ψ, pointConeMap, FieldNumbers.blockIncl, projCoord]
      rfl
  exact (RingHom.comap_ker _ _).trans
    ((congrArg RingHom.ker hcomp).trans (RingHom.ker_comp_of_injective _ hψ))

theorem replace_zeta {K : Type} [Fintype K] [DecidableEq K] {ι' : Option K → Type}
    [∀ o, Fintype (ι' o)] (F : Type) [Field F] (P : Ideal (MRing ι' F)) (hP : IsMultiProjPrime P)
    (e : ℕ) (hd : FieldNumbers.relDim P = ((e : ℕ) : WithBot (WithTop ℤ))) (c : K → ℤ)
    (bf bg : Option K → ℕ) (f g : MRing ι' F) (hf : IsMultiHomog f bf) (hg : IsMultiHomog g bg)
    (hfP : f ∉ P) (hgP : g ∉ P) (hfg : (fun o => (bf o : ℤ) - bg o) = zetaDeg - liftDeg c)
    (hdiv : ratDiv P f g = 0) :
    ∀ (n : ℕ) (Y : List (K → ℤ)), n + Y.length = e →
      intNumL F P (List.replicate n zetaDeg ++ Y.map liftDeg) =
        intNumL F P ((List.replicate n c ++ Y).map liftDeg) := by
  intro n
  induction n with
  | zero => intro Y _; simp
  | succ m ih =>
    intro Y hY
    set l := List.replicate m (zetaDeg : Option K → ℤ) ++ Y.map liftDeg with hl
    have hlen : l.length + 1 = e := by simp [hl]; omega
    have hdl : FieldNumbers.relDim P = ((l.length + 1 : ℕ) : WithBot (WithTop ℤ)) := by
      rw [hlen]; exact hd
    have hsplit : (zetaDeg : Option K → ℤ) = liftDeg c + (zetaDeg - liftDeg c) := by abel
    rw [List.replicate_succ, List.cons_append, ← hl, hsplit,
      NumericalSegreProof.intNumL_cons_add FieldNumbers.IntNumAdd.full F P hP l hdl]
    have hzero : intNumL F P ((zetaDeg - liftDeg c) :: l) = 0 := by
      rw [NumericalSegreProof.intNumL_perm F P (List.perm_append_singleton _ _).symm]
      have hcut := FieldNumbers.CutRational.full F (Option K) ι' P hP l.length hdl bf bg f g hf hg
        hfP hgP l.get
      rw [hfg, hdiv, intNum_eq_intNumL, List.ofFn_succ', List.concat_eq_append] at hcut
      simp only [Fin.snoc_castSucc, Fin.snoc_last, List.ofFn_get] at hcut
      rw [hcut]
      simp [cycEval]
    rw [hzero, add_zero]
    have hperm : (liftDeg c :: l).Perm
        (List.replicate m zetaDeg ++ (c :: Y).map liftDeg) := by
      rw [hl, List.map_cons]
      exact List.perm_middle.symm
    rw [NumericalSegreProof.intNumL_perm F P hperm, ih (c :: Y) (by simp; omega)]
    congr 1
    rw [List.replicate_succ', List.append_assoc, List.singleton_append]

end FlagBundleLineBaseProof


open FlagBundleLineBaseProof in
theorem FlagBundleLineBase.proof (hdim : FlagBundleDim.Statement)
    (hsec : FlagLineSection.Statement) (hdeg : FlagLineDegree.Statement)
    (hpf : FieldNumbers.ProjectionFormulaDegree.Statement.{0}) :
    FlagBundleLineBase.Statement := by
  intro F _ Ω _ _ K _ _ ι _ y e hV hdimV N E _ _ B w b hflag M a φ hφ Φ _ _ t ht h0 n Y hnY
  obtain ⟨hP, hPd⟩ := hdim F Ω K ι y e hV hdimV N E B w b hflag M a φ hφ Φ t ht 1 le_rfl h0
  rw [show e + 1 - 1 = e by omega] at hPd
  obtain ⟨bf, bg, f, g, hf, hg, hfP, hgP, hfg, hdiv⟩ :=
    hsec F Ω K ι y e hV hdimV N E B w b hflag M a φ hφ Φ t ht h0
  rw [replace_zeta F _ hP e hPd (a - b ⟨0, h0⟩) bf bg f g hf hg hfP hgP hfg hdiv n Y hnY]
  set L := List.replicate n (a - b ⟨0, h0⟩) ++ Y with hL
  have hLlen : L.length = e := by simp [hL]; omega
  have hcon := contractPrime_projIdeal (K := K) F y w φ (truncCoord t 1)
  have hcd : FieldNumbers.relDim (FieldNumbers.contractPrime (Function.Embedding.some : K ↪ Option K)
      (projIdeal F y w φ (truncCoord t 1))) = ((L.length : ℕ) : WithBot (WithTop ℤ)) := by
    rw [hLlen]
    exact (congrArg FieldNumbers.relDim hcon).trans (relDim_of_krull F (pointIdeal F y) e hdimV)
  have hPd' : FieldNumbers.relDim (projIdeal F y w φ (truncCoord t 1)) =
      ((L.length : ℕ) : WithBot (WithTop ℤ)) := by
    rw [hLlen]; exact hPd
  have h := (hpf F K (Option K) Function.Embedding.some (bundleIdx ι M) _ hP L.length hPd' hcd
    L.get).2
  have h2 : intNum F (FieldNumbers.contractPrime (Function.Embedding.some : K ↪ Option K)
      (projIdeal F y w φ (truncCoord t 1))) L.get = intNum F (pointIdeal F y) L.get :=
    congrArg (fun I => intNum F I L.get) hcon
  rw [hdeg F Ω K ι y e hV hdimV N E B w b hflag M a φ hφ Φ t ht h0, Nat.cast_one, one_mul,
    h2] at h
  simp only [pullDeg_some] at h
  rw [intNum_eq_intNumL, intNum_eq_intNumL, List.ofFn_get] at h
  have hmap : List.ofFn (fun i => liftDeg (L.get i)) = L.map liftDeg := by
    apply List.ext_get <;> simp
  rw [hmap] at h
  exact h

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagBundleSectionDiv
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace FlagBundleSectionDivProof

theorem eq_of_lt_of_le_of_mem_minimalPrimes {A : Type*} [CommRing A] [IsNoetherianRing A]
    {P Q W : Ideal A} [P.IsPrime] [Q.IsPrime] {x : A}
    (hW : W ∈ (P ⊔ Ideal.span {x}).minimalPrimes) (hPQ : P < Q) (hQW : Q ≤ W) : Q = W := by
  by_contra hne
  have hQW' : Q < W := lt_of_le_of_ne hQW hne
  have : W.IsPrime := hW.1.1
  let f := Ideal.Quotient.mk P
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective
  have hPW : P ≤ W := hPQ.le.trans hQW
  have hker : RingHom.ker f = P := Ideal.mk_ker
  have : (W.map f).IsPrime := Ideal.map_isPrime_of_surjective hf (by rw [hker]; exact hPW)
  have : (Q.map f).IsPrime := Ideal.map_isPrime_of_surjective hf (by rw [hker]; exact hPQ.le)
  have h1 : (W.map f).height ≤ 1 := Ideal.map_height_le_one_of_mem_minimalPrimes hW
  have hlt : Q.map f < W.map f := by
    refine (Ideal.map_mono hQW).lt_of_not_ge fun e => hQW'.not_ge ?_
    have := Ideal.comap_mono (f := f) e
    rwa [Ideal.comap_map_of_surjective f hf, Ideal.comap_map_of_surjective f hf,
      ← RingHom.ker_eq_comap_bot, hker, sup_eq_left.mpr hPW, sup_eq_left.mpr hPQ.le] at this
  have : (W.map f).FiniteHeight := ⟨Or.inr (h1.trans_lt (WithTop.coe_lt_top 1)).ne⟩
  have h2 := (Ideal.height_strict_mono_of_isPrime_of_isPrime hlt).trans_le h1
  rw [Order.lt_one_iff, Ideal.height_eq_zero_iff_eq_bot] at h2
  refine hPQ.not_ge fun q hq => ?_
  have h3 : f q ∈ Q.map f := Ideal.mem_map_of_mem f hq
  rw [h2, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at h3
  exact h3

theorem divCycle_eq_zero_of_not_mem {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
    {P W : Ideal (MRing ι R)} {x : MRing ι R} (hx : x ∉ W) : divCycle P x W = 0 := by
  unfold divCycle
  rw [dite_eq_right]
  rintro ⟨h, -⟩
  exact hx (h.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x)))

theorem divCycle_congr {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
    {P : Ideal (MRing ι R)} {x x' : MRing ι R} (h : x - x' ∈ P) : divCycle P x = divCycle P x' := by
  have hJ : P ⊔ Ideal.span {x} = P ⊔ Ideal.span {x'} := by
    apply le_antisymm
    · refine sup_le le_sup_left ?_
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
      have := Ideal.add_mem _ (Ideal.mem_sup_left h : x - x' ∈ P ⊔ Ideal.span {x'})
        (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x') : x' ∈ P ⊔ Ideal.span {x'})
      rwa [sub_add_cancel] at this
    · refine sup_le le_sup_left ?_
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
      have := Ideal.sub_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x) : x ∈ P ⊔ Ideal.span {x})
        (Ideal.mem_sup_left h : x - x' ∈ P ⊔ Ideal.span {x})
      rwa [sub_sub_cancel] at this
  funext W
  unfold divCycle
  split_ifs with h1 h2 h2
  · simp only [hJ]
  · exact absurd (hJ ▸ h1) h2
  · exact absurd (hJ.symm ▸ h2) h1
  · rfl

end FlagBundleSectionDivProof


open FlagBundleSectionDivProof in
theorem FlagBundleSectionDiv.proof (hDim : FlagBundleDim.Statement)
    (hSat : MultAtOfSaturated.Statement.{0}) (hForm : ProjIdealFormValue.Statement)
    (hTrunc : TruncSpecialize.Statement) (hChart : FlagBundleChartSection.Statement) :
    FlagBundleSectionDiv.Statement := by
  intro F _ Ω _ _ K _ _ ι _ y e hV hdim N E _ _ B w b hB M a φ hφ Φ _ _ t ht i hi bf bg f g hf hg
    hdeg hgP hval W
  classical
  have hQ : IsMultiProjPrime (projIdeal F y w φ (truncCoord t i)) :=
    (hDim F Ω K ι y e hV hdim N E B w b hB M a φ hφ Φ t ht i hi i.2.le).1
  have hP : IsMultiProjPrime (projIdeal F y w φ (truncCoord t ((i : ℕ) + 1))) :=
    (hDim F Ω K ι y e hV hdim N E B w b hB M a φ hφ Φ t ht ((i : ℕ) + 1) (by omega) i.2).1
  have := hP.isPrime
  have := hQ.isPrime
  obtain ⟨hPQ, hspec⟩ := hTrunc F Ω K ι y N E w M φ Φ t ht i
  have hti : t i ≠ 0 := ht.ne_zero i
  have hval0 := fun (d : Option K → ℕ) (x : MRing (bundleIdx ι M) F) (hx : IsMultiHomog x d) =>
    hForm F Ω K ι y N E w M φ Φ (truncCoord t ((i : ℕ) + 1)) d x hx
  have hgv := fun h => hgP ((hval0 _ _ hg).mpr h)
  have hfP : f ∉ projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) := fun h =>
    mul_ne_zero hti hgv (hval ▸ (hval0 _ _ hf).mp h)
  by_cases hW : W.IsPrime ∧ IsRelevant W ∧ projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) ≤ W
  · obtain ⟨hWp, hWrel, hPW⟩ := hW
    choose c hc using fun k => hWrel (some k)
    have hy : segreVec y c ≠ 0 := by
      unfold segreVec
      rw [Finset.prod_ne_zero_iff]
      intro k _ hk
      apply hc k (hPW ?_)
      rw [hval0 _ _ (isWeightedHomogeneous_X F _ _), eval₂_X]
      simp [projCoord, hk]
    obtain ⟨dl, dm, l, μ, m, hμ, hl, hμh, hdl, hlv, hsat⟩ :=
      hChart F Ω K ι y N E B w b hB M a φ hφ Φ t ht i c hy
    have hsW : ∀ n : ℕ, (∏ k, (X ⟨some k, c k⟩ : MRing (bundleIdx ι M) F)) ^ n ∉ W := by
      intro n h
      obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hWp)).mp (hWp.mem_of_pow_mem n h)
      exact hc k hk
    have hμW : μ ∉ W := by
      rw [hμ]
      intro h
      obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hWp)).mp h
      exact hc k (hWp.mem_of_pow_mem _ hk)
    have hμP : μ ∉ projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) := fun h => hμW (hPW h)
    have hμv := fun h => hμP ((hval0 _ _ hμh).mpr h)
    have hlP : l ∉ projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) := fun h =>
      mul_ne_zero hti hμv (hlv ▸ (hval0 _ _ hl).mp h)
    have hdeg' : bf + dm = dl + bg := by
      funext o
      have h1 := congrFun hdeg o
      have h2 := congrFun hdl o
      simp only [Pi.add_apply] at h1 h2 ⊢
      omega
    have hdiff : f * μ - l * g ∈ projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) := by
      have h2 := hl.mul hg
      rw [← hdeg'] at h2
      have h1 : IsMultiHomog (f * μ - l * g) (bf + dm) :=
        (mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.sub_mem _
          ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr (hf.mul hμh))
          ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr h2))
      rw [hval0 _ _ h1, eval₂_sub, eval₂_mul, eval₂_mul, hval, hlv]
      ring
    have hrat : ratDiv (projIdeal F y w φ (truncCoord t ((i : ℕ) + 1))) f g W =
        divCycle (projIdeal F y w φ (truncCoord t ((i : ℕ) + 1))) l W := by
      have h1 := congrFun (divCycle_congr hdiff) W
      rw [DivCycleMul.proof.{0} F (Option K) (bundleIdx ι M) _ f μ hP.isPrime hfP hμP,
        DivCycleMul.proof.{0} F (Option K) (bundleIdx ι M) _ l g hP.isPrime hlP hgP] at h1
      simp only [Pi.add_apply, divCycle_eq_zero_of_not_mem hμW] at h1
      unfold ratDiv
      omega
    rw [hrat]
    have hlQ : l ∈ projIdeal F y w φ (truncCoord t i) :=
      (hForm F Ω K ι y N E w M φ Φ (truncCoord t i) dl l hl).mpr (hspec l μ hlv)
    split_ifs with hWQ
    · subst hWQ
      obtain ⟨hmin, hmult⟩ := hSat F (Option K) (bundleIdx ι M) _ _
        (sup_le hPQ ((Ideal.span_singleton_le_iff_mem _).mpr hlQ))
        (fun q hq => by
          obtain ⟨n, hn⟩ := hsat q hq
          exact ⟨_, hsW n, hn⟩)
      unfold divCycle
      rw [dite_eq_left ⟨hmin, hQ.relevant⟩, hmult]
      rfl
    · by_contra hne
      have hmin : W ∈ (projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) ⊔ Ideal.span {l}).minimalPrimes := by
        unfold divCycle at hne
        split_ifs at hne with h
        · exact h.1
        · exact absurd rfl hne
      have hQW : projIdeal F y w φ (truncCoord t i) ≤ W := fun q hq => by
        obtain ⟨n, hn⟩ := hsat q hq
        exact (hWp.mem_or_mem (hmin.1.2 hn)).resolve_left (hsW n)
      have hPQ' : projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) < projIdeal F y w φ (truncCoord t i) :=
        lt_of_le_of_ne hPQ (fun h => hlP (by rw [h]; exact hlQ))
      exact hWQ (eq_of_lt_of_le_of_mem_minimalPrimes hmin hPQ' hQW).symm
  · have h0 : ∀ x, divCycle (projIdeal F y w φ (truncCoord t ((i : ℕ) + 1))) x W = 0 := fun x => by
      unfold divCycle
      rw [dite_eq_right]
      rintro ⟨h, hr⟩
      exact hW ⟨h.1.1, hr, le_sup_left.trans h.1.2⟩
    have hWQ : W ≠ projIdeal F y w φ (truncCoord t i) := by
      rintro rfl
      exact hW ⟨hQ.isPrime, hQ.relevant, hPQ⟩
    simp [ratDiv, h0, hWQ]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PHsymmPairFlagIndependence
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

theorem HsymmPairFlagIndependence.proof (hExp : PairNumberExpansionIndependence.Statement)
    (hClos : GenericProjClosureModel.Statement) (hSeg : SegreClosureNumber.Statement) :
    HsymmPairFlagIndependence.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hBB' w w' v v' x x' u u' f g f₂ g₂
    hF1 hF2 n z z' fz gz hz a r R hR As Bs hAs hBs Q hQ
  classical
  have hA : (hsymmTimes N n a R).IsHomogeneous (a + r) :=
    (isHomogeneous_hsymm N a).rename_isHomogeneous.mul hR.rename_isHomogeneous
  rcases Nat.eq_zero_or_pos N with rfl | hN
  ·
    obtain rfl : x = u := funext fun i => i.elim0
    obtain rfl : x' = u' := funext fun i => i.elim0
    obtain rfl : f = f₂ := funext fun i => i.elim0
    obtain rfl : g = g₂ := funext fun i => i.elim0
    refine hExp O ϖ hϖ K ι (pointIdeal O y) d hV (0 + n) _ _ _ _ (fun i => ?_) (a + r) _ hA As Bs
      hAs hBs Q hQ
    refine Fin.addCases (fun i => i.elim0) (fun j => ?_) i
    simp only [Fin.append_right]
    exact hz j
  ·
    let Φ := FractionRing (MvPolynomial (Fin N) Ω)
    let t : Fin N → Φ := fun i => algebraMap (MvPolynomial (Fin N) Ω) Φ (X i)
    have ht : AlgebraicIndependent Ω t :=
      (MvPolynomial.algebraicIndependent_X (Fin N) Ω).map'
        (f := IsScalarTower.toAlgHom Ω (MvPolynomial (Fin N) Ω) Φ)
        (IsFractionRing.injective (MvPolynomial (Fin N) Ω) Φ)
    obtain ⟨M, M', a₀, a₀', φ, φ', hφ, hφ', hZ, f₀, g₀, hD₀, hD₀gen⟩ :=
      hClos O ϖ hϖ Ω K ι y d hV N hN E B B' hBB' Φ w t ht
    have hC : (zetaPowTimes n (N - 1 + a) R).IsHomogeneous (N - 1 + a + r) := by
      have h := ((isHomogeneous_X ℤ (Fin.castAdd n (0 : Fin 1))).pow (N - 1 + a)).mul
        (hR.rename_isHomogeneous (f := (Fin.natAdd 1 : Fin n → Fin (1 + n))))
      rwa [one_mul] at h
    obtain ⟨Cs, hCs⟩ := exists_isPairExpansion hC
    rw [hSeg O ϖ hϖ Ω K ι y d hV N hN E B B' hBB' w w' x x' f g hF1 M M' a₀ a₀' φ φ' hφ hφ' Φ w t ht
        hZ f₀ g₀ hD₀ hD₀gen n z z' fz gz hz a r R hR As hAs Cs hCs Q hQ,
      hSeg O ϖ hϖ Ω K ι y d hV N hN E B B' hBB' v v' u u' f₂ g₂ hF2 M M' a₀ a₀' φ φ' hφ hφ' Φ w t ht
        hZ f₀ g₀ hD₀ hD₀gen n z z' fz gz hz a r R hR Bs hBs Cs hCs Q hQ]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsTwistedDualGensExist
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def TwistedDualGensExist.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsNoetherianRing O] (Ω : Type) [Field Ω] [Algebra O Ω]
    (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω)
    (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E] (B : ChartBundle O (segreVec y) N E),
    ∃ a₁ : K → ℤ, ∀ a : K → ℤ, a₁ ≤ a →
      ∃ (M : ℕ) (φ : Fin M → Module.Dual Ω E), IsTwistedDualGens y B a φ

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

