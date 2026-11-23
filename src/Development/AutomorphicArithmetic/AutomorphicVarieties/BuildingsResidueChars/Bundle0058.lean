module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0195
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0187
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsConj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0690
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0762

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SolvableCmExtensionTower
section
open NumberField UpperTheory.V.Af.Sol

private theorem exists_proper_nontrivial_normal_of_solvable_not_prime_card (G : Type) [Group G] [Finite G] (hs : IsSolvable G)
    (h1 : Nat.card G ≠ 1) (hp : ¬ (Nat.card G).Prime) :
    ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ := by
  by_contra hne
  push_neg at hne
  have hlt : 1 < Nat.card G := by
    have := Nat.card_pos (α := G)
    omega
  haveI : Nontrivial G := Finite.one_lt_card_iff_nontrivial.1 hlt
  haveI : IsSimpleGroup G :=
    { eq_bot_or_eq_top_of_normal := fun N hN => by
        by_cases h : N = ⊥
        · exact Or.inl h
        · exact Or.inr (hne N hN h) }
  have hc := (IsSimpleGroup.comm_iff_isSolvable (G := G)).2 hs
  letI : CommGroup G := { ‹Group G› with mul_comm := hc }
  exact hp (CommGroup.is_simple_iff_prime_card.1 ‹IsSimpleGroup G›)

private theorem rc_of_intermediateField_stable_under_complexConj {F M : Type} [Field F] [NumberField F] [Field M] [NumberField M] [Algebra F M]
    [IsCMField M] (K : IntermediateField F M)
    (hK : ∀ x ∈ K, IsCMField.complexConj M x ∈ K) : RC K := by
  have hext : ∀ φ : K →+* ℂ, ∃ Φ : M →+* ℂ, ∀ x : K, Φ x = φ x := by
    intro φ
    letI : Algebra K ℂ := φ.toAlgebra
    refine ⟨(IsAlgClosed.lift : M →ₐ[K] ℂ).toRingHom, fun x => ?_⟩
    exact (IsAlgClosed.lift : M →ₐ[K] ℂ).commutes x
  let τ : K ≃+* K :=
    { toFun := fun x => ⟨IsCMField.complexConj M x, hK x x.2⟩
      invFun := fun x => ⟨IsCMField.complexConj M x, hK x x.2⟩
      left_inv := fun x => Subtype.ext (IsCMField.complexConj_apply_apply M x)
      right_inv := fun x => Subtype.ext (IsCMField.complexConj_apply_apply M x)
      map_mul' := fun x y => Subtype.ext (by simp [map_mul])
      map_add' := fun x y => Subtype.ext (by simp [map_add (f := _)]) }
  let σ : Gal(K/ℚ) := τ.toRatAlgEquiv
  have hσ : ∀ x : K, ((σ x : K) : M) = IsCMField.complexConj M x := fun x => rfl
  have hconj : ∀ φ : K →+* ℂ, ComplexEmbedding.IsConj φ σ := by
    intro φ
    obtain ⟨Φ, hΦ⟩ := hext φ
    unfold ComplexEmbedding.IsConj
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply, ← hΦ]
    show _ = φ (σ x)
    rw [← hΦ, hσ, IsCMField.complexEmbedding_complexConj]
  by_cases h1 : σ = 1
  · left
    refine ⟨fun w => ?_⟩
    rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    have := hconj w.embedding
    rw [h1] at this
    unfold ComplexEmbedding.IsConj at this
    rw [this]
    rfl
  · right
    haveI : IsTotallyComplex K :=
      ⟨fun w => InfinitePlace.isComplex_iff.2 ((ComplexEmbedding.isConj_ne_one_iff (hconj _)).1 h1)⟩
    obtain ⟨φ0⟩ : Nonempty (K →+* ℂ) := inferInstance
    have hord : Nat.card (Subgroup.zpowers σ) = 2 := by
      rw [Nat.card_zpowers]
      exact ComplexEmbedding.orderOf_isConj_two_of_ne_one (hconj φ0) h1
    haveI : Finite (Subgroup.zpowers σ) := Nat.finite_of_card_ne_zero (by rw [hord]; norm_num)
    haveI : Fintype (Subgroup.zpowers σ) := Fintype.ofFinite _
    let L : IntermediateField ℚ K := FixedPoints.intermediateField (Subgroup.zpowers σ)
    have hfix : ∀ x : L, σ (x : K) = x := fun x => x.2 ⟨σ, Subgroup.mem_zpowers σ⟩
    haveI : IsTotallyReal L := ⟨fun w => by
      obtain ⟨W, rfl⟩ := w.comap_surjective (K := K)
      dsimp only
      rw [← InfinitePlace.mk_embedding W, InfinitePlace.comap_mk, InfinitePlace.isReal_mk_iff,
        ComplexEmbedding.isReal_iff]
      ext x
      have h := RingHom.congr_fun (hconj W.embedding) (x : K)
      rw [ComplexEmbedding.conjugate_coe_eq] at h ⊢
      simp only [RingHom.comp_apply] at h ⊢
      rw [show algebraMap L K x = (x : K) from rfl, h]
      exact congrArg W.embedding (hfix x)⟩
    haveI : Algebra.IsQuadraticExtension L K :=
      ⟨by
        rw [Nat.card_eq_fintype_card] at hord
        rw [← hord]
        exact FixedPoints.finrank_eq_card (Subgroup.zpowers σ) K⟩
    exact IsCMField.ofCMExtension L K

theorem UpperTheory.solvable_cm_extension_tower :
    UpperTheory.V.Af.Sol.Tower := by
  intro F M _ _ _ _ _ _ hs hF hM h1 hp
  obtain ⟨N, hN, hbot, htop⟩ := exists_proper_nontrivial_normal_of_solvable_not_prime_card Gal(M/F) hs
    (by rwa [IsGalois.card_aut_eq_finrank]) (by rwa [IsGalois.card_aut_eq_finrank])
  refine ⟨IntermediateField.fixedField N, ?_, ?_, IsGalois.of_fixedField_normal_subgroup N, ?_⟩
  · intro h
    apply htop
    rw [← IntermediateField.fixingSubgroup_fixedField N, h, IntermediateField.fixingSubgroup_bot]
  · intro h
    apply hbot
    rw [← IntermediateField.fixingSubgroup_fixedField N, h, IntermediateField.fixingSubgroup_top]
  · rcases hM with hM | hM
    · left
      exact IsTotallyReal.of_algebra (IntermediateField.fixedField N) M
    · apply rc_of_intermediateField_stable_under_complexConj
      intro x hx
      rw [IntermediateField.mem_fixedField_iff] at hx ⊢
      intro n hn
      obtain ⟨Φ⟩ : Nonempty (M →+* ℂ) := inferInstance
      apply Φ.injective
      have h2 := IsCMField.complexEmbedding_complexConj M (Φ.comp n.toRingHom) x
      change Φ (n (IsCMField.complexConj M x)) = (starRingEnd ℂ) (Φ (n x)) at h2
      rw [h2, hx n hn, IsCMField.complexEmbedding_complexConj]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SpehParameterStrings
section
open UpperTheory.V.Af UpperTheory.V.Af.Gu
open GlobalTheory.DefiniteBC

private theorem spehInf_eq_sum_shifted_map (d : ℕ) (m : Multiset ℂ) :
    spehInf d m = ∑ k : Fin d, Multiset.map (fun x => x + (((d:ℂ) - 1) / 2 - ((k:ℕ):ℂ))) m := by
  unfold spehInf
  rw [Fin.sum_univ_eq_sum_range (fun k => Multiset.map (fun x => x + (((d:ℂ) - 1) / 2 - (k:ℂ))) m) d]
  rw [Finset.sum_eq_multiset_sum, Finset.range_val, Multiset.range, Multiset.map_coe, Multiset.sum_coe]

private theorem infOfWeight_nodup' (n : ℕ) (lam : Formalism.BasicNotions.DomWeight n) :
    (GlobalTheory.UnitaryBC.infOfWeight lam).Nodup := by
  unfold GlobalTheory.UnitaryBC.infOfWeight
  refine Multiset.Nodup.map ?_ Finset.univ.nodup
  intro a b h
  have h2 : ((lam.w a - (a:ℕ) : ℤ) : ℂ) = ((lam.w b - (b:ℕ) : ℤ) : ℂ) := by
    push_cast
    linear_combination h
  have h3 : lam.w a - (a:ℕ) = lam.w b - (b:ℕ) := by exact_mod_cast h2
  rcases lt_trichotomy a b with hab | hab | hab
  · have := lam.anti hab.le
    have : (a:ℕ) < (b:ℕ) := hab
    omega
  · exact hab
  · have := lam.anti hab.le
    have : (b:ℕ) < (a:ℕ) := hab
    omega

private theorem multiset_map_finset_sum {ι : Type*} (s : Finset ι) (g : ℂ → ℂ) (f : ι → Multiset ℂ) :
    Multiset.map g (∑ i ∈ s, f i) = ∑ i ∈ s, Multiset.map g (f i) :=
  map_sum (Multiset.mapAddMonoidHom g) f s

theorem UpperTheory.speh_parameter_strings :
    Strings := by
  intro n c d m lam h
  have hnd := infOfWeight_nodup' n lam
  refine ⟨fun i k => ?_, ?_⟩
  · have hle1 : Multiset.map (fun x => x + (((d i:ℂ) - 1) / 2 - ((k:ℕ):ℂ))) (m i) ≤ spehInf (d i) (m i) := by
      rw [spehInf_eq_sum_shifted_map]
      exact Finset.single_le_sum (f := fun k : Fin (d i) => Multiset.map (fun x => x + (((d i:ℂ) - 1) / 2 - ((k:ℕ):ℂ))) (m i))
        (fun _ _ => Multiset.zero_le _) (Finset.mem_univ k)
    have hle2 : spehInf (d i) (m i) ≤ ∑ j, spehInf (d j) (m j) :=
      Finset.single_le_sum (f := fun j => spehInf (d j) (m j)) (fun _ _ => Multiset.zero_le _) (Finset.mem_univ i)
    have hle : Multiset.map (fun x => x + (((d i:ℂ) - 1) / 2 - ((k:ℕ):ℂ))) (m i) ≤ GlobalTheory.UnitaryBC.infOfWeight lam :=
      h ▸ hle1.trans hle2
    refine ⟨(Multiset.nodup_of_le hle hnd).of_map _, fun z hz => ?_⟩
    have hmem := Multiset.mem_of_le hle (Multiset.mem_map_of_mem _ hz)
    unfold GlobalTheory.UnitaryBC.infOfWeight at hmem
    rw [Multiset.mem_map] at hmem
    obtain ⟨j, -, hj⟩ := hmem
    refine ⟨lam.w j - (j:ℕ), ?_⟩
    unfold ex
    push_cast
    linear_combination (-1 : ℂ) * hj
  · rw [← h, multiset_map_finset_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [spehInf_eq_sum_shifted_map, multiset_map_finset_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl fun z _ => ?_
    simp only [Function.comp_apply]
    unfold ex
    push_cast
    ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SumHodgeTate
section
open UpperTheory.V.Af UpperTheory.V.Af.Gu

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.Pst

private theorem map_sum' {Γ : Type} [Group Γ] {k k' : Type} [CommRing k] [CommRing k'] {a b : ℕ}
    (f : k →+* k') (r₁ : Γ →* GL (Fin a) k) (r₂ : Γ →* GL (Fin b) k) :
    mapRep f (Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂) = Formalism.MainNotions.SumRepresentations.At.sumRep (mapRep f r₁) (mapRep f r₂) := by
  ext g i j
  change f (Matrix.fromBlocks (r₁ g : Matrix (Fin a) (Fin a) k) 0 0 (r₂ g : Matrix (Fin b) (Fin b) k)
      (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)) =
    Matrix.fromBlocks (mapRep f r₁ g : Matrix (Fin a) (Fin a) k') 0 0 (mapRep f r₂ g : Matrix (Fin b) (Fin b) k')
      (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> simp [mapRep]

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {Bw : LocBridge l E Ω Gw O} {a b : ℕ}
  {r : ↥Gw →* GL (Fin a) (Om l)} {r' : ↥Gw →* GL (Fin b) (Om l)}

private theorem model_sum {L : FinExt l} {r₁ : ↥Gw →* GL (Fin a) ↥L.1} {r₂ : ↥Gw →* GL (Fin b) ↥L.1}
    (h₁ : IsModel Bw r L r₁) (h₂ : IsModel Bw r' L r₂) :
    IsModel Bw (Formalism.MainNotions.SumRepresentations.At.sumRep r r') L (Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂) :=
  ⟨h₁.1, by rw [map_sum', h₁.2, h₂.2]⟩

private theorem dR_sum (h : IsdRAt (UpperTheory.V.Loc.PP l) Bw r) (h' : IsdRAt (UpperTheory.V.Loc.PP l) Bw r') :
    IsdRAt (UpperTheory.V.Loc.PP l) Bw (Formalism.MainNotions.SumRepresentations.At.sumRep r r') := by
  obtain ⟨L₁, r₁, m₁, -⟩ := id h
  obtain ⟨L₂, r₂, m₂, -⟩ := id h'
  have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
  have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
  have n₁ := m₁.enlarge l₁
  have n₂ := m₂.enlarge l₂
  exact ⟨_, _, model_sum n₁ n₂, (_root_.GlobalTheory.DirectSumLocal.isdRE_sumRep_and_multE_add l _ _ (UpperTheory.V.Loc.tiedP l) E Ω Gw O Bw _ a b _ _).1.2
    ⟨(n₁.isdRAt_iff _).1 h, (n₂.isdRAt_iff _).1 h'⟩⟩

private theorem jumps_sum {τ : E →+* Om l} {J J' : Multiset ℤ}
    (h : IsJumpsAt (UpperTheory.V.Loc.PP l) Bw r τ J) (h' : IsJumpsAt (UpperTheory.V.Loc.PP l) Bw r' τ J') :
    IsJumpsAt (UpperTheory.V.Loc.PP l) Bw (Formalism.MainNotions.SumRepresentations.At.sumRep r r') τ (J + J') := by
  obtain ⟨L₁, r₁, m₁, d₁, τ₁, t₁, -⟩ := id h
  obtain ⟨L₂, r₂, m₂, d₂, -⟩ := id h'
  have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
  have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
  have n₁ := m₁.enlarge l₁
  have n₂ := m₂.enlarge l₂
  have t : IsInduced Bw τ (LL' := supExt L₁ L₂) ((IntermediateField.inclusion l₁).comp τ₁) := t₁
  have S := _root_.GlobalTheory.DirectSumLocal.isdRE_sumRep_and_multE_add l _ _ (UpperTheory.V.Loc.tiedP l) E Ω Gw O Bw _ a b
    (mapRep (IntermediateField.inclusion l₁).toRingHom r₁) (mapRep (IntermediateField.inclusion l₂).toRingHom r₂)
  refine ⟨_, _, model_sum n₁ n₂, S.1.2 ⟨(n₁.isdRAt_iff _).1 ⟨_, _, m₁, d₁⟩, (n₂.isdRAt_iff _).1 ⟨_, _, m₂, d₂⟩⟩,
    _, t, fun c => ?_⟩
  rw [S.2, ← h.count_eq _ n₁ t, ← h'.count_eq _ n₂ t, Multiset.count_add, Nat.cast_add]

end

theorem UpperTheory.sum_hodge_tate :
    SumHT := by
  intro E Ω _ _ _ _ _ l _ a b r r' _ _ HT HT' H H' w A hA O _ _ _ Bw hj
  obtain ⟨d, J⟩ := H w A hA O Bw hj
  obtain ⟨d', J'⟩ := H' w A hA O Bw hj
  have e : (Formalism.MainNotions.SumRepresentations.At.sumRep r r').comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype =
      Formalism.MainNotions.SumRepresentations.At.sumRep (r.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) (r'.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) := by
    ext g i j
    rfl
  rw [e]
  exact ⟨dR_sum d d', fun τ L τ' t => jumps_sum (J τ L τ' t) (J' τ L τ' t)⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SumTwoOfHodgeTate
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Gu
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.sum_two_of_hodge_tate :
    HypothesesH → SumAway → SumHT → SumTwo := by
  intro H hA hT E Ω _ _ _ _ _ l _ ι a b r r' p p' HT HT' C C'
  obtain ⟨T⟩ := Loc.tiedP l
  have hv := GlobalTheory.BCGal.cont_sumRep r r' (Units.continuous_val.comp C.cont) (Units.continuous_val.comp C'.cont)
  have hc : Continuous (Formalism.MainNotions.SumRepresentations.At.sumRep r r') := by
    refine Units.continuous_iff.2 ⟨hv, ?_⟩
    simp only [← map_inv]
    exact hv.comp continuous_inv
  have hht := hT E Ω l a b r r' C.cont C'.cont HT HT' C.ht C'.ht
  refine ⟨hc, GlobalTheory.BCGal.ss_sumRep r r' C.ss C'.ss, hht, fun w A h rc hrc => ?_⟩
  obtain ⟨a1, b1⟩ := C.par w A h rc hrc
  obtain ⟨a2, b2⟩ := C'.par w A h rc hrc
  refine ⟨fun hw => hA E Ω l ι a b r r' C.cont C'.cont w hw A h _ _ (a1 hw) (a2 hw), fun O _ _ _ Bw hj => ?_⟩
  obtain ⟨p1, e1⟩ := b1 O Bw hj
  obtain ⟨p2, e2⟩ := b2 O Bw hj
  have p3 : IsPstAt (Loc.PP l) Bw ((Formalism.MainNotions.SumRepresentations.At.sumRep r r').comp (Dec (F := E) A).subtype) := by
    refine H.litN.aut.berger.isPstAt T Bw _ (Units.continuous_val.comp (hc.comp continuous_subtype_val)) ?_
    exact (hht w A h O Bw hj).1
  refine ⟨p3, ?_⟩
  have e : (Formalism.MainNotions.SumRepresentations.At.sumRep r r').comp (Dec (F := E) A).subtype =
      Formalism.MainNotions.SumRepresentations.At.sumRep (r.comp (Dec (F := E) A).subtype) (r'.comp (Dec (F := E) A).subtype) := by
    ext g i j
    rfl
  rw [e] at p3 ⊢
  rw [GlobalTheory.T.weilDeligneParamAboveL_directSum_potSemistable l _ _ ⟨T⟩ ι E Ω A w O Bw h hj a b _ _ p1 p2 p3]
  exact (Lev.ssCalc E Ω A w h).2.1 _ _ _ _ e1 e2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ThetaCharEqSelfOfConjugateDual
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.W (Plc)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem conjSrc_eq {E : Type} [Field E] [NumberField E] (τ : E ≃+* E) (w : HeightOneSpectrum (𝓞 E)) :
    conjSrc τ w = preplace τ w :=
  HeightOneSpectrum.ext ((GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc _ w))

private theorem normV_preplace {K : Type} [Field K] [NumberField K] (τ : K ≃+* K) (v : HeightOneSpectrum (𝓞 K)) :
    normV (preplace τ v) = normV v := by
  show Nat.card (𝓞 K ⧸ (preplace τ v).asIdeal) = Nat.card (𝓞 K ⧸ v.asIdeal)
  refine Nat.card_congr (Ideal.quotientEquiv _ _ (RingOfIntegers.mapRingEquiv τ) ?_).toEquiv
  exact (Ideal.map_comap_of_surjective (RingOfIntegers.mapRingEquiv τ : 𝓞 K →+* 𝓞 K)
    (RingOfIntegers.mapRingEquiv τ).surjective v.asIdeal).symm

private theorem isFrob_conjGal {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] {τ : K ≃+* K} {σ : Ω ≃+* Ω}
    (h : IsLift τ σ) {A A' : ValuationSubring Ω} (hA : ∀ x, σ x ∈ A' ↔ x ∈ A) {q : ℕ} {g : G K Ω}
    (hg : IsFrob (F := K) A' q g) : IsFrob (F := K) A q (conjGal h g) := by
  refine ⟨conjGal_mem_Dec h hA hg.1, fun x hx => ?_⟩
  rw [← val_lt_one hA, map_sub, apply_conjGal, map_pow]
  exact hg.2 _ ((A'.valuation_le_one_iff _).2 ((hA x).2 ((A.valuation_le_one_iff _).1 hx)))

private theorem isLift_conj {F Ω : Type} [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω]
    {c : G (maximalRealSubfield F) Ω} (hc : Af.IsConjEl c) :
    IsLift (IsCMField.complexConj F).toRingEquiv c.symm.toRingEquiv := by
  obtain ⟨j, hj⟩ := hc
  intro x
  refine c.symm_apply_eq.2 (j.injective ?_)
  rw [hj]
  have h := IsCMField.complexEmbedding_complexConj F (j.comp (algebraMap F Ω)) x
  exact (Complex.conj_conj _).symm.trans (congrArg (starRingEnd ℂ) h.symm)

theorem UpperTheory.thetaChar_eq_self_of_conjugate_dual :
    ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (art : Ideles E →* Gab E Ω), IsGlobalArtin art → ∀ (κ : HChar E) (m : ℕ), 0 < m → κ.OrderDvd m → ∀ β : G E Ω →* (Qbar l)ˣ, Continuous β → IsLAdicOf art ι κ 0 β → ∀ c : G (maximalRealSubfield E) Ω, Af.IsConjEl c → (∀ s s' : G E Ω, s'.restrictScalars (maximalRealSubfield E) = c * s.restrictScalars (maximalRealSubfield E) * c⁻¹ → β s' = (β s)⁻¹) → GlobalTheory.ThetaPull.thetaChar κ = κ := by
  intro E Ω _ _ _ _ _ _ l _ ι art ha κ m _ _ β _ hL c hc hβ
  have hLi := isLift_conj hc
  have hval : ∀ v, κ.UnrAt v → κ.UnrAt (conjSrc (IsCMField.complexConj E).toRingEquiv v) →
      κ.val (conjSrc (IsCMField.complexConj E).toRingEquiv v) = (κ.val v)⁻¹ := by
    intro v hv hv'
    rw [conjSrc_eq] at hv' ⊢
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
    obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_isFrob hA
    have hAA : ∀ y, c.symm.toRingEquiv y ∈ A ↔ y ∈ A.comap c.symm.toRingEquiv.toRingHom := fun _ => Iff.rfl
    have e1 := hL.frob_unr ha (Or.inr rfl) hv hA hσ
    have e2 := hL.frob_unr ha (Or.inr rfl) hv' (isPlaceOver_preplace hLi hAA hA) (σ := conjGal hLi σ)
      (by rw [normV_preplace]; exact isFrob_conjGal hLi hAA hσ)
    rw [hβ σ (conjGal hLi σ) (AlgEquiv.ext fun _ => rfl), Units.val_inv_eq_inv_val, e1, inv_inj, ← map_inv₀] at e2
    exact Units.ext (by rw [Units.val_inv_eq_inv_val]; exact (ι.symm.injective e2).symm)
  have hu := GlobalTheory.GalChar.unr_ae κ
  have hu' := (Function.LeftInverse.injective (GlobalTheory.ThetaPull.conjSrc_conjSrc (E := E))).tendsto_cofinite.eventually hu
  have hS := Filter.eventually_cofinite.1 (hu.and hu')
  have h : (GlobalTheory.ThetaPull.thetaChar κ).1 * κ.1⁻¹ = 1 := by
    refine GlobalTheory.FrobDense.eq_one_of_away _ ((GlobalTheory.ThetaPull.thetaChar κ).2.1.mul κ.2.1.inv) (fun k => ?_) hS.toFinset
      fun v hv => ?_
    · rw [MonoidHom.mul_apply, MonoidHom.inv_apply, κ.2.2, (GlobalTheory.ThetaPull.thetaChar κ).2.2, inv_one, one_mul]
    · rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hv
      obtain ⟨v, rfl⟩ : ∃ v', conjSrc (IsCMField.complexConj E).toRingEquiv v' = v := ⟨_, GlobalTheory.ThetaPull.conjSrc_conjSrc v⟩
      rw [GlobalTheory.ThetaPull.conjSrc_conjSrc] at hv
      refine GlobalTheory.FrobDense.eq_one_of_unif (((GlobalTheory.ThetaPull.thetaChar κ).1 * κ.1⁻¹).comp (localIdele E _)) fun y hy => ?_
      have hy' : IsUnifAt v (Units.map (conjLoc _ v).toMonoidHom y) := ((conjLoc_spec _ v).2.2 y.val).trans hy
      have h1 : κ.1 (localIdele E _ y) = κ.val _ := κ.val_eq hv.1 y hy
      have h2 : κ.1 (localIdele E v _) = κ.val v := κ.val_eq hv.2 _ hy'
      rw [MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, GlobalTheory.ThetaPull.thetaChar_apply,
        GlobalTheory.ThetaPull.conjAd_localIdele, h1, h2, hval v hv.2 hv.1, mul_inv_cancel]
  exact Subtype.ext (mul_inv_eq_one.1 h)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.TotalFrobeniusCompatibility
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
open UpperTheory.V.Af UpperTheory.V.Af.Gu

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Af.Gu

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem unr_lpSum {x y : WD h} (hx : x.unr) (hy : y.unr) : (x.lpSum y).unr := by
  induction x using Quotient.inductionOn with | h a => ?_
  induction y using Quotient.inductionOn with | h b => ?_
  have ha : a.2.Unr := hx
  have hb : b.2.Unr := hy
  show (WD.mk (a.2.sum b.2)).unr
  rw [WD.unr_mk]
  refine ⟨?_, fun σ => ?_⟩
  · rw [WDRep.sum_N, ha.1, hb.1, LinearMap.prodMap_zero]
  · rw [WDRep.sum_ρ, ha.2, hb.2]; exact LinearMap.prodMap_one

private theorem sumList_spec (g : Weil h) : ∀ (c : ℕ) (f : Fin c → WD h) (M : Fin c → Multiset ℂ),
    (∀ i, (f i).unr ∧ (f i).charPol g = ((M i).map fun b => X - C b).prod) →
    (sumList (List.ofFn f)).unr ∧ (sumList (List.ofFn f)).charPol g = ((∑ i, M i).map fun b => X - C b).prod := by
  intro c
  induction c with
  | zero =>
    intro f M _
    have e : sumList (List.ofFn f) = WD.lpZero (h := h) := by simp [sumList]
    rw [e, WD.lpZero, WD.unr_mk, WD.charPol_mk, WDRep.diag_ρ, charpoly_diagEnd]
    exact ⟨WDRep.unr_diag _, by simp⟩
  | succ c ih =>
    intro f M H
    obtain ⟨h1, h2⟩ := ih (fun i => f i.succ) (fun i => M i.succ) fun i => H i.succ
    have e : sumList (List.ofFn f) = (f 0).lpSum (sumList (List.ofFn fun i => f (Fin.succ i))) := by
      rw [List.ofFn_succ]; rfl
    rw [e, WD.charPol_lpSum, h2, (H 0).2, Fin.sum_univ_succ, Multiset.map_add (f := _), Multiset.prod_add]
    exact ⟨unr_lpSum (H 0).1 h1, rfl⟩

private theorem rec_tw_diag {rc : IrrGL (k := w.adicCompletion E) → WD h} (H : IsRec h rc) {n : ℕ}
    (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (B : Multiset ℂˣ) (hB : GlobalTheory.LFun.HasSatGL w σ.ρ B) (s : ℝ) :
    ∃ α : Fin n → ℂˣ, B = Finset.univ.val.map α ∧
      (rc (cl σ)).lpTw s = WD.mk (WDRep.diag h fun i => (α i)⁻¹ * qPow w s) := by
  obtain ⟨hu, -⟩ := GlobalTheory.RecLaws.rec_hasSatGL H σ B hB
  obtain ⟨α, hα⟩ := ParLaws.exists_hasSatake_of_unr H hu
  refine ⟨α, hB.unique (GlobalTheory.T.hasSatakeGL_of_hasSatakeParameters_principalSeries E w n _ σ.ρ α hα), ?_⟩
  have e : rc (IrrGL.of σ.ρ σ.smooth σ.irred) = WD.mk (WDRep.diag h fun i => (α i)⁻¹) :=
    ParLaws.rec_eq_diag H hα
  rw [e, WD.lpTw_mk]
  refine WD.sound ⟨.refl _ _, fun g v => funext fun i => ?_, fun v => rfl⟩
  simp [mul_zpow, mul_comm, mul_left_comm, mul_assoc]

private theorem val_inv_eq (n d k : ℕ) (a : ℂˣ) :
    (((a⁻¹ * qPow w ((ex n d k : ℝ) / 2) : ℂˣ) : ℂ)) ^ (-1 : ℤ) =
      ((((normV w : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) *
        ((a * qPow w ((k : ℝ) - ((d : ℝ) - 1) / 2) : ℂˣ) : ℂ) := by
  have hq : ((normV w : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (zero_lt_one.trans (one_lt_normV w)).ne'
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _), zpow_neg_one, Units.val_mul, mul_inv, Units.val_inv_eq_inv_val, inv_inv,
    coe_qPow, ← Complex.cpow_neg, Units.val_mul, coe_qPow, mul_left_comm, Complex.ofReal_natCast, ← Complex.cpow_add _ _ hq]
  congr 2
  simp only [ex]
  push_cast
  ring

private theorem totPar_spec {rc : IrrGL (k := w.adicCompletion E) → WD h} (H : IsRec h rc) (n c : ℕ) (a d : Fin c → ℕ)
    (ρ : ∀ i, SmIrr (GL (Fin (a i)) (w.adicCompletion E))) (S : Fin c → Multiset ℂˣ)
    (hS : ∀ i, GlobalTheory.LFun.HasSatGL w (ρ i).ρ (S i)) (g : Weil h) (hg : deg g = -1) :
    (totPar n d ρ A h rc).unr ∧
      (totPar n d ρ A h rc).charPol g = ((algSat n (normV w) (satTot w d S)).map fun b => X - C b).prod := by
  have e : algSat n (normV w) (satTot w d S) = ∑ i, ∑ k : Fin (d i),
      algSat n (normV w) ((S i).map (· * qPow w (((k : ℕ) : ℝ) - ((d i : ℝ) - 1) / 2))) := by
    have hm : ∀ {α β ι : Type} (f : α → β) (s : Finset ι) (M : ι → Multiset α),
        (∑ i ∈ s, M i).map f = ∑ i ∈ s, (M i).map f := fun f s M => map_sum (Multiset.mapAddMonoidHom f) M s
    simp only [algSat, satTot, Multiset.pure_def, Multiset.bind_def, Multiset.bind_singleton, hm]
  rw [e]
  refine sumList_spec g c _ _ fun i => sumList_spec g (d i) _ _ fun k => ?_
  obtain ⟨α, hα, e⟩ := rec_tw_diag H (ρ i) (S i) (hS i) ((ex n (d i) k : ℝ) / 2)
  rw [e, hα, WD.unr_mk, WD.charPol_mk, WDRep.diag_ρ, charpoly_diagEnd, hg]
  refine ⟨WDRep.unr_diag _, ?_⟩
  simp only [val_inv_eq, algSat, Multiset.map_map, Multiset.pure_def, Multiset.bind_def, Multiset.bind_singleton]
  rfl

end UpperTheory.V.Af.Gu

theorem UpperTheory.total_frobenius_compatibility :
    HypothesesH → FrobTot := by
  intro P F Ω _ _ _ _ _ l _ ι n c a d r _ w hl ρ S hS H A h
  have L := P.litN.loc
  obtain ⟨rc, hrc⟩ := L.llc F Ω A w h
  have hrec : IsRec h rc := GlobalTheory.T.rec_of_rec_literal L.dzc L.dzi L.exh L.multi L.cos L.zel L.geo L.bz F Ω A w h rc hrc
  have hx := (H A h rc hrec).1 hl
  have hw := hx.wdOf_eq hl
  obtain ⟨t, ht, φ, hφ, N, b, hN, -⟩ := hx
  have hsp := totPar_spec hrec n c a d ρ S hS
  refine ⟨(hN.unr_wdOf_iff hl ht ι).1 (by rw [hw]; exact (hsp (frob h)⁻¹ (by rw [deg_inv, deg_frob])).1), fun s hs => ?_⟩
  have hd : deg (⟨s, mem_Weil_of_isFrob h hs⟩ : Weil h) = 1 := deg_eq_one_iff.2 hs
  have := hN.charPol_wdOf hl ht ι (⟨s, mem_Weil_of_isFrob h hs⟩ : Weil h)⁻¹
  rw [hw, (hsp _ (by rw [deg_inv, hd])).2] at this
  exact this.symm

end
end

