module

public import Mathlib
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsIrreducibleOfClsGLEqSingle
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0337
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityConcat
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviIrreducibleTensorDecomposition
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0045
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0043
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.CasselmanSuffTemp
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0346
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmRep

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FCount
section
open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas UpperTheory.Lit.Red

private theorem UpperTheory.Lit.Full.count_map_le {α β : Type*} (e : (α →₀ ℤ) →ₗ[ℤ] (β →₀ ℤ)) (A : Set α) (B : Set β)
    (h : ∀ a ∈ A, ∀ b, e (Finsupp.single a 1) b ≠ 0 → b ∈ B) :
    (Finsupp.supported ℤ ℤ A).map e ≤ Finsupp.supported ℤ ℤ B := by
  rw [Finsupp.supported_eq_span_single ℤ A, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
  exact (Finsupp.mem_supported ℤ _).2 fun b hb => h a ha b (Finsupp.mem_support_iff.1 hb)

private theorem UpperTheory.Lit.Full.count_equiv {α β : Type*} (e : (α →₀ ℤ) ≃ₗ[ℤ] (β →₀ ℤ)) (A : Set α) (B : Set β)
    (h : ∀ a ∈ A, ∀ b, e (Finsupp.single a 1) b ≠ 0 → b ∈ B)
    (h' : ∀ b ∈ B, ∀ a, e.symm (Finsupp.single b 1) a ≠ 0 → a ∈ A) : Nonempty (A ≃ B) := by
  have h1 := count_map_le e.toLinearMap A B h
  have h2 := count_map_le e.symm.toLinearMap B A h'
  have h3 : (Finsupp.supported ℤ ℤ A).map e.toLinearMap = Finsupp.supported ℤ ℤ B := by
    refine le_antisymm h1 fun y hy => ⟨e.symm y, h2 ⟨y, hy, rfl⟩, by simp⟩
  let f : (A →₀ ℤ) ≃ₗ[ℤ] (B →₀ ℤ) :=
    ((Finsupp.supportedEquivFinsupp (R := ℤ) (M := ℤ) A).symm.trans (e.ofSubmodules _ _ h3)).trans
      (Finsupp.supportedEquivFinsupp (R := ℤ) (M := ℤ) B)
  exact ⟨(Finsupp.basisSingleOne.map f).indexEquiv Finsupp.basisSingleOne⟩

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem UpperTheory.Lit.Full.count_seg_finite (S : Multiset (IrrGL (k := k))) :
    {Δ : Segment k | Δ.ms ≤ S}.Finite := by
  classical
  refine Set.Finite.of_finite_image (f := fun Δ : Segment k => (Δ.first, Δ.len))
    (((S.toFinset.finite_toSet).prod (Set.finite_Iic S.card)).subset ?_) ?_
  · rintro _ ⟨Δ, hΔ, rfl⟩
    refine ⟨?_, ?_⟩
    · have : Δ.first ∈ Δ.ms := Segment.mem_ms.2 (Segment.mem_carrier.2 ⟨0, Δ.len_pos, by simp⟩)
      simpa using Multiset.mem_of_le hΔ this
    · simpa using Multiset.card_le_card (show Δ.ms ≤ S from hΔ)
  · intro Δ _ Δ' _ h
    exact Segment.ext_first (congrArg Prod.fst h) (congrArg Prod.snd h)

private theorem UpperTheory.Lit.Full.count_card_le (𝔪 : Multiset (Segment k)) : 𝔪.card ≤ (msupp 𝔪).card := by
  induction 𝔪 using Multiset.induction_on with
  | empty => simp
  | cons Δ 𝔪 ih =>
    rw [← Multiset.singleton_add, msupp_add, msupp_singleton]
    have := Δ.len_pos
    simp only [Multiset.card_add, Multiset.card_singleton, Segment.card_ms]
    omega

private theorem UpperTheory.Lit.Full.count_mseg_finite (S : Multiset (IrrGL (k := k))) :
    {𝔪 : Multiset (Segment k) | msupp 𝔪 = S}.Finite := by
  classical
  refine (Set.finite_Icc 0 (S.card • (count_seg_finite S).toFinset.val)).subset ?_
  intro 𝔪 h𝔪
  have h𝔪 : msupp 𝔪 = S := h𝔪
  refine ⟨Multiset.zero_le _, Multiset.le_iff_count.2 fun Δ => ?_⟩
  by_cases hΔ : Δ ∈ 𝔪
  · have h1 : Δ.ms ≤ S := by
      obtain ⟨𝔫, rfl⟩ := Multiset.exists_cons_of_mem hΔ
      rw [← h𝔪, ← Multiset.singleton_add, msupp_add, msupp_singleton]
      exact Multiset.le_add_right _ _
    have h2 : Δ ∈ (count_seg_finite S).toFinset := by simpa using h1
    rw [Multiset.count_nsmul, Multiset.count_eq_one_of_mem (Finset.nodup _) h2, mul_one, ← h𝔪]
    exact (Multiset.count_le_card _ _).trans (count_card_le 𝔪)
  · simp [Multiset.count_eq_zero_of_notMem hΔ]

private theorem UpperTheory.Lit.Full.count_msupp (m : Segment k →₀ ℕ) :
    msupp (Finsupp.toMultiset m) = GlobalTheory.CompanionTheory.Hypotheses₂.RankOne.msum m := by
  induction m using Finsupp.induction_linear with
  | zero => simp [msupp, GlobalTheory.CompanionTheory.Hypotheses₂.RankOne.msum]
  | add a b ha hb => rw [map_add (f := _), msupp_add, ha, hb, GlobalTheory.CompanionTheory.Hypotheses₂.RankOne.msum_add]
  | single Δ c =>
    rw [GlobalTheory.CompanionTheory.Hypotheses₂.RankOne.msum_eq, Finsupp.sum_single_index (zero_smul ℕ Δ.ms), Finsupp.toMultiset_single]
    induction c with
    | zero => simp [msupp]
    | succ c ih => rw [add_smul, add_smul, msupp_add, ih, one_smul, one_smul, msupp_singleton]

end

theorem UpperTheory.Lit.Full.count :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (S : Multiset (IrrGL (k := k))), {x : IrrGL (k := k) | HasSupport x.rep S}.Finite ∧ {𝔪 : Multiset (Segment k) | msupp 𝔪 = S}.Finite ∧ {x : IrrGL (k := k) | HasSupport x.rep S}.ncard = {𝔪 : Multiset (Segment k) | msupp 𝔪 = S}.ncard := by
  intro hG hBZ hZ k _ _ _ _ S
  classical
  obtain ⟨Z, Ψ, hS, hΨ, hX⟩ := hZ k
  let c := MvPolynomial.basisMonomials (Segment k) ℤ
  let e : (IrrGL (k := k) →₀ ℤ) ≃ₗ[ℤ] ((Segment k →₀ ℕ) →₀ ℤ) := Ψ.toIntLinearEquiv.trans c.repr
  have hc : ∀ p m, c.repr p m = AddMonoidAlgebra.coeff p m := fun _ _ => rfl
  have hc' : ∀ m, c.repr.symm (Finsupp.single m 1) = MvPolynomial.monomial m 1 := fun m => by
    rw [Module.Basis.repr_symm_single_one]
    simp [c]
  obtain ⟨f⟩ := count_equiv e {x : IrrGL (k := k) | HasSupport x.rep S} {m | GlobalTheory.CompanionTheory.Hypotheses₂.RankOne.msum m = S}
    (fun x hx m hm => GlobalTheory.CompanionTheory.Hypotheses₂.RankOne.msum_eq_of_coeff_ne hG hBZ hS hΨ hX hx (by rw [← hc]; exact hm))
    (fun m hm z hz => by
      have hm : GlobalTheory.CompanionTheory.Hypotheses₂.RankOne.msum m = S := hm
      show HasSupport z.rep S
      rw [← hm]
      refine GlobalTheory.LocGL.UnramSupport.hasSupport_of_monomial hS hΨ hX z.2.rep.smooth z.2.rep.irr m ?_
      rw [IrrGL.of_rep, ← hc']
      exact hz)
  let g : {m : Segment k →₀ ℕ | GlobalTheory.CompanionTheory.Hypotheses₂.RankOne.msum m = S} ≃ {𝔪 : Multiset (Segment k) | msupp 𝔪 = S} :=
    Multiset.toFinsupp.symm.toEquiv.subtypeEquiv fun m => by
      show GlobalTheory.CompanionTheory.Hypotheses₂.RankOne.msum m = S ↔ msupp (Finsupp.toMultiset m) = S
      rw [count_msupp]
  have hfin := count_mseg_finite S
  haveI := hfin.to_subtype
  exact ⟨Set.finite_coe_iff.1 (Finite.of_equiv _ (f.trans g).symm), hfin, Set.ncard_congr' (f.trans g)⟩
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FPiece
section
open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas UpperTheory.Lit.Red

section SlopeTestRemainingChoices

open GlobalTheory.JacStages GlobalTheory.LocGL.SupportUnique

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem piece_irr {s : ℕ} {d : Fin s → ℕ} {t : Fin s → ℕ} {d' : ∀ a, Fin (t a) → ℕ}
    {U V : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    {σ : Representation ℂ (∀ a, Levi k fun b => Fin (d' a b)) U} (hσ : σ.IsIrreducible)
    {ρ : Representation ℂ (Levi k fun a => Fin (d a)) V} (hρ : IsSmooth ρ) (hl : HasFiniteLength ρ)
    (h : jhMult σ (relJacD e' ρ) ≠ 0) :
    ∃ τ : IrrRep (Levi k fun a => Fin (d a)), IsSubquotient τ.ρ ρ ∧ jhMult σ (relJacD e' τ.ρ) ≠ 0 := by
  have : WellFoundedLT (Subrepresentation ρ) := ((hasFiniteLength_iff_wellFounded ρ).1 hl).2
  have key : ∀ S : Subrepresentation ρ, jhMult σ (relJacD e' S.toRepresentation) ≠ 0 →
      ∃ τ : IrrRep (Levi k fun a => Fin (d a)), IsSubquotient τ.ρ ρ ∧ jhMult σ (relJacD e' τ.ρ) ≠ 0 := by
    intro S
    induction S using WellFoundedLT.induction with
    | ind S ih =>
    intro hS
    rcases eq_or_ne S ⊥ with rfl | hne
    · have h0 : Subsingleton (⊥ : Subrepresentation ρ).toSubmodule :=
        inferInstanceAs (Subsingleton (⊥ : Submodule ℂ V))
      have h1 : Subsingleton (Jacquet (⊥ : Subrepresentation ρ).toRepresentation (relUnipD k e')) :=
        (Submodule.Quotient.mk_surjective _).subsingleton
      exact absurd (jhMult_of_subsingleton hσ _) hS
    have : WellFoundedGT (Subrepresentation ρ) := ((hasFiniteLength_iff_wellFounded ρ).1 hl).1
    obtain ⟨T, -, hT⟩ := exists_le_covBy_of_lt (bot_lt_iff_ne_bot.2 hne)
    let ι : T.toRepresentation.IntertwiningMap S.toRepresentation :=
      ⟨Submodule.inclusion hT.le, fun _ => rfl⟩
    let p : S.toRepresentation.IntertwiningMap (subQuot S T) := ⟨Submodule.mkQ _, fun _ => rfl⟩
    let j : S.toRepresentation.IntertwiningMap ρ := ⟨S.toSubmodule.subtype, fun _ => rfl⟩
    have hp : ∀ v, p v = 0 ↔ v.1 ∈ T.toSubmodule := fun v => Submodule.Quotient.mk_eq_zero _
    have hj : IsSubquotient S.toRepresentation ρ := .of_injective j Subtype.val_injective
    have hq : IsSubquotient (subQuot S T) ρ :=
      (IsSubquotient.of_surjective p (Submodule.Quotient.mk_surjective _)).trans hj
    rw [GlobalTheory.CompanionTheory.JmTrans.jhMult_relJacD_exact e' hσ ι p (hj.isSmooth hρ) (Submodule.inclusion_injective hT.le)
      (Submodule.Quotient.mk_surjective _) (fun v => ⟨fun hv => ⟨⟨v.1, (hp v).1 hv⟩, rfl⟩, by
        rintro ⟨u, rfl⟩
        exact (hp _).2 u.2⟩)] at hS
    by_cases h1 : jhMult σ (relJacD e' T.toRepresentation) = 0
    · rw [h1, zero_add] at hS
      exact ⟨⟨_, subQuot S T, hq.isSmooth hρ, isIrreducible_subQuot hT⟩, hq, hS⟩
    · exact ih T hT.lt h1
  refine key ⊤ (jhMult_ne_zero_iff.2 ((jhMult_ne_zero_iff.1 h).trans ?_))
  exact _root_.GlobalTheory.JacStagesExact.isSubquotient_relJacD k s d t d' e' _ _ ρ _
    ((isSubquotient_of_equiv (topEquiv ρ)).isSmooth hρ) (isSubquotient_of_equiv (topEquiv ρ).symm)

private theorem piece_coarse (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) {s N : ℕ} (c : Fin s → ℕ)
    (x : ∀ a, Fin (c a) → IrrGL (k := k)) (hcat : ∑ i, (Zc.Seg.concat c x i).1 = N) {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (hfl : HasFiniteLength π)
    (h1 : jm (Zc.Seg.concat c x) hcat π ≠ 0) :
    ∃ (σ : Fin s → IrrGL (k := k)) (hσ : ∑ a, (σ a).1 = N), jm σ hσ π ≠ 0 ∧
      ∀ a, ∃ hx : ∑ i, (x a i).1 = (σ a).1, jm (x a) hx (σ a).rep ≠ 0 := by
  classical
  have hA : GlobalTheory.Published.IrreducibleAdmissibleGL := fun k _ _ _ _ n V _ _ π => (hBZ k).1 (Fin n) V π
  let d : Fin s → ℕ := fun a => ∑ i, (x a i).1
  have hd : ∑ a, d a = N := by
    refine Eq.trans ?_ hcat
    calc ∑ a, d a = ∑ p : Σ a, Fin (c a), (x p.1 p.2).1 := (Fintype.sum_sigma fun p : Σ a, Fin (c a) => (x p.1 p.2).1).symm
      _ = _ := (Fintype.sum_equiv finSigmaFinEquiv.symm _ _ fun _ => rfl).symm
  let e := stdBlocks d hd
  let e' : ∀ a, (Σ b, Fin ((x a b).1)) ≃ Fin (d a) := fun a => stdBlocks (fun i => (x a i).1) rfl
  have hE : refinePlace e e' = stdBlocks (fun a => (Zc.Seg.concat c x a).1) hcat :=
    GlobalTheory.CompanionTheory.JmTrans.refinePlace_stdBlocks (x := fun a i => (x a i).1) hd (fun _ => rfl) hcat
  obtain ⟨φR⟩ := _root_.GlobalTheory.JacStages.piTensor_flatHom_equiv s c (fun a b => GL (Fin ((x a b).1)) k) _ fun a b => (x a b).rep
  obtain ⟨φS⟩ := _root_.GlobalTheory.JacStagesProof.jac_refinePlace_equiv k s N d e c (fun a b => (x a b).1) e' V π
  have hirr0 : (piTensor fun l => (Zc.Seg.concat c x l).rep).IsIrreducible :=
    GlobalTheory.CompanionTheory.SocleJm.isIrreducible_piTensor hA (Zc.Seg.concat c x)
  have hirr1 := GlobalTheory.FinGL.Transport.isIrreducible_comp _
    (flatHom fun a b => GL (Fin ((x a b).1)) k) (flatHom_surjective _) hirr0
  have hirr : (piTensor fun a => piTensor fun b => (x a b).rep).IsIrreducible :=
    GlobalTheory.Parabolic.isIrreducible_of_equiv φR hirr1
  have h2 : jhMult (piTensor fun a => piTensor fun b => (x a b).rep) (relJacD e' (jac e π)) ≠ 0 := by
    rw [← jhMult_congr_right _ φS, ← jhMult_congr_left φR]
    rw [jm, ← hE] at h1
    exact (GlobalTheory.SmGL.EmptyBlocks.jhMult_comp_surjective _ (flatHom_surjective _) _ _).trans_ne h1
  obtain ⟨τ, hτ, h3⟩ := piece_irr e' hirr (isSmooth_jac e hs) ((hBZ k).2.1 _ _ _ e V π hs hfl) h2
  obtain ⟨σ, ⟨φ⟩⟩ := GlobalTheory.CompanionTheory.LeviTensor.nonempty_equiv_piTensor hA d τ
  obtain ⟨φT⟩ := _root_.GlobalTheory.JacStages.relJacD_piTensor_equiv k s d c (fun a b => (x a b).1) e' _ fun a => (σ a).rep.ρ
  have h4 : IsSubquotient (piTensor fun a => piTensor fun b => (x a b).rep)
      (piTensor fun a => jac (e' a) (σ a).rep.ρ) :=
    ((jhMult_ne_zero_iff.1 h3).trans (_root_.GlobalTheory.JacStagesExact.isSubquotient_relJacD k s d c _ e' _ _ τ.ρ _
      (isSmooth_piTensor fun a => (σ a).rep.smooth) (isSubquotient_of_equiv φ))).trans (isSubquotient_of_equiv φT)
  refine ⟨fun a => ⟨d a, σ a⟩, hd, jhMult_ne_zero_iff.2 ((isSubquotient_of_equiv φ.symm).trans hτ),
    fun a => ⟨rfl, jhMult_ne_zero_iff.2 ?_⟩⟩
  have hi : ∀ a, (piTensor fun b => (x a b).rep).IsIrreducible :=
    fun a => GlobalTheory.CompanionTheory.SocleJm.isIrreducible_piTensor hA (x a)
  exact isSubquotient_factor (fun a => jac (e' a) (σ a).rep.ρ) a (hi a)
    ((GlobalTheory.CompanionTheory.Hypotheses₂.TD.isSubquotient_comp_mulSingle _ hi a).trans (isSubquotient_comp h4 _))

private def Wd (W : ℕ → IrrGL (k := k)) (n : ℕ) (x : IrrGL (k := k)) : Prop :=
  ∃ hd : ∑ i : Fin n, (W i).1 = x.1, jm (fun i : Fin n => W i) hd x.rep ≠ 0

private theorem wd_iff {W : ℕ → IrrGL (k := k)} {n m : ℕ} {x : IrrGL (k := k)} (h : m = n) (f : Fin m → IrrGL (k := k))
    (hf : ∀ i, f i = W i) : Wd W n x ↔ ∃ hd : ∑ i, (f i).1 = x.1, jm f hd x.rep ≠ 0 := by
  subst h
  obtain rfl : f = fun i : Fin m => W i := funext hf
  rfl

private def cut (W : ℕ → IrrGL (k := k)) (a b : ℕ) (j : Fin 2) (i : Fin (![a, b] j)) : IrrGL (k := k) :=
  W (finSigmaFinEquiv (n := ![a, b]) ⟨j, i⟩)

private theorem concat_cut (W : ℕ → IrrGL (k := k)) (a b : ℕ) (i) : Zc.Seg.concat ![a, b] (cut W a b) i = W i := by
  simp [Zc.Seg.concat, cut]

private theorem cut_zero (W : ℕ → IrrGL (k := k)) (a b : ℕ) (i) : cut W a b 0 i = W i := by
  simp [cut, finSigmaFinEquiv_apply]

private theorem cut_one (W : ℕ → IrrGL (k := k)) (a b : ℕ) (i) : cut W a b 1 i = W (a + i) := by
  simp [cut, finSigmaFinEquiv_apply]

private theorem wd_up (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) {x : IrrGL (k := k)} (y : Fin 2 → IrrGL (k := k))
    (hy : ∑ a, (y a).1 = x.1) (h : jm y hy x.rep ≠ 0) (W : ℕ → IrrGL (k := k)) (a b : ℕ) (h0 : Wd W a (y 0))
    (h1 : Wd (fun i => W (a + i)) b (y 1)) : Wd W (a + b) x := by
  have hA : GlobalTheory.Published.IrreducibleAdmissibleGL := fun k _ _ _ _ n V _ _ π => (hBZ k).1 (Fin n) V π
  have H : ∀ j, ∃ hd : ∑ i, (cut W a b j i).1 = (y j).1, jm (cut W a b j) hd (y j).rep ≠ 0 :=
    Fin.forall_fin_two.2 ⟨(wd_iff rfl _ (cut_zero W a b)).1 h0, (wd_iff rfl _ (cut_one W a b)).1 h1⟩
  choose hx hj using H
  have hcat : ∑ i, (Zc.Seg.concat ![a, b] (cut W a b) i).1 = x.1 := by
    refine Eq.trans ?_ hy
    calc _ = ∑ p : Σ j, Fin (![a, b] j), (cut W a b p.1 p.2).1 :=
          Fintype.sum_equiv finSigmaFinEquiv.symm _ _ fun _ => rfl
      _ = ∑ j, ∑ i, (cut W a b j i).1 := Fintype.sum_sigma _
      _ = _ := Finset.sum_congr rfl fun j _ => hx j
  refine (wd_iff (by simp) _ (concat_cut W a b)).2 ⟨hcat, ENat.one_le_iff_ne_zero.1 ?_⟩
  exact (ENat.one_le_iff_ne_zero.2 h).trans (GlobalTheory.CompanionTheory.JmTrans.jm_le_jm_concat hA y hy _ _ hx hcat
    (fun j => ENat.one_le_iff_ne_zero.2 (hj j)) x.rep x.2.rep.smooth x.2.rep.hasFiniteLength)

private theorem wd_down (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) {x : IrrGL (k := k)} (W : ℕ → IrrGL (k := k)) (a b : ℕ)
    (h : Wd W (a + b) x) : ∃ (y : Fin 2 → IrrGL (k := k)) (hy : ∑ a, (y a).1 = x.1), jm y hy x.rep ≠ 0 ∧ Wd W a (y 0) ∧
      Wd (fun i => W (a + i)) b (y 1) := by
  obtain ⟨hcat, h⟩ := (wd_iff (by simp) _ (concat_cut W a b)).1 h
  obtain ⟨y, hy, h1, h2⟩ := piece_coarse hBZ _ _ hcat x.rep x.2.rep.smooth x.2.rep.hasFiniteLength h
  exact ⟨y, hy, h1, (wd_iff rfl _ (cut_zero W a b)).2 (h2 0), (wd_iff rfl _ (cut_one W a b)).2 (h2 1)⟩

private theorem wd_one {W : ℕ → IrrGL (k := k)} {x : IrrGL (k := k)} : Wd W 1 x ↔ W 0 = x := by
  constructor
  · rintro ⟨hd, h⟩
    exact GlobalTheory.CompanionTheory.SegFine.eq_of_one_le_jm x x.rep (.refl _) _ hd (ENat.one_le_iff_ne_zero.2 h)
  · rintro rfl
    have hf : (fun i : Fin 1 => W i) = fun _ => W 0 := funext fun i => by simp
    refine ⟨by simp, ?_⟩
    exact (GlobalTheory.CompanionTheory.SegFine.jm_eq_one (W 0) (W 0).rep (.refl _) _ _ hf).trans_ne one_ne_zero

private theorem wd_exists (hG : GlobalTheory.Published.GeometricLemma) (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness)
    (x : IrrGL (k := k)) (hx : 0 < x.1) : ∃ (s : ℕ) (u : Fin (s + 1) → IrrGL (k := k)) (hd : ∑ i, (u i).1 = x.1),
      (∀ i, (u i).IsCusp) ∧ jm u hd x.rep ≠ 0 ∧ HasSupport x.rep (Finset.univ.val.map u) := by
  have hA : GlobalTheory.Published.IrreducibleAdmissibleGL := fun k _ _ _ _ n V _ _ π => (hBZ k).1 (Fin n) V π
  obtain ⟨s, u, e, hu, φ, hφ⟩ := GlobalTheory.CompanionTheory.CuspEmbed.main hBZ hG k x.1 (GlobalTheory.SplitRead.Irr.ofIrrRep x.2.rep)
  have hd : ∑ i, (u i).1 = x.1 := by simpa using Fintype.card_congr e
  obtain ⟨ψ⟩ := (GlobalTheory.SmGL.Placing.parInd_jac_placing k _ _ _ e (stdBlocks (fun i => (u i).1) hd) _).1
    (piTensor fun i => (u i).rep)
  let f : x.rep.IntertwiningMap (prodIrr u hd) := ψ.toIntertwiningMap.comp φ
  have hf : Function.Injective f := ψ.toLinearEquiv.injective.comp hφ
  haveI := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible x.2.rep.irr
  obtain ⟨v, hv⟩ := exists_ne (0 : x.2.rep.V)
  have h1 := GlobalTheory.CompanionTheory.FrobJm.one_le_jm hA u hd x.rep x.2.rep.smooth f
    ⟨v, fun e => hv (hf (e.trans (map_zero f).symm))⟩
  rcases s with _ | s
  · simp at hd
    omega
  exact ⟨s, u, hd, hu, ENat.one_le_iff_ne_zero.1 h1,
    hasSupport_of_isSubquotient x.2.rep.irr hu (.of_injective f hf)⟩

end SlopeTestRemainingChoices

theorem UpperTheory.Lit.Full.piece :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : IrrGL (k := k)) (P : Set (IrrGL (k := k))) (q : Fin 2 → IrrGL (k := k)) (hq : ∑ a, (q a).1 = x.1), jm q hq x.rep ≠ 0 → (FirstIn x P → 0 < (q 0).1 → ∃ A, HasSupport (q 0).rep A ∧ ∃ y ∈ A, y ∈ P) ∧ (LastIn x P → 0 < (q 1).1 → ∃ A, HasSupport (q 1).rep A ∧ ∃ y ∈ A, y ∈ P) := by
  intro hG hBZ k _ _ _ _ x P q hq h
  refine ⟨fun hP hpos => ?_, fun hP hpos => ?_⟩
  · obtain ⟨s, u, hd, hu, hj, hs⟩ := wd_exists hG hBZ (q 0) hpos
    let W : ℕ → IrrGL (k := k) := fun i => if hi : i < s + 1 then u ⟨i, hi⟩ else q 1
    have h1 : Wd W (s + 1 + 1) x := wd_up hBZ q hq h W (s + 1) 1
      ((wd_iff rfl u fun i => by simp only [W, dif_pos i.2]).2 ⟨hd, hj⟩) (wd_one.2 (by simp [W]))
    rw [add_comm] at h1
    obtain ⟨y, hy, h2, h3, -⟩ := wd_down hBZ W 1 (s + 1) h1
    have h4 : y 0 = u 0 := (wd_one.1 h3).symm.trans (by simp [W])
    exact ⟨_, hs, u 0, Multiset.mem_map_of_mem _ (Finset.mem_univ_val _), h4 ▸ hP y hy (h4 ▸ hu 0) h2⟩
  · obtain ⟨s, u, hd, hu, hj, hs⟩ := wd_exists hG hBZ (q 1) hpos
    let W : ℕ → IrrGL (k := k) := fun i => if hi : 0 < i ∧ i - 1 < s + 1 then u ⟨i - 1, hi.2⟩ else q 0
    have hW : ∀ i : Fin (s + 1), u i = W (1 + i) := fun i => by
      have hi : 0 < 1 + i.1 ∧ 1 + i.1 - 1 < s + 1 := by omega
      simp only [W, dif_pos hi]
      exact congrArg u (Fin.ext (by simp))
    have h1 : Wd W (1 + (s + 1)) x := wd_up hBZ q hq h W 1 (s + 1) (wd_one.2 (by simp [W]))
      ((wd_iff rfl u hW).2 ⟨hd, hj⟩)
    rw [add_comm] at h1
    obtain ⟨y, hy, h2, -, h3⟩ := wd_down hBZ W (s + 1) 1 h1
    have h4 : y 1 = u (Fin.last s) := (wd_one.1 h3).symm.trans (by
      rw [hW]
      exact congrArg W (by simp [add_comm]))
    exact ⟨_, hs, u (Fin.last s), Multiset.mem_map_of_mem _ (Finset.mem_univ_val _),
      h4 ▸ hP y hy (h4 ▸ hu _) h2⟩
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.TCells
section
open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas

set_option maxHeartbeats 1000000 in
theorem UpperTheory.Lit.Cas.cells :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h N : ℕ) (δ : Fin h → IrrGL (k := k)) (hd : ∑ i, (δ i).1 = N) (x : Fin 2 → IrrGL (k := k)) (hx : ∑ j, (x j).1 = N), jm x hx (prodIrr δ hd) ≠ 0 → ∃ (y : Fin h → Fin 2 → IrrGL (k := k)) (hr : ∀ i, ∑ j, (y i j).1 = (δ i).1) (hc : ∀ j, ∑ i, (y i j).1 = (x j).1), (∀ i, jm (y i) (hr i) (δ i).rep ≠ 0) ∧ ∀ j, jhMult (x j).rep (prodIrr (fun i => y i j) (hc j)) ≠ 0 := by
  intro hGL hBZ k _ _ _ _ h N δ hd x hx hne
  classical
  obtain ⟨hJ, hC⟩ := hGL k
  haveI hfin : Fintype (SizeMatrix (fun i : Fin h => Fin (δ i).1) (fun j : Fin 2 => Fin (x j).1)) := by
    haveI : Finite (SizeMatrix (fun i : Fin h => Fin (δ i).1) (fun j : Fin 2 => Fin (x j).1)) := by
      refine Finite.of_injective (β := (i : Fin h) → Fin 2 → Fin ((δ i).1 + 1))
        (fun b i j => ⟨b.1 i j, Nat.lt_succ_of_le ?_⟩) ?_
      · have hrow := b.2.1 i
        simp only [Fintype.card_fin] at hrow
        rw [← hrow]
        exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      · intro b b' hbb
        apply Subtype.ext
        funext i j
        have := congrFun (congrFun hbb i) j
        simpa using this
    exact Fintype.ofFinite _
  let f : (b : SizeMatrix (fun i : Fin h => Fin (δ i).1) (fun j : Fin 2 => Fin (x j).1)) →
      (i : Fin h) → (j : Fin 2) × Fin (b.1 i j) ≃ Fin (δ i).1 := fun b i =>
    stdBlocks (fun j => b.1 i j) (by simpa using b.2.1 i)
  let g : (b : SizeMatrix (fun i : Fin h => Fin (δ i).1) (fun j : Fin 2 => Fin (x j).1)) →
      (j : Fin 2) → (i : Fin h) × Fin (b.1 i j) ≃ Fin (x j).1 := fun b j =>
    stdBlocks (fun i => b.1 i j) (by simpa using b.2.2 j)
  have hτirr : (piTensor fun j => (x j).rep).IsIrreducible :=
    _root_.GlobalTheory.ExtTensorIrr.piTensor_isIrreducible hBZ k (Fin 2) (fun j => Fin (x j).1) (fun j => (x j).snd.rep)
  have hsm : IsSmooth (piTensor fun i => (δ i).rep) := isSmooth_piTensor (fun i => (δ i).snd.rep.smooth)
  have hne' : jhMult (piTensor fun j => (x j).rep) (jac (stdBlocks (fun j => (x j).1) hx)
      (parInd (stdBlocks (fun i => (δ i).1) hd) (piTensor fun i => (δ i).rep))) ≠ 0 := hne
  rw [JacquetOfInducedFiltration.jhMult_eq hJ (stdBlocks _ hd) (stdBlocks _ hx) hsm f g hτirr] at hne'
  obtain ⟨b, -, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne'
  obtain ⟨T, -, hT⟩ := hC (Fin h) (Fin 2) (fun i => Fin (δ i).1) (fun j => Fin (x j).1)
    (fun i j => Fin (b.1 i j)) (f b) (g b) _ (fun i => (δ i).rep) (fun i => (δ i).snd.rep.smooth)
    (fun i => hasFiniteLength_of_isIrreducible (δ i).snd.rep.irr)
  have hT' := hT ⟨_, piTensor fun j => (x j).rep, isSmooth_piTensor (fun j => (x j).snd.rep.smooth), hτirr⟩
  rw [hT'] at hb
  obtain ⟨s, -, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
  have hs1 := left_ne_zero_of_mul hs
  have hs2 := right_ne_zero_of_mul hs
  rw [Finset.prod_ne_zero_iff] at hs1
  refine ⟨fun i j => ⟨b.1 i j, s i j⟩, fun i => by simpa using b.2.1 i, fun j => by simpa using b.2.2 j,
    fun i => ?_, fun j => ?_⟩
  · exact hs1 i (Finset.mem_univ i)
  · rw [jhMult_ne_zero_iff] at hs2 ⊢
    have h1 := SupportUnique.isSubquotient_comp hs2
      (MonoidHom.mulSingle (fun j : Fin 2 => GL (Fin (x j).1) k) j)
    have h2 := GlobalTheory.CompanionTheory.Hypotheses₂.TD.isSubquotient_comp_mulSingle (fun j => (x j).rep)
      (fun j => (x j).snd.rep.irr) j
    exact SupportUnique.isSubquotient_factor _ j (x j).snd.rep.irr (h2.trans h1)
end

