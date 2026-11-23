module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0511
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0115
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarySatakeEqOfSameUnramifiedBaseChange
section
noncomputable section

namespace GlobalTheory.SatBcZero

section Weyl

open Formalism.UG GlobalTheory.SatakeWeyl

theorem weyl_of_coeff (hswap : CoeffSwap) (hneg : CoeffNeg) (L : Type) [Field L]
    [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n m : ℕ)
    (hU : IsUnramInv ϖ σ q) (hm : 2 * m ≤ n) (hm' : n ≤ 2 * m + 1) (α : Fin m → ℂ)
    (h : GU σ n → ℂ) (hh : h ∈ Hecke ℂ (KU σ n)) :
    (∀ π : Equiv.Perm (Fin m), SatU ϖ q h (α ∘ π) = SatU ϖ q h α) ∧
      ∀ i : Fin m, SatU ϖ q h (Function.update α i (α i)⁻¹) = SatU ϖ q h α := by
  have hex := fun a : Fin m → ℤ => P.fSatake_tMat_exists (n := n) hU hm a
  choose T hT using hex
  have hq : (q : ℂ) ≠ 0 := by
    have := hU.2.2.2.2.2.1
    exact_mod_cast (by omega : q ≠ 0)
  have hp : ∀ f : Fin m → ℤ, ∏ i, (q : ℂ) ^ f i = (q : ℂ) ^ ∑ i, f i := fun f =>
    (map_prod (zpowersHom ℂˣ (Units.mk0 (q : ℂ) hq)) (fun i => Multiplicative.ofAdd (f i)) Finset.univ) |>
      congrArg (Units.coeHom ℂ) |> fun e => by
        simpa [map_prod, ← ofAdd_sum] using e.symm
  set S : (Fin m → ℤ) → ℂ := fun a => (q : ℂ) ^ 0 *
    (∏ i : Fin m, (q : ℂ) ^ (-(a i) * ((n : ℤ) - 1 - 2 * (i.val : ℤ)))) *
      cellSum (KU σ n) (radU σ Fin.val) h (T a) with hSdef
  have h1 : ∀ π : Equiv.Perm (Fin m), ∀ a, S (a ∘ π) = S a := by
    refine perm_of_swap S fun i j hij a => ?_
    have hne : i ≠ j := fun e => by rw [e] at hij; omega
    simp only [hSdef]
    rw [hswap L ϖ σ q n m hU hm hm' h hh a i j hij _ _ (hT a) (hT _), ← mul_assoc, hp, hp, pow_zero, one_mul, one_mul,
      ← zpow_add₀ hq]
    congr 2
    rw [← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib, Finset.sum_eq_add_of_mem i j (by simp) (by simp) hne]
    · simp only [Function.comp, Equiv.swap_apply_left, Equiv.swap_apply_right, hij]
      push_cast
      ring
    · rintro c - ⟨hc, hc'⟩
      simp only [Function.comp, Equiv.swap_apply_of_ne_of_ne hc hc', sub_self]
  have h2 : ∀ j : Fin m, j.val + 1 = m → ∀ a, S (Function.update a j (-a j)) = S a := by
    intro j hj a
    simp only [hSdef]
    rw [hneg L ϖ σ q n m hU hm hm' h hh a j hj _ _ (hT a) (hT _), ← mul_assoc, hp, hp, pow_zero, one_mul, one_mul,
      ← zpow_add₀ hq]
    congr 2
    rw [← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib, Finset.sum_eq_single j]
    · rw [Function.update_self]
      ring
    · intro c _ hc
      rw [Function.update_of_ne hc, sub_self]
    · simp
  have h3 : ∀ j : Fin m, ∀ a, S (Function.update a j (-a j)) = S a := by
    intro j a
    have hj := j.2
    let l : Fin m := ⟨m - 1, by omega⟩
    rw [← h1 (Equiv.swap j l) a, ← h2 l (by show m - 1 + 1 = m; omega) (a ∘ Equiv.swap j l),
      ← h1 (Equiv.swap j l) (Function.update a j (-a j))]
    congr 1
    rw [Function.update_comp_equiv]
    simp
  refine ⟨fun π => ?_, fun i => ?_⟩
  · rw [satU_eq T hT, satU_eq T hT]
    exact sum_perm S π (h1 π) α
  · rw [satU_eq T hT, satU_eq T hT]
    exact sum_neg S i (h3 i) α

theorem coeff_symm : CoeffSwap ∧ CoeffNeg := by
  have hr : RankOne := _root_.GlobalTheory.SatakeWeyl.rankOne_of_steps _root_.GlobalTheory.SatakeWeyl.descent _root_.GlobalTheory.SatakeWeyl.cellInv_holds
    (_root_.GlobalTheory.SatakeWeyl.chainSum_of_unimod (_root_.GlobalTheory.SatakeWeyl.unimod_of_unimodFin _root_.GlobalTheory.SatakeWeyl.unimodFin) _root_.GlobalTheory.SatakeWeyl.chainIndex)
  have hl : LeviStep := GlobalTheory.T.unitaryCellSumLeviReduction_of_steps hr _root_.GlobalTheory.SatakeWeyl.embExists _root_.GlobalTheory.SatakeWeyl.embMem _root_.GlobalTheory.SatakeWeyl.embTorus _root_.GlobalTheory.SatakeWeyl.leviRad
    (GlobalTheory.T.unitaryUnipotentRadicalSplitting_of_leviPart _root_.GlobalTheory.SatakeWeyl.leviPart) _root_.GlobalTheory.SatakeWeyl.ContractProof.contract _root_.GlobalTheory.SatakeWeyl.TorusConjProof.torusConj
  have hi : IntIndex := _root_.GlobalTheory.SatakeWeyl.intIndex
  have ht : TraceZeroIndex := _root_.GlobalTheory.SatakeWeyl.traceZeroIndex_of_intIndex hi
  exact ⟨GlobalTheory.T.unitarySatakeCoeff_adjacentSwap_of_leviReduction hl (GlobalTheory.T.unitaryFourLeviGL2RootIndex_of_cardSq hi) _root_.GlobalTheory.SatakeWeyl.Four.cartanFour,
    _root_.GlobalTheory.SatakeWeyl.coeffNeg_of_leviStep hl (GlobalTheory.T.unitaryRankTwoRootIndex_of_traceZeroCard ht) (_root_.GlobalTheory.SatakeWeyl.Heis.indexThree hi ht)⟩

end Weyl

theorem eq_of_invariant (m : ℕ) (f : (Fin m → ℂ) → ℂ)
    (hf : ∀ α : Fin m → ℂ, (∀ π : Equiv.Perm (Fin m), f (α ∘ π) = f α) ∧
      ∀ i, f (Function.update α i (α i)⁻¹) = f α) (α α' : Fin m → ℂ)
    (h : Finset.univ.val.map α + Finset.univ.val.map (fun i => (α i)⁻¹) =
      Finset.univ.val.map α' + Finset.univ.val.map (fun i => (α' i)⁻¹)) : f α = f α' := by
  classical
  have h2 := congrArg (Multiset.map (fun x : ℂ => s(x, x⁻¹))) h
  simp only [Multiset.map_add (f := _), Multiset.map_map, Function.comp_def, inv_inv] at h2
  have e1 : ∀ γ : Fin m → ℂ, (fun i => s((γ i)⁻¹, γ i)) = fun i => s(γ i, (γ i)⁻¹) :=
    fun γ => funext fun i => Sym2.eq_swap
  rw [e1 α, e1 α'] at h2
  have h3 : Finset.univ.val.map (fun i => s(α i, (α i)⁻¹))
      = Finset.univ.val.map (fun i => s(α' i, (α' i)⁻¹)) := by
    ext c
    have := congrArg (Multiset.count c) h2
    simp only [Multiset.count_add] at this
    omega
  obtain ⟨π, hπ⟩ := GlobalTheory.exists_perm_of_univ_map_eq _ _ h3
  have hor : ∀ i, α' i = α (π i) ∨ α' i = (α (π i))⁻¹ := by
    intro i
    rcases Sym2.eq_iff.1 (hπ i) with h4 | h4
    · exact Or.inl h4.1.symm
    · exact Or.inr h4.2.symm
  have key : ∀ s : Finset (Fin m),
      f (fun i => if i ∈ s then α' i else (α ∘ π) i) = f (α ∘ π) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [Function.comp_def]
    | insert j s hj ih =>
      rw [← ih]
      rcases hor j with h6 | h6
      · congr 1
        funext i
        by_cases hij : i = j
        · subst hij
          simp [hj, h6]
        · simp [hij]
      · rw [← (hf (fun i => if i ∈ s then α' i else (α ∘ π) i)).2 j]
        congr 1
        funext i
        by_cases hij : i = j
        · subst hij
          simp [hj, h6]
        · simp [hij]
  have := key Finset.univ
  simp only [Finset.mem_univ, if_true] at this
  rw [← (hf α).1 π, ← this]

theorem satU_eq_of_ubc_eq : ∀ (K : Type) [Field K] [Valued K (WithZero (Multiplicative ℤ))] [CompleteSpace K] (ϖ : K)
    (σ : K →+* K) (q n : ℕ), Formalism.UG.IsUnramInv ϖ σ q → ∀ α α' : Fin (n / 2) → ℂ,
      Formalism.MainNotions.N.ubc n (Finset.univ.val.map α) = Formalism.MainNotions.N.ubc n (Finset.univ.val.map α') →
      ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), Formalism.UG.SatU ϖ q h α = Formalism.UG.SatU ϖ q h α' := by
  intro K _ _ _ ϖ σ q n hU α α' e φ hφ
  unfold Formalism.MainNotions.N.ubc at e
  have e1 := add_right_cancel e
  refine eq_of_invariant _ (Formalism.UG.SatU ϖ q φ)
    (fun γ => weyl_of_coeff coeff_symm.1 coeff_symm.2 K ϖ σ q n (n / 2) hU (by omega) (by omega) γ φ hφ) _ _ ?_
  simpa only [Multiset.map_map, Function.comp_def] using e1

end GlobalTheory.SatBcZero

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamOfLadicRepSumRepAwayFromLHost
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module IsNilpotent

namespace GlobalTheory.WeilDeligne.SumParam

section Blocks

variable (k : Type) [CommRing k] (a b : ℕ)

def blk : Matrix (Fin a) (Fin a) k × Matrix (Fin b) (Fin b) k →+*
    Matrix (Fin (a + b)) (Fin (a + b)) k :=
  (Matrix.reindexAlgEquiv k k finSumFinEquiv).toRingEquiv.toRingHom.comp
    { toFun := fun p => Matrix.fromBlocks p.1 0 0 p.2
      map_one' := Matrix.fromBlocks_one
      map_mul' := fun p q => by simp [Matrix.fromBlocks_multiply]
      map_zero' := by simp
      map_add' := fun p q => by simp [Matrix.fromBlocks_add] }

variable {k a b}

theorem blk_apply (p : Matrix (Fin a) (Fin a) k × Matrix (Fin b) (Fin b) k) :
    blk k a b p = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks p.1 0 0 p.2) :=
  rfl

theorem blk_smul (c : k) (p : Matrix (Fin a) (Fin a) k × Matrix (Fin b) (Fin b) k) :
    blk k a b (c • p) = c • blk k a b p := by
  rw [blk_apply, blk_apply]
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply, Prod.smul_fst,
    Prod.smul_snd]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> simp

theorem coe_sumRep {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin a) k) (ρ' : Γ →* GL (Fin b) k) (g : Γ) :
    ((Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ' g : GL (Fin (a + b)) k) : Matrix (Fin (a + b)) (Fin (a + b)) k) =
      blk k a b ((ρ g : Matrix (Fin a) (Fin a) k), (ρ' g : Matrix (Fin b) (Fin b) k)) :=
  rfl

end Blocks

theorem isNilpotent_pair {R S : Type*} [MonoidWithZero R] [MonoidWithZero S] {x : R} {y : S}
    (hx : IsNilpotent x) (hy : IsNilpotent y) : IsNilpotent (x, y) := by
  obtain ⟨m, hm⟩ := hx
  obtain ⟨n, hn⟩ := hy
  exact ⟨m + n, Prod.ext (by simp [pow_add, hm]) (by simp [pow_add, hn])⟩

theorem exp_pair {R S : Type*} [Ring R] [Ring S] [Module ℚ R] [Module ℚ S] {x : R} {y : S}
    (hx : IsNilpotent x) (hy : IsNilpotent y) : exp (x, y) = (exp x, exp y) := by
  have hp := isNilpotent_pair hx hy
  exact Prod.ext (map_exp hp (RingHom.fst R S)) (map_exp hp (RingHom.snd R S))

def eqv (a b : ℕ) : ((Fin a → ℂ) × (Fin b → ℂ)) ≃ₗ[ℂ] (Fin (a + b) → ℂ) :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin b) ℂ ℂ).symm.trans
    (LinearEquiv.funCongrLeft ℂ ℂ finSumFinEquiv.symm)

theorem eqv_toEndC {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a b : ℕ}
    (M : Matrix (Fin a) (Fin a) (Qbar l)) (M' : Matrix (Fin b) (Fin b) (Qbar l))
    (v : (Fin a → ℂ) × (Fin b → ℂ)) :
    eqv a b ((toEndC ι M).prodMap (toEndC ι M') v) = toEndC ι (blk _ a b (M, M')) (eqv a b v) := by
  obtain ⟨v1, v2⟩ := v
  funext i
  obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective i
  simp only [eqv, LinearEquiv.trans_apply, toEndC_apply, blk_apply, Matrix.reindex_apply,
    Matrix.toLin'_apply, LinearMap.prodMap_apply, LinearEquiv.funCongrLeft_apply]
  rw [← Matrix.submatrix_map, Matrix.submatrix_mulVec_equiv]
  rcases k with k | k <;> simp [Matrix.fromBlocks_map, Matrix.fromBlocks_mulVec, Function.comp_def,
    LinearEquiv.sumArrowLequivProdArrow_symm_apply_inl, LinearEquiv.sumArrowLequivProdArrow_symm_apply_inr]

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
variable {l : ℕ} [Fact l.Prime] {a b : ℕ}

theorem isMonodromy_sum {t : Ine (F := E) A →* Multiplicative ℤ_[l]}
    {ρ : G E Ω →* GL (Fin a) (Qbar l)} {ρ' : G E Ω →* GL (Fin b) (Qbar l)}
    {N : Matrix (Fin a) (Fin a) (Qbar l)} {N' : Matrix (Fin b) (Fin b) (Qbar l)}
    (hN : IsMonodromy t ρ N) (hN' : IsMonodromy t ρ' N') :
    IsMonodromy t (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') (blk _ a b (N, N')) := by
  obtain ⟨h1, U, hU, H⟩ := hN
  obtain ⟨h1', U', hU', H'⟩ := hN'
  have hp := isNilpotent_pair h1 h1'
  refine ⟨hp.map _, U ⊓ U', hU.inter hU', fun σ hσ => ?_⟩
  rw [coe_sumRep, H σ hσ.1, H' σ hσ.2, ← blk_smul, ← map_exp (hp.smul _), Prod.smul_mk,
    exp_pair (h1.smul _) (h1'.smul _)]

theorem wdMat_sum {t : Ine (F := E) A →* Multiplicative ℤ_[l]} {φ : Weil h} (hφ : deg φ = 1)
    {ρ : G E Ω →* GL (Fin a) (Qbar l)} {ρ' : G E Ω →* GL (Fin b) (Qbar l)}
    {N : Matrix (Fin a) (Fin a) (Qbar l)} {N' : Matrix (Fin b) (Fin b) (Qbar l)}
    (h1 : IsNilpotent N) (h1' : IsNilpotent N') (g : Weil h) :
    wdMat t hφ (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') (blk _ a b (N, N')) g =
      blk _ a b (wdMat t hφ ρ N g, wdMat t hφ ρ' N' g) := by
  have hp := isNilpotent_pair h1 h1'
  rw [wdMat, wdMat, wdMat, coe_sumRep, ← blk_smul, ← map_exp (hp.smul _), ← map_mul, Prod.smul_mk,
    exp_pair (h1.smul _) (h1'.smul _)]
  rfl

theorem isFrobSS_sum {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
    {ρ₁ : Weil h → Module.End ℂ V} {N₁ : Module.End ℂ V} {x : WDRep h V}
    {ρ₂ : Weil h → Module.End ℂ V'} {N₂ : Module.End ℂ V'} {y : WDRep h V'}
    (hx : IsFrobSS ρ₁ N₁ x) (hy : IsFrobSS ρ₂ N₂ y) :
    IsFrobSS (fun g => (ρ₁ g).prodMap (ρ₂ g)) (N₁.prodMap N₂) (x.sum y) := by
  refine ⟨by rw [WDRep.sum_N, hx.1, hy.1], fun g => ⟨?_, ?_⟩⟩
  · rw [WDRep.sum_ρ]
    have hc : Commute ((x.ρ g, y.ρ g) : Module.End ℂ V × Module.End ℂ V') (ρ₁ g, ρ₂ g) :=
      Prod.ext (hx.2 g).1.eq (hy.2 g).1.eq
    exact hc.map (LinearMap.prodMapRingHom ℂ V V')
  · rw [WDRep.sum_ρ]
    have hn := (isNilpotent_pair (hx.2 g).2 (hy.2 g).2).map (LinearMap.prodMapRingHom ℂ V V')
    have e : (ρ₁ g).prodMap (ρ₂ g) - (x.ρ g).prodMap (y.ρ g) =
        LinearMap.prodMapRingHom ℂ V V' (ρ₁ g - x.ρ g, ρ₂ g - y.ρ g) := by
      rw [← Prod.mk_sub_mk, map_sub]; rfl
    show IsNilpotent ((ρ₁ g).prodMap (ρ₂ g) - (x.ρ g).prodMap (y.ρ g))
    rw [e]; exact hn

theorem wdOf_sumRep (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (ι : Qbar l ≃+* ℂ)
    (ρ : G E Ω →* GL (Fin a) (Qbar l)) (ρ' : G E Ω →* GL (Fin b) (Qbar l))
    (hc : Continuous fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)))
    (hc' : Continuous fun g => ((ρ' g : GL (Fin b) (Qbar l)) : Matrix (Fin b) (Fin b) (Qbar l))) :
    wdOf h hl ι (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') = (wdOf h hl ι ρ).lpSum (wdOf h hl ι ρ') := by
  have ht := isTameChar_tameL h hl
  obtain ⟨N, hN⟩ := exists_isMonodromy h hl ht hc
  obtain ⟨N', hN'⟩ := exists_isMonodromy h hl ht hc'
  have hS := isMonodromy_sum hN hN'
  obtain ⟨x, hx⟩ := hN.exists_isFrobSS hl ht (deg_frob (h := h)) ι
  obtain ⟨y, hy⟩ := hN'.exists_isFrobSS hl ht (deg_frob (h := h)) ι
  obtain ⟨z, hz⟩ := hS.exists_isFrobSS hl ht (deg_frob (h := h)) ι
  rw [IsWDOf.wdOf_eq hl ⟨_, ht, _, deg_frob, N, x, hN, hx, rfl⟩,
    IsWDOf.wdOf_eq hl ⟨_, ht, _, deg_frob, N', y, hN', hy, rfl⟩,
    IsWDOf.wdOf_eq hl ⟨_, ht, _, deg_frob, _, z, hS, hz, rfl⟩, WD.lpSum_mk]
  refine (WD.sound ((isFrobSS_sum hx hy).iso hz (eqv a b) (fun g v => ?_) fun v => ?_)).symm
  · rw [wdMat_sum deg_frob hN.1 hN'.1]
    exact eqv_toEndC ι _ _ v
  · exact eqv_toEndC ι _ _ v

end GlobalTheory.WeilDeligne.SumParam

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open Formalism.BasicNotions.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.WeilDeligne.wdOf_sumRep_awayFrom : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a b : ℕ) (ρ : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) (ρ' : G D.host.E D.nd.Om →* GL (Fin b) (Qbar l)) (w : PlE D.host) (hw : ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal), Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) → Continuous (fun g => ((ρ' g : GL (Fin b) (Qbar l)) : Matrix (Fin b) (Fin b) (Qbar l))) → GlobalTheory.WeilDeligne.wdOf (D.nd.plOm.2 w) hw ι (Formalism.MainNotions.SumRepresentations.At.sumRep ρ ρ') = (GlobalTheory.WeilDeligne.wdOf (D.nd.plOm.2 w) hw ι ρ).lpSum (GlobalTheory.WeilDeligne.wdOf (D.nd.plOm.2 w) hw ι ρ') :=
  fun D l _ ι a b ρ ρ' w hw hc hc' =>
    GlobalTheory.WeilDeligne.SumParam.wdOf_sumRep (h := D.nd.plOm.2 w) hw ι ρ ρ' hc hc'
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamOfLadicRepTwistDetAwayFromL
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.WeilDeligne

namespace TwistAway

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {l : ℕ} [Fact l.Prime] {a : ℕ}

theorem matrix_eq_zero_of_isNilpotent {K : Type*} [Field K] {M : Matrix (Fin 1) (Fin 1) K}
    (hM : IsNilpotent M) : M = 0 := by
  have h1 := Matrix.isNilpotent_trace_of_isNilpotent hM
  rw [Matrix.trace_fin_one] at h1
  ext i j
  fin_cases i; fin_cases j
  simpa using h1.eq_zero

theorem end_eq_zero_of_isNilpotent {f : Module.End ℂ (Fin 1 → ℂ)} (hf : IsNilpotent f) : f = 0 := by
  have h1 := matrix_eq_zero_of_isNilpotent (hf.map
    (LinearMap.toMatrixAlgEquiv' : Module.End ℂ (Fin 1 → ℂ) ≃ₐ[ℂ] Matrix (Fin 1) (Fin 1) ℂ))
  have h2 : (LinearMap.toMatrixAlgEquiv' : Module.End ℂ (Fin 1 → ℂ) ≃ₐ[ℂ] Matrix (Fin 1) (Fin 1) ℂ) f =
      (LinearMap.toMatrixAlgEquiv' : Module.End ℂ (Fin 1 → ℂ) ≃ₐ[ℂ] Matrix (Fin 1) (Fin 1) ℂ) 0 := by
    rw [h1, map_zero]
  exact (LinearMap.toMatrixAlgEquiv' : Module.End ℂ (Fin 1 → ℂ) ≃ₐ[ℂ] Matrix (Fin 1) (Fin 1) ℂ).injective h2

theorem twGL_det_val (ρ : G E Ω →* GL (Fin a) (Qbar l)) (χ : G E Ω →* GL (Fin 1) (Qbar l))
    (g : G E Ω) :
    ((Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ) g : GL (Fin a) (Qbar l)) :
        Matrix (Fin a) (Fin a) (Qbar l)) =
      (χ g : Matrix (Fin 1) (Fin 1) (Qbar l)) 0 0 • (ρ g : Matrix (Fin a) (Fin a) (Qbar l)) := by
  simp [Formalism.MainNotions.SumRepresentations.At.twGL, Matrix.det_unique, Algebra.smul_def]

variable {t : Ine (F := E) A →* Multiplicative ℤ_[l]}

theorem isMonodromy_zero_of_line {χ : G E Ω →* GL (Fin 1) (Qbar l)} {N : Matrix (Fin 1) (Fin 1) (Qbar l)}
    (hN : IsMonodromy t χ N) : IsMonodromy t χ 0 := by
  rwa [matrix_eq_zero_of_isNilpotent hN.1] at hN

theorem isMonodromy_twGL {ρ : G E Ω →* GL (Fin a) (Qbar l)} {χ : G E Ω →* GL (Fin 1) (Qbar l)}
    {N : Matrix (Fin a) (Fin a) (Qbar l)} (hN : IsMonodromy t ρ N) (hχ : IsMonodromy t χ 0) :
    IsMonodromy t (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) N := by
  obtain ⟨h1, U, hU, H⟩ := hN
  obtain ⟨-, U', hU', H'⟩ := hχ
  refine ⟨h1, U ⊓ U', hU.inter hU', fun σ hσ => ?_⟩
  rw [twGL_det_val, H' σ hσ.2, H σ hσ.1]
  simp

theorem wdMat_twGL {φ : Weil h} (hφ : deg φ = 1) (ρ : G E Ω →* GL (Fin a) (Qbar l))
    (χ : G E Ω →* GL (Fin 1) (Qbar l)) (N : Matrix (Fin a) (Fin a) (Qbar l)) (g : Weil h) :
    wdMat t hφ (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) N g =
      (χ g : Matrix (Fin 1) (Fin 1) (Qbar l)) 0 0 • wdMat t hφ ρ N g := by
  rw [wdMat, wdMat, twGL_det_val, smul_mul_assoc]

theorem isFrobSS_tensor_line {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {ρ : Weil h → Module.End ℂ V} {N : Module.End ℂ V} {a₀ : WDRep h V}
    {ψ : Weil h → Module.End ℂ (Fin 1 → ℂ)} {b₀ : WDRep h (Fin 1 → ℂ)}
    (ha : IsFrobSS ρ N a₀) (hb : IsFrobSS ψ 0 b₀) :
    IsFrobSS (fun g => TensorProduct.map (ρ g) (ψ g)) (N.rTensor (Fin 1 → ℂ)) (a₀.tensor b₀) := by
  have hψ : ∀ g, b₀.ρ g = ψ g := fun g =>
    (sub_eq_zero.mp (end_eq_zero_of_isNilpotent (hb.2 g).2)).symm
  refine ⟨by rw [WDRep.tensor_N, ha.1, hb.1, LinearMap.lTensor_zero, add_zero], fun g => ⟨?_, ?_⟩⟩
  · rw [WDRep.tensor_ρ, hψ]
    show TensorProduct.map _ _ * TensorProduct.map _ _ = TensorProduct.map _ _ * TensorProduct.map _ _
    rw [← TensorProduct.map_mul, ← TensorProduct.map_mul, (ha.2 g).1.eq]
  · rw [WDRep.tensor_ρ, hψ]
    have e1 : TensorProduct.map (ρ g) (ψ g) - TensorProduct.map (a₀.ρ g) (ψ g) =
        (ρ g - a₀.ρ g).rTensor (Fin 1 → ℂ) * (ψ g).lTensor V :=
      TensorProduct.ext' fun x y => by simp [TensorProduct.sub_tmul]
    rw [e1]
    have hc : Commute ((ρ g - a₀.ρ g).rTensor (Fin 1 → ℂ)) ((ψ g).lTensor V) := by
      show _ * _ = _ * _
      rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, LinearMap.lTensor_comp_rTensor,
        LinearMap.rTensor_comp_lTensor]
    exact hc.isNilpotent_mul_right ((ha.2 g).2.map (Module.End.rTensorAlgHom ℂ V (Fin 1 → ℂ)))

def lineEquiv (V : Type) [AddCommGroup V] [Module ℂ V] : TensorProduct ℂ V (Fin 1 → ℂ) ≃ₗ[ℂ] V :=
  (TensorProduct.congr (LinearEquiv.refl ℂ V) (LinearEquiv.funUnique (Fin 1) ℂ ℂ)).trans
    (TensorProduct.rid ℂ V)

@[simp] theorem lineEquiv_tmul (V : Type) [AddCommGroup V] [Module ℂ V] (x : V) (y : Fin 1 → ℂ) :
    lineEquiv V (x ⊗ₜ y) = y 0 • x := by
  simp [lineEquiv]

end TwistAway


open TwistAway in
theorem wdOf_twGL_det : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver (F := E) A w) (l : ℕ) [Fact l.Prime] (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (ι : Qbar l ≃+* ℂ) (a : ℕ) (ρ : G E Ω →* GL (Fin a) (Qbar l)) (χ : G E Ω →* GL (Fin 1) (Qbar l)), Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) → Continuous (fun g => ((χ g : GL (Fin 1) (Qbar l)) : Matrix (Fin 1) (Fin 1) (Qbar l))) → GlobalTheory.WeilDeligne.wdOf h hl ι (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) = (GlobalTheory.WeilDeligne.wdOf h hl ι ρ).lpChar (GlobalTheory.WeilDeligne.wdOf h hl ι χ) := by
  intro E Ω _ _ _ _ _ A w h l _ hl ι a ρ χ hρ hχ
  have ht := isTameChar_tameL h hl
  obtain ⟨N, hN⟩ := exists_isMonodromy h hl ht hρ
  obtain ⟨Nχ, hNχ⟩ := exists_isMonodromy h hl ht hχ
  have hχ0 := isMonodromy_zero_of_line hNχ
  have hN' := isMonodromy_twGL hN hχ0
  obtain ⟨a₀, ha, ea⟩ := hN.wdOf_spec hl ht (deg_frob (h := h)) ι
  obtain ⟨b₀, hb, eb⟩ := hχ0.wdOf_spec hl ht (deg_frob (h := h)) ι
  obtain ⟨d, hd, ed⟩ := hN'.wdOf_spec hl ht (deg_frob (h := h)) ι
  rw [ea, eb, ed, WD.lpChar_mk]
  refine WD.sound (WDRep.Iso.symm ?_)
  rw [map_zero] at hb
  refine (isFrobSS_tensor_line ha hb).iso hd (lineEquiv _) (fun g v => ?_) (fun v => ?_)
  · induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      simp only [TensorProduct.map_tmul, lineEquiv_tmul, IsMonodromy.rep_apply, wdMat_twGL,
        wdMat_zero, toEndC_smul, map_smul, LinearMap.smul_apply]
      rw [smul_smul]
      congr 1
      simp [toEndC_apply, Matrix.mulVec, dotProduct, mul_comm]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]

end GlobalTheory.WeilDeligne
end
end

