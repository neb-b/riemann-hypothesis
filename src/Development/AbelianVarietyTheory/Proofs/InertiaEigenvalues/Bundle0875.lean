module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthQuotEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0275
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0705
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0324
public import Formalism.SharpRestriction.Bundle0002
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
public import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
public import Formalism.SharpRestriction.AdmissibleParameterJoins.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0032
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0801
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0400
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0798
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0813
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0802
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0795
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseEmbeddingReadingEvalAdelicFunction
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0803
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.NotFamConstZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterValuesInjectiveLength

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalCongruenceCountOfRootDifferenceUnit
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut Module

noncomputable section

namespace GlobalTheory.CutCoreUnit

variable {D : D7} (i : D.nd.Loc)

theorem ccOff_univ (π : D.nd.X i) : ccOff i Set.univ π = ccAt (D.nd.T i) (D.nd.Z i) π := by
  rw [ccOff, ccAt, Ideal.map]
  congr 1
  ext a
  constructor
  · rintro ⟨f, hf, h0, rfl⟩
    refine ⟨⟨f, hf⟩, ?_, rfl⟩
    change (⟨f, hf⟩ : D.nd.T i) ∈ RingHom.ker _
    rw [RingHom.mem_ker]
    funext y
    exact h0 y.1 trivial y.2
  · rintro ⟨f, hf, rfl⟩
    refine ⟨f.1, f.2, fun x _ hx => ?_, rfl⟩
    change f ∈ RingHom.ker _ at hf
    rw [RingHom.mem_ker] at hf
    exact congrFun hf ⟨x, hx⟩


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in
theorem main : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S → π ∈ D.nd.Z i → NoChiOff i r Set.univ → UnrOut i r Set.univ → (∀ v ∈ D.nd.S i, (QuadAt i r Set.univ v ∧ IsUnit (D.nd.zeta i v - 1)) ∨ PolyAt i r Set.univ π v) → (∀ v ∈ D.nd.Q i, QuadAt i r Set.univ v ∧ D.nd.zeta i v ≠ 1) → (∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), (LocBound i w hw r Set.univ (WpO D.nd i ρ π) 0 ∧ (∀ c ∈ Finset.Icc 2 D.R.t, ∀ z ∈ cutCoc i w hw r Set.univ (chiRatO D.nd i c), z ∈ BD (Br.locLat D.nbr i w hw (chiRatO D.nd i c))) ∧ ∀ z ∈ cutCoc i w hw r Set.univ (chiRatO D.nd i 1), z ∈ Z1urD (Br.locLat D.nbr i w hw (chiRatO D.nd i 1)) (Br.inert D.nbr i w hw))) → Br.sFin D.loc D.nbr i ρ π → (∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤) → D.nd.vcc i π ≤ Br.sPi D.loc D.nbr i ρ π + (∑ e ∈ Finset.Ioo 0 D.R.t, (D.what₂.shaLen (D.nd.l i) e : ℚ)) + (padicValNat (D.nd.l i) (hE D.host) : ℚ) + (D.R.t : ℚ) * ∑ q ∈ D.nd.Q i, lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i q - 1}) := by
  intro hA D i r ρ π S hr hS hZ hN hU hSv hQ hl hsel hsha
  classical
  have hπ : π ∈ (Set.univ : Set (D.nd.X i)) := trivial
  obtain ⟨L, hL⟩ := CutCore.exists_length_quot (GlobalTheory.LenUnitPow.natCast_ne_zero (D.nd.l i) (O := D.nd.O i))
  have hL0 : L ≠ 0 := by
    rintro rfl
    exact GlobalTheory.LenUnitPow.natCast_not_isUnit (D.nd.l i) (O := D.nd.O i) (CutCore.length_quot_eq_zero_iff.mp hL)
  have hd : lenQ i (del51 D.nd S S.π') = 0 :=
    CutCore.length_quot_eq_zero_iff.mpr hS.2.2.2.2.2.2.2.2.2.2.1.2.2.2
  obtain ⟨s, hs⟩ := ENat.ne_top_iff_exists.mp (ne_of_lt hsel)

  have hρ : Module.length (D.nd.O i) ↥(cocRho i r S Set.univ) ≤ (s : ℕ∞) := by
    obtain ⟨C, hC, hfin, hlen⟩ := _root_.GlobalTheory.Cut.CountL.main D i r Set.univ _ (WpO D.nd i ρ π) (cocRho i r S Set.univ) 0
      (fun w hw => ⟨(hl w hw).1, (_root_.GlobalTheory.Cut.LocalCocycleConstruction.main D i r ρ π Set.univ S hr hS hπ w hw).1⟩)
    rw [mul_zero, Nat.cast_zero, zero_mul, zero_add] at hlen
    refine hlen.trans ((_root_.GlobalTheory.Cut.SelClass.main D i ρ π C (hC.trans (_root_.GlobalTheory.Cut.CocN.main D i r ρ π Set.univ S hr hS hπ).1) hfin ?_).trans ?_)
    · intro v h1 h2 h3
      exact CutCore.resIne_eq_bot_of_le i hC
        (GlobalTheory.Proof.LocalGlobalSelmer.main D i r Set.univ S _ S.ψρ (CutCore.inR'_one i r S) hU v h1 h2 h3)
    · have hc := (CutCore.lenCob_mono i _ hC).trans (_root_.GlobalTheory.Cut.CobOrd.main D i r ρ π Set.univ S hr hS hπ).1
      rw [hd, mul_zero, nonpos_iff_eq_zero] at hc
      rw [hc, zero_add, ← hs]

  have hχ : ∀ c : Fin D.R.t, Module.length (D.nd.O i) ↥(cocChi i r S Set.univ c) ≤
      lenQ i ((D.nd.l i : ℕ) : D.nd.O i) * (if (c : ℕ) = 0 then ((padicValNat (D.nd.l i) (hE D.host) : ℕ) : ℕ∞)
          else Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) ((c : ℕ) : ℤ)) +
        ∑ q ∈ D.nd.Q i, lenQ i (D.nd.zeta i q - 1) := by
    intro c
    obtain ⟨C', hC', hq, hlen'⟩ := GlobalTheory.Cut.Peel.main D i 1 (cocChi i r S Set.univ c) (D.nd.Q i)
    have hZ1 := hC'.trans ((_root_.GlobalTheory.Cut.CocN.main D i r ρ π Set.univ S hr hS hπ).2 c)
    have hunr : ∀ v, v ∉ placesOver D.host.E (D.nd.l i) → resIne i C' v = ⊥ := by
      intro v h1
      by_cases h3 : v ∈ D.nd.Q i
      · exact hq v h3
      refine CutCore.resIne_eq_bot_of_le i hC' ?_
      by_cases h2 : v ∈ D.nd.S i
      · rcases hSv v h2 with ⟨hqd, hu⟩ | hp
        · have h := _root_.GlobalTheory.Cut.QuadN.main D i r ρ π Set.univ S hr hS hπ v (Or.inl h2) hqd c
          rw [lenQ, CutCore.length_quot_eq_zero_iff.mpr hu, nonpos_iff_eq_zero, Module.length_eq_zero_iff] at h
          exact Submodule.subsingleton_iff_eq_bot.mp h
        · exact _root_.GlobalTheory.Cut.PolynomialInertiaAction.main D i r ρ π Set.univ S hr hS hπ v h2 hp c
      · exact GlobalTheory.Proof.LocalGlobalSelmer.main D i r Set.univ S _ _ (CutCore.inR'_one i r S) hU v h1 h2 h3
    refine hlen'.trans (add_le_add ?_ (Finset.sum_le_sum fun q hq' =>
      _root_.GlobalTheory.Cut.QuadN.main D i r ρ π Set.univ S hr hS hπ q (Or.inr hq') (hQ q hq').1 c))
    by_cases hc : (c : ℕ) = 0
    · rw [if_pos hc]
      have e : (c : ℕ) + 1 = 1 := by omega
      rw [e] at hZ1
      have hloc : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), ∀ f ∈ C',
          InCut i r Set.univ (chiRatO D.nd i 1) w hw f := by
        intro w hw f hf
        have h := (_root_.GlobalTheory.Cut.LocalCocycleConstruction.main D i r ρ π Set.univ S hr hS hπ w hw).2 c f (hC' hf)
        rwa [e] at h
      refine GlobalTheory.UnramHom.length_le_classNumber hA D i C' hZ1 fun v => ?_
      by_cases hv : v ∈ placesOver D.host.E (D.nd.l i)
      · exact GlobalTheory.CutTrivIne.main D i C' v hv fun f hf =>
          (Submodule.span_le.mpr fun z hz => (hl v hv).2.2 z hz) (hloc v hv f hf)
      · exact hunr v hv
    · rw [if_neg hc]
      have h2 : 2 ≤ (c : ℕ) + 1 := by omega
      have ht : (c : ℕ) + 1 ≤ D.R.t := c.2
      have h := _root_.GlobalTheory.Cut.ShaBound.main D i ((c : ℕ) + 1) C' hZ1 h2 ht
        (fun f hf w hw => (Submodule.span_le.mpr fun z hz =>
          (hl w hw).2.1 _ (Finset.mem_Icc.mpr ⟨h2, ht⟩) z hz)
            ((_root_.GlobalTheory.Cut.LocalCocycleConstruction.main D i r ρ π Set.univ S hr hS hπ w hw).2 c f (hC' hf))) hunr
      rw [Nat.add_sub_cancel] at h
      have hc0 := (CutCore.lenCob_mono i _ hC').trans ((_root_.GlobalTheory.Cut.CobOrd.main D i r ρ π Set.univ S hr hS hπ).2 c)
      rw [hd, mul_zero, nonpos_iff_eq_zero] at hc0
      rw [hc0, zero_add] at h
      exact h

  have hz : ∀ q ∈ D.nd.Q i, lenQ i (D.nd.zeta i q - 1) = ((lenQ i (D.nd.zeta i q - 1)).toNat : ℕ∞) := by
    intro q hq
    obtain ⟨n, hn⟩ := CutCore.exists_length_quot (sub_ne_zero.mpr (hQ q hq).2)
    rw [lenQ, hn, ENat.toNat_coe]
  set z : HeightOneSpectrum (𝓞 D.host.E) → ℕ := fun q => (lenQ i (D.nd.zeta i q - 1)).toNat with hzdef
  set g : ℕ → ℕ := fun e => (Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ)).toNat with hg
  have hg' : ∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) = (g e : ℕ∞) :=
    fun e he => (ENat.coe_toNat (hsha e he).ne).symm
  have ht : 0 < D.R.t := D.R.t_odd.pos
  set h := padicValNat (D.nd.l i) (hE D.host) with hh
  have hχ' : ∀ c : Fin D.R.t, Module.length (D.nd.O i) ↥(cocChi i r S Set.univ c) ≤
      ((L * (if (c : ℕ) = 0 then h else g c) + ∑ q ∈ D.nd.Q i, z q : ℕ) : ℕ∞) := by
    intro c
    refine (hχ c).trans (le_of_eq ?_)
    rw [Finset.sum_congr rfl hz, lenQ, hL]
    by_cases hc : (c : ℕ) = 0
    · rw [if_pos hc, if_pos hc]
      push_cast
      rfl
    · rw [if_neg hc, if_neg hc, hg' c (Finset.mem_Ioo.mpr ⟨Nat.pos_of_ne_zero hc, c.2⟩)]
      push_cast
      rfl
  have htot := (_root_.GlobalTheory.CutDetOrd.main D i r ρ π Set.univ S hr hS hπ hZ hN).trans
    (add_le_add hρ (Finset.sum_le_sum fun c _ => hχ' c))
  rw [← Nat.cast_sum, ← Nat.cast_add] at htot
  have hnat := ENat.toNat_le_of_le_coe htot
  have hsum : ∑ c : Fin D.R.t, (L * (if (c : ℕ) = 0 then h else g c) + ∑ q ∈ D.nd.Q i, z q) =
      L * (h + ∑ e ∈ Finset.Ioo 0 D.R.t, g e) + D.R.t * ∑ q ∈ D.nd.Q i, z q := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, CutCore.sum_fin_ite ht, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
  rw [hsum] at hnat
  have hsp : Br.sPi D.loc D.nbr i ρ π = (s : ℚ) / L := by
    rw [Br.sPi, lenUnit, hL, ← hs, ENat.toNat_coe, ENat.toNat_coe]
  have hsh : ∑ e ∈ Finset.Ioo 0 D.R.t, (D.what₂.shaLen (D.nd.l i) e : ℚ) =
      ((∑ e ∈ Finset.Ioo 0 D.R.t, g e : ℕ) : ℚ) := by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl fun e he =>
      D.nd.sha_eq _ e (Finset.mem_Ioo.mp he).1 (Finset.mem_Ioo.mp he).2 _ (hg' e he)
  have hzq : ∑ q ∈ D.nd.Q i,
      lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i q - 1}) =
        ((∑ q ∈ D.nd.Q i, z q : ℕ) : ℚ) / L := by
    rw [Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [lenUnit, hL, ENat.toNat_coe]
    rfl
  show lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ ccAt (D.nd.T i) (D.nd.Z i) π) ≤ _
  rw [← ccOff_univ, hsp, hsh, hzq, lenUnit, hL, ENat.toNat_coe]
  have hLq : (0 : ℚ) < L := by exact_mod_cast Nat.pos_of_ne_zero hL0
  generalize (Module.length (D.nd.O i) (D.nd.O i ⧸ ccOff i Set.univ π)).toNat = a at hnat
  generalize ∑ e ∈ Finset.Ioo 0 D.R.t, g e = G at hnat ⊢
  generalize ∑ q ∈ D.nd.Q i, z q = Z at hnat ⊢
  have hq : (a : ℚ) ≤ ((s + (L * (h + G) + D.R.t * Z) : ℕ) : ℚ) := Nat.cast_le.mpr hnat
  push_cast at hq
  rw [div_le_iff₀ hLq]
  have e : ((s : ℚ) / L + G + (h : ℚ) + (D.R.t : ℚ) * ((Z : ℚ) / L)) * L =
      s + G * L + h * L + D.R.t * Z := by
    field_simp
  rw [e]
  nlinarith [hq]

end GlobalTheory.CutCoreUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodPointMultiplicityLeRankProof
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.MultiplicityBound

theorem finrank_biSup_indep {K V ι : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [DecidableEq ι] {t : ι → Submodule K V} (ht : iSupIndep t) (A : Finset ι) :
    Module.finrank K ↥(⨆ σ ∈ A, t σ) = ∑ σ ∈ A, Module.finrank K ↥(t σ) := by
  induction A using Finset.induction_on with
  | empty => simp
  | insert a A ha ih =>
    rw [Finset.sum_insert ha, ← ih]
    have hs : (⨆ σ ∈ insert a A, t σ) = t a ⊔ ⨆ σ ∈ A, t σ := by
      rw [Finset.iSup_insert]
    have hd : Disjoint (t a) (⨆ σ ∈ A, t σ) := ht.disjoint_biSup (by simpa using ha)
    rw [hs, ← Submodule.finrank_sup_add_finrank_inf_eq, hd.eq_bot, finrank_bot, add_zero]


open Classical in
noncomputable def goodRows (D : D7) (i : D.nd.Loc) : Finset D.what₂.FT :=
  Finset.univ.filter (fun σ => D.nd.goodRow σ ∧ AtM D.nd D.naut i σ)

theorem dM_eq_sum (D : D7) (hI : Rows.IsotInternal D.what₂) (i : D.nd.Loc) (j : ℕ) (h : D.nd.j i = j) :
    dM D.nd D.naut i = ∑ σ ∈ goodRows D i, Module.finrank ℂ ↥(D.what₂.isot j σ) := by
  classical
  subst h
  have hr := D.nd.j_range i
  have hind : iSupIndep (D.what₂.isot (D.nd.j i)) := (hI _ hr.1 hr.2).submodule_iSupIndep
  have hsup : goodPartM D.nd D.naut i = ⨆ σ ∈ goodRows D i, D.what₂.isot (D.nd.j i) σ := by
    unfold goodPartM goodRows
    apply iSup_congr
    intro σ
    simp
  unfold dM
  rw [hsup]
  exact finrank_biSup_indep hind _

theorem sum_mult_le (D : D7) (hZ : SumRepresentations.ConclusionZ D) (i : D.nd.Loc) :
    (∑ π ∈ D.nd.Zgood i, (D.nd.mult i π : ℝ)) ≤ (dM D.nd D.naut i : ℝ) := by
  classical
  rcases (D.nd.Zgood i).eq_empty_or_nonempty with he | hne
  · rw [he, Finset.sum_empty]
    exact Nat.cast_nonneg _
  · have hG : HG D.nd D.naut i := by
      obtain ⟨x, hx⟩ := hne
      exact ⟨x, (D.Zgood_tie i x).1 hx⟩
    have h3 := (hZ i hG).2.2
    rw [← h3, ← Nat.cast_sum]
    apply le_of_eq
    congr 1
    rw [← Finset.sum_subset (Finset.subset_univ (D.nd.Zgood i))]
    · apply Finset.sum_congr rfl
      intro x hx
      rw [if_pos ((D.Zgood_tie i x).1 hx)]
    · intro x _ hx
      rw [if_neg (fun h => hx ((D.Zgood_tie i x).2 h))]

end GlobalTheory.MultiplicityBound


open GlobalTheory.MultiplicityBound in
theorem GlobalTheory.NLink.multLe_of_rank : ∀ (D : D7) (L : SizeData₂ D), SumRepresentations.Conclusion42 D → SumRepresentations.ConclusionZ D → Rows.IsotInternal D.what₂ →
    KillingConditions.LocalisationUniqueness D → MultLe L := by
  intro D L h42 hZ hI h2 j hj w hw
  classical
  rcases (D.nd.locs j w).eq_empty_or_nonempty with he | ⟨i0, hi0⟩
  · rw [he, Finset.sum_empty]
    exact Nat.cast_nonneg _
  obtain ⟨hj0, hw0⟩ := (D.nd.locs_mem j w i0).1 hi0
  subst hj0 hw0
  have hr := D.nd.j_range i0
  have hind : iSupIndep (D.what₂.isot (D.nd.j i0)) := (hI _ hr.1 hr.2).submodule_iSupIndep
  have h1 : (∑ i ∈ D.nd.locs (D.nd.j i0) (D.nd.w i0), ∑ π ∈ D.nd.Zgood i, (D.nd.mult i π : ℝ)) ≤
      ((∑ i ∈ D.nd.locs (D.nd.j i0) (D.nd.w i0), dM D.nd D.naut i : ℕ) : ℝ) := by
    rw [Nat.cast_sum]
    exact Finset.sum_le_sum (fun i _ => sum_mult_le D hZ i)
  refine h1.trans ?_
  apply Nat.cast_le.2
  have hdisj : (↑(D.nd.locs (D.nd.j i0) (D.nd.w i0)) : Set D.nd.Loc).PairwiseDisjoint (goodRows D) := by
    intro i hi i' hi' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro σ hσ hσ'
    have hi := (D.nd.locs_mem _ _ i).1 hi
    have hi' := (D.nd.locs_mem _ _ i').1 hi'
    simp only [goodRows, Finset.mem_filter, Finset.mem_univ, true_and] at hσ hσ'
    have htw : TwistedPlaces.TwLoc D i := by
      unfold TwistedPlaces.TwLoc
      rw [hi.2]
      exact hw
    exact hne (h2 i i' htw (hi.1.trans hi'.1.symm) (hi.2.trans hi'.2.symm) σ hσ.1 hσ.2 hσ'.2)
  calc (∑ i ∈ D.nd.locs (D.nd.j i0) (D.nd.w i0), dM D.nd D.naut i)
      = ∑ i ∈ D.nd.locs (D.nd.j i0) (D.nd.w i0), ∑ σ ∈ goodRows D i,
          Module.finrank ℂ ↥(D.what₂.isot (D.nd.j i0) σ) :=
        Finset.sum_congr rfl (fun i hi => dM_eq_sum D hI i _ ((D.nd.locs_mem _ _ i).1 hi).1)
    _ = ∑ σ ∈ (D.nd.locs (D.nd.j i0) (D.nd.w i0)).biUnion (goodRows D),
          Module.finrank ℂ ↥(D.what₂.isot (D.nd.j i0) σ) :=
        (Finset.sum_biUnion hdisj).symm
    _ = Module.finrank ℂ ↥(⨆ σ ∈ (D.nd.locs (D.nd.j i0) (D.nd.w i0)).biUnion (goodRows D),
          D.what₂.isot (D.nd.j i0) σ) :=
        (finrank_biSup_indep hind _).symm
    _ ≤ Module.finrank ℂ (D.what₂.Mj (D.nd.j i0)) := Submodule.finrank_le _
    _ = L.zeroSpaceRankAtPlace (D.nd.j i0) (D.nd.w i0) := by
        unfold SizeData₂.zeroSpaceRankAtPlace Rows.Data.Zj
        rw [← D.nd.mu_w i0,
          LinearMap.finrank_range_of_inj (Formalism.MainNotions.J.theta_injective_of_scalars D h42 hI i0 hj)]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeUnitOfExportTie
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
open Formalism.MainNotions.IntegralHeckeForms (HkIdx)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.GeoTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T1 : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m} {T0 : CoreJ D} [Algebra T0.Q.c.F D.what₂.LL]
  {Rl : RealDat3 D A3 T0.Q.c.F} {cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
  {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)} {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}
  (fw : FWTie T0 Rl.toRealDat κ v₀)

theorem exists_delta_root {ρ : GlobalTheory.SeriesTie.Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (z : (Formalism.L2.Theta.AE D)ˣ) : ∃ a : FractionRing (D.ntw.O i),
      ρ.e i b a = (((ρ.B i j b).de.chi z : Circle) : ℂ) ∧ ∃ n : ℕ, n ≠ 0 ∧ a ^ n = 1 := by
  obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym z
  have hopen : IsOpen ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker : Set (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om)) := by
    have e : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker = (D.ntw.delta i).ker := by
      ext g
      cases b <;> simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]
    rw [e]
    exact D.ntw.delta_open i
  have : Finite (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om ⧸ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker) :=
    Subgroup.quotient_finite_of_isOpen _ hopen
  have hfi : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hn : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hpow : Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ ^ (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker.index = 1 := by
    rw [← map_pow]
    exact MonoidHom.mem_ker.1 (Subgroup.pow_index_mem _ σ)
  refine ⟨algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))
    (algebraMap (D.ntw.O0 i) (D.ntw.O i) ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)), ?_, _, hn, ?_⟩
  · rw [hρ.delta i j b]
    exact (GlobalTheory.SeriesTie.charOf_eq ρ.rc ((ρ.eO i b).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i))) hopen hσ hn hpow).symm
  · rw [← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, hpow, Units.val_one, map_one, map_one]

section Side

variable {i : D.ntw.Tw} (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]) (b : Bool) (j : Fin D.R.m)

theorem valC_geoHecke {P : PlE D.host} {k : ℕ} (hP : GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.IsHeckePrime T0.Q.l P.asIdeal (charAt P))
    (s : T0.Q.c.F) {f g : T0.R ((j : ℕ) + 1)} (hf : f ∈ sec (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c (wtA (κ j)) (κ j).n)
    (hfg : GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.GeoHecke T0 ((j : ℕ) + 1) P.asIdeal (charAt P) k s f g)
    (z : FrC YS iC b ((j : ℕ) + 1)) (quot : HkKer P.asIdeal (charAt P) k z → FrC YS iC b ((j : ℕ) + 1))
    (hq : ∀ C, IsHkQuot P.asIdeal (charAt P) k z C (quot C)) :
    valC z g = embC YS iC b s * ∑ᶠ C, valC (quot C) f := by
  have hrel := hfg (PAt (embC YS iC b)) z
  have hL : GlobalTheory.Reg.EvLaws (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c := (GlobalTheory.Reg.evLaws_genFr_nonempty_comp _ _ _ _ _ _).1
  have hfun := GlobalTheory.HeckePointLaw.heckePointLaws.2.2.1 _ _ _ _ (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c P.asIdeal (charAt P) k hP
  have hterm : ∀ C, hkTerm (fun S _ _ => FrPt (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c S) (fun φ y z => FrMap φ y z)
      (fun Ω _ _ _ y => hkKer (Xo := T0.Q.Xo ((j : ℕ) + 1)) P.asIdeal (charAt P) k Ω y)
      (fun Ω _ _ _ y C z => hkRelFr P.asIdeal (charAt P) k (GlobalTheory.ThetaTrace.hkTr (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c (charAt P)) Ω y C z)
      f z C = valC (quot C) f := by
    intro C
    have hex : ∃ w, hkRelFr P.asIdeal (charAt P) k (GlobalTheory.ThetaTrace.hkTr (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c (charAt P))
        (PAt (embC YS iC b)) z C w := ⟨quot C, hq C⟩
    unfold hkTerm
    rw [dite_eq_left hex]
    have hm := hfun (PAt (embC YS iC b)) z C _ _ hex.choose_spec (hq C)
    exact (GlobalTheory.Reg.PChartModel.evR_map hL hf.1 (AlgHom.id _ _) hm).symm
  change toCp _ (evR (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c g z) = _
  unfold evR
  rw [hrel, map_mul, toCp_algebraMap]
  congr 1
  unfold hkVal
  exact finsum_congr hterm

end Side

end GlobalTheory.GeoTie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HenselRootsOfLocalFamily
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut
open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.ConsExists GlobalTheory.SpanRing

namespace GlobalTheory

theorem localSubalgebra_eval_sub_mem_maximalIdeal {X O : Type} [CommRing O] [IsLocalRing O]
    (T : Subalgebra O (X → O)) [IsLocalRing T] {f : X → O} (hf : f ∈ T) (x y : X) :
    f x - f y ∈ IsLocalRing.maximalIdeal O := by
  classical
  haveI : (IsLocalRing.maximalIdeal O).IsMaximal := IsLocalRing.maximalIdeal.isMaximal O
  letI : Field (O ⧸ IsLocalRing.maximalIdeal O) := Ideal.Quotient.field _
  let ψ : X → (T →+* O ⧸ IsLocalRing.maximalIdeal O) := fun z =>
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)).comp
      ((Pi.evalRingHom (fun _ : X => O) z).comp (T.val : T →+* (X → O)))
  have hψ : ∀ z (g : T), ψ z g = Ideal.Quotient.mk (IsLocalRing.maximalIdeal O) ((g : X → O) z) :=
    fun _ _ => rfl
  have hsurj : ∀ z, Function.Surjective (ψ z) := by
    intro z q
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact ⟨algebraMap O T a, by rw [hψ]; rfl⟩
  have hker : ∀ z, RingHom.ker (ψ z) = IsLocalRing.maximalIdeal T := fun z =>
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ (hsurj z))
  have hg : (⟨f, hf⟩ - algebraMap O T (f y) : T) ∈ RingHom.ker (ψ y) := by
    rw [RingHom.mem_ker, hψ, Ideal.Quotient.eq_zero_iff_mem]
    simp
  rw [hker y, ← hker x, RingHom.mem_ker, hψ, Ideal.Quotient.eq_zero_iff_mem] at hg
  simpa using hg

theorem hensel_roots_of_local_family : ∀ {X O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [HenselianRing O (IsLocalRing.maximalIdeal O)] {t : ℕ} (T : Subalgebra O (X → O)), IsLocalRing T → ∀ (P : X → Polynomial O), (∀ j, (fun x => (P x).coeff j) ∈ T) → (∀ x, (P x).Monic ∧ (P x).natDegree = t) → ∀ (π : X) (d : Fin t → O), (∀ a b, a ≠ b → IsUnit (d a - d b)) → P π = ∏ c, (Polynomial.X - Polynomial.C (d c)) → ∀ x, ∃ β : Fin t → O, Function.Injective β ∧ P x = ∏ c, (Polynomial.X - Polynomial.C (β c)) := by
  classical
  intro X O _ _ _ _ t T hT P hcoeff hdeg π d hd hπ x
  have hmap : (P x).map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)) =
      (P π).map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)) := by
    ext j
    simp only [Polynomial.coeff_map]
    rw [Ideal.Quotient.eq]
    exact localSubalgebra_eval_sub_mem_maximalIdeal T (hcoeff j) x π
  have hroot : ∀ c, ∃ b, (P x).IsRoot b ∧ b - d c ∈ IsLocalRing.maximalIdeal O := by
    intro c
    apply HenselianRing.is_henselian (P x) (hdeg x).1 (d c)
    · rw [← Ideal.Quotient.eq_zero_iff_mem, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map,
        hmap, hπ, Polynomial.eval_map, Polynomial.eval₂_at_apply, Polynomial.eval_prod,
        Finset.prod_eq_zero (Finset.mem_univ c) (by simp), map_zero]
    · rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, ← Polynomial.derivative_map, hmap,
        Polynomial.derivative_map, Polynomial.eval_map, Polynomial.eval₂_at_apply]
      apply IsUnit.map
      rw [hπ, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ c)]
      simp only [Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_X,
        Polynomial.derivative_C, sub_zero, one_mul, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self, zero_mul, add_zero,
        Polynomial.eval_prod]
      have : ∀ a ∈ Finset.univ.erase c, IsUnit (d c - d a) := fun a ha =>
        hd c a (Finset.ne_of_mem_erase ha).symm
      exact IsUnit.prod_iff.2 this
  choose β hβ hβm using hroot
  have hinj : Function.Injective β := by
    intro a b hab
    by_contra hne
    have hmem : d b - d a ∈ IsLocalRing.maximalIdeal O := by
      have := Ideal.sub_mem _ (hβm a) (hβm b)
      rw [hab] at this
      convert this using 1; ring
    exact (IsLocalRing.mem_maximalIdeal _).mp hmem (hd b a (Ne.symm hne))
  refine ⟨β, hinj, ?_⟩
  have hx0 : P x ≠ 0 := (hdeg x).1.ne_zero
  have hle : (Finset.univ.val.map β) ≤ (P x).roots := by
    rw [Multiset.le_iff_subset (Multiset.Nodup.map hinj Finset.univ.nodup)]
    intro r hr
    obtain ⟨c, -, rfl⟩ := Multiset.mem_map.mp hr
    exact (Polynomial.mem_roots hx0).mpr (hβ c)
  have hcard : (P x).roots.card ≤ (Finset.univ.val.map β).card := by
    rw [Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin, ← (hdeg x).2]
    exact Polynomial.card_roots' _
  have heq : Finset.univ.val.map β = (P x).roots := Multiset.eq_of_le_of_card_le hle hcard
  have hrc : (P x).roots.card = (P x).natDegree := by
    rw [← heq, Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin, (hdeg x).2]
  rw [← Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq (hdeg x).1 hrc, ← heq,
    Multiset.map_map]
  rfl

end GlobalTheory
end

