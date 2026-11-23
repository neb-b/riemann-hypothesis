module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalRingCardinality.SpanPowerMembership.Places
public import Formalism.LocalRingCardinality.SpanPowerMembership.Adelic
public import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
public import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle0003
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleWeightMiddleEntries
public import Formalism.LocalRingCardinality.SpanPowerMembership.FmZeroHLatEmpty
public import Formalism.LocalRingCardinality.SpanPowerMembership.PlacesOverNcardOfSplitInj
public import Formalism.LocalRingCardinality.SpanPowerMembership.GPlacesExampleNatAct
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleNewtypesIdempotentZero
public import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtB
public import Formalism.LocalRingCardinality.SpanPowerMembership.HaarDensityNeZero
public import Formalism.LocalRingCardinality.Bundle0001
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.LocalRingCardinality.DataForms
public import Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeE
public import Mathlib
public import Formalism.CyclotomicNorms.StatementT
public import Formalism.CyclotomicNorms.NonsquarefreeBounds.IrreducibilityOfRestriction
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleRanksRankComplement

@[expose] public section

-- bundled from Formalism.LocalRingCardinality.SpanPowerMembership.ExampleClassGroupCardPos
section
noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain

structure LocalGap {R : Ranks} (H : Host R) where

  nloc : LocTheory

  nlocA : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (nloc l)

  nlocT : ∀ (l : ℕ) [Fact l.Prime], LocTied l (nloc l) (nlocA l)

theorem LocalGap.tame {R : Ranks} {H : Host R} (_G : LocalGap H) : TameHyp H := tameHyp H

def LocalGap.cd {R : Ranks} {H : Host R} (_G : LocalGap H) : CDHaar := CD.cdHaar

variable (H : Host R0) (T : ℕ) [hT : Fact T.Prime]

abbrev Tau0 : Type := ↥(R0.Psi)

theorem exampleClassGroupCard_pos {R : Ranks} (H : Host R) : 0 < exampleClassGroupCard H := by
  unfold exampleClassGroupCard
  refine Finset.prod_pos (fun k _ => pow_pos ?_ _)
  have : NeZero (H.g k) := ⟨(H.g_prime k).ne_zero⟩
  exact Nat.card_pos

abbrev rowsH : Rows.Data R0 :=
  toyRowsOfNumberField H.E H.φ₀ (@placesOf H.E _ _ H.cmStar) Tau0 card_examplePsi_eq (dstarOf T) (shaExample H)
    (shaExample_nonneg H) (exampleClassGroupCard H) (exampleClassGroupCard_pos H)

abbrev memT : Member R0 Tau0 (fun _ => hc0) := trivialMember Tau0 T (dstarOf T) (dstarOf_pos T)

theorem nHypH (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) :
    NHyp H (rowsH H T) :=
  { hsha := fun p _ e _ _ => shaExample_eq H p e
    hcard := rfl
    hg := hg }

theorem normAt_empty {K V ι : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι] [IsEmpty ι] (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (x : V) :
    Formalism.HermitianLatticesTheory.normAt b X v x = 0 := by
  simp [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm]

def spH (pz : H.E) (hpz : pz * H.conj pz = (T : H.E)) :
    @Spaces R0 H.F H.E _ _ _ _ H.cmStar _ :=
  letI := H.cmStar
  spacesExample star_isIntegral (cmData H) T hT.out pz
    (by rw [star_eq_conj H pz, mul_comm]; exact hpz)
    (exists_adelic_neg_one H (cmData H).sig (fun x => star_eq_conj H x))

abbrev sDataH (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) (ht : THyp H) :
    Formalism.MainNotions.S.Draft.SData R0 H.F H.E (conjF H) Unit Tau0 (fun _ _ => hc0) :=
  toySData (conjF H) (fun _ _ => hc0) 1 one_pos (fun _ _ l h => exampleWeight_cloud_gap_four l h)
    (fun _ _ l h => exampleWeight_middle_entries l h) (locAdj (conjF H) {H.g 0, H.g 1} (slocH H)
      (fun p hp => (splH H hg ht.jac p hp).some))


set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1600000 in
def exampleRecordOfData
    (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) (ht : THyp H)
    (hlev : T ∈ H.levelPrimes) (hpde : T ≠ H.pde ∧ T ≠ H.pde')
    (pz : 𝓞 H.E) (hK : (pz : H.E) ∈ H.K) (hpz : (pz : H.E) * H.conj (pz : H.E) = (T : H.E))
    (hcong : (pz - 1) ∈ Ideal.span {((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E)})
    (G : LocalGap H) : D7 :=
  letI : StarRing H.E := H.cmStar
  { R := R0
    host := H
    sp := spH H T pz hpz
    what₂ := rowsH H T
    eTau := Equiv.refl _
    hc := fun _ => hc0
    wordFin := inferInstanceAs (Fintype Unit)
    u₀ := ()
    hcW := fun _ _ => hc0
    hcW_base := rfl
    hcW_v := fun _ _ => rfl
    hcW_b := fun _ _ => rfl
    hcW_e := fun _ _ => rfl
    hcW_first := fun _ _ _ => rfl
    hcW_last := fun _ _ _ => rfl
    mem := fun _ => memT T
    nfLL := inferInstanceAs (NumberField H.E)
    starLL := H.cmStar
    tcLL := instTotallyComplex H
    galLL := instIsGalois H
    starLL_cx := fun x => emb_star H H.φ₀ x
    div := toyZeroLatticeDatum H.E
    div_good := ⟨(zeroHLat_good H.E).1, fun _ => (zeroHLat_good H.E).1⟩
    embE := RingHom.id _
    embE_φ₀ := rfl
    conjF := conjF H
    conjF_eq := conjF_apply H
    embE_conj := fun x => (star_eq_conj H x).symm
    LL0 := ⊤
    hostField_le_fixedField := fun _ => IntermediateField.mem_top
    O_contains := fun x => ⟨x, rfl⟩
    plEq := Equiv.refl _
    val_eq := placesOf_val_eq H.E
    ram_eq := placesOf_ram_eq H.E
    conj_val := placesOf_conj_val H.E
    T_level := fun _ => hlev
    T_norm := fun _ => ⟨pz, hK, hpz, hcong⟩
    sp_T := rfl
    cOf := fun _ => 1
    cOf_ne := fun _ => one_ne_zero
    cOf_eq := fun _ => by rw [map_one, one_mul, one_mul]
    T_win := fun _ => exampleLevel_near_lower Tau0 T
    GamP_eq := fun _ => rfl
    T_ne_pde := fun _ => hpde
    Dstar_eq := fun _ => rfl
    clsLat := fun _ _ c => Empty.elim c
    clsLat_lat := fun _ _ c => Empty.elim c
    eMu := fun _ => toyZeroSpaceEquiv Tau0 T (dstarOf T) (dstarOf_pos T)
    eMt := fun _ => toyZeroSpaceRefl
    perCol_base_eq_PtilCol := fun _ _ _ => rfl
    Bu_linL := fun _ _ => zero_isLinear
    Bu_linR := fun _ _ => zero_isLinear
    chTw := fun _ _ => (memT T).C
    memberColumns_twistedChain_base := fun _ => rfl
    e0Tw := fun _ _ => LinearEquiv.refl ℂ _
    PTw := fun _ _ => (memT T).P
    eMtTw := fun _ _ => toyZeroSpaceRefl
    perCol_tie := fun _ _ h => absurd rfl h
    vol := fun _ => 1
    vol_pos := fun _ => one_pos
    O_int := fun y => RingOfIntegers.isIntegral_coe y
    jEE := jZero H.E H.φ₀
    jEE_basis := jZero_basis H.E H.φ₀
    jN := fun _ => jZero H.E H.φ₀
    jN_basis := fun _ => jZero_basis H.E H.φ₀
    Dall_eq := rfl
    delP_eq := rfl
    Dt := ℂˣ
    detCls := fun _ _ _ => 1
    muTil := fun _ => 1
    chiD := MonoidHom.id _
    UO := ⊥
    chiD_UO := fun _ hx => Subgroup.mem_bot.mp hx
    e1Dt := exampleInverseEmbeddingProduct H (Equiv.refl Tau0)
    rest_detCharacter_on_unitary_eq := exampleCharacter_unitary_product H (Equiv.refl Tau0)
    relDet := fun N L L' => QuotientGroup.mk (relDetExample H (Equiv.refl Tau0) N L L')
    relDet_self := fun N L => by rw [relDetExample_self]; rfl
    relDet_mul := fun N L L' L'' => by rw [← QuotientGroup.mk_mul, relDetExample_mul]
    relDet_smul := fun N L L' γ h => congrArg _ (relDetExample_smul H (Equiv.refl Tau0) N L L' γ h)
    rhoDet_eq_inv_muTilde_chiD_pow := fun _ _ c => Empty.elim c
    rhoDetPrime_eq_muTilde_mul_chi_pow := fun _ i c => Empty.elim c
    dsig := toyConstantOne _
    dsig_pos := toyConstantOne_pos _
    s := sDataH H hg ht
    s_split := locAdj_split (conjF H) {H.g 0, H.g 1} (slocH H)
      (fun p hp => (splH H hg ht.jac p hp).some)
    s_HH := toySData_HH _ _ _ _ _
    s_Cu := fun u => toySData_Cu _ _ _ _ _ u _ rfl
    s_PlF := toySData_PlF _ _ _ _ _
    loc := G.nloc
    locA := G.nlocA
    locT := G.nlocT
    nd := ndToy H (rowsH H T) (nHypH H T hg)
    ntw := ntwToy H ⊤ (nHypH H T hg)
    naut := nautToy H (rowsH H T) (nHypH H T hg)
    nbc := nbcToy H (rowsH H T) (nHypH H T hg)
    nexp := nexpToy H ⊤ (nHypH H T hg)
    ntypes := ntypesT H (rowsH H T) (nHypH H T hg) ht G.tame
    nStage_trivialCharacter_compat := @ntypesT_E0Tie _ H (rowsH H T) (nHypH H T hg)
      (fun _ => inferInstanceAs (Subsingleton Z0)) (fun _ _ => inferInstanceAs (Subsingleton Z0)) ht G.tame
    nth := nthToy H ⊤ (nHypH H T hg)
    nbr := fun i => Empty.elim i
    self_good := fun i => Empty.elim i
    ntwbr := fun i => Empty.elim i
    nbr_ind := fun i => Empty.elim i
    ntwbr_ind := fun i => Empty.elim i
    loc_tie := fun i => Empty.elim i
    bc_tie := fun i => Empty.elim i
    rbar_tie := fun i => Empty.elim i
    mtpar_tie := fun i => Empty.elim i
    jetW := fun i => Empty.elim i
    jetW_l := fun i => Empty.elim i
    jetTau := fun i => Empty.elim i
    jetW1 := fun i => Empty.elim i
    resChar_thetaJetPlaceDegOne := fun i => Empty.elim i
    jetTau1 := fun i => Empty.elim i
    nStage_trivialCharacter_coeff_eq := fun g => (map_zero H.φ₀).trans (newtypes_idempotent_zero H _ _ ht G.tame g).symm
    Z_tie := example_Z_compatibility H _ _
    Zgood_tie := example_goodZ_compatibility H _ _
    etaJ_tie := example_etaJ_compatibility H _ _ (fun _ _ => rfl)
    fm := fun _ => formsToy H.φ₀ (placesOf H.E) card_examplePsi_eq (memT T).C (memT T).A (memT T).P
    eMu_isom := fun _ φ ψ => by
      rw [Subsingleton.elim φ 0, inner_zero_left]
      exact (Finset.sum_of_isEmpty _).symm
    nuIn := fun _ => 0
    nuIn_inj := fun _ x y _ => Subsingleton.elim (α := Fin 0 → H.E) x y
    nuIn_range := fun _ => Subsingleton.elim (α := Submodule H.E (Fin 0 → H.E)) _ _
    nuIn_jN := fun _ _ => funext fun c => Empty.elim c
    nuIn_norm := fun _ v x => by
      exact (normAt_empty (ι := Fin 0) _ _ _ _).trans (normAt_empty (ι := Fin 0) _ _ _ _).symm
    jEE_norm := fun x => by
      exact (normAt_empty (ι := Fin 0) _ _ _ _).trans (norm_zero (E := Z0)).symm
    sEE := ⟨0, fun x => (norm_zero (E := Z0)).trans
      ((norm_zero (E := Z0)).symm.trans (congrArg norm (Subsingleton.elim (α := Z0) 0 x)))⟩
    s_Cu_isom := fun _ φ ψ => by
      rw [Subsingleton.elim (α := Z0) φ 0]
      exact (inner_zero_left (𝕜 := ℂ) (E := Z0) ψ).trans (Finset.sum_of_isEmpty _).symm
    cd := G.cd
    jet := jetToy R0 H
    jetU := fun i => Empty.elim i
    jetL := fun i => Empty.elim i
    jetL' := fun i => Empty.elim i
    jetU1 := fun i => Empty.elim i
    jetL1 := fun i => Empty.elim i
    jetL1' := fun i => Empty.elim i
    gx := gxExample _ _
    gat := fun _ _ _ => gAtPExample _
    gat_d := fun _ _ _ => (gAtPExample_d _).trans (finrank_bot ℂ _).symm
    Y_sigval := spacesExample_Ysig _ _ _ _ _ _ _ }

end Formalism.BasicNotions.Examples₂
end
end

-- bundled from Formalism.LocalRingCardinality.SpanPowerMembership.NZRowC
section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.BasicNotions

abbrev En (n : ℕ) : Type := EuclideanSpace ℂ (Fin n)

section Rows

variable {R : Ranks} (LL : Type) [Field LL] [NumberField LL] (embLL : LL →+* ℂ) (P : Rows.Places LL)
  (Tau : Type) [Fintype Tau] (hTau : Fintype.card Tau = R.f) (Dst : ℝ)
  (sha : ℕ → ℕ → ℚ) (hsha : ∀ l e, 0 ≤ sha l e) (cg : ℕ) (hcg : 0 < cg)
  (kb : ∀ j, Tau → Fin (R.sigW j).1 → ℤ) (ks : ∀ j, Tau → Fin (R.sigW j).2 → ℤ)
  (tw : P.Pl → Bool) (htw : ∀ w, tw (P.conj w) = tw w)
  (Word : Type) (cI : Word → Type) [∀ u, Fintype (cI u)] (d Dall d0 : ℕ) (hd : d ≤ Dall)
  (FT : Type) [Fintype FT] [DecidableEq FT] (ft : Fin d → FT) (ft0 : Fin d0 → FT)
  (per : ∀ u : Word, Bool → EuclideanSpace ℂ (cI u) → En d → ℂ)
  (eta : ℕ → P.Pl → ℚ) (heta : ∀ j w, 0 ≤ eta j w)

end Rows

section RowsLemmas

variable {R : Ranks} {LL : Type} [Field LL] [NumberField LL] {embLL : LL →+* ℂ} {P : Rows.Places LL}
  {Tau : Type} [Fintype Tau] {hTau : Fintype.card Tau = R.f} {Dst : ℝ}
  {sha : ℕ → ℕ → ℚ} {hsha : ∀ l e, 0 ≤ sha l e} {cg : ℕ} {hcg : 0 < cg}
  {kb : ∀ j, Tau → Fin (R.sigW j).1 → ℤ} {ks : ∀ j, Tau → Fin (R.sigW j).2 → ℤ}
  {tw : P.Pl → Bool} {htw : ∀ w, tw (P.conj w) = tw w}
  {Word : Type} {cI : Word → Type} [∀ u, Fintype (cI u)] {d Dall d0 : ℕ} {hd : d ≤ Dall}
  {FT : Type} [Fintype FT] [DecidableEq FT] {ft : Fin d → FT} {ft0 : Fin d0 → FT}
  {per : ∀ u : Word, Bool → EuclideanSpace ℂ (cI u) → En d → ℂ}
  {eta : ℕ → P.Pl → ℚ} {heta : ∀ j w, 0 ≤ eta j w}

end RowsLemmas

section Gen

variable {R : Ranks} (D : Rows.Data R)

end Gen

end Formalism.BasicNotions.Examples₂.NZ
end
end

-- bundled from Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeH
section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

attribute [local instance] neZero_g fact_g Classical.propDecidable

variable {R : Ranks} (H : Host R)

structure Lbl where
  fA : ∀ k, (ZMod (H.g k))[X]
  fB : ∀ k, (ZMod (H.g k))[X]
  ne : ∀ k, fA k ≠ fB k
  okA : ∀ k, (fA k).Monic ∧ (fA k).natDegree = R.r ∧ (fA k).coeff 0 ≠ 0
  okB : ∀ k, (fB k).Monic ∧ (fB k).natDegree = R.r ∧ (fB k).coeff 0 ≠ 0
  good : ∀ k (PP J : Type) (t : PP → Bool), (∃ v, t v = true) → (∃ v, t v = false) →
    Formalism.CyclotomicNorms.IsGood R.r (H.g k) (fun v => if t v then fA k else fB k) (fun (_ : PP) (_ : J) => (1 : (ZMod (H.g k))ˣ))

variable {H} (Lb : Lbl H)



variable (H) (what₂ : Rows.Data R) (h : NHyp H what₂)

section Field

variable (K : Type) [Field K] [CharZero K]

end Field


end Formalism.BasicNotions.Examples₂.NZ
end
end

-- bundled from Formalism.LocalRingCardinality.SpanPowerMembership.PlLBridge
section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.PlOver

open NumberField IsDedekindDomain

variable (D : D7)

def plLEquiv (p : ℕ) [Fact p.Prime] :
    {v : HeightOneSpectrum (𝓞 D.what₂.LL) // ((p : ℕ) : 𝓞 D.what₂.LL) ∈ v.asIdeal} ≃
      {w : D.what₂.places.Pl // D.what₂.places.resChar w = p} :=
  (D.plEq.subtypeEquiv (fun w => resChar_eq_iff D p w)).symm

theorem plEq_plLEquiv (p : ℕ) [Fact p.Prime]
    (v : {v : HeightOneSpectrum (𝓞 D.what₂.LL) // ((p : ℕ) : 𝓞 D.what₂.LL) ∈ v.asIdeal}) :
    D.plEq (plLEquiv D p v).1 = v.1 := D.plEq.apply_symm_apply v.1

theorem wtLog_eq (p : ℕ) [hp : Fact p.Prime]
    (v : {v : HeightOneSpectrum (𝓞 D.what₂.LL) // ((p : ℕ) : 𝓞 D.what₂.LL) ∈ v.asIdeal}) :
    (eWL D.what₂.LL v.1 : ℝ) * Real.log (Ideal.absNorm v.1.asIdeal : ℝ) /
        (Real.log (p : ℝ) * (Module.finrank ℚ D.what₂.LL : ℝ)) =
      (D.what₂.places.ramIdx (plLEquiv D p v).1 : ℝ) *
        (padicValNat p (Ideal.absNorm (D.plEq (plLEquiv D p v).1).asIdeal) : ℝ) /
        (Module.finrank ℚ D.what₂.LL : ℝ) := by
  rw [D.ram_eq, plEq_plLEquiv]
  have := v.1.isPrime
  have : v.1.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := liesOver_of_mem _ v.2
  rw [Ideal.absNorm_eq_pow_inertiaDeg' (p := p) _ hp.out, Nat.padicValNat_def, Nat.multiplicity_prime_pow]
  have hlog : Real.log (p : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hp.out.one_lt)).ne'
  have h0 : (Module.finrank ℚ D.what₂.LL : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  push_cast
  rw [Real.log_pow]
  field_simp

end Formalism.BasicNotions.Examples₂.PlOver
end
end

-- bundled from Formalism.LocalRingCardinality.SpanPowerMembership.SizeData₂
section
noncomputable section

namespace Formalism.BasicNotions.Examples₂

open Formalism.BasicNotions

end Formalism.BasicNotions.Examples₂
end
end

