module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.ExtChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.CompatTOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.QuadraticCharpolySplitting.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0241
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0731
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.RecTExists
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.SuppFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0043
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CharDR
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PstExact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0181
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0660
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0137
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CoefficientRepTrivialOnUnramified
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartAct0
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IntegralityNearIdentity.CharOfScalar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0044
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.ExistsRec

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.ContOfFlag
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open GlobalTheory.Pst GlobalTheory.TripleGal Module
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z UpperTheory.V.Z.Ord

namespace UpperTheory.V.Z.Ord.OrdinaryPolarizedFromFlag

section Tri

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  [IsAlgClosure E Ω] {A : ValuationSubring Ω} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]

private theorem tri_dR (T : LocTied l P AI) (Bw : LocBridge l E Ω (Dec (F := E) A) O) (LL : FinExt l) (n : ℕ) :
    ∀ (r : ↥(Dec (F := E) A) →* GL (Fin n) ↥LL.1) (c : Fin n → ↥(Dec (F := E) A) →* GL (Fin 1) ↥LL.1),
    (∀ g i j, j < i → (r g).val i j = 0) → (∀ g i, (r g).val i i = (c i g).val 0 0) →
    Bw.IsdRE P LL r → ∀ i, Bw.IsdRE P LL (c i) := by
  induction n with
  | zero => exact fun _ _ _ _ _ i => i.elim0
  | succ n ih =>
    intro r c hr hc hd
    obtain ⟨r', hr'⟩ := UpperTheory.V.Loc.PstExact.exists_tail r hr
    obtain ⟨h1, h2⟩ := UpperTheory.V.Loc.PstExact.exact_line (k := ↥LL.1) (n := n)
    have h3 := LinearMap.funLeft_surjective_of_injective ↥LL.1 ↥LL.1 _ (Fin.succ_injective n)
    have hi : ∀ g v, ((LinearMap.single ↥LL.1 (fun _ : Fin (n + 1) => ↥LL.1) 0).comp
        (LinearMap.proj (0 : Fin 1) : (Fin 1 → ↥LL.1) →ₗ[↥LL.1] ↥LL.1)) (Bw.repE LL (c 0) g v) =
        Bw.repE LL r g (((LinearMap.single ↥LL.1 (fun _ : Fin (n + 1) => ↥LL.1) 0).comp
        (LinearMap.proj (0 : Fin 1) : (Fin 1 → ↥LL.1) →ₗ[↥LL.1] ↥LL.1)) v) := fun g v => by
      rw [GlobalTheory.ConjLocal.repE_apply, GlobalTheory.ConjLocal.repE_apply]
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [Matrix.mulVec, dotProduct, hc, Fin.sum_univ_succ]
      · simp [Matrix.mulVec, dotProduct, hr _ j.succ 0 (Fin.succ_pos j), Fin.sum_univ_succ]
    have hp : ∀ g v, LinearMap.funLeft ↥LL.1 ↥LL.1 (Fin.succ : Fin n → Fin (n + 1)) (Bw.repE LL r g v) =
        Bw.repE LL r' g (LinearMap.funLeft ↥LL.1 ↥LL.1 Fin.succ v) := fun g v => by
      rw [GlobalTheory.ConjLocal.repE_apply, GlobalTheory.ConjLocal.repE_apply]
      funext i
      simp [LinearMap.funLeft_apply, Matrix.mulVec, dotProduct, hr _ i.succ 0 (Fin.succ_pos i), Fin.sum_univ_succ, hr']
    obtain ⟨d₀, d₂, -⟩ := GlobalTheory.Per.ExactMult.exact_hodge_add l P AI T Bw.Kw LL _ _ _ _ _ _ _ _ hi hp h1 h3
      h2.linearMap_ker_eq.symm (by rw [IsDR, finrank_fin_fun]; exact hd)
    rw [IsDR, finrank_fin_fun] at d₀ d₂
    have hq := ih r' (fun i => c i.succ) (fun g i j hij => by rw [hr', hr g _ _ (Fin.succ_lt_succ_iff.2 hij)])
      (fun g i => by rw [hr', hc]) d₂
    exact fun i => Fin.cases d₀ hq i

private theorem flag_jumps (T : LocTied l P AI) (Bw : LocBridge l E Ω (Dec (F := E) A) O) {n : ℕ}
    (r : ↥(Dec (F := E) A) →* GL (Fin n) (Om l)) (c : Fin n → ↥(Dec (F := E) A) →* GL (Fin 1) (Om l))
    (M : GL (Fin n) (Om l)) (hr : ∀ g i j, j < i → (M * r g * M⁻¹).val i j = 0)
    (hc : ∀ g i, (M * r g * M⁻¹).val i i = (c i g).val 0 0) (τ : E →+* Om l) (J : Multiset ℤ)
    (hJ : IsJumpsAt P Bw r τ J) (i : Fin n) : ∃ a, IsJumpsAt P Bw (c i) τ {a} := by
  let r' : ↥(Dec (F := E) A) →* GL (Fin n) (Om l) := (MulAut.conj M).toMonoidHom.comp r
  have hr' : ∀ g, r' g = M * r g * M⁻¹ := fun _ => rfl
  obtain ⟨L, r₂, hm, hd, τ₂, hτ, -⟩ := (GlobalTheory.ConjLocal.local_conj l P E Ω O _ Bw n r r' M hr').2.2.2 τ J hJ
  obtain ⟨c₂, hm', hc₂⟩ := UpperTheory.V.Loc.PstExact.exists_diag Bw (r := r') hc hm
  have htri : ∀ g i j, j < i → (r₂ g).val i j = 0 := fun g i j hij => Subtype.ext (by
    have := hr g i j hij
    rw [← hr', ← hm.2] at this
    exact this)
  have hdr := tri_dR T Bw L n r₂ c₂ htri hc₂ hd i
  have hdr' : IsDR (P.PD Bw.Kw) (Bw.repE L (c₂ i)) := by
    rw [IsDR, finrank_fin_fun]
    exact hdr
  obtain ⟨hfin, -, hrk⟩ := (GlobalTheory.Per.Components.components_finrank l P AI T _ L _ (Bw.repE L (c₂ i))).1 τ₂
  obtain ⟨J', h1, h2⟩ := @GlobalTheory.HtCardProof.exists_count _ _ _ _ _ T _ _ ((c₂ i).comp Bw.e.symm.toMonoidHom) τ₂ hfin
  obtain ⟨a, rfl⟩ := Multiset.card_eq_one.1 (h1.trans ((hrk hdr').trans (finrank_fin_fun _)))
  exact ⟨a, L, c₂ i, hm' i, hdr, τ₂, hτ, h2⟩

end Tri

section Loc

variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 L)}

private theorem emb_norm (j : W.Emb l w) (x : 𝓞 L) : ‖j.1.comp (algebraMap L _) (x : L)‖ < 1 ↔ x ∈ w.asIdeal := by
  have h1 : w.asIdeal ≤ (GlobalTheory.EvExtend.placeOf (j.1.comp (algebraMap L _))).asIdeal := fun y hy => by
    rw [GlobalTheory.EvExtend.mem_placeOf, ← tendsto_pow_atTop_nhds_zero_iff_norm_lt_one]
    have h2 : Valued.v (algebraMap L (w.adicCompletion L) (y : L)) < 1 := by
      rw [show Valued.v (algebraMap L (w.adicCompletion L) (y : L)) = w.valuation L (algebraMap (𝓞 L) L y) from
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _]
      exact (HeightOneSpectrum.valuation_lt_one_iff_mem w _).2 hy
    have h3 := (j.2.tendsto 0).comp (Valued.tendsto_zero_pow_of_v_lt_one h2)
    simpa [Function.comp_def] using h3
  rw [w.isMaximal.eq_of_le (GlobalTheory.EvExtend.placeOf _).isPrime.ne_top h1, GlobalTheory.EvExtend.mem_placeOf]

private theorem cont_of_flag {n : ℕ} {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {r : Γ →* GL (Fin n) (Qbar l)}
    (hr : Continuous r) {ψ : Fin n → Γ →* (Qbar l)ˣ} (hf : W.HasFlag r ψ) (i : Fin n) : Continuous (ψ i) := by
  obtain ⟨g, hg⟩ := hf
  have h1 : Continuous fun s => (ψ i s : Qbar l) :=
    ((Units.continuous_val.comp ((continuous_const.mul hr).mul continuous_const)).matrix_elem i i).congr fun s => (hg s).2 i
  exact Units.continuous_iff.2 ⟨h1, (h1.comp continuous_inv).congr fun s => by simp⟩

private theorem ord_of_flag (N : GlobalTheory.Mem.LiteralAutomorphy.LitN) (ι : Qbar l ≃+* ℂ) (h : IsPlaceOver A w) (hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal)
    {a : Weil h →* (w.adicCompletion L)ˣ} (ha : IsLocalArtin h a) {n : ℕ} {r : ↥(Dec (F := L) A) →* GL (Fin n) (Qbar l)} (hr : Continuous r)
    {ψ : Fin n → ↥(Dec (F := L) A) →* (Qbar l)ˣ} (hf : W.HasFlag r ψ) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l L Ω (Dec (F := L) A) O) (hj : Induces Bw) (HT : (L →+* Qbar l) → Multiset ℤ)
    (hJ : ∀ (τ : L →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
      IsJumpsAt (Loc.PP l) Bw r τ (HT τ)) :
    ∃ (hh : Fin n → (L →+* Qbar l) → ℤ) (ω : Fin n → (w.adicCompletion L)ˣ →* ℂˣ), ∀ i, OrdChar ι a (ω i) (hh i) (ψ i) := by
  classical
  have art := N.aut.art
  have hD : GlobalTheory.Published.HeckeLAdicCharacterDeRham := by
    intro E Ω _ _ _ _ _ l _ P AI ht ι art ha χ n μ h1 h2 h3 w A hA O _ _ _ Bw hB
    have := N.aut.chA E Ω l P AI ht ι art ha χ n μ h1 h2 h3 w A hA O Bw hB
    exact ⟨this.1, this.2.2.2⟩
  obtain ⟨T⟩ := UpperTheory.V.Loc.tiedP l
  obtain ⟨M, hM⟩ := hf
  have hf' : W.HasFlag r ψ := ⟨M, hM⟩
  have hone : ∀ (i : Fin n) (j : W.Emb l w), ∃ b, IsJumpsAt (Loc.PP l) Bw (rk1 (ψ i)) (j.1.comp (algebraMap L _)) {b} := fun i j => by
    obtain ⟨τ', hτ'⟩ := GlobalTheory.CharAboveRead.exists_isInduced_of _ w hw (emb_norm j) A h O Bw hj
    exact flag_jumps T Bw r (fun i => rk1 (ψ i)) M (fun g => (hM g).1)
      (fun g i => ((hM g).2 i).trans (by simp [rk1])) _ _ (hJ _ _ τ' hτ') i
  let hh : Fin n → (L →+* Qbar l) → ℤ := fun i τ =>
    if hx : ∃ b, IsJumpsAt (Loc.PP l) Bw (rk1 (ψ i)) τ {b} then hx.choose else 0
  have hs : ∀ (i : Fin n) (j : W.Emb l w),
      IsJumpsAt (Loc.PP l) Bw (rk1 (ψ i)) (j.1.comp (algebraMap L _)) {hh i (j.1.comp (algebraMap L _))} := fun i j => by
    simp only [hh, dif_pos (hone i j)]
    exact (hone i j).choose_spec
  have hc := cont_of_flag hr hf'
  have hla := fun i => UpperTheory.V.Loc.laConv art art.heckeLAdicCharacter hD N.aut.berger h (ψ i) (hc i) O Bw hj
    (fun j => hh i (j.1.comp (algebraMap L _))) (hs i)
  choose ω hω using fun i => (UpperTheory.V.Loc.ordCharIff art h ι a ha (hh i) (ψ i)).1.2 ⟨hc i, hla i⟩
  exact ⟨hh, ω, hω⟩

private theorem pol_of_flag (N : GlobalTheory.Mem.LiteralAutomorphy.LitN) (ι : Qbar l ≃+* ℂ) (h : IsPlaceOver A w) (hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal)
    {a : Weil h →* (w.adicCompletion L)ˣ} (ha : IsLocalArtin h a) {n : ℕ} {r : ↥(Dec (F := L) A) →* GL (Fin n) (Qbar l)}
    {ψ : Fin n → ↥(Dec (F := L) A) →* (Qbar l)ˣ} (hf : W.HasFlag r ψ) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l L Ω (Dec (F := L) A) O) (hj : Induces Bw) (hp : IsPstAt (Loc.PP l) Bw r)
    {hh : Fin n → (L →+* Qbar l) → ℤ} {ω : Fin n → (w.adicCompletion L)ˣ →* ℂˣ} (hω : ∀ i, OrdChar ι a (ω i) (hh i) (ψ i)) (s : Weil h) :
    (wdAt (Loc.PP l) ι Bw h hj r).charPol s = ∏ i, (X - C ((ω i (a s) : ℂˣ) : ℂ)) := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨T⟩ := UpperTheory.V.Loc.tiedP l
  have hc := fun i => (UpperTheory.V.Loc.charDR N h hw ι a ha (ω i) (hh i) (ψ i) (hω i)).1 O Bw hj
  obtain ⟨-, F₂⟩ := UpperTheory.V.Loc.PstExact.flag T ι Bw h hj _ (fun i => rk1 (ψ i)) M
    (fun g => (hM g).1) (fun g i => ((hM g).2 i).trans (by simp [rk1]))
  rw [(F₂ hp).2 s]
  exact Finset.prod_congr rfl fun i _ => (hc i).2.2 s

end Loc

private theorem mem_of_prod {M : Type} [Monoid M] {n : ℕ} (f g : Fin n → (M →* ℂ))
    (h : ∀ x, ∏ j, (X - C (f j x)) = ∏ j, (X - C (g j x))) (j : Fin n) : ∃ i, g i = f j := by
  have hc := GlobalTheory.CharDeg.card_fiber_eq_of_sum_eq f g (fun x => GlobalTheory.CharDeg.sum_eq_of_prod_eq _ _ (h x)) (f j)
  haveI : Nonempty {i // f i = f j} := ⟨⟨j, rfl⟩⟩
  haveI : Finite {i // g i = f j} := inferInstance
  have hpos : 0 < Nat.card {i // g i = f j} := hc ▸ Nat.card_pos
  obtain ⟨⟨i, hi⟩⟩ := (Nat.card_pos_iff.1 hpos).1
  exact ⟨i, hi⟩

end UpperTheory.V.Z.Ord.OrdinaryPolarizedFromFlag


end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.PlainTorOfPs
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z UpperTheory.V.Z.Ord

namespace UpperTheory.V.Z.Ord.AtLOrdinary

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem plainTor_of_ps [CharZero k] {n : ℕ} (σ : SmIrr (GL (Fin n) k)) (ω : Fin n → kˣ →* ℂˣ) (hs : ∀ i, IsSmoothChar (ω i))
    (hd : ∀ i j, i ≠ j → ∃ y : Uo k, ω i y ≠ ω j y) (e : σ.ρ.Equiv (PS ω)) :
    GlobalTheory.RoadU.PlainTor (IrrGL.of σ.ρ σ.smooth σ.irred) := by
  have hμ : ∀ i, IsSmoothChar (ω i * absPow k (((n : ℂ) - 1) / 2)) := fun i => (hs i).mul (isSmoothChar_absPow _)
  have hsup := hasSupport_of_isSubquotient_prinSeries k n _ hμ ⟨_, σ.ρ, σ.smooth, σ.irred⟩
    (.of_injective e.toIntertwiningMap e.toLinearEquiv.injective)
  refine ⟨_, hsup.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred), fun y hy => ?_, fun y hy z hz e' => ?_⟩
  · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
    rfl
  · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
    obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hz
    rw [IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj] at e'
    by_cases hij : i = j
    · subst hij
      have h1 : absPow k ((1 : ℝ) : ℂ) = 1 := by
        have := mul_left_cancel (a := ω i * absPow k (((n : ℂ) - 1) / 2)) (b := 1) (c := absPow k 1) (by simpa using e')
        simpa using this.symm
      exact one_ne_zero (absPow_ofReal_eq_one.1 h1)
    · obtain ⟨y, hy⟩ := hd i j hij
      have h1 := DFunLike.congr_fun e' (y : kˣ)
      simp only [MonoidHom.mul_apply, isUnram_absPow k 1 (y : kˣ) y.2, isUnram_absPow k (((n : ℂ) - 1) / 2) (y : kˣ) y.2, mul_one] at h1
      exact hy h1

end UpperTheory.V.Z.Ord.AtLOrdinary
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.UseAtL
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Ord.useAtL' {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    {ι : Qbar l ≃+* ℂ} {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 L)} {h : IsPlaceOver A w}
    {r : Dec (F := L) A →* GL (Fin n) (Qbar l)} {lam : Wt L l n} {σ : SmIrr (GL (Fin n) (w.adicCompletion L))}
    (H : UpperTheory.V.Z.Ord.AtLT ι h r lam σ)
    (ω : Fin n → (w.adicCompletion L)ˣ →* ℂˣ) (hs : ∀ i, IsSmoothChar (ω i))
    (hd : ∀ i j, i ≠ j → ∃ y : Uo (w.adicCompletion L), ω i y ≠ ω j y) (he : Nonempty (σ.ρ.Equiv (PS ω)))
    (rc : IrrGL (k := w.adicCompletion L) → WD h) (hrc : UpperTheory.Zero.LLC.IsRecT h rc) (hab : Lev.AbW (rc (algNorm σ))) :
    DRat ι h r (fun τ => Finset.univ.val.map fun j => htW lam j τ) fun s => (rc (algNorm σ)).charPol s :=
  H ω hs hd he rc hrc hab
end

