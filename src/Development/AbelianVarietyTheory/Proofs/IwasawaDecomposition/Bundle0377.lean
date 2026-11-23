module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0011
public import Formalism.LocalToGlobal.Columns.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0207
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Formalism.LocalToGlobal.Divisibility.DivisibilityProofs.TuplesP
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0188
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdAbsNormDivsDvd
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TransportedClassSetPresentationReadsEquivariant
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.Mem.TransportRead

theorem transport_ext_eq : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {S : Formalism.L2.Col.GSD K} {G Γ G' Γ' : Type}
    [Group G] [Group Γ] [Group G'] [Group Γ'] {ι : Γ →* G} {J : Subgroup G} (A : Bridge.AdPts S ι J) (h : S.Ok)
    {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (σ : K →+* ℂ) (ρ : Γ →* Module.End ℂ W) (χ : J →* ℂˣ)
    (coef : S.V →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun i => coef (S.bV i))
    (hspan : Submodule.span ℂ (Set.range fun i => coef (S.bV i)) = ⊤)
    (hpair : ∀ x x', inner ℂ (coef x) (coef x') = σ (S.pair x x')) (hK1 : ∀ k : J, (k : G) ∈ A.K1 → χ k = 1)
    (hgl : ∀ (γ : Γ) (k : J) (v : S.V), coef (S.ρ (A.gl (γ, k)) v) = ((χ k)⁻¹ : ℂˣ) • ρ γ (coef v))
    {ι' : Γ' →* G'} {ρ' : Γ' →* Module.End ℂ W} {J' : Subgroup G'} {χ' : J' →* ℂˣ}
    (eG : G ≃* G') (eΓ : Γ ≃* Γ') (hι : ∀ γ, ι' (eΓ γ) = eG (ι γ)) (hρ : ∀ γ, ρ' (eΓ γ) = ρ γ)
    (hJ : J' = J.map eG.toMonoidHom) (hχ : ∀ (k : J) (hk : eG k ∈ J'), χ' ⟨eG k, hk⟩ = χ k)
    (f : (S.toCSD h).Forms) (g : G'),
    ((Bridge.classPresOf A h σ ρ χ coef hli hspan hpair hK1 hgl).transport eG eΓ hι hρ hJ hχ).ext (f : S.Cl → S.V) g =
      coef ((((S.res h).symm f : S.EqFun) : S.D → S.V) (A.q (eG.symm g))) := by
  intro K _ _ _ S G Γ G' Γ' _ _ _ _ ι J A h W _ _ σ ρ χ coef hli hspan hpair hK1 hgl ι' ρ' J' χ' eG eΓ hι hρ hJ hχ f g
  set P' := (Bridge.classPresOf A h σ ρ χ coef hli hspan hpair hK1 hgl).transport eG eΓ hι hρ hJ hχ with hP'
  have hJ' : ∀ x, x ∈ J' ↔ eG.symm x ∈ J := fun x => by subst hJ; exact Subgroup.mem_map_equiv
  have hspec := P'.dec_spec g
  set γ' := P'.decG g
  set c := P'.decC g
  set k' := P'.decK g
  have hy : P'.y c = eG (A.y c) := rfl
  have hc : P'.coef = coef := rfl
  let k'' : J := ⟨eG.symm (k' : G'), (hJ' _).1 k'.2⟩
  have hg : eG.symm g = ι (eΓ.symm γ') * A.y c * (k'' : G) := by
    have e : ι (eΓ.symm γ') = eG.symm (ι' γ') := by
      rw [MulEquiv.eq_symm_apply, ← hι, MulEquiv.apply_symm_apply]
    rw [e, hspec, hy]
    simp only [map_mul, MulEquiv.symm_apply_apply, k'']
  have hq : A.q (eG.symm g) = A.gl (eΓ.symm γ', k''⁻¹) • S.outSec.rep c := by
    rw [hg, A.q_mul, A.q_y]
  set φ := (S.res h).symm f with hφ
  have hφc : ((φ : S.EqFun) : S.D → S.V) (S.outSec.rep c) = (f : S.Cl → S.V) c := by
    have := Formalism.L2.Col.GSD.resOf_apply S h S.outSec φ c
    rw [← this]
    show (((S.res h) φ).1 : S.Cl → S.V) c = (f : S.Cl → S.V) c
    rw [hφ, LinearEquiv.apply_symm_apply]
  have hk : k' = ⟨eG (k'' : G), by simp only [k'', MulEquiv.apply_symm_apply]; exact k'.2⟩ :=
    Subtype.ext (by simp only [k'', MulEquiv.apply_symm_apply])
  rw [hq, φ.2, hφc, hgl]
  show (χ' k' : ℂ) • ρ' γ' (P'.coef ((f : S.Cl → S.V) c)) = _
  rw [hc, hk, hχ]
  have hγ : ρ' γ' = ρ (eΓ.symm γ') := by rw [← hρ, MulEquiv.apply_symm_apply]
  rw [hγ, map_inv, inv_inv, Units.smul_def]

end GlobalTheory.Mem.TransportRead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupleTwistRamifiedIffChosenPrimeOrConjHost
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.Col2.RamQ

theorem not_unr_iff_under_mem (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hI : I.Ok) (a : I.ι)
    (PP : HeightOneSpectrum (𝓞 X.B.host.E)) :
    ¬ (I.xi a).UnrAt PP ↔ PP.under (𝓞 X.B.host.F) ∈ Qprime (I.tup a : Chr X.B.fields.F X.B.fields.E X.B.fields.K) := by
  obtain ⟨htw, hq, -⟩ := GlobalTheory.Mem.ReadTwist.isTwist_of_reads X.B.R X.B.host X.B.fields.K X.B.embLL I.S (I.tup a) (I.xi a)
    (hI.xi_reads a)
  rw [hq]
  refine ⟨fun h => ⟨PP, rfl, h⟩, ?_⟩
  rintro ⟨P, hP, hn⟩ hu
  apply hn
  intro x hx
  have h1 := GlobalTheory.Mem.Chr.twist_pow_units_of_under_eq X.B.R X.B.host I.S (I.xi a) htw P PP hP 1
    (fun y hy => by rw [pow_one]; exact hu y hy) x hx
  simpa using h1

theorem tupleTwist_ramified_iff_chosenPrime_or_conj_host (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hI : I.Ok) (a : I.ι)
    (PP : HeightOneSpectrum (𝓞 X.B.host.E)) :
    ¬ (I.xi a).UnrAt PP ↔ PP ∈ I.Q a ∨ ∃ PP' ∈ I.Q a, Formalism.IndefR.Lev.IsConjPl (D := X.toD7) PP' PP := by
  classical
  rw [not_unr_iff_under_mem X px I hI a PP]
  have hf := Formalism.L2.DIV.auxiliary_primes_finite X.B.fields.F X.B.fields.E X.B.fields.K (I.tup a : Chr X.B.fields.F X.B.fields.E X.B.fields.K)
    (I.tup a).2.1.1.1.1.2
  have hsel : ∀ v, (I.sel v).under (𝓞 X.B.fields.F) = v := fun v => HeightOneSpectrum.ext (hI.sel_ok v)
  have memQ : ∀ v ∈ Qprime (I.tup a : Chr X.B.fields.F X.B.fields.E X.B.fields.K), I.sel v ∈ I.Q a := fun v hv => by
    unfold ColIn.Q
    rw [Formalism.L2.Col.QE, dite_eq_left hf]
    exact Finset.mem_image_of_mem _ (hf.mem_toFinset.2 hv)
  have under_of_mem : ∀ P ∈ I.Q a, P.under (𝓞 X.B.host.F) ∈ Qprime (I.tup a : Chr X.B.fields.F X.B.fields.E X.B.fields.K) :=
    fun P hP => by
      obtain ⟨v, hv, hs, -⟩ := ColIn.exists_of_mem_Q I hP
      rw [← hs, hsel]
      exact hv
  constructor
  · intro hv
    have key : ∀ Q P : Pl X.toD7.host.E, Q.under (𝓞 X.toD7.host.F) = P.under (𝓞 X.toD7.host.F) →
        Q = P ∨ Q = Formalism.DivisionValues.conjPl P := fun Q P h => GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq h
    have e : PP.under (𝓞 X.B.host.F) = (I.sel (PP.under (𝓞 X.B.host.F))).under (𝓞 X.B.fields.F) := (hsel _).symm
    rcases key PP (I.sel (PP.under (𝓞 X.B.host.F))) e with h | h
    · left
      rw [h]
      exact memQ _ hv
    · right
      exact ⟨_, memQ _ hv, GlobalTheory.GoodPrimes.isConjPl_iff.2 h⟩
  · rintro (h | ⟨PP', h, hc⟩)
    · exact under_of_mem _ h
    · have e : PP'.under (𝓞 X.B.host.F) = PP.under (𝓞 X.B.host.F) := GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc
      rw [← e]
      exact under_of_mem _ h

theorem ram_iff : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px), I.Ok → ∀ (a : I.ι) (PP : Pl X.toD7.host.E),
    ¬ (I.xi a).UnrAt PP ↔ PP ∈ I.Q a ∨ ∃ PP' ∈ I.Q a, Formalism.IndefR.Lev.IsConjPl (D := X.toD7) PP' PP :=
  fun X px I hI a PP => tupleTwist_ramified_iff_chosenPrime_or_conj_host X px I hI a PP

end GlobalTheory.Mem.Col2.RamQ

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypePlaceLevelPlacesDistinctUnderlying
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelTypePlace

theorem not_two_primes {R : Type*} [CommRing R] (P : Ideal R) [hP : P.IsPrime] {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hne : p ≠ q) (h1 : (p : R) ∈ P) (h2 : (q : R) ∈ P) : False := by
  have hc : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hq).mpr hne)
  obtain ⟨a, b, hab⟩ := hc.map (Int.castRingHom R)
  apply hP.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  simp only [eq_intCast, Int.cast_natCast]
  exact P.add_mem (P.mul_mem_left _ h1) (P.mul_mem_left _ h2)

theorem natCast_mem_of_card {E : Type} [Field E] [NumberField E] (PP : IsDedekindDomain.HeightOneSpectrum (𝓞 E))
    {q : ℕ} (hc : Nat.card (𝓞 E ⧸ PP.asIdeal) = q) (hq0 : q ≠ 0) : (q : 𝓞 E) ∈ PP.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← hc, ← nsmul_one]
  exact card_nsmul_eq_zero'

theorem offPlace : ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → (∀ PP, PP ∈ L.Pg ↔ ∃ k v, PP = D.naut.plGw k v) → ∀ (t : T) (s : ReciprocityTheory.Aut.SplitPlace D.host.E), s.w ∈ L.Pg → (∀ PP ∈ L.Pg, PP ≠ s.w → ¬ NG.OverPl PP s.v) ∧ (∀ PP ∈ L.Q t, ¬ NG.OverPl PP s.v) ∧ s.w ∉ L.Q t ∧ (L.xiH t).UnrAt s.w := by
  intro D T L μ0 hL hPg t s hs

  have hA : ∀ PP : Pl D.host.E, NG.OverPl PP s.v → ∀ p : ℕ, (p : 𝓞 D.host.E) ∈ s.w.asIdeal →
      (p : 𝓞 D.host.E) ∈ PP.asIdeal := by
    intro PP hov p hp
    have h1 : (p : 𝓞 (maximalRealSubfield D.host.E)) ∈ s.v.asIdeal := by
      rw [← s.w_under, Ideal.mem_comap, map_natCast]; exact hp
    rw [← hov, Ideal.mem_comap, map_natCast] at h1; exact h1
  have hgne : ∀ k k' : Fin 2, k ≠ k' → D.host.g k ≠ D.host.g k' := by
    intro k k' h
    fin_cases k <;> fin_cases k' <;> first | exact absurd rfl h | exact D.host.g_ne | exact D.host.g_ne.symm
  obtain ⟨k, v, hkv⟩ := (hPg s.w).1 hs
  have hgk : (D.host.g k : 𝓞 D.host.E) ∈ s.w.asIdeal := by rw [hkv]; exact D.naut.plGw_over k v

  have hQ : ∀ PP ∈ L.Q t, (D.host.g k : 𝓞 D.host.E) ∈ PP.asIdeal → False := by
    intro PP hP hg
    obtain ⟨q, hq, hcard, -, hqg⟩ := (hL.Q_pl t PP hP).1
    exact not_two_primes PP.asIdeal (D.host.g_prime k) hq (hqg k).symm hg
      (natCast_mem_of_card PP hcard hq.ne_zero)
  have h3 : s.w ∉ L.Q t := fun h => hQ s.w h hgk
  refine ⟨?_, fun PP hP hov => hQ PP hP (hA PP hov _ hgk), h3, ?_⟩
  · intro PP hP hne hov
    rcases GlobalTheory.SplitPlaceOver.eq_or_isConjPl D s PP hov with e | hc
    · exact hne e.symm
    obtain ⟨k', v', hkv'⟩ := (hPg PP).1 hP
    have hk : k' = k := by
      by_contra hk
      have h1 : (D.host.g k' : 𝓞 D.host.E) ∈ PP.asIdeal := by rw [hkv']; exact D.naut.plGw_over k' v'
      exact not_two_primes PP.asIdeal (D.host.g_prime k') (D.host.g_prime k) (hgne k' k hk) h1
        (hA PP hov _ hgk)
    subst hk
    rw [hkv, hkv'] at hc
    exact D.naut.plGw_nconj k' v' v hc
  · by_contra hn
    rcases (hL.Q_ram t s.w).1 hn with h | ⟨PP', hP', hc⟩
    · exact h3 h
    obtain ⟨q, hq, hcard, -, hqg⟩ := (hL.Q_pl t PP' hP').1
    obtain ⟨c', hc', hcq⟩ := hc _ (natCast_mem_of_card PP' hcard hq.ne_zero)
    have hq' : (q : 𝓞 D.host.E) = c' := by
      apply RingOfIntegers.ext
      rw [hcq]; simp
    exact not_two_primes s.w.asIdeal (D.host.g_prime k) hq (hqg k).symm hgk (hq' ▸ hc')

end GlobalTheory.LevelTypePlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypePrimesDisjointTwistChosenPrimes
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.Mem.LevDisj

theorem places_disjoint : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)),
    I.Ok → ValsIn I → LevOf X I U L → ∀ t : TupU I U, Disjoint (X.B.primes px).vGs (Formalism.L2.Col.QE I.sel t.1) := by
  intro X px I U L hI _ _ t
  rw [Finset.disjoint_left]
  intro P hG hQ
  exact GlobalTheory.KFormsCmp.disj (GlobalTheory.BasePrimes.primes_ok X.B px).1 hI.sel_ok t.1 hI.g_mem hQ hG

end GlobalTheory.Mem.LevDisj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValSubLtOfHasRes
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.PtStab

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hasRes_of_sub {P : HeightOneSpectrum (𝓞 E)} {a b : P.adicCompletion E} {c : 𝓞 E ⧸ P.asIdeal}
    (h : HasRes P a c) (hab : Valued.v (a - b) < 1) : HasRes P b c := by
  obtain ⟨r, hr, hv⟩ := h
  refine ⟨r, hr, ?_⟩
  have e : b - algebraMap E _ (algebraMap (𝓞 E) E r) = (a - algebraMap E _ (algebraMap (𝓞 E) E r)) - (a - b) := by ring
  rw [e]
  exact Valuation.map_sub_lt _ hv hab

theorem val_sub_lt_of_hasRes {P : HeightOneSpectrum (𝓞 E)} {a b : P.adicCompletion E} {c : 𝓞 E ⧸ P.asIdeal}
    (h : HasRes P a c) (h' : HasRes P b c) : Valued.v (a - b) < 1 := by
  obtain ⟨r, hr, hv⟩ := h
  obtain ⟨r', hr', hv'⟩ := h'
  have hmem : r - r' ∈ P.asIdeal := Ideal.Quotient.eq.1 (hr.trans hr'.symm)
  have e : a - b = (a - algebraMap E _ (algebraMap (𝓞 E) E r)) - (b - algebraMap E _ (algebraMap (𝓞 E) E r')) +
      algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E (r - r')) := by
    simp only [map_sub]
    ring
  rw [e]
  refine Valuation.map_add_lt _ (Valuation.map_sub_lt _ hv hv') ?_
  rw [valued_algebraMap]
  exact (HeightOneSpectrum.valuation_lt_one_iff_mem _ _).2 hmem

theorem val_sub_lt_of_hatL {n : ℕ} (a b : Matrix (Fin n) (Fin n) (AfE F E)) (P : HeightOneSpectrum (𝓞 E)) (i : Fin n)
    {N : Submodule (𝓞 E) (Fin n → E)}
    (h : ∀ y ∈ N, Valued.v (adAt F P ((a *ᵥ fun j => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (y j)) i -
      (b *ᵥ fun j => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (y j)) i)) < 1)
    {z : Fin n → AfE F E} (hz : z ∈ Formalism.L2.Herm.hatL (F := F) N) :
    Valued.v (adAt F P ((a *ᵥ z) i - (b *ᵥ z) i)) < 1 := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    exact h v hv
  | zero => simp
  | add x y _ _ hx hy =>
    have e : (a *ᵥ (x + y)) i - (b *ᵥ (x + y)) i = ((a *ᵥ x) i - (b *ᵥ x) i) + ((a *ᵥ y) i - (b *ᵥ y) i) := by
      simp only [Matrix.mulVec_add, Pi.add_apply]
      ring
    rw [e, map_add (adAt F P)]
    exact Valuation.map_add_lt _ hx hy
  | smul c x _ hx =>
    have e0 : c • x = (c : AfE F E) • x := rfl
    have e : (a *ᵥ (c • x)) i - (b *ᵥ (c • x)) i = (c : AfE F E) * ((a *ᵥ x) i - (b *ᵥ x) i) := by
      rw [e0, Matrix.mulVec_smul, Matrix.mulVec_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
      ring
    rw [e, map_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' ((mem_rInt_iff F E _).1 c.2 P)) hx

variable [StarRing E] {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem pullV_mul_stab (g g' h : GL (Fin n) (AfE F E)) (x : Sp E n) :
    GlobalTheory.Mem.Col2.pullV (h * (g⁻¹ * g')) x =
      ((g'⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
        ((g : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ GlobalTheory.Mem.Col2.pullV h x) := by
  unfold GlobalTheory.Mem.Col2.pullV
  simp only [Matrix.mulVec_mulVec, ← Units.val_mul, _root_.mul_inv_rev, inv_inv, mul_assoc]

theorem pullV_eq_of_mul (g h : GL (Fin n) (AfE F E)) (x : Sp E n) :
    GlobalTheory.Mem.Col2.pullV h x = ((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
                 ((g : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ GlobalTheory.Mem.Col2.pullV h x) := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem val_sub_pullV_lt {g g' h : GL (Fin n) (AfE F E)} {p q : DecoF E n ST SG Q}
    (hg : IsPtOf hc g p) (hh : IsPtOf hc h q) {P : HeightOneSpectrum (𝓞 E)} (i : Fin n)
    (hP : ∀ y ∈ p.deco.1.N, Valued.v (adAt F P (GlobalTheory.Mem.Col2.pullV g y i - GlobalTheory.Mem.Col2.pullV g' y i)) < 1)
    {x : Sp E n} (hx : x ∈ q.deco.1.N) :
    Valued.v (adAt F P (GlobalTheory.Mem.Col2.pullV h x i - GlobalTheory.Mem.Col2.pullV (h * (g⁻¹ * g')) x i)) < 1 := by
  have hu : GlobalTheory.Mem.Col2.pullV h x ∈ Formalism.L2.Herm.hatL (F := F) (stdLat E n) :=
    (hh.lat _).1 (Submodule.subset_span ⟨x, hx, rfl⟩)
  have hz : (g : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ GlobalTheory.Mem.Col2.pullV h x ∈ Formalism.L2.Herm.hatL (F := F) p.deco.1.N := by
    refine (hg.lat _).2 ?_
    rwa [← pullV_eq_of_mul]
  have := val_sub_lt_of_hatL _ _ P i (fun y hy => hP y hy) hz
  rwa [← pullV_eq_of_mul, ← pullV_mul_stab] at this

theorem isPtOf_mul_stab : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))), ∀ (g g' h : GL (Fin n) (AfE F E)) (p q : DecoF E n ST SG Q), IsPtOf hc g p → IsPtOf hc g' p → IsPtOf hc h q → IsPtOf hc (h * (g⁻¹ * g')) q := by
  intro F E _ _ _ _ _ _ hc n ST SG Q g g' h p q hg hg' hh
  refine ⟨mul_mem hh.uni (mul_mem (inv_mem hg.uni) hg'.uni), fun x => ?_, fun P x hx i hi => ?_, fun w x hx i => ?_,
    fun P i j => ?_⟩
  · have e : (((h * (g⁻¹ * g'))⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ x =
        ((g'⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
          ((g : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
            (((h⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ x)) := by
      simp only [Matrix.mulVec_mulVec, ← Units.val_mul, _root_.mul_inv_rev, inv_inv, mul_assoc]
    rw [e, hh.lat x, ← hg'.lat, hg.lat, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
  · refine hasRes_of_sub (hh.f P x hx i hi) ?_
    rw [← map_sub]
    refine val_sub_pullV_lt hg hh i (fun y hy => ?_) hx
    rw [map_sub]
    exact val_sub_lt_of_hasRes (hg.f P y hy i hi) (hg'.f P y hy i hi)
  · refine hasRes_of_sub (hh.be w x hx i) ?_
    rw [← map_sub]
    refine val_sub_pullV_lt hg hh i (fun y hy => ?_) hx
    rw [map_sub]
    exact val_sub_lt_of_hasRes (hg.be w y hy i) (hg'.be w y hy i)
  · have hgg : (g : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F P.1) =
        (g' : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F P.1) := by
      ext a b
      simp only [Matrix.map_apply]
      rw [hg.fr, hg'.fr]
    have hs : (((g⁻¹ * g' : GL (Fin n) (AfE F E))) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F P.1) = 1 := by
      rw [Units.val_mul, Matrix.map_mul, ← hgg, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.map_one _ (map_zero _) (map_one _)]
    have e : adAt F P.1 (((h * (g⁻¹ * g') : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j) =
        ((((h * (g⁻¹ * g') : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E))).map (adAt F P.1)) i j := rfl
    rw [e, Units.val_mul, Matrix.map_mul, hs, mul_one, Matrix.map_apply]
    exact hh.fr P i j

end GlobalTheory.Mem.Col2.PtStab

end
end

