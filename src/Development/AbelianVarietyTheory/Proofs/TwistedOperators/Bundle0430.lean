module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0423
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0215
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0202
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1548
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1283
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1256
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorBasisChangeEqSubstitution
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1183
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1516
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0210
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousThetaTransformAdelicSchwartz

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCompactMeetsBesselTopRationalOrbits
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Mi.SepPer (contLeft)

namespace GlobalTheory.BesCover

open GlobalTheory.Per GlobalTheory.Per.Inhab

theorem exists_compact_cover {D : D7} {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} {ρ : ℕ}
    {e : Matrix (Fin B.rank) (Fin ρ) D.host.E} (he : IsIsoSub B e) (hι : HSpace.IsIsomEmb A B ι) (hA : IsAniso A)
    (hnorm : ∀ δ γ, EmbRel B A ι δ γ → ∀ n ∈ NFlag B e, δ * n * δ⁻¹ ∈ NFlag B e)
    {t : GA D A → GA D B} (ht : ∀ h, EmbRel B A ι (t h) h) :
    ∃ Ω : Set (GA D B), IsCompact Ω ∧ ∀ (h : GA D A) (n : NFlag B e), ∃ γ ∈ GQ B, γ * ((n : GA D B) * t h) ∈ Ω := by
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.Mem.AnisoQuotient.exists_compact D A hA
  obtain ⟨K', hK', hcov'⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D B _ _ he).1
  obtain ⟨s, hc, hs, hq⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D B A ι hι
  obtain ⟨-, -, -, -, _, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  obtain rfl : t = s := funext fun h => (hs h _).1 (ht h)
  refine ⟨(fun q : GA D A × NFlag B e => (q.2 : GA D B) * s q.1) '' (K ×ˢ K'),
    (hK.prod hK').image ((continuous_subtype_val.comp continuous_snd).mul (hc.comp continuous_fst)), fun g n => ?_⟩
  obtain ⟨γ, hγ, k, hk, rfl⟩ := hcov g
  obtain ⟨γ', hγ', k', hk', e⟩ := hcov' ⟨_, hnorm _ γ⁻¹ ((hs _ _).2 rfl) n n.2⟩
  have e' : s γ⁻¹ * n * (s γ⁻¹)⁻¹ = (γ' : GA D B) * k' := congrArg Subtype.val e
  have e1 : (n : GA D B) = s γ * (γ' * k') * (s γ)⁻¹ := by
    rw [← e']; simp only [map_inv, inv_inv, mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
  refine ⟨(s γ * γ')⁻¹, inv_mem (mul_mem (hq γ hγ) hγ'), (k, k'), ⟨hk, hk'⟩, ?_⟩
  rw [e1]
  simp only [map_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left]

theorem bplus_cover : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G), M.IsRow →
    ∃ Ω : Set (GA D (G.V (.grid D.R.m 0))), IsCompact Ω ∧ ∀ (h : GA D (G.V (.top 0))) (n : NFlag (G.V (.grid D.R.m 0)) G.besTop.e),
      ∃ γ ∈ GQ (G.V (.grid D.R.m 0)), γ * ((n : GA D (G.V (.grid D.R.m 0))) * embTop G h) ∈ Ω := by
  intro D T L sc G W M _
  have hV := G.isV (X := .top 0) (Nat.zero_le _) (fun j e => by cases e)
  have hA : IsAniso (G.V (.top 0)) := GlobalTheory.Per.isAniso_of_posDef hV.sigOK fun τ => by
    rw [hV.sig τ, hV.rank]; simp [Node.neg]
  have hι := (G.rowDec 0 (by have := D.R.two_le_m; omega)).isom
  have hs : ∀ h, EmbRel _ _ (G.rowDec 0 (by have := D.R.two_le_m; omega)).ι (embTop G h) h :=
    fun h => (embRel_iff _ h _).2 rfl
  exact exists_compact_cover G.besTop.e_iso hι hA
    (fun δ γ h n hn => (GlobalTheory.BesselChar.besChar_conj W.ψ G.besTop δ γ h n hn).1) hs

end GlobalTheory.BesCover
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEqMulOfResSNeOne
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx GlobalTheory.Chain
open IsDedekindDomain NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IdemRes

theorem exists_pow_eq_span {E : Type} [Field E] [NumberField E] (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) :
    ∃ h : ℕ, 0 < h ∧ ∃ x : 𝓞 E, I ^ h = Ideal.span {x} := by
  have hm : I ∈ nonZeroDivisors (Ideal (𝓞 E)) := mem_nonZeroDivisors_of_ne_zero hI
  refine ⟨Fintype.card (ClassGroup (𝓞 E)), Fintype.card_pos, ?_⟩
  have h1 : ClassGroup.mk0 (⟨I, hm⟩ ^ Fintype.card (ClassGroup (𝓞 E))) = 1 := by
    rw [map_pow, pow_card_eq_one]
  have h2 := (ClassGroup.mk0_eq_one_iff (pow_mem hm (Fintype.card (ClassGroup (𝓞 E))))).1 h1
  exact ⟨_, h2.span_singleton_generator.symm⟩

theorem exists_eq_mul_of_resS_ne_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : Formalism.L2.DIV.Pl E) (ε : Formalism.L2.Herm.intAf F E) (hε : ε * ε = ε) (h : Formalism.L2.DIV.resS F P ε ≠ 1) :
    ∃ x ∈ P.asIdeal, x ≠ 0 ∧ ∃ s : Formalism.L2.Herm.intAf F E, ε = s * Formalism.L2.DIV.oToS F E x := by
  have := P.isPrime
  have h0 : Formalism.L2.DIV.resS F P ε = 0 := by
    have h1 : Formalism.L2.DIV.resS F P ε * (Formalism.L2.DIV.resS F P ε - 1) = 0 := by
      rw [mul_sub, ← map_mul, hε, mul_one, sub_self]
    exact (mul_eq_zero.1 h1).resolve_right (sub_ne_zero.2 h)
  have hm : ε ∈ Formalism.L2.DIV.idS F P.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact (map_eq_zero_iff _ (RingEquiv.ofBijective (Formalism.L2.DIV.cmpS F P.asIdeal)
      (Formalism.L2.DIV.cmpS_bij (F := F) P.asIdeal P.ne_bot)).symm.injective).1 h0
  obtain ⟨n, hn, x, hx⟩ := exists_pow_eq_span P.asIdeal P.ne_bot
  have hp := Ideal.pow_mem_pow hm n
  have hi : ε ^ n = ε := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    exact IsIdempotentElem.pow_succ_eq m hε
  rw [hi, Formalism.L2.DIV.idS, ← Ideal.map_pow, hx, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hp
  obtain ⟨s, hs⟩ := hp
  refine ⟨x, Ideal.pow_le_self hn.ne' (hx ▸ Ideal.mem_span_singleton_self x), ?_, s, hs.symm⟩
  rintro rfl
  rw [Ideal.span_singleton_eq_bot.2 rfl] at hx
  exact P.ne_bot (pow_eq_zero_iff hn.ne' |>.1 hx)

theorem toEAf_mem_of_finPart {D : D7} {w : AE D} (hw : finPart D w ∈ intAE D) :
    toEAf D w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  change Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E (finPart D w) ∈ _
  generalize finPart D w = z at hw
  induction hw using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, rfl⟩ := hy
    exact GlobalTheory.PlaceDatum.tmul_mem_int ⟨x, rfl⟩ ha
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha

theorem resS_idem_eq_one : ∀ (D : D7) (e : AE D) (P : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e P →
    ∃ h : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, Formalism.L2.DIV.resS D.host.F P ⟨toEAf D e, h⟩ = 1 := by
  intro D e P he
  have h1 : e * e = e := he.1.1
  have hint : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    toEAf_mem_of_finPart (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, h1]))
  refine ⟨hint, ?_⟩
  by_contra hne
  obtain ⟨x, hxP, hx0, s, hs⟩ := exists_eq_mul_of_resS_ne_one P ⟨toEAf D e, hint⟩
    (Subtype.ext (by change toEAf D e * toEAf D e = toEAf D e; rw [← RingHom.map_mul, h1])) hne
  have hs' : toEAf D e = (s : Formalism.IndefR.Datum.EAf D) * eToEAf D (x : D.host.E) := congrArg Subtype.val hs
  refine (he.2 x hx0).1 hxP (GlobalTheory.PlaceDatum.finPart_mem_of_toEAf ?_)
  have hx0' : (x : D.host.E) ≠ 0 := fun h => hx0 (RingOfIntegers.coe_eq_zero_iff.1 h)
  have h2 : toEAf D (incA D ((x : D.host.E)⁻¹)) = eToEAf D ((x : D.host.E)⁻¹) := rfl
  rw [RingHom.map_mul, h2, hs', mul_assoc, ← RingHom.map_mul, mul_inv_cancel₀ hx0', RingHom.map_one, mul_one]
  exact s.2

end GlobalTheory.IdemRes

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralInverseAtSplitPlacesOfUnits
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.LocalInvIdem

theorem toEAf_surj {D : D7} (a : EAf D) : ∃ α : AE D, toEAf D α = a := by
  induction a using TensorProduct.induction_on with
  | zero => exact ⟨0, RingHom.map_zero _⟩
  | add x y hx hy =>
    obtain ⟨p, hp⟩ := hx
    obtain ⟨q, hq⟩ := hy
    exact ⟨p + q, by rw [RingHom.map_add (f := _), hp, hq]⟩
  | tmul x y => exact ⟨pairA D.host.F 0 y ⊗ₜ[D.host.F] x, rfl⟩

theorem inv_of_chart {D : D7} {ePP α : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v}
    (hC : GlobalTheory.SplitHecke.Chart ePP v π) {c : Fv D.host.F v} (hc : π α = c) (hv1 : Valued.v c = 1) :
    ∃ γ : AE D, finPart D γ ∈ intAE D ∧ α * γ = ePP := by
  have hc0 : c ≠ 0 := by
    intro h; rw [h, map_zero] at hv1; exact zero_ne_one hv1
  obtain ⟨t, ht⟩ := hC.1 c⁻¹
  refine ⟨ePP * t, ?_, ?_⟩
  · refine (hC.2.2.2 t).2 (GlobalTheory.SplitHecke.isInt_Ov.2 ?_)
    rw [ht, HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv1, inv_one]
  · have h1 : π (α * t - 1) = 0 := by
      rw [map_sub, map_mul, ht, hc, mul_inv_cancel₀ hc0, map_one, sub_self]
    have h2 := (hC.2.1 _).1 h1
    linear_combination h2

theorem exists_local_inv {D : D7} {PP : Pl D.host.E} {ePP : AE D} (hPP : Formalism.L2.NTheta.IsIdemAt ePP PP)
    (α : AE D) (ha : toEAf D α ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (hu : IsUnit (Formalism.L2.DIV.resS D.host.F PP ⟨toEAf D α, ha⟩)) :
    ∃ γ : AE D, finPart D γ ∈ intAE D ∧ α * γ = ePP := by
  obtain ⟨v, τ, hIdem, hP⟩ := GlobalTheory.SplitIdemDict.exists_emb hPP
  have hProj := (GlobalTheory.SplitIdemDict.isProjAt_iff τ PP).2 hP
  obtain ⟨⟨r, -, hr0, -, hrS⟩, -⟩ := GlobalTheory.PlaceRed.red_dict D v (splitProj τ) PP hProj
  obtain ⟨hC, hE, -⟩ := GlobalTheory.SplitProjChart.chart_rdA D v (splitProj τ) ePP hIdem
  obtain ⟨hmem, hrr⟩ := hrS (toEAf D α) ha
  obtain ⟨c, hc⟩ : ∃ c, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA (splitProj τ) α = c := ⟨_, rfl⟩
  have hcE := (hE α).trans hc
  have : Nontrivial (Formalism.L2.DIV.kP PP) := Ideal.Quotient.nontrivial_iff.2 PP.isPrime.ne_top
  have hv1 : Valued.v c = 1 := by
    have hle : Valued.v c ≤ 1 := by
      rw [← hcE]; exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 hmem
    refine le_antisymm hle (not_lt.1 fun hlt => hu.ne_zero ?_)
    rw [← hrr]
    refine (hr0 _).2 ?_
    exact (congrArg Valued.v hcE).trans_lt hlt
  exact inv_of_chart hC hc hv1

theorem exists_inv : ∀ {D : D7} (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z → ∀ (a : EAf D) (ha : a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), (∀ PP ∈ Z, IsUnit (Formalism.L2.DIV.resS D.host.F PP ⟨a, ha⟩)) → ∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, a * w * toEAf D e = toEAf D e := by
  intro D Z e he a ha hZ
  obtain ⟨α, rfl⟩ := toEAf_surj a
  obtain ⟨es, hes, hsum⟩ := he.1
  have key : ∀ PP ∈ Z, ∃ γ : AE D, finPart D γ ∈ intAE D ∧ α * γ = es PP :=
    fun PP hPP => exists_local_inv (hes PP hPP) α ha (hZ PP hPP)
  choose! γ hγ1 hγ2 using key
  refine ⟨toEAf D (∑ PP ∈ Z, γ PP), GlobalTheory.IdemIntegral.toEAf_mem_of_finPart ?_, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sum (finPart D)]; exact sum_mem fun PP hPP => hγ1 PP hPP
  · have hαw : α * ∑ PP ∈ Z, γ PP = e := by
      rw [Finset.mul_sum, hsum]; exact Finset.sum_congr rfl fun PP hPP => hγ2 PP hPP
    have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
    rw [← map_mul, ← map_mul, hαw, hee]

end GlobalTheory.LocalInvIdem
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockPolynomialTmulSchwartzBruhatMemAlgebraicData
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix

noncomputable section

namespace GlobalTheory.SquareAgree

theorem pureA_mem_algD : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w), M.IsGood ψ →
    ∀ f ∈ M.Pol ψ τ, ∀ g ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F),
      GlobalTheory.WeilM.pureA F f g ∈ GlobalTheory.SquareAgree.algD M ψ τ := by
  intro F E _ _ _ _ _ σ n d X W M ψ τ hM f hf g hg
  obtain ⟨m, c, φ, hφSB, hφstd, hgeq⟩ := GlobalTheory.EvAdm.exists_sum_finprod hg
  have hφvac : ∀ k, ∀ᶠ v in Filter.cofinite, φ k v = M.vac v := fun k =>
    ((hφstd k).and hM.std).mono fun v h => h.1.trans h.2.symm
  have h1 : GlobalTheory.WeilM.pureA F (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) g =
      ∑ k, c k • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (φ k) := by
    rw [hgeq]
    funext x
    simp only [GlobalTheory.WeilM.pureA, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
    rw [mul_left_comm]
    rfl
  rw [h1]
  exact Submodule.sum_mem _ fun k _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨f, φ k, hf, hφSB k, hφvac k, rfl⟩)

end GlobalTheory.SquareAgree

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorNegSpaceFrameChangeConjSubst
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockNegSubst

open MvPolynomial

theorem map_conj_substF {ι : Type} {N n : ℕ} (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ)
    (P : MvPolynomial (ι × Fin N × Fin n) ℂ) :
    MvPolynomial.map (starRingEnd ℂ) (GlobalTheory.CompactHowe.substF h g P) =
      GlobalTheory.CompactHowe.substF (fun τ => (h τ).map (starRingEnd ℂ)) (fun τ => (g τ).map (starRingEnd ℂ))
        (MvPolynomial.map (starRingEnd ℂ) P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp only [GlobalTheory.CompactHowe.substF, MvPolynomial.aeval_C, MvPolynomial.map_C, MvPolynomial.algebraMap_eq,
      Algebra.algebraMap_self, RingHom.id_apply]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
  | mul_X p v hp =>
    rw [map_mul (GlobalTheory.CompactHowe.substF h g), map_mul (MvPolynomial.map (starRingEnd ℂ)), hp,
      map_mul (MvPolynomial.map (starRingEnd ℂ)), map_mul, MvPolynomial.map_X, GlobalTheory.CompactHowe.substF_X,
      GlobalTheory.CompactHowe.substF_X]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X, Matrix.map_apply]

theorem map_conj_conj {σ : Type} (P : MvPolynomial σ ℂ) :
    MvPolynomial.map (starRingEnd ℂ) (MvPolynomial.map (starRingEnd ℂ) P) = P := by
  rw [MvPolynomial.map_map]
  have e : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ := RingHom.ext fun z => Complex.conj_conj z
  rw [e, MvPolynomial.map_id]

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem pureTensorO_negSp_map_conj {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (f : WO (GlobalTheory.ChiGrid.negSp S) T → ℂ) (Q : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    pureTensorO ψ θ (GlobalTheory.ChiGrid.negSp S) T (fun _ => -1) (fun _ => 1) BS BT f (MvPolynomial.map (starRingEnd ℂ) Q) =
      fun x => starRingEnd ℂ (pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) BS BT
        (fun w => starRingEnd ℂ (f w)) Q x) := by
  funext x
  induction Q using MvPolynomial.induction_on' with
  | monomial k a =>
    have hm := GlobalTheory.FockConj.pureTensorO_negSp_monomial ψ θ S T (fun _ => 1) (fun _ => 1) BS BT f hψ hθ k x
    have e1 : (MvPolynomial.monomial k a : MvPolynomial (FVar D T.rank S.rank) ℂ) = a • MvPolynomial.monomial k 1 := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    have e2 : MvPolynomial.map (starRingEnd ℂ) (MvPolynomial.monomial k a : MvPolynomial (FVar D T.rank S.rank) ℂ) =
        (starRingEnd ℂ a) • MvPolynomial.monomial k 1 := by
      rw [MvPolynomial.map_monomial, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [e2, e1, map_smul, map_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, ← hm]
  | add p q hp hq =>
    rw [map_add (f := _), map_add (f := _), map_add (f := _), Pi.add_apply, Pi.add_apply, hp, hq, map_add (f := _)]

end GlobalTheory.FockNegSubst

namespace GlobalTheory.FockNegSubst

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem pureTensorO_negSp_subst : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (BS u : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT v : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO (GlobalTheory.ChiGrid.negSp S) T → ℂ), IsThetaFunO ψ (GlobalTheory.ChiGrid.negSp S) T f → ∀ P : MvPolynomial (FVar D T.rank S.rank) ℂ, pureTensorO ψ θ (GlobalTheory.ChiGrid.negSp S) T (fun _ => -1) (fun _ => 1) (fun τ => BS τ * u τ) (fun τ => BT τ * v τ) f P = pureTensorO ψ θ (GlobalTheory.ChiGrid.negSp S) T (fun _ => -1) (fun _ => 1) BS BT f (GlobalTheory.CompactHowe.substF (fun τ => (v τ).map (starRingEnd ℂ)) (fun τ => (((u τ)⁻¹)ᵀ).map (starRingEnd ℂ)) P) := by
  intro D ψ θ S T hψ hθ BS u BT v f hf P
  have hf' : IsThetaFunO ψ S T (fun w => starRingEnd ℂ (f w)) := GlobalTheory.CjNeg.theta_negS' hψ hf
  rw [← map_conj_conj P,
    pureTensorO_negSp_map_conj ψ θ S T hψ hθ (fun τ => BS τ * u τ) (fun τ => BT τ * v τ) f
      (MvPolynomial.map (starRingEnd ℂ) P),
    GlobalTheory.FockBaseChange.pureTensorO_subst D ψ θ S T hψ hθ BS u BT v _ hf' (MvPolynomial.map (starRingEnd ℂ) P),
    ← map_conj_substF, pureTensorO_negSp_map_conj ψ θ S T hψ hθ BS BT f]

end GlobalTheory.FockNegSubst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrChInv
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AvgCol

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def frRel (W : G.Weil) {U : Set T} (N : Std G U) (X : Node) (τ : D.what₂.Tau) :
    Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ :=
  (W.onb X τ)⁻¹ * N.frC X τ

def frCh (W : G.Weil) {U : Set T} (N : Std G U) (j : ℕ) :
    PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank →ₐ[ℂ] PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank :=
  GlobalTheory.CompactHowe.substF (fun τ => frRel W N (.top (j + 1)) τ) (fun τ => ((frRel W N (.top j) τ)⁻¹)ᵀ)

def frChInv (W : G.Weil) {U : Set T} (N : Std G U) (j : ℕ) :
    PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank →ₐ[ℂ] PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank :=
  GlobalTheory.CompactHowe.substF (fun τ => (frRel W N (.top (j + 1)) τ)⁻¹) (fun τ => (frRel W N (.top j) τ)ᵀ)

end GlobalTheory.AvgCol

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameAdjointPartAtMovedRationalPointRow
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftDat

theorem frMapAdj_partAt_actO_finW : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (ΛT : Lt D.host.E T.rank), IsSelfDualC T ΛT → IsAA C.X.Λ ΛT → ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)), Formalism.L2.DIV.IsFrame βS (stdL D.host.E S.rank) → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), Pg.Nonempty → (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ e : AE D, IsIdemSum e (Pg ∪ Q) → ∀ (a : AE D) (k₀ : GA D S), (∃ b : AE D, a * b = e) → GlobalTheory.LiftLevel.IsMover S T βS βT e a k₀ → GlobalTheory.LiftLevel.IsGen C βS βT Pg Q e a → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊤ → GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊥ → IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q)) → IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (Ideal.span {2}) → ∀ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E, frMapAdj S T βS βT (GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T y))) = Matrix.of fun i j => GlobalTheory.LiftDat.rowAdj T βT a e (y i) 0 j := by
  intro D S T C hn ΛT hsd hAA βS βT hfS hfT Pg Q ξ hPg h2 e he a k₀ hab hmov hgen h1 h2' h3 h4 y
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hcc : cA D e * cA D e = cA D e := by rw [← map_mul, hee]
  have hp : ∀ (c : AE D) (z : WO S T), GlobalTheory.LiftLevel.partAt c z = c • z := fun c z => by
    ext i j; simp [GlobalTheory.LiftLevel.partAt, smul_eq_mul]
  have hcomm : GlobalTheory.LiftLevel.partAt (cA D e) (actO S T k₀ 1 (finW S T y)) =
      actO S T k₀ 1 (GlobalTheory.LiftLevel.partAt (cA D e) (finW S T y)) := by
    rw [hp, hp]
    show _ = HMul.hMul (HMul.hMul (mt T 1) ((cA D e • finW S T y : WO S T) : Matrix (Fin T.rank) (Fin S.rank) (AE D))) (mt S k₀⁻¹)
    rw [Matrix.mul_smul, Matrix.smul_mul]
    rfl
  have hx : IsHalf (cA D e) (GlobalTheory.LiftLevel.partAt (cA D e) (finW S T y)) := fun i j => by
    simp only [GlobalTheory.LiftLevel.partAt, Matrix.map_apply, ← mul_assoc, hcc]
  rw [hcomm, hmov.2.2 _ hx]
  unfold GlobalTheory.LiftLevel.adjA frMapAdj
  rw [C.m.gS]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  have hi : ((1 : Matrix (Fin S.rank) (Fin S.rank) D.host.E)⁻¹).map (incA D) = 1 := by
    rw [inv_one]; exact Matrix.map_one (incA D) (map_zero _) (map_one _)
  rw [hi, Matrix.one_mul]
  ext i j
  simp only [rowAdj, Matrix.smul_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, Matrix.transpose_apply,
    GlobalTheory.LiftLevel.partAt, finW]

end GlobalTheory.LiftDat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsDatumLinear
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

namespace GlobalTheory.SquareAgree

theorem isDatum_linear : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ {Z : Type} (crd : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Z), IsDatum M ψ crd 0 0 ∧ ∀ (Φ Φ' : (Fin n × Fin d → AF F) → ℂ) (f f' : Z → ℂ) (c : ℂ), IsDatum M ψ crd Φ f → IsDatum M ψ crd Φ' f' → IsDatum M ψ crd (Φ + c • Φ') (f + c • f') := by
  intro F E _ _ _ _ _ σ n d Y Wd M ψ hψ Z crd
  have hn : ∀ x, ‖ψ x‖ = 1 := GlobalTheory.StdCharFromIsStd.norm_psi hψ
  refine ⟨⟨Submodule.zero_mem _, fun u => ?_⟩, fun Φ Φ' f f' c h h' =>
    ⟨Submodule.add_mem _ h.1 (Submodule.smul_mem _ c h'.1), fun u => ?_⟩⟩
  · have e : M.co.rho ψ u (0 : (Fin n × Fin d → AF F) → ℂ) = 0 := funext fun x => by
      simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]
    rw [e]
    simp [GlobalTheory.WeilM.thetaSum]
  · have s1 : Summable fun ξ : Fin n × Fin d → F => M.co.rho ψ u Φ (fun i => algebraMap F (AF F) (ξ i)) :=
      (GlobalTheory.ThetaTrCont.schA_cont F ψ hψ.1 hn h.1).1 (M.co.e u)
    have s2 : Summable fun ξ : Fin n × Fin d → F => M.co.rho ψ u Φ' (fun i => algebraMap F (AF F) (ξ i)) :=
      (GlobalTheory.ThetaTrCont.schA_cont F ψ hψ.1 hn h'.1).1 (M.co.e u)
    have e : M.co.rho ψ u (Φ + c • Φ') = M.co.rho ψ u Φ + c • M.co.rho ψ u Φ' := funext fun x => by
      simp only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← h.2 u, ← h'.2 u]
    unfold GlobalTheory.WeilM.thetaSum
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [s1.tsum_add (s2.mul_left c), tsum_mul_left]

end GlobalTheory.SquareAgree
end

