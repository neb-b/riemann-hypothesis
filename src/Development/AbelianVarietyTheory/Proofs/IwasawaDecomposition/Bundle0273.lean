module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1085
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHermPosChainRealEndSpaceTuple
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0226
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0250
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecompositionGroupLocalGaloisIso
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothAdmissibleUnitaryMemSupIsotypicParts
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeMarkingAdmissible
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef

theorem mulVec_congr {A : Type} [CommRing A] {n N : ℕ} (P Q : Matrix (Fin n) (Fin n) A) {x y w : Fin n → A}
    (e : x - Q *ᵥ y = N • w) : P *ᵥ x - (P * Q) *ᵥ y = N • P *ᵥ w := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_sub, e, Matrix.mulVec_smul]

theorem latW_rfl {D : D7} {W : HSp D} (L : Lt D.host.E W.rank) : latW (T := W) rfl L = L := rfl

section

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {W : HSp D}
  {ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)} {h : GA D W}

theorem markAd_rfl (l : Level H) (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) :
    MarkAd (T := W) rfl l ι h mk ↔ ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ w ∈ latGHat W h,
      finVec W (mk a) - (finHom W h).1 *ᵥ (finVec W (ι a)) = l.M • w := Iff.rfl

theorem finVec_add' (a b : Fin W.rank → D.host.E) : finVec W (a + b) = finVec W a + finVec W b :=
  GlobalTheory.AdLat.cap_fv_add D.host.F a b

theorem finVec_nsmul' (n : ℕ) (a : Fin W.rank → D.host.E) : finVec W (n • a) = n • finVec W a :=
  GlobalTheory.AdLat.cap_fv_nsmul D.host.F n a

theorem finVec_sub' (a b : Fin W.rank → D.host.E) : finVec W (a - b) = finVec W a - finVec W b :=
  funext fun _ => TensorProduct.tmul_sub _ _ _

theorem markOver_of_markAd {l l₂ : Level H} (hM : l.M ∣ l₂.M) (hI : Mfr l₂ ≤ Mfr l)
    {mk mk₂ : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)} (h1 : MarkAd (T := W) rfl l ι h mk)
    (h2 : MarkAd (T := W) rfl l₂ ι h mk₂) : MarkOver l l₂ (latG W h) mk mk₂ := by
  intro a ha
  have hM0 : l.M ≠ 0 := by have := l.three_le; omega
  obtain ⟨c, hc⟩ := hM
  obtain ⟨w, hw, e⟩ := (markAd_rfl l mk).1 h1 a (Submodule.smul_mono_left hI ha)
  obtain ⟨w', hw', e'⟩ := (markAd_rfl l₂ mk₂).1 h2 a ha
  obtain ⟨u, hu, eu⟩ := GlobalTheory.MarkCoset.finVec_div W l.M hM0 (mk₂ a - mk a) (c • w' - w)
    ((finVec_sub' _ _).trans (GlobalTheory.AdMark.sub_congr hc e e'))
  refine ⟨u, ((GlobalTheory.MarkCoset.latG_spec D W h).1 u).2 (hu ▸ sub_mem (nsmul_mem hw' c) hw), ?_⟩
  rw [← eu]
  abel

theorem finHom_mulVec_finVec {δ : GA D W} {ga : GL (Fin W.rank) D.host.E}
    (hδ : Formalism.L2.Theta.mt W δ = (ga : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (incA D))
    (v : Fin W.rank → D.host.E) : (finHom W δ).1 *ᵥ finVec W v = finVec W (ga.1 *ᵥ v) := by
  funext i
  have hf : ∀ i j, (finHom W δ).1 i j = (1 : Af D.host.F) ⊗ₜ ga.1 i j := fun i j => by
    have he' : (matHom W δ).1 i j = (1 : AF D.host.F) ⊗ₜ ga.1 i j := congrFun (congrFun hδ i) j
    change Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) ((matHom W δ).1 i j) = _
    rw [he', Algebra.TensorProduct.map_tmul, map_one]
    rfl
  simp only [Matrix.mulVec, dotProduct, hf, finVec, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one,
    TensorProduct.tmul_sum]

theorem mem_latGHat_mul (δ : GA D W) (z : Fin W.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    (finHom W δ).1 *ᵥ z ∈ latGHat W (δ * h) ↔ z ∈ latGHat W h := by
  rw [(GlobalTheory.MarkCoset.latG_spec D W h).2, (GlobalTheory.MarkCoset.latG_spec D W (δ * h)).2]
  refine exists_congr fun y => and_congr_right fun _ => ?_
  rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec]
  refine ⟨fun e => ?_, fun e => by rw [e]⟩
  have := congrArg (fun v => ((finHom W δ)⁻¹).1 *ᵥ v) e
  simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Units.inv_mul_cancel_left] at this
  exact this

end

theorem markAd_laws : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (W : HSp D) (r : ℕ) (hr : W.rank = r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)), LatEmb W ι → ∀ (h : GA D W) (L : Lt D.host.E r), latW hr L = latG W h → ∀ l : Level H, (∃ mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E), (∀ a, mk a ∈ L) ∧ MarkAd hr l ι h mk) ∧ ∀ mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E), (∀ a, mk a ∈ L) → MarkAd hr l ι h mk → IsMark l L mk ∧ (∀ mk' : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E), (∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ u ∈ L, mk' a = mk a + l.M • u) → MarkAd hr l ι h mk') ∧ (∀ l₂ : Level H, l.M ∣ l₂.M → Mfr l₂ ≤ Mfr l → ∀ mk₂ : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E), (∀ a, mk₂ a ∈ L) → MarkAd hr l₂ ι h mk₂ → MarkOver l l₂ L mk mk₂) ∧ ∀ (δ : GA D W) (ga : GL (Fin r) D.host.E), Formalism.L2.Theta.mt W δ = ((ga : Matrix (Fin r) (Fin r) D.host.E).submatrix (Fin.cast hr) (Fin.cast hr)).map (incA D) → latW hr (mapL ga L) = latG W (δ * h) ∧ MarkAd hr l ι (δ * h) (mvMap ga mk) := by
  intro D H Dw W r hr ι hι h L hL l
  subst hr
  rw [latW_rfl] at hL
  subst hL
  obtain ⟨mk₀, hm0, ha0, -⟩ := GlobalTheory.AdMark.exists_marking D H Dw l l W _ rfl ι hι dvd_rfl le_rfl h
  rw [GlobalTheory.AdMark.latR_rfl] at hm0
  replace ha0 : MarkAd (T := W) rfl l ι h mk₀ := ha0
  refine ⟨⟨mk₀, hm0.mem, ha0⟩, fun mk hmem hmk => ⟨?_, ?_, ?_, ?_⟩⟩
  · have ho := markOver_of_markAd dvd_rfl le_rfl hmk ha0
    refine ⟨hmem, ?_, fun v hv => ?_⟩
    · rintro a ha ⟨u, hu, e⟩
      obtain ⟨u', hu', e'⟩ := ho a ha
      exact hm0.inj a ha ⟨u + u', add_mem hu hu', by rw [e', e, smul_add]⟩
    · obtain ⟨a, ha, u, hu, e⟩ := hm0.surj v hv
      obtain ⟨u', hu', e'⟩ := ho a ha
      exact ⟨a, ha, u' + u, add_mem hu' hu, by rw [e, e', smul_add, add_assoc]⟩
  · intro mk' hc
    refine (markAd_rfl l mk').2 fun a ha => ?_
    obtain ⟨u, hu, e⟩ := hc a ha
    obtain ⟨w, hw, e'⟩ := (markAd_rfl l mk).1 hmk a ha
    refine ⟨w + finVec W u, add_mem hw (((GlobalTheory.MarkCoset.latG_spec D W h).1 u).1 hu), ?_⟩
    rw [e, finVec_add', finVec_nsmul', smul_add, ← e']
    abel
  · intro l₂ hM hI mk₂ _ h2
    exact markOver_of_markAd hM hI hmk h2
  · intro δ ga hδ
    have hf := finHom_mulVec_finVec (δ := δ) (ga := ga) hδ
    constructor
    · rw [latW_rfl]
      ext v
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine ((GlobalTheory.MarkCoset.latG_spec D W (δ * h)).1 _).2 ?_
        change finVec W (ga.1 *ᵥ x) ∈ _
        rw [← hf, mem_latGHat_mul]
        exact ((GlobalTheory.MarkCoset.latG_spec D W h).1 _).1 hx
      · intro hv
        have hri : ga.1 *ᵥ ((ga⁻¹).1 *ᵥ v) = v := by
          rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
        refine ⟨(ga⁻¹).1 *ᵥ v, ((GlobalTheory.MarkCoset.latG_spec D W h).1 _).2 ?_, hri⟩
        rw [← mem_latGHat_mul δ, hf, hri]
        exact ((GlobalTheory.MarkCoset.latG_spec D W (δ * h)).1 _).1 hv
    · refine (markAd_rfl l _).2 fun a ha => ?_
      obtain ⟨w, hw, e⟩ := (markAd_rfl l mk).1 hmk a ha
      refine ⟨_, (mem_latGHat_mul δ w).2 hw, ?_⟩
      change finVec W (ga.1 *ᵥ mk a) - _ = _
      rw [← hf, map_mul, Units.val_mul]
      exact mulVec_congr _ _ e

end GlobalTheory.OneMapRef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open Formalism.L2.Host (HChar atFin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.LevTwist

theorem conjP_ne {R : Ranks} (H : Formalism.BasicNotions.Host R) {P : HeightOneSpectrum (𝓞 H.E)} (h : IsSplitPl H P) : conjPrime₂ P ≠ P := by
  intro e
  obtain ⟨x, hx, hy⟩ := h
  have hc : IsConjPl H P P := (isConjPl_iff H P P).2 e.symm
  have e1 : ((cO H.E x : 𝓞 H.E) : H.E) = H.conj (x : H.E) := bridge_star_holds R H x
  exact hy _ e1 ((hc x _ e1).1 hx)

variable {B : Base} {X : PreX B.toPre} {I : ColIn B X}

theorem under_sel (h : I.Ok) (v : HeightOneSpectrum (𝓞 B.host.F)) : (I.sel v).under (𝓞 B.host.F) = v :=
  HeightOneSpectrum.ext (h.sel_ok v)

theorem good_of_mem (h : I.Ok) {P : HeightOneSpectrum (𝓞 B.host.E)} (hP : P ∈ I.SQ) :
    I.sel (P.under (𝓞 B.host.F)) = P ∧ GoodPl B.host.E I.S (P.under (𝓞 B.host.F)) := by
  obtain ⟨a, ha⟩ := I.mem_SQ.1 hP
  obtain ⟨v, -, rfl, hg⟩ := I.exists_of_mem_Q ha
  rw [under_sel h]
  exact ⟨rfl, hg⟩

theorem plc_mem (h : I.Ok) {P : HeightOneSpectrum (𝓞 B.host.E)} (hP : P ∈ (B.primes X).vGs) :
    Formalism.EigenvalueLevelCeiling.plc (P.under (𝓞 B.host.F)) ∈ I.S := by
  classical
  have hPr := (GlobalTheory.BasePrimes.primes_ok B X).1
  have h0 : ∀ i, B.fields.conjO ((B.primes X).piG i) ≠ 0 := fun i h => by
    have := hPr.piG_norm i
    rw [h, mul_zero] at this
    exact (hPr.g_prime i).ne_zero (Nat.cast_eq_zero.1 this.symm)
  have hm : ∃ i, B.fields.conjO ((B.primes X).piG i) ∈ P.asIdeal := by
    unfold Primes.vGs Primes.vG at hP
    simpa only [Finset.mem_union, mem_divs (h0 _), Fin.exists_fin_two] using hP
  obtain ⟨i, hi⟩ := hm
  have h1 : ((B.primes X).g i : 𝓞 B.fields.E) ∈ P.asIdeal := by
    rw [← hPr.piG_norm i]; exact Ideal.mul_mem_left _ _ hi
  rw [(ReadTwist.plc_under_eq_iff (F := B.host.F) P (hPr.g_prime i)).2 h1]
  exact h.g_mem i

theorem levOk_twists : ∀ (B : Base) (X : PreX B.toPre) (I : ColIn B X), I.Ok → LevOk B.host (B.primes X).vGs I.SQ ∧ Disjoint (B.primes X).vGs I.SQ ∧ ∀ a, KDq B.host (I.Q a) ≤ ((I.xi a).1.comp (finPartI B.host.E)).ker ∧ (I.xi a).IsUnitary := by
  classical
  intro B X I h
  have hb := levOk_base B X
  have hu : ∀ P : HeightOneSpectrum (𝓞 B.host.E), (conjPrime₂ P).under (𝓞 B.host.F) = P.under (𝓞 B.host.F) := fun P =>
    (under_eq_iff B.host P _).2 (Or.inr rfl)
  refine ⟨⟨hb.cover, fun P hP hP' => ?_⟩, Finset.disjoint_left.2 fun P h1 h2 => (good_of_mem h h2).2.2.2 (plc_mem h h1),
    fun a => ?_⟩
  · simp only [Finset.mem_union] at hP hP'
    rcases hP with hP | hP <;> rcases hP' with hP' | hP'
    · exact hb.split P (by simpa using hP) (by simpa using hP')
    · refine (good_of_mem h hP').2.2.2 ?_
      rw [hu]
      exact plc_mem h hP
    · refine (good_of_mem h hP).2.2.2 ?_
      rw [← hu]
      exact plc_mem h hP'
    · have e := (good_of_mem h hP').1
      rw [hu, (good_of_mem h hP).1] at e
      exact conjP_ne B.host ((GoodPlace.goodPl_under_iff _ B.host _ P).1 (good_of_mem h hP).2).1 e.symm
  · obtain ⟨⟨⟨n, hn, ho⟩, hT, hta, -⟩, hq, -⟩ :=
      ReadTwist.isTwist_of_reads B.R B.host B.LL B.embLL I.S (I.tup a) (I.xi a) (h.xi_reads a)
    refine ⟨KDq_le_ker_of_tame _ hT hta fun w hw => by_contra fun hr => hw (Or.inr ?_), fun x => ?_⟩
    · have hfin : (Qprime (I.tup a : Chr B.fields.F B.fields.E B.fields.K)).Finite :=
        ((UnrAe.finite_ramified (I.xi a)).image (·.under (𝓞 B.host.F))).subset fun v hv => by
          obtain ⟨P, e, hP⟩ := (hq v).1 hv
          exact ⟨P, hP, e⟩
      have hmem : I.sel (w.under (𝓞 B.host.F)) ∈ I.Q a := by
        unfold ColIn.Q QE
        rw [dite_eq_left hfin]
        convert Finset.mem_image_of_mem I.sel (hfin.mem_toFinset.2 ((hq _).2 ⟨w, rfl, hr⟩))
      rcases (under_eq_iff B.host _ w).1 (under_sel h _).symm with e | e
      · exact Or.inl (e ▸ hmem)
      · exact Or.inr ⟨_, hmem, (isConjPl_iff B.host _ _).2 e⟩
    · have h1 : (I.xi a).1 x ^ n = 1 := congrArg (fun χ : Formalism.L2.Host.HChar B.host.E => χ.1 x) ho
      have h2 : ‖(((I.xi a).1 x : ℂˣ) : ℂ)‖ ^ n = 1 := by
        rw [← norm_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, norm_one]
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h2

end GlobalTheory.Mem.LevTwist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftHilbertModelInjectiveContainsGoodForms
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.LiftHilbertModel

open Formalism.IndefR.Mult GlobalTheory.HilbertLevels

theorem hasPeterssonInner_smul_measure' {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (μ : Measure (GA D V))
    (𝓕 : Set (GA D V)) {T T' : MMap M} {c : ℂ} {a : ℝ} (ha : 0 ≤ a) (h : IsMultIP M μ 𝓕 T T' c) :
    IsMultIP M (ENNReal.ofReal a • μ) 𝓕 T T' ((a : ℂ) * c) := by
  intro v v'
  obtain ⟨h1, h2⟩ := h v v'
  refine ⟨?_, ?_⟩
  · unfold IntegrableOn at h1 ⊢
    rw [Measure.restrict_smul]
    exact h1.smul_measure ENNReal.ofReal_ne_top
  · rw [Measure.restrict_smul, integral_smul_measure, h2, ENNReal.toReal_ofReal ha, Complex.real_smul, mul_assoc]

theorem ipM_smul_measure {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (μ : Measure (GA D V))
    (𝓕 : Set (GA D V)) {T T' : MMap M} {a : ℝ} (ha : 0 ≤ a) (hne : ∀ τ, ∃ w : M.sm τ, w ≠ 0)
    (h : ∃ c, IsMultIP M μ 𝓕 T T' c) :
    ipM M (ENNReal.ofReal a • μ) 𝓕 T T' = (a : ℂ) * ipM M μ 𝓕 T T' := by
  choose w hw using hne
  have hv0 : ∏ τ, ⟪(w τ : M.H τ), (w τ : M.H τ)⟫_ℂ ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ _ => inner_self_ne_zero.2 fun h => hw τ (Submodule.coe_eq_zero.1 h)
  have h1 := hasPeterssonInner_smul_measure' M μ 𝓕 ha (ipM_spec M μ 𝓕 T T' h)
  exact hasPeterssonInner_unique M _ 𝓕 T T' w hv0 (ipM_spec M _ 𝓕 T T' ⟨_, h1⟩) h1

theorem mult_mono {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : Formalism.IndefR.Datum.InfFam D) (M : DSModel V S) {J J' : Set (GA D V)}
    {χ χ' : GA D V → ℂ} (h : ∀ k ∈ J', k ∈ J ∧ χ k = χ' k) : Mult θ M J χ ≤ Mult θ M J' χ' :=
  Submodule.span_mono fun _ hX =>
    ⟨hX.aut, hX.cusp, fun v k hk g => (h k hk).2 ▸ hX.lev v k (h k hk).1 g, hX.equiv, hX.cont⟩

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

theorem wat_le_wall (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (P : LevelP R.Pg D.R.r ℂ) : R.Wat i σ P ≤ R.Wall i σ :=
  le_trans inf_le_left (mult_mono R.θ (R.MW i σ) (levS_mono fun x hx =>
    lev_datY_triv D.R.r D.R.t 0 (r_le_rank_Wc i) R.Pg ∅ P (fun _ _ => 1) (fun _ => 1) x hx))

theorem model_facts (hI : Inputs D) (hM : R.IsModels) (y : Hd R) (i : Fin D.R.m) :
    Function.Injective (R.HW i (sg0 D A)).e ∧
      R.Wat i (sg0 D A) (R.levL F false (sg0 D A)) ≤ LinearMap.range (R.HW i (sg0 D A)).e ∧
      ∀ u v, (y.L F).ipWc i (PiTensorProduct.lift ((R.HW i (sg0 D A)).e u)) (PiTensorProduct.lift ((R.HW i (sg0 D A)).e v)) =
        (((RealDat.nP F false)⁻¹ : ℝ) : ℂ) * ⟪u, v⟫_ℂ := by
  obtain ⟨h1, h2, h3⟩ := hM.HW i (sg0 D A)
  refine ⟨h1, h2 ▸ wat_le_wall R i _ _, fun u v => ?_⟩
  have h0 := hM.νW i
  have hu : (R.HW i (sg0 D A)).e u ∈ R.Wall i (sg0 D A) := h2 ▸ LinearMap.mem_range_self _ u
  have hv : (R.HW i (sg0 D A)).e v ∈ R.Wall i (sg0 D A) := h2 ▸ LinearMap.mem_range_self _ v
  have hs := ipM_smul_measure (R.MW i (sg0 D A)) (R.νW i) (R.fdW i) (inv_pos.2 (nP_pos F false)).le
    (hI.sm _ _ _) (hI.schur _ (D.sp.W_sig _) _ R.θ _ _ _ _ _ hM.inf h0.1.1 h0.2 _ hu _ hv)
  have e : (y.L F).ipWc i (PiTensorProduct.lift ((R.HW i (sg0 D A)).e u)) (PiTensorProduct.lift ((R.HW i (sg0 D A)).e v)) =
      (∏ ρ, ((dimK _ _ (kapAt (Wc D i) (sg0 D A) ρ) : ℚ) : ℂ)) *
        ipMT (R.MW i (sg0 D A)) (ENNReal.ofReal (RealDat.nP F false)⁻¹ • R.νW i) (R.fdW i)
          (PiTensorProduct.lift ((R.HW i (sg0 D A)).e u)) (PiTensorProduct.lift ((R.HW i (sg0 D A)).e v)) := rfl
  rw [e, h3, ipMT, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, hs, ipAt, mul_left_comm]

end

theorem hilbert_model_lift : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), (∀ o : D.what₂.O, ∃ k : Ks, algebraMap Ks D.what₂.LL k = D.what₂.OtoLL o) → Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat) (i : Fin D.R.m), Function.Injective (R.toRealDat.HW i (sg0 D A3.A)).e ∧ R.toRealDat.Wat i (sg0 D A3.A) (R.toRealDat.levL F.lv2 false (sg0 D A3.A)) ≤ LinearMap.range (R.toRealDat.HW i (sg0 D A3.A)).e ∧ ∀ u v, (y.L F.lv2).ipWc i (PiTensorProduct.lift ((R.toRealDat.HW i (sg0 D A3.A)).e u)) (PiTensorProduct.lift ((R.toRealDat.HW i (sg0 D A3.A)).e v)) = (((RealDat.nP F.lv2 false)⁻¹ : ℝ) : ℂ) * ⟪u, v⟫_ℂ := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG _ hI hP _ y i
  exact model_facts R.toRealDat F.lv2 hI hP.char.base.models y i

end GlobalTheory.LiftHilbertModel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftLabelPartFinrankEqRowsPartFinrank
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

namespace GlobalTheory.Mem.R3.LamDim

theorem finrank_twSub (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (V : Submodule ℂ E) :
    Module.finrank ℂ (Tw.sub s V) = Module.finrank ℂ V := by
  let j : V ≃+ Tw.sub s V :=
    { toFun := fun x => ⟨Tw.mk s (x : E), x.2⟩
      invFun := fun y => ⟨Tw.out (y : Tw s E), y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  have hi : Function.Bijective (cj s) :=
    ⟨fun a b h => by simpa [cj_cj] using congrArg (cj s) h, fun z => ⟨cj s z, cj_cj s z⟩⟩
  have h := rank_eq_of_equiv_equiv (cj s) j hi (fun r m => by
    apply Subtype.ext
    show r • (m : E) = cj s (cj s r) • (m : E)
    rw [cj_cj])
  unfold Module.finrank
  rw [h]

theorem twSub_inf (s : Bool) {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (V W : Submodule ℂ E) :
    Tw.sub s (V ⊓ W) = Tw.sub s V ⊓ Tw.sub s W := by
  ext x; exact Iff.rfl

theorem finrank_comap_of_inj {M E : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup E] [Module ℂ E]
    (f : M →ₗ[ℂ] E) (hf : Function.Injective f) (S : Submodule ℂ E) :
    Module.finrank ℂ (S.comap f) = Module.finrank ℂ (S ⊓ LinearMap.range f : Submodule ℂ E) := by
  rw [LinearEquiv.finrank_eq (Submodule.equivMapOfInjective f hf (S.comap f)), Submodule.map_comap_eq, inf_comm]

end GlobalTheory.Mem.R3.LamDim


open GlobalTheory.Mem.R3.LamDim in
set_option maxHeartbeats 2000000 in
theorem GlobalTheory.Mem.R3.finrank_liftLabel_eq_finrank_face3 : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ (i : Fin D.R.m) (p : A3.fam3.base3.Ix), Module.finrank ℂ ((R.Wp3 i p).comap (Y.mj.eW i)) = Module.finrank D.what₂.LL ((s0Of R F).Ep p) := by
  intro _ _ _ _ D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH _ i p
  set s := twAt D.what₂.embLL A3.A.v0 with hs

  have hinj : Function.Injective (Y.mj.eW i) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 := Y.mj.eW_norm i x
    rw [hx, norm_zero, zero_pow two_ne_zero] at h1
    have hn : (0 : ℝ) < RealDat.nP F.lv2 false := RealDat.nP_pos (F := F.lv2) false
    have h2 : ‖x‖ ^ 2 = 0 := by
      rcases mul_eq_zero.1 h1.symm with h | h
      · exact absurd h hn.ne'
      · exact h
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)

  have hrg : LinearMap.range (Y.mj.eW i) = R.toRealDat.WS F.lv2 false i (sg0 D A3.A) := by
    rw [Y.mj.eW_range i, hH.aux.levelW false i (sg0 D A3.A)]

  have hw : LinearMap.range ((R.toCx3 F).w0C false i) = Tw.sub s (R.toRealDat.WS F.lv2 false i (sg0 D A3.A)) := by
    apply le_antisymm
    · rintro _ ⟨y, rfl⟩
      show ((Real.sqrt (RealDat.nP F.lv2 false) : ℝ) : ℂ) •
        (show R.toRealDat.WS F.lv2 false i (sg0 D A3.A) from (R.toCx3 F).wC false i A3.fam3.base3.v0 y).1 ∈ _
      exact Submodule.smul_mem (R.toRealDat.WS F.lv2 false i (sg0 D A3.A)) _
        (show R.toRealDat.WS F.lv2 false i (sg0 D A3.A) from (R.toCx3 F).wC false i A3.fam3.base3.v0 y).2
    · intro x hx
      have hle : R.toRealDat.WS F.lv2 false i (sg0 D A3.A) ≤
          Submodule.comap (Tw.mkL s (R.HW i (sg0 D A3.A)).H) (LinearMap.range ((R.toCx3 F).w0C false i)) := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨k, rfl⟩
        exact GlobalTheory.TwParts.mk_bC_mem_range R F i k
      exact hle hx
  have hD := hH.prim.dimParts i p
  have hR := complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim
  have key := CxData.finrank_Ep (R.toCx3 F) F.cr false (hR.wf false) (hR.what₂ false).1 (hR.rowHyp false).h3
    (hR.partsE false) p
  have key2 : Module.finrank D.what₂.LL ((s0Of R F).Ep p) =
      Module.finrank ℂ ((R.toCx3 F).EEp p ⊓ (R.toCx3 F).EEl false : Submodule ℂ (R.toCx3 F).EE) := key
  rw [key2, ← hD, finrank_comap_of_inj _ hinj, hrg, hw]
  show _ = Module.finrank ℂ (Tw.sub s (R.Wp3 i p) ⊓ Tw.sub s (R.toRealDat.WS F.lv2 false i (sg0 D A3.A)) : Submodule ℂ _)
  rw [← twSub_inf, finrank_twSub]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MinpolyIrreducibleLocalEmbedding
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocIrred

theorem minpoly_map_adicCompletion_irreducible : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)), IsPlaceOver A v → (∀ σ : G K Ω, ∃ τ ∈ Dec (F := K) A, ∀ x : L, τ (algebraMap L Ω x) = σ (algebraMap L Ω x)) → ∀ ι : Ω →ₐ[K] Kbar v, IsLocEmb A v ι → ∀ α : L, Irreducible ((minpoly K α).map (algebraMap K (v.adicCompletion K))) := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ A v hA hdec ι hι α
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  haveI : Normal K Ω := IsAlgClosure.normal K Ω
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  set a : Ω := algebraMap L Ω α with ha
  have hPa : minpoly K a = minpoly K α := by
    have := minpoly.algHom_eq (IsScalarTower.toAlgHom K L Ω) (algebraMap L Ω).injective α
    simpa [ha] using this
  rw [← hPa]
  have haint : IsIntegral K a := (Algebra.IsAlgebraic.isAlgebraic a).isIntegral
  set P := minpoly K a with hP
  have hsep : P.Separable := (minpoly.irreducible haint).separable
  set β := ι a with hβdef
  have hβ : IsIntegral (v.adicCompletion K) β := Algebra.IsIntegral.isIntegral β
  set Q := minpoly (v.adicCompletion K) β with hQ
  have hQdvd : Q ∣ P.map (algebraMap K (v.adicCompletion K)) := by
    apply minpoly.dvd
    rw [Polynomial.aeval_map_algebraMap, hβdef, Polynomial.aeval_algHom_apply, hP, minpoly.aeval, map_zero]
  obtain ⟨θ, -, -, hlift⟩ := GlobalTheory.LocDec.decomposition_mulEquiv_galLoc K Ω A v hA ι hι
  set R := (P.map (algebraMap K Ω)).roots with hR
  have hRcard : Multiset.card R = P.natDegree :=
    by
    rw [hR, IsAlgClosed.card_roots_eq_natDegree, Polynomial.natDegree_map]
  have hRnd : R.Nodup := Polynomial.nodup_roots (hsep.map)
  have hSnd : (R.map ι).Nodup := hRnd.map ι.injective
  have hQ0 : Q ≠ 0 := minpoly.ne_zero hβ
  have hsub : R.map ι ≤ (Q.map (algebraMap (v.adicCompletion K) (Kbar v))).roots := by
    rw [Multiset.le_iff_subset hSnd]
    intro y hy
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hy
    have hr0 : Polynomial.aeval r P = 0 := by
      have := (Polynomial.mem_roots_map (minpoly.ne_zero haint)).mp hr
      rwa [Polynomial.aeval_def]
    obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root' haint.isAlgebraic hr0
    obtain ⟨τ, hτ, hτσ⟩ := hdec σ
    have hg : θ ⟨τ, hτ⟩ β = ι r := by
      rw [hβdef, hlift ⟨τ, hτ⟩ a, ← hσ]
      exact congrArg ι (hτσ α)
    rw [Polynomial.mem_roots_map hQ0, ← Polynomial.aeval_def, ← hg, Polynomial.aeval_algEquiv,
      AlgHom.comp_apply, hQ, minpoly.aeval, map_zero]
  have hdeg : P.natDegree ≤ Q.natDegree := by
    calc P.natDegree = Multiset.card (R.map ι) := by rw [Multiset.card_map, hRcard]
      _ ≤ Multiset.card (Q.map (algebraMap (v.adicCompletion K) (Kbar v))).roots := Multiset.card_le_card hsub
      _ ≤ (Q.map (algebraMap (v.adicCompletion K) (Kbar v))).natDegree := Polynomial.card_roots' _
      _ = Q.natDegree := Polynomial.natDegree_map _
  have heq : P.map (algebraMap K (v.adicCompletion K)) = Q :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hβ) ((minpoly.monic haint).map _) hQdvd
      (by rw [Polynomial.natDegree_map]; exact hdeg)
  rw [heq]
  exact minpoly.irreducible hβ

end GlobalTheory.LocIrred
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothAdmissibleUnitaryMemSupIsotypicPartsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_admissible_unitary_mem_sup_isotypic_parts : ∀ (D : D7) (n : ℕ) (A : Type) [AddCommGroup A] [Module ℂ A] (ρ : Formalism.AUTREP.GAf D.host.E n →* Module.End ℂ A) (C : Submodule ℂ A) (B : A → A → ℂ), (∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, ∀ c : ℂ, B x (y + c • z) = B x y + c * B x z) → (∀ x ∈ C, ∀ y ∈ C, B x y = starRingEnd ℂ (B y x)) → (∀ x ∈ C, x ≠ 0 → 0 < (B x x).re) → (∀ h, ∀ x ∈ C, ρ h x ∈ C) → (∀ h, ∀ x ∈ C, ∀ y ∈ C, B (ρ h x) (ρ h y) = B x y) → (∀ N : ℕ, 0 < N → FiniteDimensional ℂ ↥(Submodule.span ℂ {x | x ∈ C ∧ ∀ κ, Formalism.L2.NG.Cong D.host.E n N κ → ρ κ x = x})) → (∀ x ∈ C, ∃ N : ℕ, 0 < N ∧ ∀ κ, Formalism.L2.NG.Cong D.host.E n N κ → ρ κ x = x) → ∀ x ∈ C, x ∈ ⨆ π : Formalism.L2.NG.FinTyp D.host.E n, principalLevelFrame.isotIn (D := D) ρ C π := by
  first | exact @GlobalTheory.SpanIsot.span_isotIn | exact GlobalTheory.SpanIsot.span_isotIn | (intros; apply GlobalTheory.SpanIsot.span_isotIn <;> assumption)
end

