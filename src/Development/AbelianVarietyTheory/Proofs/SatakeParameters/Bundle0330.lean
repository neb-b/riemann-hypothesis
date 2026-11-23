module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0030
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0029
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.GramLevelZeroEqReindex
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ChiFinOfGlevH
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BaseLatticeSelfDualOfLocalEq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0317
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0323
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0244
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0286
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0324
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FirstCoupledKernelEquivariantCosets
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0267
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0275
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0327
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAdelicLatticeTupleDecomposition
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelB

theorem dec_exists : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → Nonempty (Dec J std)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD
  classical
  refine ⟨{ gam := fun j hj La => if h : ((sysS H X std).Pj j).IsLatTup La.2 then Classical.choose (hD j hj La h).2.1 else 1,
            kap := fun j hj La => if h : ((sysS H X std).Pj j).IsLatTup La.2 then
              Classical.choose (Classical.choose_spec (hD j hj La h).2.1).2 else 1,
            mem := ?_, eq := ?_ }⟩
  · intro j hj La
    by_cases h : ((sysS H X std).Pj j).IsLatTup La.2
    · rw [dif_pos h]
      exact (Classical.choose_spec (hD j hj La h).2.1).1
    · rw [dite_eq_right h]
      exact Subgroup.one_mem _
  · intro j hj La h
    simp only [dif_pos h]
    exact Classical.choose_spec (Classical.choose_spec (hD j hj La h).2.1).2

end GlobalTheory.TwV.DelB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsComparisonSiteDataOverChainCharts
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SiteEx


set_option maxHeartbeats 4000000 in
theorem siteD_exists : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (μ : D.what₂.Tup) (J : JIn t u μ), (D.what₂.places.resChar w) ∉ Dx.Qp μ → ∃ Z : SiteD J.Gd.herm u w hg (ex.tw.fm u μ), Z.Fo = foOf J.Hh J.St J.val ∧ SiteGood Z ∧ SiteRest Z ex.cmp ∧ ∀ i hi, Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E (Z.S i hi).B = (J.A.crd (i + 1) hi)⁻¹ := by
  intro D L hT Gi Gl Kc Dx cX ex t u w hg μ J hQ
  have hfr := GlobalTheory.Ggeo.FracLocal.isFractionRing_gat Gl u w hg
  have hrat := GlobalTheory.TwUChiRat.chiRatAll_of_adTie t u μ J.St J.A J.Hh.dt J.a J.tie J.kin
  have hpT : ∀ i (hi : i ≤ D.R.m), ¬ D.what₂.places.resChar w ∣ (J.St i hi).T := fun i hi => by
    rw [J.tie.T_eq i hi]; exact hg.2.2.2.2.2
  have hψ : ∀ i hi, PsiEx (foOf J.Hh J.St J.val i hi) (ex.cmp.embW u w hg) := fun i hi =>
    psiEx_of (foOf J.Hh J.St J.val i hi) (ex.cmp.embW u w hg) hfr (fun β => hrat (i + 1) hi β)
      (fun β => J.ord (i + 1) hi β)
  let Z : SiteD J.Gd.herm u w hg (ex.tw.fm u μ) :=
    { Fo := foOf J.Hh J.St J.val
      chFin := fun i hi => J.fin (i + 1) hi
      S := fun i hi =>
        { B := (Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E).symm (J.A.crd (i + 1) hi)⁻¹
          B_lat := fun β => _root_.GlobalTheory.BaseAtCompan.isBaseAt_inv_of_latCo J.Gd.herm u w hg hi ((J.St (i + 1) hi).K β).lev (J.A.crd (i + 1) hi) J.a
            (hpT (i + 1) hi) (J.base (i + 1) hi β)
          ψ := fun β => (hψ i hi β).choose
          fin := fun β => fin_of _ β _ } }
  refine ⟨Z, rfl, ⟨fun i hi => hpT (i + 1) hi, fun i hi w' hw' => ?_, fun i hi => trivial⟩, ⟨fun i hi => ?_, fun i hi β => ?_, fun i hi β cl => ?_⟩,
    fun i hi => ?_⟩
  · exact GlobalTheory.TwU.not_mem_underSB_of_gIdx t u w hg μ hQ w' (J.tie.bad (i + 1) hi w' hw')
  · show cT (sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E
        ((Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E).symm (J.A.crd (i + 1) hi)⁻¹)).1 * gramN D (i + 1) hi *
      (Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E
        ((Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E).symm (J.A.crd (i + 1) hi)⁻¹)).1 = 1
    rw [MulEquiv.apply_symm_apply]
    exact std_of_C _ _ _ (J.pins.crd_orth (i + 1) hi)
  · exact (hψ i hi β).choose_spec
  · exact chRat_ofChiD J.chiD _ _ _
  · show Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E
        ((Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E).symm (J.A.crd (i + 1) hi)⁻¹) = _
    exact MulEquiv.apply_symm_apply _ _

end GlobalTheory.SiteEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsH90EqOneOffOfNormOneAtSplitPlace
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

namespace GlobalTheory.TwV.Xc.Unif

theorem exists_h90_eq_oneOff_of_normOne_at_split_place : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (w : HeightOneSpectrum (𝓞 F)) (spl : E ⊗[F] w.adicCompletion F ≃+* w.adicCompletion F × w.adicCompletion F), (∀ x, spl (sigR σ (w.adicCompletion F) x) = swapR (w.adicCompletion F) (spl x)) → ∀ (π : (AfE F E)ˣ), π ∈ U1 σ → OneOff w π → ∃ x : (AfE F E)ˣ, h90 σ x = π ∧ OneOff w x := by
  intro F E _ _ _ _ _ σ w spl hsig π hπ hoff
  set p : E ⊗[F] w.adicCompletion F := prV (E := E) w (π : AfE F E) with hp
  have hπe : (π : AfE F E) = oneAt w p := ext_prV fun w' => by
    by_cases h : w' = w
    · subst h; rw [prV_oneAt_self]
    · rw [prV_oneAt_ne w w' h]; exact hoff w' h
  have hU : (π : AfE F E) * sigR σ (FiniteAdeleRing (𝓞 F) F) (π : AfE F E) = 1 := by
    have := congrArg (fun u : (AfE F E)ˣ => (u : AfE F E)) ((MonoidHom.mem_ker).1 hπ)
    simpa [conjId] using this
  have hp1 : p * sigR σ (w.adicCompletion F) p = 1 := by
    have h2 := congrArg (prV (E := E) w) hU
    rw [hπe, sigR_oneAt, oneAt_mul, prV_oneAt_self, map_one] at h2
    exact h2
  have hab : (spl p).1 * (spl p).2 = 1 ∧ (spl p).2 * (spl p).1 = 1 := by
    have h3 := congrArg spl hp1
    rw [map_mul, hsig, map_one] at h3
    exact ⟨congrArg Prod.fst h3, congrArg Prod.snd h3⟩
  let c : (E ⊗[F] w.adicCompletion F)ˣ :=
    ⟨spl.symm ((spl p).1, 1), spl.symm ((spl p).2, 1),
      by rw [← map_mul]; apply spl.injective; rw [RingEquiv.apply_symm_apply, map_one]; exact Prod.ext hab.1 (mul_one _),
      by rw [← map_mul]; apply spl.injective; rw [RingEquiv.apply_symm_apply, map_one]; exact Prod.ext hab.2 (mul_one _)⟩
  refine ⟨oneAtU w c, ?_, fun w' hw' => prV_oneAt_ne w w' hw' _⟩
  apply Units.ext
  have hval : ((h90 σ (oneAtU w c) : (AfE F E)ˣ) : AfE F E) =
      oneAt w (c : E ⊗[F] w.adicCompletion F) *
        sigR σ (FiniteAdeleRing (𝓞 F) F) (oneAt w ((c⁻¹ : (E ⊗[F] w.adicCompletion F)ˣ) : E ⊗[F] w.adicCompletion F)) := by
    simp only [h90, MonoidHom.div_apply, MonoidHom.id_apply, div_eq_mul_inv, Units.val_mul, conjId, map_inv]
    rfl
  rw [hval, sigR_oneAt, oneAt_mul, hπe]
  congr 1
  apply spl.injective
  rw [map_mul, hsig]
  show spl (spl.symm ((spl p).1, 1)) * swapR (w.adicCompletion F) (spl (spl.symm ((spl p).2, 1))) = spl p
  rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  show ((spl p).1 * 1, 1 * (spl p).2) = spl p
  rw [mul_one, one_mul]

end GlobalTheory.TwV.Xc.Unif
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNatCastCoprimeMemHeightOneSpectrum
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

namespace GlobalTheory

theorem natCast_mem_heightOneSpectrum_coprime :
    ∀ {E : Type} [Field E] [NumberField E] (p : ℕ), p.Prime → ∀ (P : HeightOneSpectrum (𝓞 E)), ((p : ℕ) : 𝓞 E) ∉ P.asIdeal → ∃ ℓ : ℕ, 0 < ℓ ∧ ((ℓ : ℕ) : 𝓞 E) ∈ P.asIdeal ∧ Nat.Coprime ℓ p := by
  intro E _ _ p hp P hpP
  have hN : Ideal.absNorm P.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact P.ne_bot
  haveI : P.asIdeal.IsPrime := P.isPrime
  have hmem : ∀ n : ℕ, ((n : 𝓞 E) ∈ P.asIdeal ↔ ringChar (𝓞 E ⧸ P.asIdeal) ∣ n) := by
    intro n
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact ringChar.spec _ n
  have hq0 : ringChar (𝓞 E ⧸ P.asIdeal) ≠ 0 := by
    intro h0
    have := (hmem _).1 (Ideal.absNorm_mem P.asIdeal)
    rw [h0, zero_dvd_iff] at this
    exact hN this
  have hqp : (ringChar (𝓞 E ⧸ P.asIdeal)).Prime :=
    (CharP.char_is_prime_or_zero (𝓞 E ⧸ P.asIdeal) _).resolve_right hq0
  refine ⟨ringChar (𝓞 E ⧸ P.asIdeal), hqp.pos, (hmem _).2 dvd_rfl, ?_⟩
  refine (Nat.coprime_primes hqp hp).2 ?_
  intro hq
  exact hpP ((hmem p).2 (hq ▸ dvd_rfl))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNatMulDivPowMemIntegralFiniteAdele
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

set_option maxHeartbeats 800000

namespace GlobalTheory.DivInt
open GlobalTheory.AdeleBaseChange Formalism.UG.P

theorem exists_nat_mul_div_pow_mem : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (w : HeightOneSpectrum (𝓞 F)) (z : AfE F E), (∀ w', w' ≠ w → prV (E := E) w' z = 0) → ∀ (ℓ : ℕ), ((ℓ : ℕ) : 𝓞 F) ∉ w.asIdeal → ∃ D : ℕ, 0 < D ∧ ∀ n : ℕ, (((D : E) / (ℓ : E) ^ n) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) * z ∈ RInt F E := by
  intro F E _ _ _ _ _ w z hz ℓ hℓ
  obtain ⟨ι, hι⟩ := exists_toAd F E
  obtain ⟨x, r, hr, hzr⟩ := exists_approx z
  obtain ⟨D, hD, hDx⟩ := exists_nat_mul_integral ({x} : Finset E)
  obtain ⟨o, ho⟩ := hDx x (Finset.mem_singleton_self x)
  have hDz : algebraMap E _ (D : E) * ι z ∈ intAd E := by
    rw [hzr, map_add (f := _), map_tmul_one hι, mul_add, ← map_mul, ← nsmul_eq_mul, ← ho]
    exact add_mem (algebraMap_int_mem o) (mul_mem (by
      rw [← map_natCast (algebraMap (𝓞 E) E)]; exact algebraMap_int_mem _) (map_mem_int hι hr))
  refine ⟨D, hD, fun n => mem_int_of_map hι ?_⟩
  intro P
  rw [map_mul, map_tmul_one hι]
  change algebraMap E (P.adicCompletion E) ((D : E) / (ℓ : E) ^ n) * ι z P ∈ P.adicCompletionIntegers E
  by_cases hP : P.under (𝓞 F) = w
  · have hv : Valued.v (algebraMap E (P.adicCompletion E) (ℓ : E)) = 1 := by
      rw [levelaf_valued_algebraMap, ← map_natCast (algebraMap (𝓞 E) E),
        HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
      intro hm
      apply hℓ
      rw [← hP, HeightOneSpectrum.under_asIdeal, Ideal.mem_comap, map_natCast]
      exact hm
    have h1 := hDz P
    change algebraMap E (P.adicCompletion E) (D : E) * ι z P ∈ P.adicCompletionIntegers E at h1
    have e : algebraMap E (P.adicCompletion E) ((D : E) / (ℓ : E) ^ n) * ι z P =
        (algebraMap E (P.adicCompletion E) (ℓ : E))⁻¹ ^ n *
          (algebraMap E (P.adicCompletion E) (D : E) * ι z P) := by
      rw [div_eq_mul_inv, map_mul, map_inv₀, map_pow, inv_pow]; ring
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h1 ⊢
    rw [e, map_mul, map_pow, map_inv₀, hv, inv_one, one_pow, one_mul]
    exact h1
  · have h0 : ι z P = 0 := (prV_eq_zero_iff hι (P.under (𝓞 F)) z).1 (hz _ hP) P rfl
    rw [h0, mul_zero]
    exact zero_mem _

end GlobalTheory.DivInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteAdeleIsoComponentZeroOfInfinitelyDivisible
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

theorem GlobalTheory.TwV.Xc.exists_pow_lt_of_lt_one_intZ (x γ : WithZero (Multiplicative ℤ)) (hx : x ≠ 0) (hγ : γ < 1) :
    ∃ n : ℕ, γ ^ n < x := by
  by_cases h0 : γ = 0
  · exact ⟨1, by simp [h0, zero_lt_iff.2 hx]⟩
  obtain ⟨a, rfl⟩ := WithZero.ne_zero_iff_exists.1 hx
  obtain ⟨g, rfl⟩ := WithZero.ne_zero_iff_exists.1 h0
  have hg : Multiplicative.toAdd g < 0 := by
    have : g < 1 := by exact_mod_cast hγ
    exact this
  refine ⟨(Multiplicative.toAdd a).natAbs + 1, ?_⟩
  rw [← WithZero.coe_pow, WithZero.coe_lt_coe]
  show Multiplicative.toAdd (g ^ ((Multiplicative.toAdd a).natAbs + 1)) < Multiplicative.toAdd a
  rw [toAdd_pow, nsmul_eq_mul]
  push_cast
  have h1 := neg_abs_le (Multiplicative.toAdd a)
  have h2 : Multiplicative.toAdd g ≤ -1 := by omega
  have h3 := abs_nonneg (Multiplicative.toAdd a)
  nlinarith

theorem GlobalTheory.TwV.Xc.adIso_comp_zero_of_div : ∀ {F E F' E' : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Field F'] [NumberField F'] [Field E'] [NumberField E'] [Algebra F' E'] (iE : E' ≃+* E) (iA : AfE F' E' ≃+* AfE F E), (∀ x : E', iA (x ⊗ₜ[F'] 1) = iE x ⊗ₜ[F] 1) → (∀ y, iA y ∈ RInt F E ↔ y ∈ RInt F' E') → ∀ (ι : AfE F' E' ≃+* FiniteAdeleRing (𝓞 E') E'), GlobalTheory.TwU.IsAdIso ι → ∀ (z : AfE F E) (ℓ D : ℕ), 0 < ℓ → 0 < D → (∀ n : ℕ, (((D : E) / (ℓ : E) ^ n) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) * z ∈ RInt F E) → ∀ (P : HeightOneSpectrum (𝓞 E')), ((ℓ : ℕ) : 𝓞 E') ∈ P.asIdeal → ι (iA.symm z) P = 0 := by
  intro F E F' E' _ _ _ _ _ _ _ _ _ _ iE iA hrat hint ι hι z ℓ D hℓ hD hdiv P hP
  set y := ι (iA.symm z) with hy

  have hc : ∀ n : ℕ, iA.symm (((D : E) / (ℓ : E) ^ n) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F))
      = ((D : E') / (ℓ : E') ^ n) ⊗ₜ[F'] (1 : FiniteAdeleRing (𝓞 F') F') := by
    intro n
    rw [RingEquiv.symm_apply_eq, hrat]
    simp [map_div₀, map_pow, map_natCast]
  have hbound : ∀ n : ℕ, Valued.v (((D : E') / (ℓ : E') ^ n : E') : P.adicCompletion E') * Valued.v (y P) ≤ 1 := by
    intro n
    have hmem := hdiv n
    have h1 : iA.symm ((((D : E) / (ℓ : E) ^ n) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) * z) ∈ RInt F' E' := by
      rw [← hint, RingEquiv.apply_symm_apply]; exact hmem
    have h2 := (hι.2 _).1 h1 P
    rw [map_mul, hc, map_mul, hι.1, ← hy] at h2
    rw [← map_mul]
    simpa using h2
  have hval : ∀ c : E', Valued.v ((c : E') : P.adicCompletion E') = P.valuation E' c :=
    fun c => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P c
  have hℓE : ((ℓ : 𝓞 E') : E') = (ℓ : E') := by simp
  have hlt : P.valuation E' (ℓ : E') < 1 := by
    rw [← hℓE]
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem P _).2 hP
  have hℓ0 : P.valuation E' (ℓ : E') ≠ 0 := by
    rw [Ne, map_eq_zero]; exact_mod_cast hℓ.ne'
  have hD0 : P.valuation E' (D : E') ≠ 0 := by
    rw [Ne, map_eq_zero]; exact_mod_cast hD.ne'
  by_contra hyP
  have hyv : Valued.v (y P) ≠ 0 := by
    rw [Ne, map_eq_zero]; exact hyP
  obtain ⟨n, hn⟩ := GlobalTheory.TwV.Xc.exists_pow_lt_of_lt_one_intZ
    (P.valuation E' (D : E') * Valued.v (y P)) (P.valuation E' (ℓ : E')) (mul_ne_zero hD0 hyv) hlt
  have hb := hbound n
  rw [hval, map_div₀, map_pow] at hb
  have hpos : (0 : WithZero (Multiplicative ℤ)) < P.valuation E' (ℓ : E') ^ n :=
    zero_lt_iff.2 (pow_ne_zero _ hℓ0)
  have : P.valuation E' (D : E') * Valued.v (y P) ≤ P.valuation E' (ℓ : E') ^ n := by
    have he : P.valuation E' (D : E') * Valued.v (y P)
        = P.valuation E' (D : E') / P.valuation E' (ℓ : E') ^ n * Valued.v (y P) * P.valuation E' (ℓ : E') ^ n := by
      rw [div_mul_eq_mul_div, div_mul_cancel₀ _ (pow_ne_zero _ hℓ0)]
    rw [he]
    simpa using mul_le_mul' hb (le_refl (P.valuation E' (ℓ : E') ^ n))
  exact absurd hn (not_lt.2 this)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDatumLevelEquivarianceAtMatrixSteps
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV


set_option maxHeartbeats 1000000 in
theorem levAt_mat : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    PtEx A a → MuLaw t u μ dtU → ∀ i hi, i < t.m2 → PtAway A a i hi → LevAt A dtU a i hi) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie hEx hMu i hi him _ β β' x x' x₁ x₁' κ κ' e1 e1' z
  have hm := m_eq t μ
  have hi0 : i < D.R.m := by omega
  have hi1 : i + 1 < D.R.m := by omega
  have H0 : (∃ p, IsPtAd A a i (Nat.le_of_succ_le hi) β x p) ∧ ∃ p', IsPtAd A a (i + 1) hi β' x' p' :=
    ⟨hEx _ _ _ _, hEx _ _ _ _⟩
  have H1 : (∃ p, IsPtAd A a i (Nat.le_of_succ_le hi) β x₁ p) ∧ ∃ p', IsPtAd A a (i + 1) hi β' x₁' p' :=
    ⟨hEx _ _ _ _, hEx _ _ _ _⟩
  unfold xiAd
  rw [dite_eq_left H0, dite_eq_left H1]
  have hp := H0.1.choose_spec
  have hp' := H0.2.choose_spec
  have hq := H1.1.choose_spec
  have hq' := H1.2.choose_spec
  generalize H0.1.choose = p at hp ⊢
  generalize H0.2.choose = p' at hp' ⊢
  generalize H1.1.choose = q at hq ⊢
  generalize H1.2.choose = q' at hq' ⊢
  unfold xiPt
  rw [dite_eq_left him, dite_eq_left him]
  obtain ⟨k, c, hk, hc, hχ, hd⟩ := GlobalTheory.T.levelMoved_point_frames_matrixSteps A dtU a hPin hTie i hi0 him.le β x x₁ κ e1 p q hp hq
  obtain ⟨k', c', hk', hc', hχ', hd'⟩ := GlobalTheory.T.levelMoved_point_frames_matrixSteps A dtU a hPin hTie (i + 1) hi1 him β' x' x₁' κ' e1' p' q' hp' hq'
  obtain ⟨hN, hf⟩ := _root_.GlobalTheory.TwV.LevDeco.ptAd_mul_lev_deco A dtU a hPin hTie i (Nat.le_of_succ_le hi) β x x₁ κ e1 p q hp hq
  obtain ⟨hN', hf'⟩ := _root_.GlobalTheory.TwV.LevDeco.ptAd_mul_lev_deco A dtU a hPin hTie (i + 1) hi β' x' x₁' κ' e1' p' q' hp' hq'
  obtain ⟨hmu, -⟩ := GlobalTheory.T.muCharacter_det_level_eq_local_tame_product A dtU a hPin hTie hMu i hi0 i (Nat.le_of_succ_le hi) β κ _ hd
  obtain ⟨-, hmu'⟩ := GlobalTheory.T.muCharacter_det_level_eq_local_tame_product A dtU a hPin hTie hMu i hi0 (i + 1) hi β' κ' _ hd'
  have core : ∀ W, muOf t u μ dtU (i + 1) (Matrix.GeneralLinearGroup.det κ'.1) * ((((St i (Nat.le_of_succ_le hi)).K β).lev.chi κ : ℂˣ) : ℂ) *
      t.seam.σ₀ (XiEntry t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) i (A.ib i hi β) (A.ib (i + 1) hi1 β') q q' W) =
      muOf t u μ dtU (i + 1) (Matrix.GeneralLinearGroup.det κ.1) * ((((St (i + 1) hi).K β').lev.chi κ' : ℂˣ) : ℂ) *
      t.seam.σ₀ (XiEntry t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) i (A.ib i hi β) (A.ib (i + 1) hi1 β') p p' W) := by
    intro W
    have e0 : phiT t.X.K q.deco.1 q'.deco.1 W = phiT t.X.K p.deco.1 p'.deco.1 W := by
      unfold phiT
      refine @if_congr _ _ _ (_) (_) _ _ _ _ ?_ rfl rfl
      simp only [Deco.at, hN, hN', hf, hf']
    have law := GlobalTheory.MatLaw.xiEntry_law hPin.fields.ok t.pr_ok hPin.sel (t.idx_ok μ) him
      (γ := 1) (γ' := 1) (p := p) (q := q) (p' := p') (q' := q') (κ := k) (κ' := k') (a := c) (a' := c')
      (fun P => by rw [hk P, OneMemClass.coe_one, one_mul]) (fun P => by rw [hk' P, OneMemClass.coe_one, one_mul]) hc hc' W
      (by exact e0)
    have hW : ((1 : UF t.X.E (D.R.N (i + 1))).1.toLinearMap ∘ₗ W ∘ₗ (1 : UF t.X.E (D.R.N i)).1.symm.toLinearMap) = W :=
      LinearMap.ext fun v => rfl
    rw [hW, Finset.prod_mul_distrib] at law
    have law' := congrArg t.seam.σ₀ law
    simp only [map_mul, Units.val_mul, Pi.inv_apply] at law'
    have hCC : t.seam.σ₀ (((∏ P, c P : t.X.Kˣ)) : t.X.K) * t.seam.σ₀ ((((∏ P, c P)⁻¹ : t.X.Kˣ)) : t.X.K) = 1 := by
      rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
    linear_combination (-(t.seam.σ₀ (∏ P, rhoT t.Ch t.sel (t.tup μ) i P ((LinearEquiv.det ((k' P)⁻¹).1 : t.X.Eˣ) : t.X.E)) *
        t.seam.σ₀ (((∏ P, c P : t.X.Kˣ)) : t.X.K) * t.seam.σ₀ (XiEntry t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) i (A.ib i hi β) (A.ib (i + 1) hi1 β') q q' W))) * hmu
      + (muOf t u μ dtU (i + 1) (Matrix.GeneralLinearGroup.det κ.1) * t.seam.σ₀ (((∏ P, c P : t.X.Kˣ)) : t.X.K)) * law'
      + (muOf t u μ dtU (i + 1) (Matrix.GeneralLinearGroup.det κ.1) * t.seam.σ₀ (((∏ P, c' P : t.X.Kˣ)) : t.X.K) *
        t.seam.σ₀ (XiEntry t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) i (A.ib i hi β) (A.ib (i + 1) hi1 β') p p' W)) * hCC
      + (((((St i (Nat.le_of_succ_le hi)).K β).lev.chi κ : ℂˣ) : ℂ) *
        t.seam.σ₀ (XiEntry t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) i (A.ib i hi β) (A.ib (i + 1) hi1 β') q q' W)) * hmu'
      + (t.seam.σ₀ (∏ P, rhoT t.Ch t.sel (t.tup μ) i P ((LinearEquiv.det ((k' P)⁻¹).1 : t.X.Eˣ) : t.X.E)) *
        t.seam.σ₀ (XiEntry t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) i (A.ib i hi β) (A.ib (i + 1) hi1 β') q q' W)) * hχ
      - (muOf t u μ dtU (i + 1) (Matrix.GeneralLinearGroup.det κ.1) *
        t.seam.σ₀ (XiEntry t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) i (A.ib i hi β) (A.ib (i + 1) hi1 β') p p' W)) * hχ'
  exact core _

end GlobalTheory.TwV

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FirstCoupledStepAdelicDatumLawTargetLevel
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

noncomputable section

namespace GlobalTheory.CplTarget

section Local

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}

theorem xiCpl1_moved (hX : X.Ok) (hPr : Pr.Ok) (hL : L.Ok Ch sel mu cst G m2) {u : Pr.Word} {al : L.β m2} {b : L.β (m2 + 1)}
    (p : ChPt (R := R) sel mu u m2) (p' q' : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1))))
    (κ : GLQ X.E (R.N (m2 + 1)) (rowSG Pr sel mu)) (c : rowSG Pr sel mu → X.Kˣ)
    (hfr : ∀ P, frsF sel mu q' P = frsF sel mu p' P * ((κ P)⁻¹).1)
    (hc : ∀ P, GlobalTheory.TopLaw.LevAt (L.levG (m2 + 1) b) (L.levQ (m2 + 1) b) P (κ P) (c P)) (x : HomE X.E (R.N m2) (R.N (m2 + 1)))
    (hphi : phiT X.K p.deco.1 q'.deco.1 x = phiT X.K p.deco.1 p'.deco.1 x) :
    XiCpl1 Ch sel mu cst L m2 al p q' Y x * ∏ P : rowSG Pr sel mu, rhoS Ch sel mu m2 P ((LinearEquiv.det (κ P).1 : X.Eˣ) : X.E) =
      ((∏ P, c P : X.Kˣ) : X.K) * XiCpl1 Ch sel mu cst L m2 al p p' Y x := by
  unfold XiCpl1
  rw [hphi, mul_assoc, mul_left_comm _ (phiT _ _ _ _), ← Finset.prod_mul_distrib, Units.coe_prod, ← Finset.prod_mul_distrib]
  refine congrArg _ (Finset.prod_congr rfl fun P _ => ?_)
  have e1 : inFr (frsF sel mu p P) (frsF sel mu q' P) x = (κ P).1.toLinearMap ∘ₗ inFr (frsF sel mu p P) (frsF sel mu p' P) x := by
    rw [hfr]
    refine LinearMap.ext fun w => ?_
    rfl
  have e2 : (frsF sel mu q' P).symm (repY Y) = (κ P).1 ((frsF sel mu p' P).symm (repY Y)) := by
    rw [hfr]
    rfl
  rw [e1, e2]
  exact GlobalTheory.CoupledLaw.psiAt_target hX hPr hL (hc P) (L.h m2 al P) _ _

end Local


set_option maxHeartbeats 1000000 in
theorem levAt_target : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a → MuLaw t u μ dtU → ∀ i hi, i = t.m2 → PtAway A a i hi →
  ∀ β β' (x : UA D i (Nat.le_of_succ_le hi)) (x' x₁' : UA D (i + 1) hi) (κ' : ((St (i + 1) hi).K β').lev.U) p p' p₁',
    x₁'.1 = x'.1 * κ'.1 → IsPtAd A a i (Nat.le_of_succ_le hi) β x p → IsPtAd A a (i + 1) hi β' x' p' →
    IsPtAd A a (i + 1) hi β' x₁' p₁' → ∀ w,
    muOf t u μ dtU (i + 1) (Matrix.GeneralLinearGroup.det κ'.1) * t.seam.σ₀ (xiPt A i hi β β' p p₁' w) =
      ((((St (i + 1) hi).K β').lev.chi κ' : ℂˣ) : ℂ) * t.seam.σ₀ (xiPt A i hi β β' p p' w)) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hT' _hE hMu i hi hi2 hAw β β' x x' x₁' κ' p p' p₁' hx hp hp' hp₁' w
  subst hi2
  obtain ⟨q', κ'', hq', hphi, hfr, hin⟩ := GlobalTheory.T.chartPoint_right_translate_by_level_coupled_step A dtU a hP hT' hi β' x' x₁' κ' p' hx hp'
  obtain ⟨c, hc, hχ⟩ := _root_.GlobalTheory.CplLev.levAt_cpl A dtU a hP hT' β' κ' κ'' hin
  have hst := _root_.GlobalTheory.CplCoset.sameCoset_kappa A dtU a hP hT' β' κ' κ'' hin
  have hmu := _root_.GlobalTheory.CplMuDet.muOf_det_cpl A dtU a hP hT' hMu β' κ' κ'' hin
  have hAw' := hAw β β' x x₁' x x₁' p q' p p₁' hp hq' hp hp₁' fun v _ => ⟨rfl, rfl⟩
  rw [hAw']
  have law := xiCpl1_moved (Ch := t.Ch) (cst := t.cst μ) hP.fields.ok t.pr_ok (t.idx_ok μ) (al := A.ib t.m2 hi β)
    (b := A.ib (t.m2 + 1) (cpl_lt t μ) β') p p' q' (cosetOf A (t.m2 + 1) hi β' p') κ'' c hfr hc w (hphi p w)
  have hcos : cosetOf A (t.m2 + 1) hi β' q' = cosetOf A (t.m2 + 1) hi β' p' := by
    ext y
    unfold cosetOf y0At
    simp only [Set.mem_setOf_eq, dif_pos rfl]
    refine forall_congr' fun P => ?_
    rw [hfr P]
    exact hst P _
  have ex1 : xiPt A t.m2 hi β β' p q' w = XiCpl1 t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.m2 (A.ib t.m2 hi β) p q'
      (cosetOf A (t.m2 + 1) hi β' q') w := by
    unfold xiPt
    rw [dite_eq_right (lt_irrefl _), if_pos rfl]
  have ex2 : xiPt A t.m2 hi β β' p p' w = XiCpl1 t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.m2 (A.ib t.m2 hi β) p p'
      (cosetOf A (t.m2 + 1) hi β' p') w := by
    unfold xiPt
    rw [dite_eq_right (lt_irrefl _), if_pos rfl]
  rw [ex1, ex2, hcos, hmu, ← hχ, ← map_mul, ← map_mul, mul_comm (∏ P : SB t μ, _), law]

end GlobalTheory.CplTarget
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleChartSuccEqComponentChartStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_tuple_chart_succ_eq_component_chart : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ j (hj : j + 1 ≤ D.R.m) (La : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → (I.at' j hj).st.T = (D.mem u).A.T ∧ ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La)).lev.Lb = ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).lev.Lb ∧ ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La)).lev.U = ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).lev.U ∧ ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La)).lev.Uloc = ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).lev.Uloc ∧ ∀ hc : (I.at' j hj).st.chOf (clsOf (S := (I.at' j hj).st) (H.core j hj) La.1 La.2) = ((I.at' j hj).st.eC.symm La.1).1, (J.St (j + 1) hj).y (clsAt X H (j + 1) La.1 La.2) = ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).y ⟨_, hc⟩ := by
  first | exact @GlobalTheory.TwV.chart_succ_eq | exact GlobalTheory.TwV.chart_succ_eq | (intros; apply GlobalTheory.TwV.chart_succ_eq <;> assumption)
end

