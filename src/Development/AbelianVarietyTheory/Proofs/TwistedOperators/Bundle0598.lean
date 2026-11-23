module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0008
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0577
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0588
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0061
public import Formalism.LocalToGlobal.Columns.DecoFin
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0589
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0546
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0398
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0053
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSplit
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelOfDualParameter
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0474
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1468
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetScalarUnitModulus
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0519
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0586

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeReadingKernelsMatchCosetsThroughFrame
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

set_option autoImplicit false

namespace GlobalTheory.HeckeTerm

open NumberField in
theorem splitSup {D : D7} (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) {P : Formalism.L2.DIV.Pl D.host.E}
    (h : Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal ≠ P.asIdeal) :
    P.asIdeal ⊔ P.asIdeal.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = ⊤ := by
  by_contra hne
  have hsub : P.asIdeal.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) ≤ P.asIdeal :=
    le_sup_right.trans (P.isMaximal.eq_of_le hne le_sup_left).ge
  apply h
  rw [Formalism.L2.Col.conjIdeal_asIdeal]
  refine (P.isMaximal.eq_of_le (Formalism.L2.Col.conjPrime₂ P).isPrime.ne_top fun a ha => ?_).symm
  rw [Formalism.L2.Col.mem_conjP]
  have : Formalism.L2.Col.cO D.host.E a = H.bar a := RingOfIntegers.ext (H.bar_eq a).symm
  rw [this]
  exact hsub (Ideal.mem_map_of_mem (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) ha)

theorem phiW_unfold {D : D7} (T : CoreJ D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) {W : HSp D} (hV : T.V j σ = W)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) (g : GA D W) :
    castDict hV (T.phiJ j σ a f) g = (lieFac (T.Q.Dw j) (xiR D) a : ℂ) *
      (T.cE j σ (castDict hV (T.dict j σ) g).1 * castDict hV (T.mu j σ) g *
        rdU (T.U j σ) f (castDict hV (T.dict j σ) g).1 (castDict hV (T.dict j σ) g).2) := by
  subst hV
  rfl

theorem heckeTerm : ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.SplitLinearModel D → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.VacFixed D →
    ∀ (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i,
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i σ hV →
    ∀ (P : Formalism.L2.DIV.Pl D.host.E) (p k : ℕ) (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))),
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsUnitaryHeckeOperatorSplitPrimeData T R i P p k α Rc →
    ∀ (h : GA D (Wc D i))
      (hx : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).dom),
      letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
      haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
      ∃ e : hkKer (Xo := T.Q.Xo ((i : ℕ) + 1)) P.asIdeal p k (CAt σ)
          ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) ≃ Rc,
        ∀ C, (∃ z, hkRelFr P.asIdeal p k (GlobalTheory.ThetaTrace.hkTr (T.Q.Xo ((i : ℕ) + 1)) T.Q.c p) (CAt σ)
              ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) C z) ∧
          ∀ z, hkRelFr P.asIdeal p k (GlobalTheory.ThetaTrace.hkTr (T.Q.Xo ((i : ℕ) + 1)) T.Q.c p) (CAt σ)
              ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) C z →
          ∀ f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (wtA (κ i)) (κ i).n,
            (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) *
              (T.cE ((i : ℕ) + 1) σ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) h) *
              σ (hkScal T.Q.c 1 P.asIdeal k D.R.nV) * toC (evR (T.Q.Xo ((i : ℕ) + 1)) T.Q.c f z) =
            (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.muAt T R i P)⁻¹ ^ k * GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.phiW T i σ hV (wtA (κ i)) f (h * (e C : GA D (Wc D i))) := by
  intro D hP hS hVF G _ _ Pl0 T0 A T _ R F κ v₀ hlev hgrp hfam hmod hthp ht i σ hσ hV hpin P p k α Rc hs h hx
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
  obtain ⟨e, he⟩ := GlobalTheory.T.heckeKernel_complex_point_matches_cosets D hP hS hVF G Pl0 T0 A T R F κ v₀ hlev hgrp hfam hmod hthp ht i σ hσ hV hpin P p k α Rc hs h hx
  refine ⟨e, fun C => ⟨?_, fun z hz f hf => ?_⟩⟩
  · have hsp := splitSup T.Q.H hs.1.1
    have hHP : GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.IsHeckePrime T.Q.l P.asIdeal p :=
      GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.isHeckePrime_iff.2 ⟨P.isMaximal, hsp, hs.2.1, hs.2.2.1, hs.2.2.2.1⟩
    have hT := hP.2.1 _ _ _ _ (T.Q.Xo ((i : ℕ) + 1)) T.Q.c P.asIdeal p k hHP
    exact @hT (CAt σ) _ (inferInstanceAs (IsAlgClosed ℂ)) _ _ C
  · obtain ⟨hx', t, ht1, hB⟩ := he C z hz
    have hg := GlobalTheory.T.heckeTerm_generator_constant_via_frame D hP hS hVF G Pl0 T0 A T R F κ v₀ hlev hgrp hfam hmod hthp ht i σ hσ hV hpin P p k α Rc hs h hx
      _ (e C).2 C z hz hx' t ht1 hB
    have hw := GlobalTheory.FrameEval.evR_frBor _ _ _ _ _ _ (CAt σ) _ _ f hf t _ z hB
    have hwc : wchar (ex (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i)) (κ i).n) t = (t none : CAt σ) ^ (κ i).n := by
      unfold wchar
      rw [Finset.prod_eq_single none (fun j _ hj => by rw [ht1 j hj]; simp) (fun h0 => absurd (Finset.mem_univ _) h0)]
      rfl
    rw [hwc] at hw
    show _ = _ * castDict hV (T.phiJ ((i : ℕ) + 1) σ (wtA (κ i)) f) (h * (e C : GA D (Wc D i)))
    rw [phiW_unfold]
    have hr : rdU (T.U ((i : ℕ) + 1) σ) f (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * (e C : GA D (Wc D i)))).1
        (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * (e C : GA D (Wc D i)))).2 =
        toC (evR (T.Q.Xo ((i : ℕ) + 1)) T.Q.c f ((T.U ((i : ℕ) + 1) σ).un _ ⟨_, hx'⟩)) := dif_pos hx'
    rw [hr, hw]
    have hz' : toC ((t none : CAt σ) ^ (κ i).n * evR (T.Q.Xo ((i : ℕ) + 1)) T.Q.c f ((T.U ((i : ℕ) + 1) σ).un _ ⟨_, hx'⟩)) =
        toC (t none : CAt σ) ^ (κ i).n * toC (evR (T.Q.Xo ((i : ℕ) + 1)) T.Q.c f ((T.U ((i : ℕ) + 1) σ).un _ ⟨_, hx'⟩)) := rfl
    rw [hz']
    linear_combination ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) *
      toC (evR (T.Q.Xo ((i : ℕ) + 1)) T.Q.c f ((T.U ((i : ℕ) + 1) σ).un _ ⟨_, hx'⟩))) * hg

end GlobalTheory.HeckeTerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdealMembershipOffModulus
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.DepthIdeal

open GlobalTheory.SeeSaw (FI idV dI)
open GlobalTheory.FinPlLoc (idem)
open Formalism.IndefR.Fin

variable {D : D7}

theorem phiE_one (v : GlobalTheory.FinPl.Pl D) : phiE (D := D) v 1 = idem D (· = v) := by
  classical
  have h : sglV v (1 : v.adicCompletion D.host.F) = GlobalTheory.FinPlLoc.ePl D (· = v) := by
    apply af_ext; intro u
    rw [GlobalTheory.FinPlLoc.evalV_ePl]
    by_cases hu : u = v
    · subst hu; rw [sglV_same, if_pos rfl]
    · rw [sglV_ne v _ hu, if_neg hu]
  unfold idem
  rw [← h]
  rfl

variable {T : Type} {L : LevCh D T}

theorem belowPl_w (P : Places L) {v : GlobalTheory.FinPl.Pl D} (hv : v ∈ P.S0) : belowPl (P.w v) = v := by
  conv_rhs => rw [← P.under_w hv]
  rfl

theorem exists_idem (P : Places L) {v : GlobalTheory.FinPl.Pl D} (hv : v ∈ P.S0) {e : AE D} (he : IsIdemSum e P.W0) :
    ∃ f : AE D, Formalism.L2.NTheta.IsIdemAt f (P.w v) ∧ (1 - e) * idem D (· = v) = cA D f := by
  classical
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  have hmem : ∀ PP, PP ∈ P.W0 ↔ ∃ u ∈ P.S0, P.w u = PP := fun PP => by
    unfold Places.W0
    convert Finset.mem_image
  have hw : P.w v ∈ P.W0 := (hmem _).2 ⟨v, hv, rfl⟩
  have heps : ∀ u ∈ P.S0, es (P.w u) + cA D (es (P.w u)) = phiE u 1 := fun u hu => by
    have := below_of_idemAt (hes _ ((hmem _).2 ⟨u, hu, rfl⟩))
    rwa [belowPl_w P hu] at this
  have hfix : ∀ u ∈ P.S0, es (P.w u) * phiE u 1 = es (P.w u) := fun u hu => by
    have h := hes _ ((hmem _).2 ⟨u, hu, rfl⟩)
    rw [← heps u hu, mul_add, h.1.1, h.1.2.1, add_zero]
  refine ⟨es (P.w v), hes _ hw, ?_⟩
  have hsum : (∑ PP ∈ P.W0, es PP) * phiE v 1 = es (P.w v) := by
    rw [Finset.sum_mul, Finset.sum_eq_single (P.w v), hfix v hv]
    · intro PP hPP hne
      obtain ⟨u, hu, rfl⟩ := (hmem _).1 hPP
      have huv : u ≠ v := fun h => hne (h ▸ rfl)
      rw [← hfix u hu, mul_assoc, phiE_orth huv, mul_zero]
    · intro h; exact absurd hw h
  rw [← phiE_one, sub_mul, one_mul, hsum, ← heps v hv, add_sub_cancel_left]

theorem exists_modul_conj (P : Places L) (sc : Consts) {v : GlobalTheory.FinPl.Pl D} (hv : v ∈ P.S0) :
    ∃ x ∈ P.modul sc, ∃ y : 𝓞 D.host.E, y ∉ (P.w v).asIdeal ∧ (y : D.host.E) = star (x : D.host.E) := by
  classical
  have hu : ∀ u ∈ P.S0, ∃ a ∈ (P.w u).asIdeal, ∃ b : 𝓞 D.host.E, b ∉ (P.w v).asIdeal ∧
      (b : D.host.E) = star (a : D.host.E) := by
    intro u hu
    by_cases huv : u = v
    · subst huv
      obtain ⟨f, hf⟩ := P.w_split u hu
      have hs := idemAt_split hf
      unfold Formalism.IndefR.Lev.IsConjPl at hs
      push Not at hs
      obtain ⟨a, ha, hb⟩ := hs
      exact ⟨a, ha, starO a, fun h => hb _ h rfl, rfl⟩
    · have hne : ¬ u.asIdeal ≤ v.asIdeal := fun hle =>
        huv (HeightOneSpectrum.ext (u.isMaximal.eq_of_le v.isPrime.ne_top hle))
      obtain ⟨t, htu, htv⟩ := Set.not_subset.1 hne
      refine ⟨algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t, ?_, algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t, ?_, ?_⟩
      · have : t ∈ (belowPl (P.w u)).asIdeal := by rw [belowPl_w P hu]; exact htu
        exact this
      · intro h
        apply htv
        have : t ∈ (belowPl (P.w v)).asIdeal := h
        rwa [belowPl_w P hv] at this
      · rw [algebraMap_O]
        exact (D.sp.cm.sig.commutes _).symm
  choose! a ha b hb hab using hu
  refine ⟨∏ u ∈ P.S0, a u ^ P.depth sc u, ?_, ∏ u ∈ P.S0, b u ^ P.depth sc u, ?_, ?_⟩
  · exact Ideal.prod_mem_prod fun u hu => Ideal.pow_mem_pow (ha u hu) _
  · intro hmem
    obtain ⟨u, hu, hmem'⟩ := (Ideal.IsPrime.prod_mem_iff (hp := (P.w v).isPrime)).1 hmem
    exact hb u hu ((P.w v).isPrime.mem_of_pow_mem _ hmem')
  · change algebraMap (𝓞 D.host.E) D.host.E _ = star (algebraMap (𝓞 D.host.E) D.host.E _)
    rw [map_prod, map_prod, star_prod]
    refine Finset.prod_congr rfl fun u hu => ?_
    rw [map_pow, map_pow, star_pow]
    exact congrArg (· ^ P.depth sc u) (hab u hu)

theorem idV_le_dI (P : Places L) {v : GlobalTheory.FinPl.Pl D} (hv : v ∈ P.S0) :
    idV (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AAbar) v ≤ idV (dI D) v := by
  refine GlobalTheory.StairLine.idV_le_of_loc fun z hz => ⟨_, GlobalTheory.AAUnit.absNorm_cmIdeal_not_mem_gridPlaces P hv, ?_⟩
  have e : dI D = D.host.AA * (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AAbar) := by
    unfold dI; ring
  have e2 : algebraMap D.host.F D.host.E ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.F) =
      ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) := by
    rw [← algebraMap_O, map_natCast]; rfl
  rw [e, e2]
  exact FractionalIdeal.mul_mem_mul (GlobalTheory.HostClear.absNorm_mem_AA D) hz

theorem compl_mem (P : Places L) (sc : Consts) {v : GlobalTheory.FinPl.Pl D} (hv : v ∈ P.S0) {e : AE D} (he : IsIdemSum e P.W0)
    (𝔞 : FI D) {s : AE D} (hs : s ∈ idV (𝔞 * ((P.modul sc : Ideal (𝓞 D.host.E)) : FI D)⁻¹) v) :
    (1 - e) * idem D (· = v) * s ∈ idV 𝔞 v := by
  obtain ⟨f, hf, hfe⟩ := exists_idem P hv he
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_modul_conj P sc hv
  have hy0 : y ≠ 0 := fun h => hy (h ▸ zero_mem _)
  have hx0 : (x : D.host.E) ≠ 0 := by
    intro h
    apply hy0
    apply FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E
    rw [map_zero]
    change (y : D.host.E) = 0
    rw [hxy, h, star_zero]
  have hm0 : ((P.modul sc : Ideal (𝓞 D.host.E)) : FI D) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 (P.modul_ne_bot sc)
  have h1 : idem D (· = v) * incA D x ∈ idV ((P.modul sc : Ideal (𝓞 D.host.E)) : FI D) v := by
    unfold idem
    rw [mul_comm, GlobalTheory.SeeSaw.IdVMul.incA_mul_tmul, mul_one]
    refine GlobalTheory.SeeSaw.IdVMul.gen_mem (GlobalTheory.FinPlLoc.ePl_int _) (fun w hw => ?_)
      ((FractionalIdeal.mem_coeIdeal _).2 ⟨x, hx, rfl⟩)
    rw [GlobalTheory.FinPlLoc.evalV_ePl, if_neg hw]
  have h2 := GlobalTheory.SeeSaw.IdVMul.mul_mem_idV h1 hs
  rw [mul_left_comm, mul_inv_cancel₀ hm0, mul_one] at h2
  have hint : finPart D (cA D f * incA D (x : D.host.E)⁻¹) ∈ intAE D := by
    have h3 : finPart D (f * incA D (y : D.host.E)⁻¹) ∈ intAE D := not_not.1 (mt (hf.2 y hy0).2 hy)
    have h4 := cF_int h3
    rwa [← finPart_cA, cA_mul_incA, hxy, star_inv₀, star_star] at h4
  have h5 : cA D f * incA D (x : D.host.E)⁻¹ ∈ idV (1 : FI D) v := by
    refine (GlobalTheory.SeeSaw.idV_one_eq_intAt D v _).2 ⟨?_, hint⟩
    rw [← hfe]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (GlobalTheory.FinPlLoc.idem_mem_idAt _))
  have h6 := GlobalTheory.SeeSaw.IdVMul.mul_mem_idV h5 h2
  rw [one_mul, ← hfe] at h6
  have e1 : incA D (x : D.host.E)⁻¹ * incA D x = 1 := by rw [← map_mul, inv_mul_cancel₀ hx0, map_one]
  have e2 := GlobalTheory.FinPlLoc.idem_mul_self (D := D) (· = v)
  have e3 : (1 - e) * idem D (· = v) * incA D (x : D.host.E)⁻¹ * (idem D (· = v) * incA D x * s) =
      (1 - e) * idem D (· = v) * s := by
    calc _ = (1 - e) * (idem D (· = v) * idem D (· = v)) * (incA D (x : D.host.E)⁻¹ * incA D x) * s := by ring
      _ = _ := by rw [e1, e2, mul_one]
  rwa [e3] at h6

theorem mem_dI_of_half : All fun {D} _ _ _ {G} _ _ => ∀ v ∈ G.pl.S0, ∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ s ∈ idAt D (· = v), s ∈ GlobalTheory.SeeSaw.idV (GlobalTheory.SeeSaw.dI D * ((G.modul : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹) v → e * s ∈ GlobalTheory.SeeSaw.idV (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AAbar) v → s ∈ GlobalTheory.SeeSaw.idV (GlobalTheory.SeeSaw.dI D) v := by
  intro D _ T L μ0 _ sc G W M _ v hv e he s hs h1 h2
  have hA := idV_le_dI G.pl hv h2
  have hB := compl_mem G.pl sc hv he (dI D) h1
  rw [mul_assoc, (GlobalTheory.FinPlLoc.mem_idAt_iff _ s).1 hs] at hB
  have := add_mem hA hB
  rwa [← add_mul, add_sub_cancel, one_mul] at this

end GlobalTheory.DepthIdeal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsTypeAtDualParIffStarIsTypeAt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TypeConj

open Matrix Formalism.IndefR.Mult GlobalTheory.ConjDS GlobalTheory.ConjMult

variable {D : D7}

theorem isTypeAt_star (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (P : SPar) (φ : GA D V → ℂ)
    (h : IsTypeAt θ V τ P φ) : IsTypeAt θ V τ (dualPar P) fun g => star (φ g) := by
  obtain ⟨H, i1, i2, σ, lam, ε, Q, hE, hD, hQ, hG, hx⟩ := h
  letI := i1; letI := i2
  have hJ := GlobalTheory.SmoothAutCheck.gramAt_unit V τ
  have e : ∀ g, rv (Q.submatrix Fin.revPerm (Equiv.refl _) * g * (Q.submatrix Fin.revPerm (Equiv.refl _))⁻¹) =
      Q * g * Q⁻¹ := by
    intro g
    rw [inv_submatrix_equiv]
    have : Q.submatrix Fin.revPerm (Equiv.refl _) * g * Q⁻¹.submatrix (Equiv.refl _) Fin.revPerm =
        rv (Q * g * Q⁻¹) := by
      ext i j
      simp [rv, Matrix.mul_apply]
    rw [this, rv_rv]
  have hc : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w : Cj H,
      cj H ((fun g => cjOp (σ (rv g))) (Q.submatrix Fin.revPerm (Equiv.refl _) * g *
        (Q.submatrix Fin.revPerm (Equiv.refl _))⁻¹) w) = (fun g => σ (Q * g * Q⁻¹)) g (cj H w) := by
    intro g _ w
    show σ (rv _) (cj H w) = _
    rw [e]
  have hc' : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w : H,
      (cj H).symm ((fun g => σ (Q * g * Q⁻¹)) g w) = (fun g => cjOp (σ (rv g))) (Q.submatrix Fin.revPerm (Equiv.refl _) * g *
        (Q.submatrix Fin.revPerm (Equiv.refl _))⁻¹) ((cj H).symm w) := by
    intro g hg w
    apply (cj H).injective
    rw [hc g hg, LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]
  have hfold : ∀ l : List (Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ X ∈ l, X ∈ lieAt V τ) → ∀ w : Cj H,
      l.foldr (dRep (fun g => σ (Q * g * Q⁻¹))) (cj H w) =
        cj H (l.foldr (dRep (fun g => (fun g => cjOp (σ (rv g))) (Q.submatrix Fin.revPerm (Equiv.refl _) * g *
          (Q.submatrix Fin.revPerm (Equiv.refl _))⁻¹))) w) := by
    intro l
    induction l with
    | nil => intro _ _; rfl
    | cons X l ih =>
      intro hl w
      rw [List.foldr_cons, ih (fun Y hY => hl Y (List.mem_cons_of_mem _ hY)), dRep_conj hJ (cj H) hc (hl X List.mem_cons_self),
        List.foldr_cons]
  have hn : ∀ l : List (Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ X ∈ l, X ∈ lieAt V τ) → ∀ w : Cj H,
      ‖l.foldr (dRep (fun g => (fun g => cjOp (σ (rv g))) (Q.submatrix Fin.revPerm (Equiv.refl _) * g *
          (Q.submatrix Fin.revPerm (Equiv.refl _))⁻¹))) w‖ =
        ‖l.foldr (dRep (fun g => σ (Q * g * Q⁻¹))) (cj H w)‖ := by
    intro l hl w
    rw [hfold l hl, LinearIsometryEquiv.norm_map]
  refine ⟨Cj H, inferInstance, inferInstance, fun g => cjOp (σ (rv g)), nr lam, fun a => ε a.rev,
    Q.submatrix Fin.revPerm (Equiv.refl _), isEnum_dual hE, isDS_transfer (fun _ => rfl) (cj H) (fun _ _ => rfl) hD,
    (Matrix.isUnit_submatrix_equiv _ _).2 hQ, ?_, fun x => ?_⟩
  · rw [← hG, ← rv_Jm (ε := fun a => ε a.rev) (ε' := ε) (fun a => by simp), rv,
      conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv]
    rfl
  obtain ⟨v, hv, ℓ, hℓ, ⟨S, C, hS, hb, hsum, B, hB, hBb⟩, hs⟩ := hx x
  let ℓ' : ℕ → (Cj H →ₗ[ℂ] ℂ) := fun i =>
    { toFun := fun w => star (ℓ i (cj H w))
      map_add' := fun x y => by simp
      map_smul' := fun a x => by rw [map_smulₛₗ, map_smul]; simp }
  refine ⟨fun i => (cj H).symm (v i), fun i => smoothVec_conj hJ (cj H).symm hc' (hv i), ℓ', fun i => ?_,
    ⟨S, C, hS, fun i w hw => ?_, fun S' hS' => ?_, B, hB, fun g hg w hw => ?_⟩, fun g hg => ?_⟩
  · obtain ⟨ℓ'', h1, h2⟩ := sobCont_conj hJ (cj H) hc (hℓ i)
    have : ℓ'' = ℓ' i := LinearMap.ext h2
    rw [← this]; exact h1
  · have h1 := hb i (cj H w) (smoothVec_conj hJ (cj H) hc hw)
    have h2 : (S.map fun l => ‖l.foldr (dRep (fun g => (fun g => cjOp (σ (rv g))) (Q.submatrix Fin.revPerm (Equiv.refl _) * g *
          (Q.submatrix Fin.revPerm (Equiv.refl _))⁻¹))) w‖) = S.map fun l => ‖l.foldr (dRep (fun g => σ (Q * g * Q⁻¹))) (cj H w)‖ :=
      List.map_congr_left fun l hl => hn l (hS l hl) w
    rw [h2]
    exact (norm_star _).trans_le h1
  · have h2 : ∀ i, (S'.map fun l => ‖l.foldr (dRep (fun g => (fun g => cjOp (σ (rv g))) (Q.submatrix Fin.revPerm (Equiv.refl _) * g *
          (Q.submatrix Fin.revPerm (Equiv.refl _))⁻¹))) ((cj H).symm (v i))‖) =
        S'.map fun l => ‖l.foldr (dRep (fun g => σ (Q * g * Q⁻¹))) (v i)‖ := fun i =>
      List.map_congr_left fun l hl => by rw [hn l (hS' l hl), LinearIsometryEquiv.apply_symm_apply]
    simp only [h2]
    exact hsum S' hS'
  · have h2 := hc g hg w
    have h3 : ∀ u : Cj H, (S.map fun l => ‖l.foldr (dRep (fun g => (fun g => cjOp (σ (rv g))) (Q.submatrix Fin.revPerm (Equiv.refl _) * g *
          (Q.submatrix Fin.revPerm (Equiv.refl _))⁻¹))) u‖) = S.map fun l => ‖l.foldr (dRep (fun g => σ (Q * g * Q⁻¹))) (cj H u)‖ :=
      fun u => List.map_congr_left fun l hl => hn l (hS l hl) u
    rw [h3, h3, h2]
    exact hBb g hg (cj H w) (smoothVec_conj hJ (cj H) hc hw)
  · have e2 : ∀ i, ℓ' i ((fun g => cjOp (σ (rv g))) (Q.submatrix Fin.revPerm (Equiv.refl _) * g *
          (Q.submatrix Fin.revPerm (Equiv.refl _))⁻¹) ((cj H).symm (v i))) = star (ℓ i (σ (Q * g * Q⁻¹) (v i))) := by
      intro i
      show star (ℓ i (cj H _)) = _
      rw [hc g hg, LinearIsometryEquiv.apply_symm_apply]
    simp only [e2]
    exact (hs g hg).star

theorem isTypeAt_dualPar_iff : ∀ {D : D7} (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (P : SPar) (φ : GA D V → ℂ),
    IsTypeAt θ V τ (Formalism.IndefR.Mult.dualPar P) φ ↔ IsTypeAt θ V τ P fun g => star (φ g) := by
  intro D θ V τ P φ
  constructor
  · intro h
    have := isTypeAt_star θ V τ _ _ h
    rwa [dualPar_dualPar] at this
  · intro h
    have := isTypeAt_star θ V τ _ _ h
    simpa only [star_star] using this

end GlobalTheory.TypeConj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetScalarIdempotentValue
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.SplitMoveKappa

theorem qbar_of_root {ζ : ℂ} {n : ℕ} (hn : 0 < n) (hζ : ζ ^ n = 1) : ζ ∈ TaylorLogMetric.Qbar := by
  have halg : IsAlgebraic ℚ ζ := by
    refine ⟨Polynomial.X ^ n - Polynomial.C 1, ?_, ?_⟩
    · exact Polynomial.X_pow_sub_C_ne_zero hn 1
    · simp [hζ]
  exact mem_algebraicClosure_iff.2 halg

theorem mod1All_root {ζ : ℂ} {n : ℕ} (hn : 0 < n) (hζ : ζ ^ n = 1) : Mod1All ζ := by
  refine ⟨qbar_of_root hn hζ, fun σ => ?_⟩
  have h1 : (⟨ζ, qbar_of_root hn hζ⟩ : TaylorLogMetric.Qbar) ^ n = 1 := by ext; simpa using hζ
  have h2 : (σ ⟨ζ, qbar_of_root hn hζ⟩) ^ n = 1 := by rw [← map_pow, h1, map_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 (by rw [← norm_pow, h2, norm_one])

theorem lamC_mem {q : ℕ} [Fact q.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[q]) {x : ℂ} (h : x ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam x = lam ⟨x, h⟩ := dif_pos h

theorem unitAt_mul {q : ℕ} [Fact q.Prime] {x y : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) (hy : y ∈ TaylorLogMetric.Qbar)
    (ux : GlobalTheory.MovedKappaEx.UnitAt q x) (uy : GlobalTheory.MovedKappaEx.UnitAt q y) : GlobalTheory.MovedKappaEx.UnitAt q (x * y) := by
  intro lam
  have e : (⟨x * y, mul_mem hx hy⟩ : TaylorLogMetric.Qbar) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
  have hx' := ux lam
  have hy' := uy lam
  rw [lamC_mem lam hx] at hx'
  rw [lamC_mem lam hy] at hy'
  rw [lamC_mem lam (mul_mem hx hy), e, map_mul, norm_mul, hx', hy', one_mul]

theorem unitAt_inv {q : ℕ} [Fact q.Prime] {x : ℂ} (hx : x ∈ TaylorLogMetric.Qbar)
    (ux : GlobalTheory.MovedKappaEx.UnitAt q x) : GlobalTheory.MovedKappaEx.UnitAt q x⁻¹ := by
  intro lam
  have e : (⟨x⁻¹, inv_mem hx⟩ : TaylorLogMetric.Qbar) = (⟨x, hx⟩ : TaylorLogMetric.Qbar)⁻¹ := rfl
  have hx' := ux lam
  rw [lamC_mem lam hx] at hx'
  rw [lamC_mem lam (inv_mem hx), e, map_inv₀, norm_inv, hx', inv_one]

theorem unitAt_root (q : ℕ) [Fact q.Prime] {ζ : ℂ} {n : ℕ} (hn : 0 < n) (hζ : ζ ^ n = 1) :
    GlobalTheory.MovedKappaEx.UnitAt q ζ := by
  intro lam
  have h1 : (⟨ζ, qbar_of_root hn hζ⟩ : TaylorLogMetric.Qbar) ^ n = 1 := by ext; simpa using hζ
  have h2 : (lam ⟨ζ, qbar_of_root hn hζ⟩) ^ n = 1 := by rw [← map_pow, h1, map_one]
  rw [lamC_mem lam (qbar_of_root hn hζ)]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 (by rw [← norm_pow, h2, norm_one])

end GlobalTheory.SplitMoveKappa
end
end

