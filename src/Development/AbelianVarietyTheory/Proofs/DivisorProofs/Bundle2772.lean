module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0526
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0245
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0527
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0092
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1222
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0164
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0241
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0274
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0280
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0277
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0144
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0275
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0282
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1260
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1250
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2695
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateSimilitudeHeckeTranslateLatticeSystem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1293
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1273
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2583
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2754
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeFormAnisoOfGlobalEuler
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.BottomRallis

variable {D : D7}

theorem siegelWeilFockAniso_of_siegelWeilAnisotropic (hSW : GlobalTheory.Published.SiegelWeilAnisotropicUnitary) (D : D7) :
    SiegelWeilFockAniso D := by
  intro ψ A B ha hab hB χB omh homh a hmaj θ sS sB hθ hS hBc hKc ν 𝓕 hcov mH hmH φ hF
  have hK := _root_.GlobalTheory.Core.Rk.IP.isKFinVec_of_isFockVec D ψ θ (dblSp A) B 1 χB omh sS sB homh hθ hS hBc (Khat A a) (isCompact_Khat A a) hKc φ hF
  have hI : HasIwasawa D.sp.cm.sig (dblSp A).gram (Khat A a) :=
    _root_.GlobalTheory.Core.Rk.IP.hasIwasawa_KAd_selfDual D A (frameLat A) a (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat A) hmaj
  have hB' : IsAniso B := wittIndex_eq_zero_iff_isAniso.1 hB
  obtain ⟨hint, hv⟩ := hSW D ψ A B ha (ha.trans hab.le) hB' χB omh homh a hmaj hI ν 𝓕 hcov mH hmH φ hF.1 hK
  rw [if_pos hab, one_smul] at hv
  exact ⟨hint, hv⟩

end GlobalTheory.BottomRallis

namespace GlobalTheory.BottomRallis

variable {D : D7}

theorem heckeFormAniso_of_global_euler (D : D7) (hG : GlobalFormAniso D) (hE : EulerRight D) : HeckeFormAniso D := by
  intro ψ θ A B χA χB sA sB t cA a om ν 𝓕 hP hw LA LB Sf Φ₁ Φ₂ hF₁ hF₂ hU m mH hm hmH u₁ hu₁ u₂ hu₂ par hpar
    hsph hs
  obtain ⟨s₁, hs₁, hint⟩ := hs
  obtain ⟨hUp₁, hUp₂, hZint, z, hz, hpet⟩ :=
    hG A LA hU.sdA ψ θ B χA χB sA sB t cA a om ν 𝓕 hP hw m mH hm hmH Φ₁ Φ₂ hF₁ hF₂ u₁ hu₁ u₂ hu₂
  obtain ⟨hA1, ht1, hB, -⟩ := hP.setting
  have hs0 : sZero A B = (t : ℂ) / 2 := by
    simp only [sZero, hB]; push_cast; ring
  have hs0re : (sZero A B).re = (t : ℝ) / 2 := by rw [hs0]; simp
  obtain ⟨hcont, hbd, -⟩ := _root_.GlobalTheory.Core.Rk.IP.hgtL_props D A LA a hU.sdA hP.maj
  have hflat : ∀ s, integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s =
      GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral.flatIntegrand (fun g => wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g)
        (fun g => (hgtL A LA a g : ℝ)) (sZero A B) s := by
    intro s; funext g
    simp only [integrand, GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral.flatIntegrand, npow]; ring
  have hmeas : Measurable (fun g => (hgtL A LA a g : ℝ)) := (NNReal.continuous_coe.comp hcont).measurable
  have hfz := _root_.GlobalTheory.FlatFamily.flatZetaHolomorphic (GA D A) (m.restrict (openOff A LA Sf)) (fun g => wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g)
    (fun g => (hgtL A LA a g : ℝ)) (sZero A B) (s₁ : ℂ) hmeas (fun g => by exact_mod_cast (hbd g).1)
    (fun g => by exact_mod_cast (hbd g).2) (by rw [← hflat]; exact hint)
  have hint0 : IntegrableOn (fun g => wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g) (openOff A LA Sf) m := by
    have := hfz.1.1 (sZero A B) (by simp only [Set.mem_setOf_eq, Complex.ofReal_re, hs0re]; linarith)
    rwa [GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral.flatIntegrand_self] at this
  refine ⟨hUp₁, hUp₂, hint0, fun l hl => ?_⟩
  have hd := GlobalTheory.T.partialNormalizingFactorProduct_analytic_ne_zero D (Sf : Set (FinPl D)) A.rank B.rank
  have hER : EqRight (fun s => ∫ g, integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s g ∂m)
      (fun s => LFun.LSD D Sf par χB (s + 1 / 2) / LFun.dSfun D.host.E (Sf : Set (FinPl D)) A.rank B.rank s *
        ∫ g in openOff A LA Sf, integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s g ∂m) := by
    refine ⟨(A.rank : ℝ) + 1, fun s hs => ?_⟩
    have hs' : (A.rank : ℝ) + 1 < s.re := hs
    refine hE ψ θ A B χA χB sA sB t cA a om ν 𝓕 hP LA LB Sf Φ₁ Φ₂ hF₁.1 hF₂.1 hU m hm u₁ hu₁ u₂ hu₂ par hpar hsph s hs'
      (hZint s ?_)
    have : (0 : ℝ) ≤ A.rank := Nat.cast_nonneg _
    linarith
  have hY : DifferentiableOn ℂ (fun s => ∫ g in openOff A LA Sf, integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s g ∂m)
      (rightOf s₁) := by
    have h2 := hfz.2.1
    simp only [Complex.ofReal_re] at h2
    refine h2.congr fun s _ => ?_
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral.flatZeta, hflat]
  have hL : HolValueAt (fun s => LFun.LSD D Sf par χB (s + 1 / 2)) (sZero A B) l := by rw [hs0]; exact hl
  have hmain := _root_.GlobalTheory.Core.Rk.IP.holValueAt_eq_div_mul _ _ _ _ (sZero A B) z l s₁ (by rw [hs0re]; positivity) (by rw [hs0re]; exact hs₁)
    hd.1 (fun s hs => (hd.2 s hs).1) hY hER hz hL
  rw [hpet, hmain, ← hs0]
  simp only [integrand_sZero]
  ring

theorem rcoef_one {A : HSp D} (m : Measure (GA D A)) (g : GA D A) :
    rcoef m (fun _ : GA D A => (1 : ℂ)) (fun _ => 1) g = (volQ A m : ℂ) := by
  simp [rcoef, petersson, pet, rTr, GlobalTheory.AutomorphicL2Unitary.descend, volQ]

end GlobalTheory.BottomRallis

namespace GlobalTheory.BottomRallis

variable {D : D7}

end GlobalTheory.BottomRallis

namespace GlobalTheory.BottomRallis

theorem prod_range_sub_eq_prod_Icc (f : ℤ → ℂ) (a h : ℕ) (e : ℤ) (he : (a : ℤ) = h + e) :
    ∏ i ∈ Finset.range a, f ((h : ℤ) - i) = ∏ s ∈ Finset.Icc (1 - e) (h : ℤ), f s := by
  refine Finset.prod_nbij' (fun i => (h : ℤ) - i) (fun s => ((h : ℤ) - s).toNat) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.coe_range, Set.mem_Iio, Finset.mem_coe, Finset.mem_range] at hi
    simp only [Finset.coe_Icc, Set.mem_Icc, Finset.mem_coe, Finset.mem_Icc]
    omega
  · intro s hs
    simp only [Finset.coe_Icc, Set.mem_Icc, Finset.mem_coe, Finset.mem_Icc] at hs
    simp only [Finset.coe_range, Set.mem_Iio, Finset.mem_coe, Finset.mem_range]
    omega
  · intro i _
    simp
  · intro s hs
    simp only [Finset.coe_Icc, Set.mem_Icc, Finset.mem_coe, Finset.mem_Icc] at hs
    omega
  · intro i _
    rfl

end GlobalTheory.BottomRallis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateWeilLocal
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField GlobalTheory.UPel.HT.HeckeAd

noncomputable section

namespace GlobalTheory.UPel.HT.HeckeAd.TateTranslAt

open GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.Hecke.TateTransl GlobalTheory.UPel.HT.HeckeAd.TateTranslSys

theorem exists_tateIsoO_of_given {p : ℕ} [Fact p.Prime] (D : Datum p) {R : Type} [CommRing R] (b : Base D R)
    (h : ℕ → D.La →+ D.La) (u : ℕ → ℤ) (c k N : ℕ) (hcp : c.Coprime p) (hkp : k.Coprime p) (hN : 3 ≤ N)
    (hNp : N.Coprime p) (hck : c ∣ k ^ 2)
    (hlin : ∀ n, 0 < n → n.Coprime p → ∀ (a : D.O) (x : D.La), ∃ z, h n (a • x) = a • h n x + n • z)
    (hcomp : ∀ n m, 0 < n → 0 < m → (n * m).Coprime p → (∀ x, ∃ z, h (n * m) x = h n x + n • z) ∧
      (n : ℤ) ∣ u (n * m) - u n)
    (hsim : ∀ n, 0 < n → n.Coprime p → IsCoprime (u n) (n : ℤ) ∧
      ∀ x y, (n : ℤ) ∣ D.EF (h n x) (h n y) - c * u n * D.EF x y)
    (hsurj : ∀ n, 0 < n → n.Coprime p → ∀ x, ∃ y z, h n y = k • x + n • z)
    {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b (N * k) s) (A' : Over S) [GrpObj A'] [IsCommMonObj A']
    (act' : OActN D.O A') (ψ : o.A ⟶ A') (hA' : IsAbelianScheme A') (hψ : IsMonHom ψ)
    (hGal : GlobalTheory.ZM.IsGaloisCover (heckeSubA o (h (N * k)) N) (fun g => (transl g.1).left) ψ.left)
    (hact : ∀ c' : D.O, o.act.act c' ≫ ψ = ψ ≫ act'.act c') (P' : LB (G2 A').left) (hP' : P'.IsLB)
    (hiso : LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) (P'.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)))
    (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (β : R →+* κ)
    (I : TateIsoO D κ (Over.mk x ⟶ o.A) (fun c g => g ≫ o.act.act c)
      (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)))
    (hI : ∀ y, toUnit _ ≫ o.eta y = I.ev (N * k) y) :
    ∃ I' : TateIsoO D κ (Over.mk x ⟶ A') (fun c g => g ≫ act'.act c)
        (fun n g g' z => Out.WeilIs A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) n g g' (unitOn z)),
      (∀ y, toUnit _ ≫ (o.eta (h (N * k) y) ≫ ψ) = I'.ev N y) ∧
      ∀ n, 0 < n → n.Coprime p → ∀ y, I'.ev n y = I.ev (n * k) (h (n * k) y) ≫ ψ := by
  haveI := D.freeLa
  have kpos : 0 < k := levelPos_of_coprime hkp
  have cpos : 0 < c := levelPos_of_coprime hcp
  have Npos : 0 < N := by omega
  let Ψ : (Over.mk x ⟶ o.A) →* (Over.mk x ⟶ A') :=
    MonoidHom.mk' (fun t => t ≫ ψ) (fun a a' => MonObj.mul_comp a a' ψ)
  have hΨ : ∀ t, Ψ t = t ≫ ψ := fun _ => rfl
  have hlev : ∀ n, 0 < n → n.Coprime p → ∀ w, I.ev (n * k) (n • w) = I.ev k w := fun n hn hnp w =>
    ev_mul_nsmul I n k hn kpos (Nat.Coprime.mul_left hkp hnp) w

  have hk_eq : ∀ n, 0 < n → n.Coprime p → ∀ z, I.ev k (h (n * k) z) = I.ev k (h k z) := by
    intro n hn hnp z
    obtain ⟨z', hz'⟩ := (hcomp k n kpos hn (Nat.Coprime.mul_left hkp hnp)).1 z
    rw [mul_comm n k, hz', I.add, (I.ker k kpos hkp (k • z')).2 ⟨z', rfl⟩, _root_.mul_one]
  have hker : ∀ t : Over.mk x ⟶ o.A, t ≫ ψ = 1 ↔ ∃ z, t = I.ev (N * k) (N • h (N * k) z) := by
    intro t
    constructor
    · intro ht
      have e1 : t.left ≫ ψ.left = (1 : Over.mk x ⟶ o.A).left ≫ ψ.left := by
        rw [← Over.comp_left, ← Over.comp_left, ht, MonObj.one_comp]
      obtain ⟨g, hg, -⟩ := hGal.fibre κ (1 : Over.mk x ⟶ o.A).left t.left e1.symm
      obtain ⟨z, hz⟩ := g.2
      refine ⟨z, ?_⟩
      have e2 : t = (1 : Over.mk x ⟶ o.A) ≫ transl g.1 :=
        Over.OverMorphism.ext (by rw [Over.comp_left]; exact hg.symm)
      rw [e2, one_comp_transl_pt, hz, hI]
    · rintro ⟨z, rfl⟩
      rw [← hI, Category.assoc, comp_eq_one_of_transl ψ (o.eta (N • h (N * k) z))
        (hGal.inv ⟨_, mem_heckeSubA o (h (N * k)) N z⟩), MonObj.comp_one]
  have hkerN : ∀ n, 0 < n → n.Coprime p → ∀ t : Over.mk x ⟶ o.A,
      t ≫ ψ = 1 ↔ ∃ z, t = I.ev (n * k) (n • h (n * k) z) := by
    intro n hn hnp t
    rw [hker]
    have e : ∀ z, I.ev (N * k) (N • h (N * k) z) = I.ev (n * k) (n • h (n * k) z) := fun z => by
      rw [hlev N Npos hNp, hk_eq N Npos hNp, hlev n hn hnp, hk_eq n hn hnp]
    simp only [e]
  have ker' : ∀ n, 0 < n → n.Coprime p → ∀ y, I.ev (n * k) (h (n * k) y) ≫ ψ = 1 ↔ ∃ z, y = n • z := by
    intro n hn hnp y
    have hnk : 0 < n * k := Nat.mul_pos hn kpos
    have hnkp : (n * k).Coprime p := Nat.Coprime.mul_left hnp hkp
    rw [hkerN n hn hnp]
    constructor
    · rintro ⟨z, hz⟩
      obtain ⟨v, hv⟩ := (ev_eq_iff I (n * k) hnk hnkp _ _).1 hz
      obtain ⟨z', hz'⟩ := exists_nsmul_of_map_eq D h u c k hcp hkp hcomp hsim hsurj n hn hnp (y - n • z) v
        (by rw [map_sub, map_nsmul, hv])
      exact ⟨z + z', by rw [smul_add, ← hz', add_sub_cancel]⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z, by rw [map_nsmul]⟩
  have htor : ∀ n, 0 < n → n.Coprime p → ∀ y, (I.ev (n * k) (h (n * k) y) ≫ ψ) ^ n = 1 := by
    intro n hn hnp y
    rw [← hΨ, ← map_pow, hΨ, ← TateTransl.ev_nsmul, ← map_nsmul]
    exact (ker' n hn hnp (n • y)).2 ⟨y, rfl⟩
  have onto' : ∀ n, 0 < n → n.Coprime p → ∀ q : Over.mk x ⟶ A',
      q ^ n = 1 ↔ ∃ y, I.ev (n * k) (h (n * k) y) ≫ ψ = q := by
    intro n hn hnp q
    constructor
    · intro hq
      haveI := hGal.fin
      haveI := hGal.onto
      obtain ⟨a₀, ha₀⟩ := GlobalTheory.GeomSurj.exists_lift_of_surjective ψ.left q.left
      let a : Over.mk x ⟶ o.A := Over.homMk a₀ (by
        show a₀ ≫ o.A.hom = x
        rw [← Over.w ψ, ← Category.assoc, ← ha₀, Over.w q]; rfl)
      have ha : a ≫ ψ = q := Over.OverMorphism.ext (by rw [Over.comp_left]; exact ha₀.symm)
      have han : (a ^ n) ≫ ψ = 1 := by rw [← hΨ, map_pow, hΨ, ha, hq]
      obtain ⟨z, hz⟩ := (hkerN n hn hnp _).1 han
      have hnk : 0 < n * k := Nat.mul_pos hn kpos
      have hnkp : (n * k).Coprime p := Nat.Coprime.mul_left hnp hkp
      have hak : a ^ (n * k) = 1 := by
        rw [pow_mul, hz, ← TateTransl.ev_nsmul, I.ker _ hnk hnkp]
        exact ⟨h (n * k) z, by rw [smul_smul, mul_comm]⟩
      obtain ⟨w, hw⟩ := (I.onto _ hnk hnkp a).1 hak
      rw [← hw, ← TateTransl.ev_nsmul, ev_eq_iff I _ hnk hnkp] at hz
      obtain ⟨v, hv⟩ := hz
      have e1 : n • (w - h (n * k) z - k • v) = 0 := by rw [smul_sub, smul_sub, smul_smul, ← hv, sub_self]
      have e2 : w - h (n * k) z - k • v = 0 := by
        have e3 : ((n : ℤ)) • (w - h (n * k) z - k • v) = 0 := by rw [natCast_zsmul]; exact e1
        exact (smul_eq_zero.1 e3).resolve_left (by exact_mod_cast hn.ne')
      have e4 : w = h (n * k) z + k • v := by rw [sub_sub, sub_eq_zero] at e2; exact e2
      obtain ⟨y'', z'', hy''⟩ := hsurj (n * k) hnk hnkp v
      have e5 : h (n * k) (z + y'') = w + (n * k) • z'' := by rw [map_add (f := _), hy'', e4, add_assoc]
      refine ⟨z + y'', ?_⟩
      rw [e5, I.add, (I.ker _ hnk hnkp ((n * k) • z'')).2 ⟨z'', rfl⟩, _root_.mul_one, hw, ha]
    · rintro ⟨y, rfl⟩
      exact htor n hn hnp y
  have hnκ : ∀ n : ℕ, n.Coprime p → (n : κ) ≠ 0 := fun n hnp => by
    have h := (b.unit n hnp).map β
    rw [map_natCast] at h
    exact h.ne_zero
  have hiso2 : LBIso (ReciprocityTheory.ChartRestriction.G.Geo.Tor.lbPow (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) (k ^ 2 / c))
      ((P'.pull (lift (𝟙 A') (𝟙 A')).left).pull ψ.left) := by
    refine (GlobalTheory.CechPic.cls_eq_iff (LB.isLB_linComb (pull_isLB o.isLB _) _ _) (pull_isLB (pull_isLB hP' _) _)).1 ?_
    rw [GlobalTheory.CechPic.cls_lbPow (pull_isLB o.isLB _), GlobalTheory.CechPic.cls_pull o.isLB, GlobalTheory.CechPic.cls_pull (pull_isLB hP' _),
      GlobalTheory.CechPic.cls_pull hP', ← GlobalTheory.CechPic.pull_comp]
    have h1 := (GlobalTheory.CechPic.cls_eq_iff (LB.isLB_linComb o.isLB _ _) (pull_isLB hP' _)).2 hiso
    rw [GlobalTheory.CechPic.cls_linComb o.isLB, GlobalTheory.CechPic.cls_pull hP'] at h1
    simp only [GlobalTheory.CechPic.pull_id, one_smul, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at h1
    have h2 := congrArg (GlobalTheory.CechPic.pull (lift (𝟙 o.A) (𝟙 o.A)).left) h1
    rw [map_nsmul, ← GlobalTheory.CechPic.pull_comp] at h2
    rw [h2]
    congr 1
    simp only [sq2, ← Over.comp_left, comp_lift, Category.id_comp, lift_fst_assoc, lift_snd_assoc, Category.comp_id]

  have hmc : k ^ 2 / c * c = k ^ 2 := Nat.div_mul_cancel hck
  have hm0 : 0 < k ^ 2 / c := Nat.div_pos (Nat.le_of_dvd (by positivity) hck) cpos
  have hmp : (k ^ 2 / c).Coprime p :=
    Nat.Coprime.coprime_dvd_left (Dvd.intro c hmc) (Nat.Coprime.pow_left 2 hkp)
  let ev' : ℕ → D.La → (Over.mk x ⟶ A') := fun n y =>
    if 0 < n ∧ n.Coprime p then I.ev (n * k) (h (n * k) y) ≫ ψ else 1
  have hev' : ∀ n, 0 < n → n.Coprime p → ∀ y, ev' n y = I.ev (n * k) (h (n * k) y) ≫ ψ :=
    fun n hn hnp y => if_pos ⟨hn, hnp⟩
  refine ⟨⟨fun n => I.ζ n ^ u n, ?_, ?_, ev', ?_, ?_, ?_, ?_, ?_, ?_⟩, fun y => ?_, hev'⟩
  · intro n hn hnp
    exact (I.ζ_prim n hn hnp).zpow_of_gcd_eq_one (u n) (Int.isCoprime_iff_gcd_eq_one.1 (hsim n hn hnp).1)
  · intro n m hn hm hnm
    show (I.ζ (n * m) ^ u (n * m)) ^ m = I.ζ n ^ u n
    rw [← I.ζ_pow n m hn hm hnm]
    simp only [← zpow_natCast, ← zpow_mul]
    apply zpow_eq_zpow_of_dvd (I.ζ_prim (n * m) (Nat.mul_pos hn hm) hnm).pow_eq_one
    obtain ⟨t, ht⟩ := (hcomp n m hn hm hnm).2
    exact ⟨t, by push_cast; linear_combination (m : ℤ) * ht⟩
  · intro n y y'
    simp only [ev']
    split_ifs with hn
    · rw [map_add (f := _), I.add, MonObj.mul_comp]
    · rw [_root_.mul_one]
  · intro n b' y
    simp only [ev']
    split_ifs with hn
    · have hnk : 0 < n * k := Nat.mul_pos hn.1 kpos
      have hnkp : (n * k).Coprime p := Nat.Coprime.mul_left hn.2 hkp
      obtain ⟨z, hz⟩ := hlin (n * k) hnk hnkp b' y
      rw [hz, I.add, (I.ker _ hnk hnkp _).2 ⟨z, rfl⟩, _root_.mul_one, I.lin, Category.assoc, hact,
        ← Category.assoc]
    · haveI := act'.hom b'
      rw [MonObj.one_comp]
  · intro n hn hnp y
    rw [hev' n hn hnp]
    exact ker' n hn hnp y
  · intro n hn hnp q
    simp only [hev' n hn hnp]
    exact onto' n hn hnp q
  · intro n m hn hm hnm y
    have hn' : n.Coprime p := Nat.Coprime.coprime_dvd_left (dvd_mul_right n m) hnm
    have hnk : 0 < n * k := Nat.mul_pos hn kpos
    have hnkm : (n * k * m).Coprime p := by rw [Nat.mul_right_comm]; exact Nat.Coprime.mul_left hnm hkp
    rw [hev' (n * m) (Nat.mul_pos hn hm) hnm, hev' n hn hn', ← hΨ, ← map_pow, hΨ, Nat.mul_right_comm n m k,
      I.tower (n * k) m hnk hm hnkm]
    obtain ⟨z, hz⟩ := (hcomp (n * k) m hnk hm hnkm).1 y
    rw [hz, I.add, (I.ker _ hnk (Nat.Coprime.mul_left hn' hkp) _).2 ⟨z, rfl⟩, _root_.mul_one]
  · intro n hn hnp y y'
    have hnk : 0 < n * k := Nat.mul_pos hn kpos
    have hnkp : (n * k).Coprime p := Nat.Coprime.mul_left hnp hkp
    have hnkc : (n * k * c).Coprime p := Nat.Coprime.mul_left hnkp hcp
    have hrep : ∀ y, I.ev (n * k) (h (n * k) y) = I.ev (n * k) (h (n * k * c) y) := fun y => by
      obtain ⟨z, hz⟩ := (hcomp (n * k) c hnk cpos hnkc).1 y
      rw [hz, I.add, (I.ker _ hnk hnkp _).2 ⟨z, rfl⟩, _root_.mul_one]
    rw [hev' n hn hnp, hev' n hn hnp]
    obtain ⟨e, he⟩ := GlobalTheory.WeilGeomPt.exists_weilIs_geomPt S A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) hA'
      (pull_isLB hP' _) κ x n hn (hnκ n hnp) _ _ (htor n hn hnp y) (htor n hn hnp y')
    have h2 := GlobalTheory.WeilIsogeny.weilIs_pull_hom GlobalTheory.globalFns_holds o.ab (pull_isLB o.isLB _) (pull_isLB hP' _) ψ
      hiso2 he
    rw [hrep y, hrep y'] at h2
    have hNp' : (n * (k ^ 2 / c * k ^ 2)).Coprime p :=
      Nat.Coprime.mul_left hnp (Nat.Coprime.mul_left hmp (Nat.Coprime.pow_left 2 hkp))
    have h3 := weilIs_ev_value o I k (k ^ 2 / c) n kpos hm0 hn hNp' _ _ e (by rw [Nat.cast_mul]; exact h2)
    have h4 : I.ζ (n * (k ^ 2 / c * k ^ 2)) ^ (2 * D.EF ((k ^ 2 / c) • h (n * k * c) y) ((k ^ 2 / c) • h (n * k * c) y'))
        = (I.ζ n ^ u n) ^ (2 * D.EF y y') := by
      rw [← I.ζ_pow n (k ^ 2 / c * k ^ 2) hn (by positivity) hNp']
      simp only [← zpow_natCast, ← zpow_mul]
      apply zpow_eq_zpow_of_dvd (I.ζ_prim _ (by positivity) hNp').pow_eq_one
      obtain ⟨t, ht⟩ := (hsim (n * k * c) (by positivity) hnkc).2 y y'
      obtain ⟨s', hs'⟩ := (hcomp n (k * c) hn (by positivity) (by rw [← _root_.mul_assoc]; exact hnkc)).2
      rw [← _root_.mul_assoc] at hs'
      have hmcZ : ((k ^ 2 / c : ℕ) : ℤ) * (c : ℤ) = (k : ℤ) ^ 2 := by exact_mod_cast hmc
      simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
      refine ⟨2 * s' * D.EF y y' + 2 * k * t, ?_⟩
      simp only [Nat.cast_mul, Nat.cast_pow] at ht hs' ⊢
      linear_combination (2 * ((k ^ 2 / c : ℕ) : ℤ) * ((k ^ 2 / c : ℕ) : ℤ)) * ht
        + (2 * ((k ^ 2 / c : ℕ) : ℤ) * (k : ℤ) ^ 2 * D.EF y y') * hs'
        + (2 * ((k ^ 2 / c : ℕ) : ℤ) * u (n * k * c) * D.EF y y'
          + 2 * ((k ^ 2 / c : ℕ) : ℤ) * (n : ℤ) * (k : ℤ) * t) * hmcZ
    rw [h3, h4] at he
    exact he
  · show toUnit _ ≫ (o.eta (h (N * k) y) ≫ ψ) = ev' N y
    rw [hev' N Npos hNp, ← Category.assoc, hI]

end GlobalTheory.UPel.HT.HeckeAd.TateTranslAt

namespace GlobalTheory.UPel.HT.HeckeAd

end GlobalTheory.UPel.HT.HeckeAd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductiveMixedHeightTensorAdditive
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem recVal_tens_cons : ArchInteg → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 + 1 : ℕ) → ∀ T, IsMix q (e + 1) T → ∀ (M : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r) (A B : HermLB q) (L : Fin e → HermLB q), recVal (T (e + 1) (Fin.cons (A.tens B) L)) (Fin.cons (A.tens B) L : Fin (e + 1) → HermLB q) M hr = recVal (T (e + 1) (Fin.cons A L)) (Fin.cons A L : Fin (e + 1) → HermLB q) M hr + recVal (T (e + 1) (Fin.cons B L)) (Fin.cons B L : Fin (e + 1) → HermLB q) M hr := by
  intro hA k _ Y _ _ q hq e hdim T hT M r hr A B L
  have hN := hq.isNoetherian
  have hfin := (M.div hr).finite_support_mult
  have hm := (_root_.GlobalTheory.MixAdd.mixArch_add_diag hA k Y q hq M r hr).1 e hdim A B L
  have hsupp : ∀ (f : Y → ℝ), (Function.support fun z => ((M.div hr).mult z : ℝ) * f z).Finite := fun f =>
    hfin.subset fun z hz h => hz (by simp [h])
  unfold recVal
  rw [hm]
  have hsum : (∑ᶠ z, ((M.div hr).mult z : ℝ) * T (e + 1) (Fin.cons (A.tens B) L) z) =
      (∑ᶠ z, ((M.div hr).mult z : ℝ) * T (e + 1) (Fin.cons A L) z) +
        ∑ᶠ z, ((M.div hr).mult z : ℝ) * T (e + 1) (Fin.cons B L) z := by
    rw [← finsum_add_distrib (hsupp _) (hsupp _)]
    refine finsum_congr fun z => ?_
    by_cases h0 : (M.div hr).mult z = 0
    · simp [h0]
    · have hc := CartierDiv.coheight_eq_one_of_mult_ne_zero h0
      have hd := ((_root_.GlobalTheory.MixHt.dimOne k Y q hq (e + 1) hdim).1 z).1 hc
      rw [hT.add e A B L z le_rfl hd, mul_add]
  rw [hsum]
  ring

end GlobalTheory.MixHt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralityFittedIdentity
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField
open Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts

namespace GlobalTheory.BigTop.Fun.IntTie

theorem gBig_dep {Q : GP} (h : GBig @Q) :
    GBig fun {D} {T} {Lc} {sc} G μ₀ C x b => 1 ≤ sc.cDep ∧ sc.cDep ≤ C ∧ @Q D T Lc sc G μ₀ C x b := by
  obtain ⟨CF0, h⟩ := h
  refine ⟨max CF0 1, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h⟩ := h ε CF (le_of_max_le_left hCF)
  exact ⟨max C0 CF, x0, fun C hC D large₂ he hx hR T Lc μ hL G =>
    ⟨le_of_max_le_right hCF, le_of_max_le_right hC, h C (le_of_max_le_left hC) D large₂ he hx hR T Lc μ hL G⟩⟩

theorem gBig_and {Q Q' : GP} (h : GBig @Q) (h' : GBig @Q') :
    GBig fun {D} {T} {Lc} {sc} G μ₀ C x b => @Q D T Lc sc G μ₀ C x b ∧ @Q' D T Lc sc G μ₀ C x b := by
  obtain ⟨a, h⟩ := h
  obtain ⟨a', h'⟩ := h'
  refine ⟨max a a', fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h⟩ := h ε CF (le_of_max_le_left hCF)
  obtain ⟨C1, x1, h'⟩ := h' ε CF (le_of_max_le_right hCF)
  exact ⟨max C0 C1, max x0 x1, fun C hC D large₂ he hx hR T Lc μ hL G =>
    ⟨h C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) hR T Lc μ hL G,
     h' C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) hR T Lc μ hL G⟩⟩

theorem integralNormBound_mono {K : Type} [Field K] [NumberField K] {ι : Type} {dl : Formalism.PairingDivisionLocalBalance.Pl K → ℝ} {zA zA' : ι → K}
    {B B' : ℝ} (h : NonArchimedeanDefectBound dl zA zA' B) (hB : B ≤ B') : NonArchimedeanDefectBound dl zA zA' B' :=
  ⟨h.1, fun F => (h.2.1 F).trans hB, h.2.2⟩

end GlobalTheory.BigTop.Fun.IntTie

end
end

