module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2728
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2804
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1222
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2799
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1250
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1662
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1233
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1256
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0792
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0609
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0284
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1254
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0247
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2798
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeActionAdelicLattice
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2108

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivisibleGroupIsogenyBasicProperties
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu

section

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k]

theorem pow_smul_cancel {G H : PDivGroup p k} (a : ℕ) {X Y : G ⟶ H}
    (h : (p : ℤ_[p]) ^ a • X = (p : ℤ_[p]) ^ a • Y) : X = Y := by
  induction a generalizing X Y with
  | zero => simpa using h
  | succ a ih =>
    apply ih
    rw [← sub_eq_zero, ← smul_sub]
    apply eq_zero_of_prime_smul_eq_zero
    rw [smul_smul, ← pow_succ', smul_sub, h, sub_self]

theorem finrank_A (G : PDivGroup p k) (n : ℕ) : Module.finrank k (G.A n) = p ^ (n * G.height) := by
  have h := G.rank_eq n ⟨⊥, Ideal.isPrime_bot⟩
  simpa [Module.rankAtStalk_eq_finrank_of_free] using h

theorem isIsog_pow_smul_id (G : PDivGroup p k) (m : ℕ) : IsIsog ((p : ℤ_[p]) ^ m • 𝟙 G) :=
  ⟨m, 𝟙 G, Category.comp_id _, Category.id_comp _⟩

theorem hasLogDeg_pow_smul_id (G : PDivGroup p k) (m : ℕ) :
    HasLogDeg ((p : ℤ_[p]) ^ m • 𝟙 G) (m * G.height) := by
  refine ⟨m, fun n hn => ?_⟩
  obtain ⟨f, hf, hk⟩ := G.exists_res_le hn
  have e : Hom.app ((p : ℤ_[p]) ^ m • 𝟙 G) n = mulBy (R := k) (A := G.A n) (p ^ m) := by
    rw [← Nat.cast_pow, natCast_smul_id_app]
  rw [e]
  change Module.finrank k (G.A n ⧸ torsionIdeal (R := k) (A := G.A n) (p ^ m)) = _
  rw [← hk]
  exact ((Ideal.quotientKerAlgEquivOfSurjective (f := (f : G.A n →ₐ[k] G.A m)) hf).toLinearEquiv.finrank_eq).trans
    (finrank_A G m)

theorem isIsog_comp {G H K : PDivGroup p k} {f : G ⟶ H} {g : H ⟶ K} (hf : IsIsog f)
    (hg : IsIsog g) : IsIsog (f ≫ g) := by
  obtain ⟨a, f', h1, h2⟩ := hf
  obtain ⟨b, g', h3, h4⟩ := hg
  refine ⟨a + b, g' ≫ f', ?_, ?_⟩
  · calc (f ≫ g) ≫ g' ≫ f' = f ≫ (g ≫ g') ≫ f' := by simp only [Category.assoc]
      _ = (p : ℤ_[p]) ^ (a + b) • 𝟙 G := by
        rw [h3, Linear.smul_comp, Category.id_comp, Linear.comp_smul, h1, smul_smul, ← pow_add,
          add_comm b a]
  · calc (g' ≫ f') ≫ f ≫ g = g' ≫ (f' ≫ f) ≫ g := by simp only [Category.assoc]
      _ = (p : ℤ_[p]) ^ (a + b) • 𝟙 K := by
        rw [h2, Linear.smul_comp, Category.id_comp, Linear.comp_smul, h4, smul_smul, ← pow_add]

theorem isIsog_of_comp {G H K : PDivGroup p k} {f : G ⟶ H} {g : H ⟶ K} (hf : IsIsog f)
    (hfg : IsIsog (f ≫ g)) : IsIsog g := by
  obtain ⟨a, f', h1, h2⟩ := hf
  obtain ⟨b, u, h3, h4⟩ := hfg
  refine ⟨a + b, (p : ℤ_[p]) ^ a • (u ≫ f), ?_, ?_⟩
  · calc g ≫ ((p : ℤ_[p]) ^ a • (u ≫ f)) = ((p : ℤ_[p]) ^ a • 𝟙 H) ≫ g ≫ u ≫ f := by
          rw [Linear.comp_smul, Linear.smul_comp, Category.id_comp]
      _ = f' ≫ ((f ≫ g) ≫ u) ≫ f := by rw [← h2]; simp only [Category.assoc]
      _ = (p : ℤ_[p]) ^ (a + b) • 𝟙 H := by
        rw [h3, Linear.smul_comp, Category.id_comp, Linear.comp_smul, h2, smul_smul, ← pow_add,
          add_comm b a]
  · calc ((p : ℤ_[p]) ^ a • (u ≫ f)) ≫ g = (p : ℤ_[p]) ^ a • (u ≫ f ≫ g) := by
          rw [Linear.smul_comp, Category.assoc]
      _ = (p : ℤ_[p]) ^ (a + b) • 𝟙 K := by rw [h4, smul_smul, ← pow_add]

variable [CharP k p]

theorem hasLogDeg_zero_iff_isIso {G H : PDivGroup p k} (f : G ⟶ H) (hf : IsIsog f) :
    HasLogDeg f 0 ↔ IsIso f := by
  constructor
  · rintro ⟨N, hN⟩
    obtain ⟨a, f', h1, h2⟩ := hf
    have hs : Function.Surjective (f.app (N + a)) :=
      (_root_.GlobalTheory.Dieu.surjective_iff_finrank_quot_kerIdeal_eq_one k (G.A (N + a)) (H.A (N + a)) (f.app (N + a))).2
        ((hN (N + a) (Nat.le_add_right N a)).trans (pow_zero p))
    set f'' : H ⟶ G := (p : ℤ_[p]) ^ N • f' with hf''
    have e1 : f ≫ f'' = (p : ℤ_[p]) ^ (N + a) • 𝟙 G := by
      rw [hf'', Linear.comp_smul, h1, smul_smul, ← pow_add]
    have e2 : f'' ≫ f = (p : ℤ_[p]) ^ (N + a) • 𝟙 H := by
      rw [hf'', Linear.smul_comp, h2, smul_smul, ← pow_add]
    have hc : f''.conv (N + a) = 1 := by
      have h3 : precomp (H.A (N + a)) (f.app (N + a)) (f''.conv (N + a)) =
          precomp (H.A (N + a)) (f.app (N + a)) 1 := by
        rw [map_one, ← comp_conv_left, e2, pow_smul_conv]
      refine WithConv.ofConv_injective (BialgHom.ext fun x => ?_)
      obtain ⟨y, rfl⟩ := hs x
      exact DFunLike.congr_fun (congrArg WithConv.ofConv h3) y
    obtain ⟨g, hg⟩ := _root_.GlobalTheory.PDivGroup.DivP.divisible_of_conv_eq_one p k H G (N + a) f'' hc
    refine ⟨⟨g, ?_, ?_⟩⟩
    · refine pow_smul_cancel (N + a) ?_
      rw [← Linear.comp_smul, ← hg, e1]
    · refine pow_smul_cancel (N + a) ?_
      rw [← Linear.smul_comp, ← hg, e2]
  · intro hi
    refine ⟨0, fun n _ => ?_⟩
    rw [pow_zero]
    refine (_root_.GlobalTheory.Dieu.surjective_iff_finrank_quot_kerIdeal_eq_one k (G.A n) (H.A n) (f.app n)).1 fun x => ⟨(inv f).app n x, ?_⟩
    have h := congrArg (fun φ : G ⟶ G => φ.app n x) (IsIso.hom_inv_id f)
    exact h

theorem isog_basics : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (G : PDivGroup p k),
    (∀ m : ℕ, IsIsog ((p : ℤ_[p]) ^ m • 𝟙 G) ∧ HasLogDeg ((p : ℤ_[p]) ^ m • 𝟙 G) (m * G.height)) ∧
    (∀ (H K : PDivGroup p k) (f : G ⟶ H) (g : H ⟶ K), IsIsog f → IsIsog g → IsIsog (f ≫ g)) ∧
    (∀ (H K : PDivGroup p k) (f : G ⟶ H) (g : H ⟶ K), IsIsog f → IsIsog (f ≫ g) → IsIsog g) ∧
    ∀ (H : PDivGroup p k) (f : G ⟶ H), IsIsog f → (HasLogDeg f 0 ↔ IsIso f) :=
  fun _ _ _ _ _ G => ⟨fun m => ⟨isIsog_pow_smul_id G m, hasLogDeg_pow_smul_id G m⟩,
    fun _ _ _ _ => isIsog_comp, fun _ _ _ _ => isIsog_of_comp,
    fun _ f => hasLogDeg_zero_iff_isIso f⟩

end

end GlobalTheory.Dieu
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialLFunctionEqNormalizingFactorDefiniteBotto
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)

namespace GlobalTheory.BottomLVal

open GlobalTheory.LFun

private theorem par_eq_trivPar {D : D7} {n : ℕ} (J : Matrix (Fin n) (Fin n) D.host.E)
    (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (S : Set (FinPl D)) (par : Fam D.host.E)
    (h : IsParamFun D.sp.cm.sig J L S (fun _ => (1 : ℂ)) par) :
    ∀ w ∉ above D.host.E S, par w = GlobalTheory.BottomRallis.trivPar (D := D) n w := by
  intro w hw
  have hx := h _ hw w rfl
  have h0 : (fun _ : GAd D.sp.cm.sig J => (1 : ℂ)) ≠ 0 := fun e => one_ne_zero (congrFun e 1)
  refine hx.unique ?_
  rcases hx with ⟨hs, e, he, -⟩ | ⟨hw', τ, ϖ, e, α, hϖ, he, -, -⟩
  · exact Or.inl ⟨hs, e, he, ((LFun.Model.hasSatGL_trivial w n).2 1 (GlobalTheory.LGrp.mem_fixed.2 fun _ _ => rfl)
      one_ne_zero).map (LinearMap.pi fun _ => LinearMap.id) (fun _ _ => rfl) h0⟩
  · refine Or.inr ⟨hw', τ, ϖ, e, _, hϖ, he, ((LFun.Model.hasSatU_trivial hϖ (LFun.qV_ne_zero _) n).2 1
      (GlobalTheory.LGrp.mem_fixed.2 fun _ _ => rfl) one_ne_zero).map hϖ (LinearMap.pi fun _ => LinearMap.id) (fun _ _ => rfl) h0, ?_⟩
    rw [GlobalTheory.Core.Rk.Exh.Model.bcParam_rho]
    exact GlobalTheory.Core.Rk.Exh.Model.seg_eq_str (LFun.qV_ne_zero _) (LFun.InertChart.absNorm_eq D.sp.cm.deg2 hw') _

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}

private theorem mem_sfB (G : GridData L sc) (t : T) (v : FinPl D) :
    v ∈ GlobalTheory.BottomIPData.sfB G t ↔ v ∈ G.pl.S0 ∨ ∃ P ∈ L.Q t, P.under (𝓞 D.host.F) = v := by
  classical
  simp only [GlobalTheory.BottomIPData.sfB, GlobalTheory.FunObj.locPl, GlobalTheory.ChiGrid.Places.W0, Finset.mem_image, Finset.mem_union]
  constructor
  · rintro ⟨w, ⟨u, hu, rfl⟩ | hw, rfl⟩
    · exact Or.inl ((G.pl.under_w hu).symm ▸ hu)
    · exact Or.inr ⟨w, hw, rfl⟩
  · rintro (hv | ⟨P, hP, rfl⟩)
    · exact ⟨_, Or.inl ⟨v, hv, rfl⟩, G.pl.under_w hv⟩
    · exact ⟨P, Or.inr hP, rfl⟩

private theorem nuH_unrAt_iff (G : GridData L sc) (t : T) (i j : Fin D.R.m) (P : HeightOneSpectrum (𝓞 D.host.E))
    (hS0 : P.under (𝓞 D.host.F) ∉ G.pl.S0) : (nuH G t i j).UnrAt P ↔ (L.xiH t).UnrAt P := by
  have hS1 : P.under (𝓞 D.host.F) ∉ S1 D := fun h => hS0 (G.pl.mem_S0_of_sum_eq.2 (Or.inr h))
  have a1 : 1 ≤ D.R.m - i := by have := i.2; omega
  have a2 : D.R.m - i ≤ D.R.m := by omega
  have hchi : (G.ch.chiH (D.R.m - i)).UnrAt P := G.ch.unr _ a1 a2 P hS0
  have hmu : (L.C.mu0 j).UnrAt P := (L.C.isMu0 j).unr P fun k hk => hS1 ((S1_mem_OmF D).2 (by
    have : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (P.under (𝓞 D.host.F)).asIdeal := by
      show algebraMap _ (𝓞 D.host.E) _ ∈ P.asIdeal
      rw [map_natCast]; exact hk
    fin_cases k
    · exact Or.inl this
    · exact Or.inr (Or.inl this)))
  refine ⟨fun hnu => ?_, fun hxi => ?_⟩
  · have e : L.xiH t = nuH G t i j * (L.C.mu0 j)⁻¹ * G.ch.chiH (D.R.m - i) := by
      rw [nuH]
      have key : ∀ {M : Type} [CommGroup M] (a x c : M), x = a * x / c * a⁻¹ * c := fun a x c => by
        rw [div_mul_eq_mul_div, div_mul_cancel, mul_comm a x, mul_inv_cancel_right]
      exact key _ _ _
    rw [e]
    exact (hnu.mul hmu.inv).mul hchi
  · rw [nuH, div_eq_mul_inv]
    exact (hmu.mul hxi).mul hchi.inv

private theorem nuH_not_unrAt_iff {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc) (t : T) (i j : Fin D.R.m)
    (P : HeightOneSpectrum (𝓞 D.host.E)) :
    ¬ (nuH G t i j).UnrAt P ↔ P.under (𝓞 D.host.F) ∈ GlobalTheory.BottomIPData.sfB G t := by
  rw [mem_sfB]
  by_cases h0 : P.under (𝓞 D.host.F) ∈ G.pl.S0
  · exact iff_of_true (GlobalTheory.SqStep.nuH_not_unrAt_above hL G t i j P h0) (Or.inl h0)
  · rw [nuH_unrAt_iff G t i j P h0, hL.Q_ram t P, or_iff_right h0]
    constructor
    · rintro (h | ⟨Q, h, hc⟩)
      · exact ⟨P, h, rfl⟩
      · exact ⟨Q, h, GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc⟩
    · rintro ⟨Q, h, e⟩
      by_cases hq : Q = P
      · exact Or.inl (hq ▸ h)
      · exact Or.inr ⟨Q, h, GlobalTheory.UnderConj.isConjPl_of_under_eq_of_ne D Q P e hq⟩

private theorem prod_range_sub (f : ℤ → ℂ) (a h : ℕ) (e : ℤ) (he : (a : ℤ) = h + e) :
    ∏ i ∈ Finset.range a, f ((h : ℤ) - i) = ∏ s ∈ Finset.Icc (1 - e) (h : ℤ), f s := by
  refine Finset.prod_nbij' (fun i => (h : ℤ) - i) (fun s => ((h : ℤ) - s).toNat) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_range] at hi
    simp only [Finset.mem_Icc]
    omega
  · intro s hs
    simp only [Finset.mem_Icc] at hs
    simp only [Finset.mem_range]
    omega
  · intro i _
    simp
  · intro s hs
    simp only [Finset.mem_Icc] at hs
    omega
  · intro i _
    rfl

private theorem bot_ranks (D : D7) (i j : ℕ) : 1 ≤ botSmall D i j ∧ botBig D i j + botSmall D i j = 2 * h0 D i j ∧
    botBig D i j = h0 D i j + e0 D i j := by
  obtain ⟨h1, h2, h3⟩ := ranks_exact D i j
  have e : rankV D (i + 1) (j + 1) = rankV D i j + D.R.t + sLen D := by simp only [rankV]; ring
  have h4 : D.R.r ≤ rankV D i j := by simp only [rankV]; omega
  have h5 : D.R.m < D.R.r := by have := D.R.m_add_three_le_k; unfold Ranks.r; omega
  simp only [h0, e0]
  omega

end GlobalTheory.BottomLVal

theorem _root_.GlobalTheory.T.partialLFunction_eq_normalizingFactor_definiteBottom : GBig fun {D} T Lc _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → ∀ t : T, ∀ par : GlobalTheory.LFun.Fam D.host.E, GlobalTheory.LFun.IsParamFun D.sp.cm.sig (GlobalTheory.Grid.neg A).gram X.rA.Λ ((GlobalTheory.BottomIPData.sfB G t : Finset (FinPl D)) : Set (FinPl D)) (fun _ => (1 : ℂ)) par →
  ∃ κ : ℂ, κ ≠ 0 ∧ ∀ Λ : ℂ → ℂ, GlobalTheory.CMVal.IsHeckeL (nuH G t i j) Λ →
    HolValueAt (fun s => GlobalTheory.LFun.LSD D (GlobalTheory.BottomIPData.sfB G t) par (GlobalTheory.BottomIPData.betaB G i j / GlobalTheory.BottomIPData.alphaB Lc i j t) (s + 1 / 2)) ((A'.rank : ℂ) / 2)
      (κ * GlobalTheory.LFun.dSfun D.host.E ((GlobalTheory.BottomIPData.sfB G t : Finset (FinPl D)) : Set (FinPl D)) (GlobalTheory.Grid.neg A).rank WW.rank ((A'.rank : ℂ) / 2) *
        ∏ s ∈ Icc (1 - (e0 D i j : ℤ)) (h0 D i j : ℤ), Λ s) := by
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D _ _ _ _ T Lc μ₀ hL G W i j A A' WW X hX t par hpar => ?_⟩⟩
  obtain ⟨r1, r2, r3⟩ := GlobalTheory.BottomLVal.bot_ranks D i j
  rw [← hX.rank'] at r1 r2
  rw [← hX.rank] at r2 r3
  have hd := GlobalTheory.LFun.dSfun_ne_zero_of_re_pos (E := D.host.E)
    ((GlobalTheory.BottomIPData.sfB G t : Finset (FinPl D)) : Set (FinPl D)) (GlobalTheory.Grid.neg A).rank WW.rank
    (s := (A'.rank : ℂ) / 2) (by
      have : (1 : ℝ) ≤ A'.rank := by exact_mod_cast r1
      simp only [Complex.div_ofNat_re, Complex.natCast_re]
      linarith)
  refine ⟨_, inv_ne_zero hd, fun Λ hΛ => ?_⟩
  rw [inv_mul_cancel₀ hd, one_mul]
  have hν : (GlobalTheory.BottomIPData.betaB G i j / GlobalTheory.BottomIPData.alphaB Lc i j t)⁻¹ = G.nu t i (j + 1) := by
    rw [inv_div]
    exact mul_div_mul_right_eq_div _ _ _
  have hc := chrEq_nu G t i j hL
  have hU : GlobalTheory.LFun.UnrOff (GlobalTheory.BottomIPData.betaB G i j / GlobalTheory.BottomIPData.alphaB Lc i j t)
      ((GlobalTheory.BottomIPData.sfB G t : Finset (FinPl D)) : Set (FinPl D)) := fun w hw => by
    rw [← inv_inv (GlobalTheory.BottomIPData.betaB G i j / GlobalTheory.BottomIPData.alphaB Lc i j t), hν]
    exact ((GlobalTheory.LFun.unrAt_iff_of_chrEq hc w).2
      (not_not.1 (mt (GlobalTheory.BottomLVal.nuH_not_unrAt_iff hL G t i j w).1 hw))).inv
  obtain ⟨σ, hσ⟩ := GlobalTheory.RallisEuler.trivPar_euler _ _ A.rank hU
  have hH : Differentiable ℂ fun s : ℂ => ∏ k ∈ range A.rank, Λ (s + (A.rank : ℂ) / 2 - k) :=
    by
      generalize range A.rank = S
      induction S using Finset.induction_on with
      | empty => simp
      | @insert k S hk ih =>
        simp only [Finset.prod_insert hk]
        exact (hΛ.1.comp (by fun_prop)).mul ih
  refine ⟨fun s : ℂ => ∏ k ∈ range A.rank, Λ (s + (A.rank : ℂ) / 2 - k),
    ⟨Set.univ, trivial, isRightDomain_univ, fun s _ => (hH.analyticAt s).meromorphicAt,
      max σ ((A.rank : ℝ) / 2 + 1), fun s hs => ?_⟩, hH.analyticAt _, ?_⟩
  · have hs1 : σ < s.re := (le_max_left _ _).trans_lt hs
    have hs2 : (A.rank : ℝ) / 2 + 1 < s.re := (le_max_right _ _).trans_lt hs
    refine Eq.trans ?_ ((hσ hs1).trans
      (GlobalTheory.LFun.LSTw_congr (GlobalTheory.BottomLVal.par_eq_trivPar _ _ _ par hpar) _ _).symm)
    refine Finset.prod_congr rfl fun k hk => ?_
    have hk' : (k : ℝ) + 1 ≤ A.rank := by exact_mod_cast Finset.mem_range.1 hk
    rw [hν, GlobalTheory.LFun.charL_eq_of_chrEq hc]
    refine (GlobalTheory.SqStep.heckeL_eq_of_ram
      (fun w hw => (GlobalTheory.BottomLVal.nuH_not_unrAt_iff hL G t i j w).2 hw) hΛ ?_).symm
    simp only [Complex.sub_re, Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re]
    linarith
  · rw [← GlobalTheory.BottomLVal.prod_range_sub (fun s => Λ s) A.rank (h0 D i j) (e0 D i j) (by exact_mod_cast r3)]
    refine Finset.prod_congr rfl fun k _ => congrArg Λ ?_
    have : (A.rank : ℂ) + A'.rank = 2 * (h0 D i j : ℕ) := by exact_mod_cast r2
    push_cast
    linear_combination this / 2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPointsMixMaximalMinorFockVectorsUnitary
section
open NumberField MeasureTheory
open scoped Classical ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.NormDict.RealB.subst_minorPol_unitary : ∀ (D : D7) {a d N n : ℕ} {m : D.what₂.Tau → ℕ} (hN : N = d) (hn : n = a) (K : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ), (∀ τ, K τ ∈ Matrix.unitaryGroup (Fin N) ℂ) → ∃ U : Matrix (Tup D a d m) (Tup D a d m) ℂ, U ∈ Matrix.unitaryGroup (Tup D a d m) ℂ ∧ ∀ T : Tup D a d m, GlobalTheory.CompactHowe.substF K (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) (MvPolynomial.rename (fun k : Formalism.MainNotions.GL3Theta.Idx D a d => ((k.1, Fin.cast hN.symm k.2.1, Fin.cast hn.symm k.2.2) : D.what₂.Tau × Fin N × Fin n)) (minorPol D T)) = ∑ T', U T T' • MvPolynomial.rename (fun k : Formalism.MainNotions.GL3Theta.Idx D a d => ((k.1, Fin.cast hN.symm k.2.1, Fin.cast hn.symm k.2.2) : D.what₂.Tau × Fin N × Fin n)) (minorPol D T') := by
  intro D a d N n m hN hn K hK
  subst hN hn
  have hr : (MvPolynomial.rename (fun k : Formalism.MainNotions.GL3Theta.Idx D n N => ((k.1, Fin.cast rfl k.2.1, Fin.cast rfl k.2.2) : D.what₂.Tau × Fin N × Fin n)) : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D n N) ℂ →ₐ[ℂ] _) = AlgHom.id ℂ _ := by
    simp only [Fin.cast_eq_self, Prod.mk.eta]
    exact MvPolynomial.rename_id
  simp only [hr, AlgHom.id_apply]
  exact ⟨_, _root_.GlobalTheory.unitary_tensor_places_positions D.what₂.Tau {s : Fin n → Fin N // StrictMono s} m _ fun τ => _root_.GlobalTheory.minorsMatrix_mem_unitaryGroup (a := n) (K τ) (hK τ),
    fun T => by rw [_root_.GlobalTheory.NormDict.substF_minorPol_eq_sum D K T]; rfl⟩

namespace GlobalTheory.NormDict.RealB

theorem real_mix : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (X : Data P), IsDict P X →
    ∀ k ∈ GinfC X.B, ∃ U : Matrix (Tup D P.a P.d P.n) (Tup D P.a P.d P.n) ℂ, U ∈ Matrix.unitaryGroup (Tup D P.a P.d P.n) ℂ ∧
      ∀ T, X.om (1, k) (X.fock T) = ∑ T', U T T' • X.fock T' := by
  intro D cc δ t0 Q P X hX k hk
  have hF := hX.1
  have hW := hX.2.weil
  have hθ := hX.2.inf
  let K : D.what₂.Tau → Matrix (Fin X.B.rank) (Fin X.B.rank) ℂ := fun τ => compAt X.θ τ (Formalism.L2.Theta.mt X.B k)
  have hKu : ∀ τ, K τ ∈ Matrix.unitaryGroup (Fin X.B.rank) ℂ := fun τ => GlobalTheory.RealColAct.compAt_mem_unitary hθ hF.gramB k τ
  obtain ⟨U₀, hU₀, hsub⟩ := GlobalTheory.NormDict.RealB.subst_minorPol_unitary D (m := P.n) X.rkB X.rkA K hKu
  have c1 : ∀ (V : HSp D) τ, compAt X.θ τ (Formalism.L2.Theta.mt V 1) = 1 := fun V τ =>
    Matrix.map_one (f := (X.θ τ).comp (infPart D)) (map_zero _) (map_one _)
  have gr1 : ∀ (V : HSp D), V.gram = 1 → ∀ τ, gramAt D V τ = 1 := fun V h τ => by
    rw [gramAt, h, Matrix.map_one _ (map_zero _) (map_one _)]
  have cart : ∀ (V : HSp D), V.gram = 1 → ∀ τ, IsCartanInv (gramAt D V τ) 1 := fun V h τ => by
    rw [gr1 V h]; exact ⟨Matrix.mul_one _, by simp, by rw [Matrix.mul_one]; exact Matrix.PosDef.one⟩
  obtain ⟨η, e1, e2, e3, e4⟩ := _root_.GlobalTheory.Mem.EtaTilde.exists_etaTilde D
  obtain ⟨x, hx, -⟩ := GlobalTheory.VacuumCharacter.exists_root hθ X.A (fun τ => by rw [gr1 _ hF.gramA]; simp) 1 (one_mem _)
  obtain ⟨y, hy, -⟩ := GlobalTheory.VacuumCharacter.exists_root hθ X.B (fun τ => by rw [gr1 _ hF.gramB]; simp) k hk
  have hvac := _root_.GlobalTheory.WeilVacChar.vacuum_character D X.ψ hW.std X.A X.B X.θ hθ X.χA X.χB X.om η ⟨e1, e4, e3, e2⟩ hW (fun _ => 1) (fun _ => 1)
    (cart _ hF.gramA) (cart _ hF.gramB) 1 (one_mem _) k hk (fun τ => by rw [Matrix.one_mul, Matrix.mul_one])
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) x y hx hy X.vac hX.2.vac_theta hX.2.vac_fock
  obtain ⟨c, hc1, hcv⟩ : ∃ c : ℂ, ‖c‖ = 1 ∧ X.om (1, k) X.vac = c • X.vac := by
    refine ⟨_, ?_, hvac⟩
    rw [norm_mul, Circle.norm_coe, one_mul, norm_prod]
    refine Finset.prod_eq_one fun τ _ => ?_
    rw [GlobalTheory.KJReal.detPlus_one_one, inv_one, c1, Matrix.det_one, one_pow, mul_one, norm_pow]
    have hd := Matrix.det_of_mem_unitary (hKu τ)
    rw [show ‖(compAt X.θ τ (Formalism.L2.Theta.mt X.B k)).det‖ = 1 from CStarRing.norm_of_mem_unitary hd, one_pow]
  refine ⟨c • U₀, ?_, fun T => ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff] at hU₀ ⊢
    rw [star_smul, Matrix.smul_mul, Matrix.mul_smul, hU₀, smul_smul, RCLike.star_def, Complex.mul_conj,
      Complex.normSq_eq_norm_sq, hc1]
    simp
  · have e2 := (GlobalTheory.OrientedHeis.om_pureTensorO D X.ψ X.θ X.A X.B X.χA X.χB X.om hW hθ (fun _ => 1) (fun _ => 1)
      (fun _ => 1) (fun _ => 1 * 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun τ => 1 * K τ) 1 k
      (fun τ => by rw [c1, Matrix.one_mul]) (fun τ => by rw [Matrix.one_mul, Matrix.mul_one])
      (fun τ => by rw [c1, Matrix.one_mul]) (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) X.vac hX.2.vac_theta
      (MvPolynomial.rename X.var (minorPol D T))).2
    have e3 := GlobalTheory.T.fockPolynomialVector_basisChange_eq_substitution D X.ψ X.θ X.A X.B hW.std hθ (fun _ => 1) (fun _ => 1) (fun _ => 1) K X.vac hX.2.vac_theta
      (MvPolynomial.rename X.var (minorPol D T))
    have e4 := hsub T
    simp only [inv_one, Matrix.transpose_one] at e3
    change X.om (1, k) (pureTensorO X.ψ X.θ X.A X.B (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) X.vac _) = _
    rw [e2, hcv, GlobalTheory.FiniteFock.pureTensorO_smul, e3]
    change c • (pureTensorO X.ψ X.θ X.A X.B (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) X.vac) (GlobalTheory.CompactHowe.substF K (fun _ => 1) (MvPolynomial.rename (fun k : Formalism.MainNotions.GL3Theta.Idx D P.a P.d => ((k.1, Fin.cast X.rkB.symm k.2.1, Fin.cast X.rkA.symm k.2.2) : D.what₂.Tau × Fin X.B.rank × Fin X.A.rank)) (minorPol D T))) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e4, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun T' _ => ?_
    rw [map_smul, smul_smul, Matrix.smul_apply, smul_eq_mul]
    rfl

end GlobalTheory.NormDict.RealB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawTripleFirstFiniteDatumRiggedFrames
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

namespace GlobalTheory.FrDict

theorem fst_isFinF : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (α β : T → ((AE D)ˣ →* Circle)) (νH : T → Formalism.L2.Host.HChar D.host.E) (S : T → Finset (HeightOneSpectrum (𝓞 D.host.E))) (FA : GlobalTheory.ChainFr.Fr A) (FW : GlobalTheory.ChainFr.Fr WW), (∀ τ, (GlobalTheory.SquareComm.frSgn true FA).cart τ = -X.rA.s τ) → (∀ τ, FW.cart τ = X.rW.s τ) → X.Is ψ θ α β νH S → ∀ t, GlobalTheory.SquareComm.IsFinF ψ θ true FA FW (X.f t) := by
  intro D T A A' WW X ψ θ α β νH S FA FW hFA hFW hX t
  have hv := hX.isVac
  have hν : Formalism.L2.Theta.IsHeckeChar D (α t / β t) := by
    have h := (hX.weil t).hecT
    rw [← inv_div]
    refine ⟨?_, fun x => ?_⟩
    · exact continuous_inv.comp h.1
    · show ((β t / α t) _)⁻¹ = 1
      rw [h.2 x, inv_one]
  have hI : X.ideal S t ≠ ⊥ := by
    unfold Tri.ideal
    rw [← Ideal.zero_eq_bot]
    refine Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ ?_
    rw [Ideal.zero_eq_bot]
    exact w.ne_bot
  obtain ⟨f₁, h1, h1t⟩ := GlobalTheory.Adopt.first_standard_pair_member_has_theta_function D ψ θ A WW X.rA X.rW (α t / β t) (X.e t) (S t) (X.ideal S t) X.vac
    hX.rigA hX.rigW hν (hX.idem t) hI hv
  have heq : X.f t = f₁ := by
    obtain ⟨⟨Tm, hT⟩, hall⟩ := hX.fst t
    rw [hall Tm hT, h1.2 Tm hT]
  have hft : IsThetaFunO ψ (GlobalTheory.Grid.neg A) WW (X.f t) := heq ▸ h1t
  refine ⟨hft, fun τ => ?_⟩
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hX.idem t)
  have hF := GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hv.1.1.1 hv.2.inf ho.infPart_eq ho.conj.infPart_eq
    (hX.fst t) hv.2.theta hft (hv.2.fock τ)
  rw [hFA τ, hFW τ]
  exact hF

end GlobalTheory.FrDict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeActionAdelicLatticeStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.similitude_action_adelic_lattice : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (N : ℕ), 0 < N → N.Coprime p → ∀ t : SimSys D N N, ∃ h ∈ L.KN N, ∀ n : ℕ, 0 < n → n.Coprime p → ∀ x : D.La, ∃ w ∈ LaHat D, L.actG h (inAf D x) = inAf D (t.g n x) + n • w := by
  first | (exact @GlobalTheory.AdelicSim.exists_mem_KN) | (exact GlobalTheory.AdelicSim.exists_mem_KN) | (intros; apply GlobalTheory.AdelicSim.exists_mem_KN <;> assumption)
end

