module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0382
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0102
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0378
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0370
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0324
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0374
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0343
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleRankR
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0368
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalDualityFiniteDiscreteModules
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0344
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitDeltaOfPrismIdealEqSpan
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem isUnit_δ_of_I_eq_span : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B : Obj l R) (d : B.A),
    B.I = Ideal.span {d} → IsUnit (B.D.δ d) := by
  intro l hl R _ B d hI
  by_contra hu
  obtain ⟨m, hm, hdm⟩ := Ideal.exists_le_maximal (Ideal.span {B.D.δ d})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hδd : B.D.δ d ∈ m := hdm (Ideal.mem_span_singleton_self _)
  have hJ : JJ B ≤ m := by
    have h1 : JJ B ≤ (⊥ : Ideal B.A).jacobson := @IsAdicComplete.le_jacobson_bot _ _ _ B.complete
    exact h1.trans (sInf_le ⟨bot_le, hm⟩)
  have hlm : (l : B.A) ∈ m := hJ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))
  have hdm' : d ∈ m := hJ (Ideal.mem_sup_right (by rw [hI]; exact Ideal.mem_span_singleton_self _))
  have hmem := B.l_mem
  rw [hI, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton_sup] at hmem
  obtain ⟨a, y, hy, hle⟩ := hmem
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  have hl2 : 2 ≤ l := hl.out.two_le
  have hφ : B.D.φ d ∈ m ^ 2 := by
    rw [B.D.φ_eq]
    refine Ideal.add_mem _ ?_ ?_
    · have : d ^ l = d ^ 2 * d ^ (l - 2) := by rw [← pow_add]; congr 1; omega
      rw [this]; exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hdm' 2)
    · rw [pow_two]; exact Ideal.mul_mem_mul hlm hδd
  have hy2 : c * B.D.φ d ∈ m ^ (1 + 1) := Ideal.mul_mem_left _ _ hφ
  have hδy : B.D.δ (c * B.D.φ d) ∈ m := by
    simpa using _root_.GlobalTheory.BSP.delta_pow_succ_mem_pow l B.A B.D m hlm 1 _ hy2
  have hδad : B.D.δ (a * d) ∈ m := by
    rw [B.D.δ_mul]
    refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_
    · exact Ideal.mul_mem_left _ _ hδd
    · exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hdm' _ hl.out.pos)
    · exact Ideal.mul_mem_left _ _ hδd
  have hsum : ∑ k ∈ Finset.Ioo 0 l, ((l.choose k / l : ℕ) : B.A) * (a * d) ^ k * (c * B.D.φ d) ^ (l - k) ∈ m :=
    Ideal.sum_mem _ fun k hk =>
      Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _
        (Ideal.pow_mem_of_mem _ (Ideal.mul_mem_left _ _ hdm') _ (Finset.mem_Ioo.1 hk).1))
  have hδl : B.D.δ (l : B.A) ∈ m := by
    rw [← hle, B.D.δ_add]
    exact Ideal.sub_mem _ (Ideal.add_mem _ hδad hδy) hsum
  exact (_root_.GlobalTheory.BSP.LSq.l_not_mem_sq l B.A B.D m hm.ne_top hlm).2 hδl

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnivCharWithUnivChar
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.TwistDet

namespace GlobalTheory.UnivChar

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

section Chosen

def IsUnivChar (Y : NExp D.R D.host D.what₂ D.LL0 N X) : Prop :=
  ∀ i Q M, Y.delU i Q M = GalChar.delU D.host X.cc (X.l i) Q M

def withUnivChar (Y : NExp D.R D.host D.what₂ D.LL0 N X) : NExp D.R D.host D.what₂ D.LL0 N X :=
  { Y with
    delU := fun i Q M => GalChar.delU D.host X.cc (X.l i) Q M
    delU_unr := fun i => (GalChar.universal_anticyclotomic_character_laws D.host X.cc (X.l i)).1
    delU_l := fun i => (GalChar.universal_anticyclotomic_character_laws D.host X.cc (X.l i)).2.1
    delU_anti := fun i => (GalChar.universal_anticyclotomic_character_laws D.host X.cc (X.l i)).2.2.1
    delU_open := fun i => (GalChar.universal_anticyclotomic_character_laws D.host X.cc (X.l i)).2.2.2.1
    delU_res := fun i => (GalChar.universal_anticyclotomic_character_laws D.host X.cc (X.l i)).2.2.2.2.1
    delU_conj := fun i => (GalChar.universal_anticyclotomic_character_laws D.host X.cc (X.l i)).2.2.2.2.2.1 }

end Chosen

section Family


variable (X) in
abbrev Fam (i : X.Tw) (M : ℕ) : Type := PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M)))

variable {i : X.Tw} {M : ℕ} (H : Subgroup (GE N)) (S : Finset (PlE D.host)) (d : Fam X i M)



variable {H S d}

end Family

section Record

variable {H : X.Tw → ℕ → Subgroup (GE N)} {S : X.Tw → ℕ → Finset (PlE D.host)} {d : ∀ i M, Fam X i M}

end Record

theorem delUTie_of_isUnivChar (Y : NExp D.R D.host D.what₂ D.LL0 N X) : K1 X → IsUnivChar Y → DelUTie Y :=
  fun hK hY => GalChar.delUTie_of_exists Y hY hK

end GlobalTheory.UnivChar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsoLocAppendSingleton
section
noncomputable section

namespace GlobalTheory.LocCongrRoad

open GlobalTheory.LiftLeaf GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

private theorem foldr_lpSum_lpTw_lpChar (hL : CharSum N A) {w : PlE H} (x c : A.LP w) (hc : A.lpDim c = 1)
    (s : ℝ) (L : List ℝ) :
    L.foldr (fun k acc => A.lpSum (A.lpTw (A.lpChar x c) (s - k)) acc) (A.lpZero w) =
      A.lpChar (L.foldr (fun k acc => A.lpSum (A.lpTw x (s - k)) acc) (A.lpZero w)) c := by
  induction L with
  | nil => exact ((hL w (A.lpZero w) (A.lpZero w) c 0 hc).2.2).symm
  | cons k L ih =>
    rw [List.foldr_cons, List.foldr_cons, ih, (hL w _ _ c 0 hc).1, (hL w _ (A.lpZero w) c _ hc).2.1]

theorem spehLoc_twist (hL : CharSum N A) (p : Part A.CG) (χ : A.CG 1) (w : PlE H) :
    spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w = A.lpChar (spehLoc N A p w) (A.locG χ w) := by
  unfold spehLoc
  simp only [A.locG_tw]
  exact foldr_lpSum_lpTw_lpChar N A hL (A.locG p.π w) (A.locG χ w) (A.locG_dim χ w) _ _

theorem isoLoc_twist (hL : CharSum N A) (S : List (Part A.CG)) (χ : A.CG 1) (w : PlE H) :
    isoLoc N A (twistIso N A S χ) w = A.lpChar (isoLoc N A S w) (A.locG χ w) := by
  have hχ : A.lpDim (A.locG χ w) = 1 := A.locG_dim χ w
  induction S with
  | nil => exact ((hL w (A.lpZero w) (A.lpZero w) (A.locG χ w) 0 hχ).2.2).symm
  | cons p S ih =>
    change A.lpSum (spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w) (isoLoc N A (twistIso N A S χ) w) =
      A.lpChar (A.lpSum (spehLoc N A p w) (isoLoc N A S w)) (A.locG χ w)
    rw [spehLoc_twist N A hL p χ w, ih, (hL w _ _ _ 0 hχ).1]

theorem isoLoc_append_singleton (S : List (Part A.CG)) (q : Part A.CG) (w : PlE H) :
    isoLoc N A (S ++ [q]) w = A.lpSum (isoLoc N A S w) (spehLoc N A q w) := by
  induction S with
  | nil => exact A.lpSum_comm _ _
  | cons p S ih =>
    change A.lpSum (spehLoc N A p w) (isoLoc N A (S ++ [q]) w) =
      A.lpSum (A.lpSum (spehLoc N A p w) (isoLoc N A S w)) (spehLoc N A q w)
    rw [ih, A.lpSum_assoc]

end GlobalTheory.LocCongrRoad
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LabelTwistMultipliesRootsOfTameLabels
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf

namespace GlobalTheory.TwistLabel

theorem teich_zero' {g : ℕ} [Fact g.Prime] (t : Formalism.CyclotomicNorms.Fbar g →* ℂ)
    (ht : ∀ x y, x ≠ 0 → y ≠ 0 → t x = t y → x = y) : t 0 = 0 := by
  classical
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset (Formalism.CyclotomicNorms.Fbar g))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  by_contra h0
  have h1 : t 0 * t x = t 0 * t 1 := by rw [← map_mul, ← map_mul, zero_mul, zero_mul]
  exact hx.2 (ht x 1 hx.1 one_ne_zero (mul_left_cancel₀ h0 h1))

theorem teich_injective' {g : ℕ} [Fact g.Prime] (t : Formalism.CyclotomicNorms.Fbar g →* ℂ)
    (ht : ∀ x y, x ≠ 0 → y ≠ 0 → t x = t y → x = y) : Function.Injective t := by
  have h0 := teich_zero' t ht
  have hne : ∀ x, x ≠ 0 → t x ≠ 0 := fun x hx => ((IsUnit.mk0 x hx).map t).ne_zero
  intro x y h
  by_cases hx : x = 0
  · by_contra hxy
    exact hne y (fun hy => hxy (hx.trans hy.symm)) (by rw [← h, hx, h0])
  · by_cases hy : y = 0
    · exact absurd (by rw [h, hy, h0]) (hne x hx)
    · exact ht x y hx hy h

theorem prod_scaleRoots {α : Type*} (s : Multiset α) (f : α → ℂ) (c : ℂ) :
    ((s.map fun x => X - C (f x)).prod).scaleRoots c = (s.map fun x => X - C (f x * c)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s IH =>
    rw [Multiset.map_cons, Multiset.prod_cons, mul_scaleRoots', X_sub_C_scaleRoots, IH,
      Multiset.map_cons, Multiset.prod_cons]
    rw [leadingCoeff_X_sub_C, one_mul, ne_eq, leadingCoeff_eq_zero]
    exact (monic_multiset_prod_of_monic _ _ fun a _ => monic_X_sub_C _).ne_zero

theorem roots_prod_map {α : Type*} (s : Multiset α) (f : α → ℂ) :
    ((s.map fun x => X - C (f x)).prod).roots = s.map f := by
  rw [show (s.map fun x => X - C (f x)) = (s.map f).map (fun a => X - C a) by rw [Multiset.map_map]; rfl]
  exact roots_multiset_prod_X_sub_C _

end GlobalTheory.TwistLabel

open GlobalTheory.TwistLabel in
theorem main : ∀ D : D7, SumRepresentations.tie0 D → IneRep D → LabDepth D → LabGen D → LabChar D := by
  intro D hT _ hDep hGen k w hw L χ u hL hχ hχl
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨γ, hγ, hG⟩ := hGen
  have hLP := hT.1
  have hγI : γ k w ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) := (hγ.2 k w hw).1
  have hdim : D.naut.lpDim (D.naut.lpChar L χ) = D.naut.lpDim L := D.naut.lpDim_char L χ hχ
  have hχdeg : (D.naut.items₂ k w χ).natDegree = D.naut.lpDim χ := by rw [hχl, natDegree_X_sub_C, hχ]
  have hχtame : TameLP D χ := ((hDep k w hw χ).2).1 hχdeg
  have hLtame : TameLP D L := ((hDep k w hw L).2).1 hL
  have hLχtame : TameLP D (D.naut.lpChar L χ) := by
    intro σ hσ hwσ
    have h1 := hχtame σ hσ hwσ
    rw [hχ, pow_one] at h1
    have h2 := ((hLP w L L χ χ 0 hχ hχ).2.2.2.2.2 σ hσ).2 1 (by rw [h1, map_one])
    rw [h2, hLtame σ hσ hwσ, scaleRoots_one, hdim]
  have hfull : (D.naut.items₂ k w (D.naut.lpChar L χ)).natDegree = D.naut.lpDim L := by
    rw [← hdim]; exact ((hDep k w hw _).2).2 hLχtame
  refine ⟨hfull, ?_⟩
  set u' := algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (u : ZMod (D.host.g k)) with hu'
  have hrχ : Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w χ) = {u'} := by
    rw [hχl, Formalism.CyclotomicNorms.rootsBar, Polynomial.map_sub, map_X, map_C, roots_X_sub_C]
  have hχγ : D.naut.inePol χ (γ k w) = X - C (D.ntypes.teichC k u') := by
    rw [hG k w hw χ hχdeg, hrχ]; simp
  have hsc := ((hLP w L L χ χ 0 hχ hχ).2.2.2.2.2 (γ k w) hγI).2 _ hχγ
  rw [hG k w hw L hL, prod_scaleRoots, hG k w hw _ (hfull.trans hdim.symm)] at hsc
  have hr := congrArg Polynomial.roots hsc
  rw [roots_prod_map, roots_prod_map] at hr
  have hinj := teich_injective' (D.ntypes.teichC k) (D.ntypes.teichC_inj k)
  apply Multiset.map_injective hinj
  rw [hr, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro x _
  simp [Function.comp, map_mul]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LamConductorExponent
section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie

theorem mu0_del_tame {D : D7} (C : CharFrame D) (l : ℕ) (j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    (C.mu0 j * C.delAt l).LevelLe w 1 := by
  have hd : (C.delAt l).TameAt w := by
    unfold CharFrame.delAt; split_ifs
    · exact C.isDel'.tame w
    · exact C.isDel.tame w
  exact HChar.LevelLe.mul ((C.isMu0 j).tame w) hd

theorem mu0_del_unr {D : D7} (C : CharFrame D) (l : ℕ) (j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : ¬ Over4 D.host w) : (C.mu0 j * C.delAt l).UnrAt w := by
  have h1 : ∀ k, ¬ OverP D.host (D.host.g k) w := fun k hk => hw (Or.inl ⟨k, hk⟩)
  have hd : (C.delAt l).UnrAt w := by
    unfold CharFrame.delAt; split_ifs
    · exact C.isDel'.unr w (fun h => hw (Or.inr (Or.inr h)))
    · exact C.isDel.unr w (fun h => hw (Or.inr (Or.inl h)))
  exact HChar.UnrAt.mul ((C.isMu0 j).unr w h1) hd

theorem lam0_expAt : ∀ (D : D7) (Z : LamDat D), Z.Ok → ∀ (l : ℕ) (j a : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E)),
    ExpAt (Z.lam0 l j a) w (expIn (cond0 D.host Z.w0) (below w)) := by
  intro D Z hZ l j a w
  obtain ⟨h4, h0, hO⟩ := expIn_cond0 D.R D.host Z.q0 Z.w0 hZ.places w
  have hA := hZ.aux a
  unfold LamDat.lam0
  by_cases hw : Over4 D.host w
  · rw [h4 hw]
    exact expAt_mul_inv _ (Z.chi a) _ w 2 (by norm_num) (hA.two w hw) (mu0_del_tame Z.C l j w)
  · by_cases hb : below w = below Z.w0
    · rw [(h0 hb).2]
      have hu := mu0_del_unr Z.C l j w hw
      exact expAt_mul_inv _ (Z.chi a) _ w 1 le_rfl (hA.one w hb) ((HChar.unrAt_iff _ _).1 hu)
    · rw [hO hw hb]
      have hu := HChar.UnrAt.mul (mu0_del_unr Z.C l j w hw) (HChar.UnrAt.inv (hA.unr w hw hb))
      intro m
      exact ⟨fun _ => Nat.zero_le m, fun _ => HChar.UnrAt.levelLe hu m⟩

end GlobalTheory.LamTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeDualCyclotomic
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory

theorem tate_double_annihilator : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l), ∀ (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ S : Submodule O (↥(GK K) → A'.V ⧸ LA'.T), BD LA' ≤ S → S ≤ divisibleCocycles LA' → ∀ c ∈ divisibleCocycles LA', (∀ d ∈ latticeCocycles LA, (∀ s ∈ S, CobO (P.PD K) L1 (cupLD LA' m d s)) → CobO (P.PD K) L1 (cupLD LA' m d c)) → c ∈ S := by
  intro hT l _ P K LL _ _ _ O _ _ hO L1 hL1 A A' LA LA' m hdual S hBS hSZ c hc hann
  obtain ⟨β, hβ0, hβB, -⟩ := GlobalTheory.T.integral_tate_pairing_lattice_dual hT l P K LL O hO L1 hL1 A A' LA LA' m hdual
  haveI : Module.Finite O (LatticeCohomology LA) := GlobalTheory.T.finite_H1_period_datum hT l P K LL O hO A LA
  let e : (LL ⧸ L1.T) ≃ₗ[O] (LL ⧸ LinearMap.range (Algebra.linearMap O LL)) :=
    Submodule.quotEquivOfEq _ _ hL1
  let β₁ : ↥(latticeCocycles LA) →ₗ[O] ↥(divisibleCocycles LA') →ₗ[O] (LL ⧸ LinearMap.range (Algebra.linearMap O LL)) :=
    β.compr₂ e.toLinearMap
  have hβ₁ : ∀ d c, β₁ d c = 0 ↔ β d c = 0 := fun d c => by
    simp only [β₁, LinearMap.compr₂_apply, LinearEquiv.coe_coe]
    exact e.map_eq_zero_iff
  have hker : (latticeCoboundaries LA).comap (latticeCocycles LA).subtype ≤ LinearMap.ker β₁ := by
    intro d hd
    rw [LinearMap.mem_ker]
    ext c
    exact (hβ₁ d c).2 (hβB d c hd)
  let β₂ : LatticeCohomology LA →ₗ[O] ↥(divisibleCocycles LA') →ₗ[O] (LL ⧸ LinearMap.range (Algebra.linearMap O LL)) :=
    ((latticeCoboundaries LA).comap (latticeCocycles LA).subtype).liftQ β₁ hker
  have hβ₂ : ∀ d c, β₂ (Submodule.Quotient.mk d) c = β₁ d c := fun d c => rfl
  have key := GlobalTheory.T.mem_of_forall_annihilator_annihilator_fieldModIntegers l LL O hO (LatticeCohomology LA) ↥(divisibleCocycles LA') β₂ (S.comap (divisibleCocycles LA').subtype) ?_
    ⟨c, hc⟩ ?_
  · exact key
  · intro c' hc'
    show c'.1 ∈ S
    apply hBS
    apply GlobalTheory.T.lattice_dual_pairing_cyclotomic hT l P K LL O hO L1 hL1 A A' LA LA' m hdual c'.1 c'.2
    intro d hd
    have h := hc' (Submodule.Quotient.mk ⟨d, hd⟩)
    rw [hβ₂, hβ₁] at h
    exact (hβ0 ⟨d, hd⟩ c').1 h
  · intro d hd
    induction d using Submodule.Quotient.induction_on with
    | _ d0 =>
    rw [hβ₂, hβ₁]
    apply (hβ0 d0 ⟨c, hc⟩).2
    apply hann d0.1 d0.2
    intro s hs
    have h := hd ⟨s, hSZ hs⟩ hs
    rw [hβ₂, hβ₁] at h
    exact (hβ0 d0 ⟨s, hSZ hs⟩).1 h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LenUnitLeOfFamily
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules

namespace GlobalTheory.EtaFromCut

open Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br Formalism.NG Formalism.NG.QuotientPowerLengths IsDiscreteValuationRing

section General

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X : Type} [Fintype X]
  {M : Type} [AddCommGroup M] [Module O M] [Module.Finite O M]
  (T : Subalgebra O (X → O)) (act : T →ₐ[O] Module.End O M)

theorem congMod_le_of_family (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y) (S : Finset X)
    (E : Set (Module.End O M)) (a : X → O)
    (hc : ∀ α ∈ E, ∀ f : T, α * act f = act f * α)
    (h1 : ∀ x ∈ S, ∃ α ∈ E, ∀ u ∈ Vx T (actK T act).toRingHom x,
      α.baseChange (FractionRing O) u = a x • u)
    (h0 : ∀ α ∈ E, ∀ x, x ∉ S → ∀ u ∈ Vx T (actK T act).toRingHom x,
      α.baseChange (FractionRing O) u = 0) :
    Module.length O (CongMod T (actK T act).toRingHom (latIn O M) (S : Set X)) ≤
      ∑ x ∈ S, (finrank (FractionRing O) (Vx T (actK T act).toRingHom x) : ℕ∞) * addVal O (a x) := by
  have hspan := eigSpan T act hsep
  have hcK : ∀ α ∈ E, ∀ f : T, α.baseChange (FractionRing O) * (actK T act).toRingHom f =
      (actK T act).toRingHom f * α.baseChange (FractionRing O) := by
    intro α hα f
    show α.baseChange (FractionRing O) * (act f).baseChange (FractionRing O) =
      (act f).baseChange (FractionRing O) * α.baseChange (FractionRing O)
    rw [← LinearMap.baseChange_mul, hc α hα f, LinearMap.baseChange_mul]
  refine congMod_le hspan (latIn O M) fg_latIn S ((fun α => α.baseChange (FractionRing O)) '' E)
    (fun x => addVal O (a x)) ?_ ?_ ?_ ?_
  · rintro _ ⟨α, hα, rfl⟩ f
    exact hcK α hα f
  · rintro _ ⟨α, hα, rfl⟩ v hv
    exact baseChange_latIn α v hv
  · rintro _ ⟨α, hα, rfl⟩ v _
    have hle : (⨆ x, Vx T (actK T act).toRingHom x) ≤
        (Formalism.NG.VS T (actK T act).toRingHom (S : Set X)).comap (α.baseChange (FractionRing O)) := by
      refine iSup_le fun x u hu => ?_
      rw [Submodule.mem_comap]
      by_cases hx : x ∈ S
      · refine le_iSup₂ (f := fun y (_ : y ∈ (S : Set X)) => Vx T (actK T act).toRingHom y) x hx ?_
        refine mem_Vx.mpr fun f => ?_
        rw [← Module.End.mul_apply, ← hcK α hα f, Module.End.mul_apply, mem_Vx.mp hu f,
          LinearMap.map_smul_of_tower]
      · rw [h0 α hα x hx u hu]
        exact zero_mem _
    rw [hspan] at hle
    exact hle (Submodule.mem_top (x := v))
  · intro x hx
    obtain ⟨α, hα, h⟩ := h1 x hx
    exact ⟨_, ⟨α, hα, rfl⟩, a x, h, le_rfl⟩

theorem lenUnit_le_of_family (l : ℕ) (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y) (S : Finset X)
    (E : Set (Module.End O M)) (a : X → O) (ha : ∀ x ∈ S, a x ≠ 0)
    (hc : ∀ α ∈ E, ∀ f : T, α * act f = act f * α)
    (h1 : ∀ x ∈ S, ∃ α ∈ E, ∀ u ∈ heckeEig T act x, α.baseChange (FractionRing O) u = a x • u)
    (h0 : ∀ α ∈ E, ∀ x, x ∉ S → ∀ u ∈ heckeEig T act x, α.baseChange (FractionRing O) u = 0) :
    lenUnit (O := O) l
        (↥((latIn O M ⊔ (⨆ x ∈ (S : Set X)ᶜ, heckeEig T act x).restrictScalars O) ⊓
            (⨆ x ∈ (S : Set X), heckeEig T act x).restrictScalars O) ⧸
          (latIn O M ⊓ (⨆ x ∈ (S : Set X), heckeEig T act x).restrictScalars O).comap
            ((latIn O M ⊔ (⨆ x ∈ (S : Set X)ᶜ, heckeEig T act x).restrictScalars O) ⊓
              (⨆ x ∈ (S : Set X), heckeEig T act x).restrictScalars O).subtype) ≤
      ∑ π ∈ S, (heckeMult T act π : ℚ) * lenUnit (O := O) l (O ⧸ Ideal.span {a π}) := by
  have hE : heckeEig T act = Vx T (actK T act).toRingHom := funext (heckeEig_eq T act)
  rw [hE] at h1 h0
  have hlen := (len_le T act hsep (latIn O M) S).trans
    (congMod_le_of_family T act hsep S E a hc h1 h0)
  simp only [heckeMult, lenUnit, IdempotentNormalFormsLenFacts.length_quot_span]
  rw [hE]
  have hsum : ∑ x ∈ S, (Module.finrank (FractionRing O) (Vx T (actK T act).toRingHom x) : ℕ∞) *
        addVal O (a x) =
      ((∑ x ∈ S, Module.finrank (FractionRing O) (Vx T (actK T act).toRingHom x) *
        (addVal O (a x)).toNat : ℕ) : ℕ∞) := by
    push_cast
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [ENat.natCast_toNat (fun h => ha x hx (addVal_eq_top_iff.mp h))]
  rw [hsum] at hlen
  have hnat := ENat.toNat_le_of_le_natCast hlen
  simp only [← mul_div_assoc, ← Finset.sum_div]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  exact_mod_cast hnat

end General

theorem etaBound_of_fam : ∀ (D : D7) (CT : ℕ) (i : D.nd.Loc) (k : Fin 2) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (eta : ℕ), CongruenceFamilyEndomorphisms CT i k ρ eta → EtaBound CT i k ρ eta := by
  rintro D CT i k ρ eta ⟨E, a, c, hE, hg⟩
  refine ⟨c, ?_, fun π hπ => (hg π hπ).2.2.2⟩
  rw [etaLoc_eq]
  refine (lenUnit_le_of_family (D.nd.T i) (D.nd.act i) (D.nd.l i) (D.nd.T_sep i) (D.nd.Zgood i) E a
    (fun π hπ => (hg π hπ).1) (fun α hα => (hE α hα).1) (fun π hπ => (hg π hπ).2.1)
    (fun α hα => (hE α hα).2)).trans ?_
  exact Finset.sum_le_sum fun π hπ =>
    mul_le_mul_of_nonneg_left (hg π hπ).2.2.1 (Nat.cast_nonneg _)

theorem etaBound_of_cut : ∀ (D : D7) (CT : ℕ) (i : D.nd.Loc) (k : Fin 2) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (eta : ℕ), CongruenceLocalDecomposition CT i k ρ eta → EtaBound CT i k ρ eta :=
  fun D CT i k ρ eta h => etaBound_of_fam D CT i k ρ eta (GlobalTheory.CutFam.fam_of_cut D CT i k ρ eta h)

end GlobalTheory.EtaFromCut
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalDualityFiniteDiscreteModulesStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.ResDual
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_duality_finite_discrete_modules : PoitouTateTotallyComplex → LocalFiniteness → GlobalFiniteness → GlobalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [Finite k] [CharP k l] (M : Type) [AddCommGroup M] [Module k M] [TopologicalSpace M] [DiscreteTopology M] [Finite M] (M' : Type) [AddCommGroup M'] [Module k M'] [TopologicalSpace M'] [DiscreteTopology M'] [Finite M'] (ρ : Representation k (G F Ω) M) (ρ' : Representation k (G F Ω) M') (χ : G F Ω → k) (P : M →ₗ[k] M' →ₗ[k] k), ContAction ρ → ContAction ρ' → (∀ g, χ g = (((cycMod F Ω l 1 g : (ZMod (l ^ 1))ˣ) : ZMod (l ^ 1)).val : k)) → (∀ x, (∀ y, P x y = 0) → x = 0) → (∀ y, (∀ x, P x y = 0) → y = 0) → (∀ g x y, P (ρ g x) (ρ' g y) = χ g * P x y) → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (A : Formalism.GaloisCohomology.Places F Ω), ContainsAbove S l → (∀ v ∉ S, ∀ B : ValuationSubring Ω, IsPlaceOver B v → ∀ σ ∈ Ine (F := F) B, ρ σ = 1) → ∀ (L : ∀ v, Submodule k (H1 (ρ.comp (Dec (F := F) (A.1 v)).subtype))) (L' : ∀ v, Submodule k (H1 (ρ'.comp (Dec (F := F) (A.1 v)).subtype))), (∀ v ∉ S, L v = Formalism.GaloisCohomology.unrAt ρ (A.1 v)) → (∀ v ∉ S, L' v = Formalism.GaloisCohomology.unrAt ρ' (A.1 v)) → (∀ v ∈ S, ∀ y : Z1 (ρ'.comp (Dec (F := F) (A.1 v)).subtype), Submodule.Quotient.mk y ∈ L' v ↔ ∀ x : Z1 (ρ.comp (Dec (F := F) (A.1 v)).subtype), Submodule.Quotient.mk x ∈ L v → CupCob (fun g : Dec (F := F) (A.1 v) => χ g.1) (ρ'.comp (Dec (F := F) (A.1 v)).subtype) P x.1 y.1) → Finite (Formalism.GaloisCohomology.SelAll ρ A L) ∧ Finite (Formalism.GaloisCohomology.SelAll ρ' A L') ∧ Nat.card (Formalism.GaloisCohomology.SelAll ρ A L) * Nat.card (H0 ρ') * (∏ v ∈ S, Nat.card (H0 (ρ.comp (Dec (F := F) (A.1 v)).subtype))) * Nat.card M ^ InfinitePlace.nrComplexPlaces F = Nat.card (Formalism.GaloisCohomology.SelAll ρ' A L') * Nat.card (H0 ρ) * ∏ v ∈ S, Nat.card (L v) := by
  first | exact @GlobalTheory.DualPairFormula.greenbergWiles_dualPair | exact GlobalTheory.DualPairFormula.greenbergWiles_dualPair | (intros; apply GlobalTheory.DualPairFormula.greenbergWiles_dualPair <;> assumption)
end

