module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1483
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1380
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1486
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1484
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1479

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerTangentVectorsLift
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagTan

theorem le_preimage_of_trivSqZeroExt {L M : Type} [Field L] [AddCommGroup M] [Module L M] [Module Lᵐᵒᵖ M]
    [IsCentralScalar L M] {T : Scheme.{0}} (φ : TrivSqZeroExt L M →+* L) (hφ : ∀ a, φ a = a.fst)
    (x : Sp (TrivSqZeroExt L M) ⟶ T) (V : T.Opens) (h : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ V) : ⊤ ≤ x ⁻¹ᵁ V := by
  intro s _
  let q : PrimeSpectrum L := ⟨⊥, Ideal.isPrime_bot⟩
  have hp : (spMap φ) q = s := by
    refine PrimeSpectrum.ext (Ideal.ext fun a => ?_)
    change φ a ∈ (⊥ : Ideal L) ↔ a ∈ s.asIdeal
    rw [Ideal.mem_bot, hφ]
    constructor
    · intro ha
      refine s.2.mem_of_pow_mem 2 ?_
      rw [show a ^ 2 = 0 by
        rw [pow_two, show a = TrivSqZeroExt.inr a.snd from TrivSqZeroExt.ext ha rfl, TrivSqZeroExt.inr_mul_inr]]
      exact s.asIdeal.zero_mem
    · intro ha
      by_contra h0
      exact s.2.ne_top (s.asIdeal.eq_top_of_isUnit_mem ha (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (Ne.isUnit h0)))
  have h₁ : (spMap φ ≫ x) q ∈ V := h (Set.mem_univ _)
  exact hp ▸ h₁

theorem IsKS.sum_of_der : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {K : Type} [Field K] [Algebra c.F K] {y : FrPt Xo c K} (hy : KSIso (psiSet H) y)
    {ι : Type} [Fintype ι] {x : ι → (Sp (DualNumber K) ⟶ Xo.X)} (hx : ∀ a, GlobalTheory.FlagTan.IsTanX y (x a))
    {Mx : ι → HIx Dw (psiSet H) → K} (hM : ∀ a, GlobalTheory.FlagTan.IsKS (psiSet H) y (x a) (Mx a))
    {x' : Sp (DualNumber K) ⟶ Xo.X} (hx' : GlobalTheory.FlagTan.IsTanX y x') (m : ι → K)
    (h : ∀ (O : Xo.X.Opens) (f : Γ(Xo.X, O)) (h' : ⊤ ≤ x' ⁻¹ᵁ O) (hc : ∀ a, ⊤ ≤ x a ⁻¹ᵁ O),
      (evalPt x' O h' f).snd = ∑ a, m a * (evalPt (x a) O (hc a) f).snd), GlobalTheory.FlagTan.IsKS (psiSet H) y x' (∑ a, m a • Mx a) := by
  intro E _ _ _ H Dw l Xo c K _ _ y hy ι _ x hx Mx hM x' hx' m h
  obtain ⟨X, -, hXy, hX⟩ := hy
  have ex : ∀ a, x a = spMap (dir c (Mx a)).toRingHom ≫ X := fun a => ((hX _ (hx a)).2 _).1 (hM a)
  refine ((hX x' hx').2 _).2 ?_
  obtain ⟨U, hU, hpU, -⟩ := Opens.isBasis_iff_nbhd.1 Xo.X.isBasis_affineOpens
    (Opens.mem_top (y.x (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)))
  have hyU : ⊤ ≤ y.x ⁻¹ᵁ U := fun s _ => by
    have : s = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K) := Subsingleton.elim _ _
    subst this
    exact hpU
  have hXU : ⊤ ≤ X ⁻¹ᵁ U :=
    le_preimage_of_trivSqZeroExt (TrivSqZeroExt.fstHom c.F K (HIx Dw (psiSet H) → K)).toRingHom (fun _ => rfl) X U
      (by rw [hXy]; exact hyU)
  have htan : ∀ z : Sp (DualNumber K) ⟶ Xo.X, IsTanX y z → ⊤ ≤ z ⁻¹ᵁ U := fun z hz =>
    le_preimage_of_trivSqZeroExt (red c K).toRingHom (fun _ => rfl) z U (by rw [hz.2]; exact hyU)
  have hev : ∀ (N : HIx Dw (psiSet H) → K) (z : Sp (DualNumber K) ⟶ Xo.X)
      (hz : z = spMap (dir c N).toRingHom ≫ X) (hzU : ⊤ ≤ z ⁻¹ᵁ U) (f : Γ(Xo.X, U)),
      evalPt z U hzU f = dir c N (evalPt X U hXU f) := by
    intro N z hz hzU f
    subst hz
    exact evalPt_spMap_comp _ X U hXU hzU f
  have hx'U := htan x' hx'
  have hcU : ∀ a, ⊤ ≤ x a ⁻¹ᵁ U := fun a => htan _ (hx a)
  set M'' : HIx Dw (psiSet H) → K := ∑ a, m a • Mx a
  have hzU : ⊤ ≤ (spMap (dir c M'').toRingHom ≫ X) ⁻¹ᵁ U := by
    intro s hs
    exact hXU (Set.mem_univ _)
  refine ext_evalPt hU hx'U hzU (RingHom.ext fun f => ?_)
  rw [hev M'' _ rfl hzU f]
  refine TrivSqZeroExt.ext ?_ ?_
  · have e1 := evalPt_spMap_comp (red c K).toRingHom x' U hx'U (by rw [hx'.2]; exact hyU) f
    have e2 := evalPt_spMap_comp (TrivSqZeroExt.fstHom c.F K (HIx Dw (psiSet H) → K)).toRingHom X U hXU
      (by rw [hXy]; exact hyU) f
    simp only [hx'.2, hXy] at e1 e2
    rw [fst_dir]
    exact e1.symm.trans e2
  · rw [h U f hx'U hcU, snd_dir]
    simp only [fun a => hev (Mx a) (x a) (ex a) (hcU a) f, snd_dir, M'', Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => by ring

end GlobalTheory.FlagTan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevRowSuccInfUA
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.FunObj.LevRowSucc

open GlobalTheory.AdIsom GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents

variable {D : D7}

theorem mem_O_iff {w : Pl D.host.E} (a : Kw w) : a ∈ 𝒪[Kw w] ↔ Valued.v a ≤ 1 := by
  have : (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (valuation (Kw w)) Valued.v).le_one_iff_le_one

theorem inBasis_val {n n' : ℕ} (h : n' = n) (β x : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E) (i j : Fin n') :
    (inBasis h β w x).val i j = cpt w ((β⁻¹ * x * β).val (Fin.cast h i) (Fin.cast h j)) := by
  simp only [inBasis, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  rfl

theorem ent_of_KO {n n' : ℕ} (h : n' = n) (β x : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E)
    (hx : inBasis h β w x ∈ KO (Kw w) (Fin n')) :
    (∀ i j, Valued.v (cpt w ((β⁻¹ * x * β).val i j)) ≤ 1) ∧ ∀ i j, Valued.v (cpt w ((β⁻¹ * x⁻¹ * β).val i j)) ≤ 1 := by
  subst h
  obtain ⟨h1, h2⟩ := (mem_KO_iff _).1 hx
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · have := (mem_O_iff _).1 (h1 i j)
    rwa [inBasis_val] at this
  · have := (mem_O_iff _).1 (h2 i j)
    rwa [← map_inv, inBasis_val] at this

theorem KO_of_St {n n' : ℕ} (h : n' = n) (β : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E) {x : GL (Fin n) (Lev.EAf D)}
    (hx : x ∈ St β) : inBasis h β w x ∈ KO (Kw w) (Fin n') := by
  subst h
  obtain ⟨z, rfl⟩ := hx
  have e1 : β⁻¹ * frGL β z * β = intGL D.host.F D.host.E _ z := by
    show β⁻¹ * (β * intGL D.host.F D.host.E _ z * β⁻¹) * β = _
    group
  have e2 : β⁻¹ * (frGL β z)⁻¹ * β = intGL D.host.F D.host.E _ z⁻¹ := by
    rw [← map_inv]
    show β⁻¹ * (β * intGL D.host.F D.host.E _ z⁻¹ * β⁻¹) * β = _
    group
  refine (mem_KO_iff _).2 ⟨fun i j => (mem_O_iff _).2 ?_, fun i j => (mem_O_iff _).2 ?_⟩
  · rw [inBasis_val, e1]
    exact (mem_OA _).1 (z.val _ _).2 w
  · rw [← map_inv, inBasis_val, e2]
    exact (mem_OA _).1 ((z⁻¹).val _ _).2 w

theorem idem_smul_mem {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {β : GL (Fin n) (Lev.EAf D)}
    (hβ : IsFrame β Λ) {w : Pl D.host.E} {x : GL (Fin n) (Lev.EAf D)}
    (hx : ∀ i j, Valued.v (cpt w ((β⁻¹ * x * β).val i j)) ≤ 1) {y : Fin n → Lev.EAf D} (hy : y ∈ hat Λ) :
    idem w • (x.val *ᵥ y) ∈ hat Λ := by
  rw [mem_hat, hβ] at hy ⊢
  intro i
  have e : (β⁻¹).val *ᵥ (idem w • (x.val *ᵥ y)) = idem w • ((β⁻¹ * x * β).val *ᵥ ((β⁻¹).val *ᵥ y)) := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.val_mul, Units.val_mul,
      Matrix.mul_assoc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [e, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine sum_mem fun j _ => ?_
  rw [← mul_assoc]
  exact mul_mem ((idem_mul_mem_iff w _).2 (hx i j)) (hy j)

theorem hA_unitary {V : HSp D} {x : GL (Fin V.rank) (Lev.EAf D)} (hx : x ∈ UA D.sp.cm V.gram)
    (a b : Fin V.rank → Lev.EAf D) : hA V (x.val *ᵥ a) (x.val *ᵥ b) = hA V a b := by
  have hx' : Formalism.UG.cT (cjA D) x.val * V.gram.map (inc D) * x.val = V.gram.map (inc D) := hx
  have e2 : ∀ u v : Fin V.rank → Lev.EAf D,
      Formalism.UG.hform (cjA D) (V.gram.map (inc D)) u v = (cjA D ∘ u) ⬝ᵥ (V.gram.map (inc D) *ᵥ v) := by
    intro u v
    simp only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, Function.comp_apply, mul_assoc]
  have e3 : cjA D ∘ (x.val *ᵥ b) = (cjA D ∘ b) ᵥ* Formalism.UG.cT (cjA D) x.val := by
    funext i
    rw [Formalism.UG.cT, vecMul_transpose, Function.comp_apply, RingHom.map_mulVec]
  rw [hA_eq, hA_eq, e2, e2, e3, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hx']

theorem transfer {V : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hsd : IsSelfDualC V Λ)
    {x : GL (Fin V.rank) (Lev.EAf D)} (hU : x ∈ UA D.sp.cm V.gram) {w : Pl D.host.E}
    (h : ∀ y ∈ hat Λ, idem w • ((x⁻¹).val *ᵥ y) ∈ hat Λ) {y : Fin V.rank → Lev.EAf D} (hy : y ∈ hat Λ) :
    idem (GlobalTheory.IdemSupport.cP w) • (x.val *ᵥ y) ∈ hat Λ := by
  rw [mem_hat_iff_of_selfDual hsd]
  intro z hz
  have e : z = x.val *ᵥ ((x⁻¹).val *ᵥ z) := by rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
  rw [hA_smul_right, cjA_idem, GlobalTheory.StdFrames.cP_cP, e, hA_unitary hU, ← hA_smul_left]
  exact (mem_hat_iff_of_selfDual hsd y).1 hy _ (h z hz)

theorem givenLevel_succ {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E) (a : ℕ) :
    ∀ b, b ≠ 0 → givenLevel G t w (a + 1, b) = KO (Kw w) (Fin ((locGrid G t w).rank (a + 1, b)))
  | 0, h => absurd rfl h
  | _ + 1, _ => rfl


set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem prodLev_inf_UA {V : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {β : GL (Fin V.rank) (Lev.EAf D)}
    (hβ : IsFrame β Λ) (hsd : IsSelfDualC V Λ) (P : Finset (Pl D.host.E)) {n' : P → ℕ} (hn : ∀ w, n' w = V.rank)
    (K : ∀ w : P, Subgroup (GL (Fin (n' w)) (Kw w.1))) (hK : ∀ w, K w = KO (Kw w.1) (Fin (n' w))) :
    prodLev β P hn K ⊓ UA D.sp.cm V.gram = congLev D.sp.cm V.gram Λ ⊤ := by
  rw [congLev_top]
  have key : ∀ g ∈ prodLev β P hn K ⊓ UA D.sp.cm V.gram, ∀ (Q : Pl D.host.E), ∀ y ∈ hat Λ,
      idem Q • (g.val *ᵥ y) ∈ hat Λ := by
    rintro g hg Q y hy
    obtain ⟨hg, hU⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨hA', hB'⟩ := Subgroup.mem_inf.1 hg
    have hA : ∀ w : P, (∀ i j, Valued.v (cpt w.1 ((β⁻¹ * g * β).val i j)) ≤ 1) ∧
        ∀ i j, Valued.v (cpt w.1 ((β⁻¹ * g⁻¹ * β).val i j)) ≤ 1 := fun w => by
      have := Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 hA' w)
      rw [hK] at this
      exact ent_of_KO _ β g w.1 this
    by_cases hQ : ∃ w ∈ P, Q.under (𝓞 D.host.F) = w.under (𝓞 D.host.F)
    · obtain ⟨w, hw, hQw⟩ := hQ
      rcases GlobalTheory.IdemSupport.eq_or_eq_cP hQw with rfl | rfl
      · exact idem_smul_mem hβ (hA ⟨Q, hw⟩).1 hy
      · exact transfer hsd hU (fun y hy => idem_smul_mem hβ (hA ⟨w, hw⟩).2 hy) hy
    · push Not at hQ
      have := Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hB' Q) hQ)
      exact idem_smul_mem hβ (ent_of_KO _ β g Q this).1 hy
  ext x
  constructor
  · intro hx
    have hS : x ∈ St β := (GlobalTheory.LevSplit.mem_St_iff β Λ hβ x).2
      ⟨fun y hy => mem_hat_of_idem hsd.1.fg fun Q => key x hx Q y hy,
        fun y hy => mem_hat_of_idem hsd.1.fg fun Q => key x⁻¹ (inv_mem hx) Q y hy⟩
    obtain ⟨h1, h2⟩ := (GlobalTheory.LevSplit.mem_St_iff β Λ hβ x).1 hS
    refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).2, ?_⟩
    intro y
    refine ⟨fun hy => h1 y hy, fun hy => ?_⟩
    have := h2 _ hy
    rw [mulVec_mulVec, Units.inv_mul, one_mulVec] at this
    exact this
  · intro hx
    obtain ⟨hU, hst⟩ := Subgroup.mem_inf.1 hx
    have hS : x ∈ St β := (GlobalTheory.LevSplit.mem_St_iff β Λ hβ x).2
      ⟨fun y hy => (hst y).1 hy, fun y hy => (hst _).2 (by rw [mulVec_mulVec, Units.mul_inv, one_mulVec]; exact hy)⟩
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun w => ?_,
      Subgroup.mem_iInf.2 fun w' => Subgroup.mem_iInf.2 fun _ => ?_⟩, hU⟩
    · rw [Subgroup.mem_comap, hK]
      exact KO_of_St _ β w.1 hS
    · rw [Subgroup.mem_comap]
      exact KO_of_St _ β w' hS

end GlobalTheory.FunObj.LevRowSucc

namespace GlobalTheory.FunObj.GridChoice

open GlobalTheory.FunObj.LevRowSucc

theorem levRow_succ_inf_UA {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) {U : Set T}
    (S : GridChoice W U) (t : T) (i : ℕ) (h : i + 1 ≤ D.R.m) :
    S.levRow t (i + 1) h ⊓ UA D.sp.cm (G.V (.grid (i + 1) D.R.m)).gram = G.levMax (.grid (i + 1) D.R.m) := by
  have hm : D.R.m ≠ 0 := by have := D.R.two_le_m; omega
  rw [GridData.levMax]
  exact prodLev_inf_UA (S.B.isFrame (i + 1) D.R.m (by omega) h le_rfl)
    (G.isV (X := .grid (i + 1) D.R.m) ⟨h, le_rfl⟩ fun j e => by cases e).sd (locPl G t) _ _
    fun w => givenLevel_succ G t w.1 i D.R.m hm

end GlobalTheory.FunObj.GridChoice
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviNormalizesUnipotentRadicalBis
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.StdPar GlobalTheory.ResLine
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT)
open Matrix

noncomputable section
namespace GlobalTheory.ResLine.LeviFacts

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}


omit [NumberField E] in
theorem dual_eq {k : ℕ} (C : Matrix (Fin n) (Fin k) E) (g : GAd σ J) (B : Matrix (Fin k) (Fin k) (AF F ⊗[F] E))
    (e : (matHom _ σ J g).1 * adMat F C = adMat F C * B) :
    cT (sigR (AF F) σ) B * adMat F (cT (σ : E →+* E) C * J) * (matHom _ σ J g).1 = adMat F (cT (σ : E →+* E) C * J) := by
  have c1 : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) E), cT (sigR (AF F) σ) (adMat F Z) = adMat F (cT (σ : E →+* E) Z) :=
    fun Z => rfl
  have hu : cT (sigR (AF F) σ) (matHom _ σ J g).1 * adMat F J * (matHom _ σ J g).1 = adMat F J := g.2
  have h1 : adMat F (cT (σ : E →+* E) C * J) = cT (sigR (AF F) σ) (adMat F C) * adMat F J := by
    rw [c1]; exact Matrix.map_mul
  rw [h1, ← Matrix.mul_assoc, ← Formalism.UG.cT_mul, ← e, Formalism.UG.cT_mul, Matrix.mul_assoc, Matrix.mul_assoc,
    ← Matrix.mul_assoc _ (adMat F J), hu]

omit [NumberField E] in
theorem unipRad_fix {k : ℕ} {C : Matrix (Fin n) (Fin k) E} {u : GAd σ J} (hu : u ∈ unipRad σ J C) :
    (matHom _ σ J u).1 * adMat F C = adMat F C := by
  have : unipRad σ J C ≤ frameStab σ J C ⊥ := (Subgroup.closure_le _).2 fun g hg => ⟨1, one_mem _, by
    have h1 := hg.1
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1
    rw [h1]; simp⟩
  obtain ⟨B, hB, e⟩ := this hu
  rw [Subgroup.mem_bot.1 hB] at e
  simpa using e

variable {X Y : Matrix (Fin n) (Fin r) E}

theorem mem_unipRad_iff (hW : IsWittFrame σ J X Y) (k : Fin r) (g : GAd σ J) :
    g ∈ unipRad σ J (initCols X k) ↔ (matHom _ σ J g).1 * adMat F (initCols X k) = adMat F (initCols X k) ∧
      ∀ y, adMat F (cT (σ : E →+* E) (initCols X k) * J) *ᵥ y = 0 →
        ∃ a, adMat F (initCols X k) *ᵥ a = (matHom _ σ J g).1 *ᵥ y - y := by
  have e1 : {i | ∃ k' ∈ ({k} : Finset (Fin r)), i ≤ k'} = {i | i ≤ k} := by simp
  refine ⟨fun hg => ⟨unipRad_fix hg, fun y hy => ?_⟩, fun ⟨h1, h2⟩ => Subgroup.subset_closure ⟨?_, ?_, fun x hx => ?_⟩⟩
  · rw [← unip_singleton hW] at hg
    have := hg.2.2 y (by rw [e1, mem_colPerp_iff]; exact hy)
    rwa [e1, mem_colSpan_iff] at this
  · rw [Matrix.sub_mul, h1, Matrix.one_mul, sub_self]
  · have := dual_eq (initCols X k) g 1 (by rw [h1, Matrix.mul_one])
    rw [Formalism.UG.cT_one, Matrix.one_mul] at this
    rw [Matrix.mul_sub, Matrix.mul_one, this, sub_self]
  · have := h2 (fun i => inclR (F := F) (AF F) (x i)) (by
      funext i
      exact (RingHom.map_mulVec (inclR (F := F) (AF F)) _ x i).symm.trans (by rw [hx]; exact map_zero _))
    exact this.imp fun a ha => by rw [sub_mulVec, one_mulVec, ha]

theorem conj_mem (hW : IsWittFrame σ J X Y) (k : Fin r) {m u : GAd σ J} (hm : m ∈ frameStab σ J (initCols X k) ⊤)
    (hu : u ∈ unipRad σ J (initCols X k)) : m * u * m⁻¹ ∈ unipRad σ J (initCols X k) := by
  rw [mem_unipRad_iff hW] at hu ⊢
  obtain ⟨B', -, e'⟩ := inv_mem hm
  obtain ⟨B, -, e⟩ := hm
  have hmm : (matHom _ σ J m).1 * (matHom _ σ J m⁻¹).1 = 1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  refine ⟨?_, fun y hy => ?_⟩
  · rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Matrix.mul_assoc, Matrix.mul_assoc, e', ← Matrix.mul_assoc (Units.val _) _ B'.1,
      hu.1, ← e', ← Matrix.mul_assoc, hmm, Matrix.one_mul]
  · have hd := dual_eq (initCols X k) m B.1 e
    obtain ⟨a, ha⟩ := hu.2 ((matHom _ σ J m⁻¹).1 *ᵥ y) (by
      rw [← hd, mulVec_mulVec, Matrix.mul_assoc, hmm, Matrix.mul_one, ← mulVec_mulVec, hy, mulVec_zero])
    refine ⟨B.1 *ᵥ a, ?_⟩
    rw [mulVec_mulVec, ← e, ← mulVec_mulVec, ha, mulVec_sub, mulVec_mulVec, mulVec_mulVec, mulVec_mulVec, hmm, one_mulVec,
      map_mul, map_mul, Units.val_mul, Units.val_mul]

theorem eq_one (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) (k : Fin r) {g : GAd σ J}
    (hg : g ∈ unipRad σ J (initCols X k)) (hm : g ∈ frameStab σ J (initCols Y k) ⊤) : g = 1 := by
  rw [mem_unipRad_iff hW] at hg
  obtain ⟨B, -, e⟩ := hm
  have hT : cT (σ : E →+* E) (initCols X k) * J * initCols Y k = 1 := Matrix.ext fun i j =>
    (congrFun (congrFun hW.xy (i.castLE k.2)) (j.castLE k.2)).trans (by simp [Matrix.one_apply])
  have hT' : cT (σ : E →+* E) (initCols Y k) * J * initCols X k = 1 := Matrix.ext fun i j =>
    (congrFun (congrFun (yx h hJ hW) (i.castLE k.2)) (j.castLE k.2)).trans (by simp [Matrix.one_apply])
  have aT : adMat F (cT (σ : E →+* E) (initCols X k) * J) * adMat F (initCols Y k) = 1 := by
    rw [← Matrix.map_mul, hT, Matrix.map_one _ (map_zero _) (map_one _)]
  have aT' : adMat F (cT (σ : E →+* E) (initCols Y k) * J) * adMat F (initCols X k) = 1 := by
    rw [← Matrix.map_mul, hT', Matrix.map_one _ (map_zero _) (map_one _)]
  have d1 := dual_eq (initCols X k) g 1 (by rw [hg.1, Matrix.mul_one])
  rw [Formalism.UG.cT_one, Matrix.one_mul] at d1
  have hB : B.1 = 1 := by
    have := congrArg (adMat F (cT (σ : E →+* E) (initCols X k) * J) * ·) e
    simp only [← Matrix.mul_assoc] at this
    rw [d1, aT, Matrix.one_mul] at this
    exact this.symm
  have d2 := dual_eq (initCols Y k) g _ e
  rw [hB, Formalism.UG.cT_one, Matrix.one_mul] at d2
  rw [hB, Matrix.mul_one] at e
  have h0 : ∀ y, adMat F (cT (σ : E →+* E) (initCols X k) * J) *ᵥ y = 0 → (matHom _ σ J g).1 *ᵥ y = y := fun y hy => by
    obtain ⟨a, ha⟩ := hg.2 y hy
    have := congrArg (adMat F (cT (σ : E →+* E) (initCols Y k) * J) *ᵥ ·) ha
    simp only [mulVec_mulVec, mulVec_sub] at this
    rw [aT', d2, sub_self, one_mulVec] at this
    rw [this, mulVec_zero] at ha
    exact sub_eq_zero.1 ha.symm
  have h1 : ∀ y, (matHom _ σ J g).1 *ᵥ y = y := fun y => by
    have := h0 (y - adMat F (initCols Y k) *ᵥ adMat F (cT (σ : E →+* E) (initCols X k) * J) *ᵥ y) (by
      rw [mulVec_sub, mulVec_mulVec (M := adMat F (cT (σ : E →+* E) (initCols X k) * J)), aT, one_mulVec, sub_self])
    rw [mulVec_sub, mulVec_mulVec (M := (matHom _ σ J g).1), e] at this
    exact sub_left_injective this
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
  have := h1 (Pi.single j 1)
  rw [mulVec_single_one] at this
  exact (congrFun this i).trans (Pi.single_apply _ _ _)

theorem mul_one_by_one {R : Type} [CommRing R] (C : Matrix (Fin n) (Fin 1) R) (B : Matrix (Fin 1) (Fin 1) R) :
    C * B = B.det • C := by
  ext i j
  rw [Subsingleton.elim j 0]
  simp [Matrix.mul_apply, mul_comm]

theorem absE_of_scales {x : Matrix (Fin n) (Fin 1) E} {L : Matrix (Fin 1) (Fin n) E} (hL : L * x = 1) {γ : GAd σ J}
    (hγ : γ ∈ ratPts σ J) {l : (AF F ⊗[F] E)ˣ} (e : Scales σ J x γ l) : absE F E l = 1 := by
  rw [← range_ratEmb] at hγ
  obtain ⟨γ0, rfl⟩ := hγ
  have hmat : (matHom _ σ J (ratEmb σ J γ0)).1 = (γ0.1.1 : Matrix (Fin n) (Fin n) E).map (inclR (F := F) (AF F)) := by
    ext s t; rfl
  have hL' : adMat F L * adMat F x = 1 := by
    rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]
  set c : E := (L * γ0.1.1 * x) 0 0 with hc
  have hl : l.1 = inclR (F := F) (AF F) c := by
    have := congrArg (adMat F L * ·) e
    simp only [Matrix.mul_smul] at this
    rw [hL', hmat, ← Matrix.mul_assoc, ← Matrix.map_mul, ← Matrix.map_mul] at this
    have := congrFun (congrFun this 0) 0
    rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at this
    exact this.symm
  by_cases hc0 : c = 0
  · have : Subsingleton (AF F ⊗[F] E) := by
      have h01 := l.mul_inv
      rw [hl, hc0, map_zero, zero_mul] at h01
      exact subsingleton_of_zero_eq_one h01
    rw [Subsingleton.elim l 1, map_one]
  · have := GlobalTheory.Doubling.absE_inclR (F := F) (E := E) (Units.mk0 c hc0)
    rwa [show (Units.map (inclR (F := F) (AF F)).toMonoidHom (Units.mk0 c hc0)) = l from
      Units.ext (by simp [hl])] at this

theorem levi_facts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J →
    IsWittFrame σ J X Y →
    (∀ m ∈ levi σ J X Y {0}, ∀ u ∈ unipRad σ J (ResLine.col X), m * u * m⁻¹ ∈ unipRad σ J (ResLine.col X)) ∧
    (∀ g ∈ unipRad σ J (ResLine.col X), g ∈ levi σ J X Y {0} → g = 1) ∧
    (∀ γ ∈ ratPts σ J, γ ∈ levi σ J X Y {0} → γ ∈ leviOne σ J X Y {0}) ∧
    (∀ u ∈ unipRad σ J (ResLine.col X), Scales σ J (ResLine.col X) u 1) ∧
    (∀ m ∈ leviOne σ J X Y {0}, ∃ l, Scales σ J (ResLine.col X) m l ∧ absE F E l = 1) ∧
    ∀ γ ∈ ratPts σ J, ∀ l, Scales σ J (ResLine.col X) γ l → absE F E l = 1 := by
  intro F E _ _ _ _ _ σ n J r X Y h hJ hW
  have hc : ResLine.col X = initCols X 0 := by
    ext i j
    rw [Subsingleton.elim j 0]
    rfl
  have hlev : ∀ m ∈ levi σ J X Y {0}, m ∈ frameStab σ J (initCols X 0) ⊤ ∧ m ∈ frameStab σ J (initCols Y 0) ⊤ :=
    fun m hm => by
      simp only [levi, Subgroup.mem_iInf] at hm
      exact hm 0 (Finset.mem_singleton_self _)
  have hT' : cT (σ : E →+* E) (initCols Y 0) * J * initCols X 0 = 1 := Matrix.ext fun i j =>
    (congrFun (congrFun (yx h hJ hW) (i.castLE (0 : Fin (r + 1)).2)) (j.castLE (0 : Fin (r + 1)).2)).trans
      (by simp only [Matrix.one_apply, Fin.castLE_inj])
  have h6 : ∀ γ ∈ ratPts σ J, ∀ l, Scales σ J (initCols X 0) γ l → absE F E l = 1 := fun γ hγ l e =>
    absE_of_scales hT' hγ e
  rw [hc]
  refine ⟨fun m hm u hu => conj_mem hW 0 (hlev m hm).1 hu, fun g hg hm => eq_one h hJ hW 0 hg (hlev g hm).2,
    fun γ hγ hm => ⟨hm, ?_⟩, fun u hu => ?_, fun m hm => ?_, h6⟩
  · show γ ∈ ⨅ k ∈ ({0} : Finset (Fin (r + 1))),
      frameStab σ J (initCols X k) ((absE F E).comp Matrix.GeneralLinearGroup.det).ker
    simp only [Subgroup.mem_iInf]
    intro k hk
    obtain rfl := Finset.mem_singleton.1 hk
    obtain ⟨B, -, e⟩ := (hlev γ hm).1
    exact ⟨B, h6 γ hγ (Matrix.GeneralLinearGroup.det B) (e.trans (mul_one_by_one _ _)), e⟩
  · exact (unipRad_fix hu).trans (one_smul _ _).symm
  · have h2 : m ∈ ⨅ k ∈ ({0} : Finset (Fin (r + 1))),
      frameStab σ J (initCols X k) ((absE F E).comp Matrix.GeneralLinearGroup.det).ker := hm.2
    simp only [Subgroup.mem_iInf] at h2
    obtain ⟨B, hB, e⟩ := h2 0 (Finset.mem_singleton_self _)
    exact ⟨Matrix.GeneralLinearGroup.det B, e.trans (mul_one_by_one _ _), hB⟩

end GlobalTheory.ResLine.LeviFacts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrientedModelThetaFunctionBounded
section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

namespace GlobalTheory.TowerFD

theorem thetaFunOF_bounded : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (nS nT : ℕ)
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
      ∀ f : WOF F E nS nT → ℂ, IsThetaFunOF σ JS JT ξ₀ ψ f → ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := by
  intro F E _ _ _ _ _ σ nS nT JS JT ξ₀ ψ hψ f hf
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨K, hK, hx⟩ := GlobalTheory.AdelicMatrixLattice.cocompact_tensor (F := F) (E := E) (AF F)
    (GlobalTheory.AdeleCocompact.exists_compact_adele F)
  choose c hc using hx
  have hKc : IsCompact (Set.univ.pi (fun _ : Fin nT => Set.univ.pi fun _ : Fin nS => K) :
      Set (WOF F E nS nT)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hK
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hf.cont.continuousOn
  refine ⟨C, fun w => ?_⟩
  have hmem : ratWF (Matrix.of fun i j => c (w i j)) + w ∈
      (Set.univ.pi (fun _ : Fin nT => Set.univ.pi fun _ : Fin nS => K) : Set (WOF F E nS nT)) :=
    fun i _ j _ => hc (w i j)
  have h := hC _ hmem
  have hq := hf.quasi (Matrix.of fun i j => c (w i j)) w
  have h2 : ‖f w‖ = ‖f (ratWF (Matrix.of fun i j => c (w i j)) + w)‖ := by
    rw [hq, norm_mul, hψ.2.1, one_mul]
  exact h2.trans_le h

end GlobalTheory.TowerFD
end

