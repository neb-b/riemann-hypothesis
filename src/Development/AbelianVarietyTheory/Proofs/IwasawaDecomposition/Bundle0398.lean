module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0383
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0392
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0372
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0389
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0253
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceDoubleCosetOperatorsCommuteSpherical
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0390
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0006
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RationalRootsDef
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0346
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0355

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitHeckeOperatorInverseConjugatePlaceCosetSum
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HeckeEigCoset

open GlobalTheory.LFun.ConjPlace

theorem heckeVec_Tj_inv_conj_eq_sum : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L)
    (ϖ : s.v.adicCompletion (maximalRealSubfield L)), IsUnif L s.v ϖ → ∀ (k : ℕ), k ≤ n →
    ∀ (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* (GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L), Continuous i →
    ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) ((GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L)) V)
    (R : Finset (GAf L n)), (∀ γ ∈ R, γ ∈ tSet L n s ϖ k) → (∀ x ∈ tSet L n s ϖ k, ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ Umax L n) →
    ∀ e ∈ GlobalTheory.PRep.fixed ρ (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n),
      GlobalTheory.LFun.heckeVec ρ (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n)
                   (fun g => Formalism.UG.Tj ℂ n (Formalism.UG.Ov L (GlobalTheory.HeckeFrob.conjSplit s).w) (i ϖ) k g⁻¹) e =
        ∑ γ ∈ R, ρ (Matrix.GeneralLinearGroup.map i.toRingHom ((GlobalTheory.HeckeFrob.conjSplit s).loc n γ)) e := by
  intro L _ _ _ n s ϖ hϖ k hk i hi V _ _ ρ R hR1 hR2 e he
  classical
  have hO : ∀ a, i a ∈ Formalism.UG.Ov L (GlobalTheory.HeckeFrob.conjSplit s).w ↔
      a ∈ (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring := by
    intro a
    have h := _root_.GlobalTheory.IsoInteg.valued_le_one_iff_of_continuous _ _ s.v (GlobalTheory.HeckeFrob.conjSplit s).w i hi a
    exact h.trans (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).symm
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    have h0 : Valued.v (0 : s.v.adicCompletion (maximalRealSubfield L)) = WithZero.exp (-1 : ℤ) := hϖ
    rw [map_zero] at h0
    exact WithZero.exp_ne_zero h0.symm
  set ϖu : (s.v.adicCompletion (maximalRealSubfield L))ˣ := Units.mk0 ϖ hϖ0 with hϖu
  have ha : invT i n (dGL n ϖu k) = (dGL n (Units.map (i : _ →* _) ϖu) k)⁻¹ := by
    rw [← invT_dGL, map_inv, inv_inv]
  have h1 : (fun g => Formalism.UG.Tj ℂ n (Formalism.UG.Ov L (GlobalTheory.HeckeFrob.conjSplit s).w) (i ϖ) k g⁻¹) =
      Formalism.UG.dosetInd ℂ (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n) (invT i n (dGL n ϖu k)) := by
    funext g
    have hiϖ : i ϖ = ((Units.map (i : s.v.adicCompletion (maximalRealSubfield L) →* (GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L) ϖu :
        ((GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L)ˣ) : (GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L) := by
      rw [Units.coe_map, hϖu, Units.val_mk0]
      rfl
    rw [hiϖ, Tj_apply, Formalism.UG.dosetInd, Set.indicator_apply, Pi.one_apply]
    refine if_congr ?_ rfl rfl
    rw [DoubleCoset.mem_doubleCoset, ha]
    constructor
    · rintro ⟨x, hx, y, hy, h⟩
      exact ⟨y⁻¹, inv_mem hy, x⁻¹, inv_mem hx, by rw [← inv_inv g, h]; group⟩
    · rintro ⟨x, hx, y, hy, h⟩
      exact ⟨y⁻¹, inv_mem hy, x⁻¹, inv_mem hx, by rw [h]; group⟩
  have hK : ∀ x : GAf L n, TrivOutside {s.v} x → (x ∈ tSet L n s ϖ k ↔ invT i n (s.loc n x) ∈
      DoubleCoset.doubleCoset (invT i n (dGL n ϖu k)) (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n : Set _)
        (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n)) := by
    intro x hx
    rw [tSet, Set.mem_setOf_eq, DoubleCoset.mem_doubleCoset]
    constructor
    · rintro ⟨-, A, hA, B, hB, h⟩
      refine ⟨invT i n A, (mem_iff_invT i hO A).1 hA, invT i n B, (mem_iff_invT i hO B).1 hB, ?_⟩
      have : s.loc n x = A * dGL n ϖu k * B := Units.ext (by rw [Units.val_mul, Units.val_mul, h]; rfl)
      rw [this, map_mul, map_mul]
    · rintro ⟨A', hA', B', hB', h⟩
      obtain ⟨A, rfl⟩ := (invT i n).surjective A'
      obtain ⟨B, rfl⟩ := (invT i n).surjective B'
      rw [← map_mul, ← map_mul, (invT i n).apply_eq_iff_eq] at h
      refine ⟨hx, A, (mem_iff_invT i hO A).2 hA', B, (mem_iff_invT i hO B).2 hB', ?_⟩
      rw [h]
      rfl
  have hφK : ∀ x : GAf L n, TrivOutside {s.v} x →
      (invT i n (s.loc n x) ∈ GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n ↔ x ∈ Umax L n) :=
    fun x hx => (mem_iff_invT i hO _).symm.trans (GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff s hx)
  have hRa : ∀ γ' ∈ R.image (fun γ => invT i n (s.loc n γ)), γ' ∈ DoubleCoset.doubleCoset (invT i n (dGL n ϖu k))
      (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n : Set _) (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n) := by
    intro γ' hγ'
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.1 hγ'
    exact (hK γ (hR1 γ hγ).1).1 (hR1 γ hγ)
  have hRb : ∀ g ∈ DoubleCoset.doubleCoset (invT i n (dGL n ϖu k))
      (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n : Set _) (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n),
      ∃! γ', γ' ∈ R.image (fun γ => invT i n (s.loc n γ)) ∧ γ'⁻¹ * g ∈ GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n := by
    intro g hg
    obtain ⟨-, -, hlift⟩ := _root_.GlobalTheory.SplitAdelic.main L n s
    obtain ⟨x, ⟨hx, hxg⟩, -⟩ := hlift ((invT i n).symm g)
    have hgx : g = invT i n (s.loc n x) := by rw [hxg]; simp
    have hxT : x ∈ tSet L n s ϖ k := (hK x hx).2 (hgx ▸ hg)
    obtain ⟨γ, ⟨hγ, hγx⟩, huniq⟩ := hR2 x hxT
    have key : ∀ δ ∈ R, (invT i n (s.loc n δ))⁻¹ * g ∈ GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n ↔
        δ⁻¹ * x ∈ Umax L n := by
      intro δ hδ
      rw [hgx, ← map_inv, ← map_inv, ← map_mul, ← map_mul]
      exact hφK _ (GlobalTheory.HeckeScalarSph.triv_mul (GlobalTheory.HeckeScalarSph.triv_inv (hR1 δ hδ).1) hx)
    refine ⟨invT i n (s.loc n γ), ⟨Finset.mem_image_of_mem _ hγ, (key γ hγ).2 hγx⟩, ?_⟩
    rintro γ' ⟨hγ', hγ'g⟩
    obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.1 hγ'
    rw [huniq δ ⟨hδ, (key δ hδ).1 hγ'g⟩]
  have hinj : Set.InjOn (fun γ => invT i n (s.loc n γ)) R := by
    intro γ₁ h₁ γ₂ h₂ heq
    have hγ₂ := hR1 γ₂ h₂
    obtain ⟨γ, -, huniq⟩ := hR2 γ₂ hγ₂
    have e1 : γ₁⁻¹ * γ₂ ∈ Umax L n := by
      rw [← hφK _ (GlobalTheory.HeckeScalarSph.triv_mul (GlobalTheory.HeckeScalarSph.triv_inv (hR1 γ₁ h₁).1) hγ₂.1), map_mul, map_mul,
        map_inv, map_inv]
      simp only at heq
      rw [heq, inv_mul_cancel]
      exact one_mem _
    exact (huniq γ₁ ⟨h₁, e1⟩).trans (huniq γ₂ ⟨h₂, by rw [inv_mul_cancel]; exact one_mem _⟩).symm
  rw [h1, GlobalTheory.LFun.heckeVec_dosetInd he hRa hRb, Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [GlobalTheory.HeckeEigConj.map_loc_conjSplit]

end GlobalTheory.HeckeEigCoset
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdDecoratedLatticeRightTranslateLevelQ
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.Mem.R3.LiftBrg.ActQ

theorem castGL_castGL_symm {R : Type} [CommRing R] {a b : ℕ} (h : a = b) (m : GL (Fin b) R) :
    castGL h (castGL h.symm m) = m := by
  subst h
  ext i j
  simp [castGL]

theorem castGL_mem_St_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {a b : ℕ} (h : a = b) (m : GL (Fin a) (E ⊗[F] Formalism.L2.Herm.Af F)) (hm : m ∈ Formalism.L2.DIV.St 1) :
    castGL h m ∈ Formalism.L2.DIV.St 1 := by
  subst h
  have e : castGL (rfl : a = a) m = m := by
    ext i j
    simp [castGL]
  rwa [e]

theorem ptS_mul_Q : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → ValsIn I → LevOf X I U L → ∀ (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (LiftBrg.EA X)), LiftBrg.FrameOK X I U i t A k →
    ∀ (κ : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q) (x : Bridge.Gf (Vc X.toD7 i)),
      LiftBrg.ActQ.ptS X I U i t A k (x * κ) =
        ((1 : Formalism.L2.Col.UF X.B.fields.E X.B.R.nV), (LiftBrg.ActQ.redZ X I U L i t A k κ)⁻¹) • LiftBrg.ActQ.ptS X I U i t A k x := by
  intro X px I U L _ _ hL i t A k hF κ x
  obtain ⟨-, hASt, hAU, hkU, hkSt, -⟩ := hF
  set w : Bridge.Gf (Vc X.toD7 i) → GL (Fin X.B.R.nV) (EA X) := fun g =>
    castGL (rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7) (g : GL (Fin (Vc X.toD7 i).rank) _)) with hw
  have hwmul : w (x * κ) = w x * w κ := by
    simp only [hw, Subgroup.coe_mul, map_mul]

  have hconj : ∀ g : GL (Fin (Vc X.toD7 i).rank) (EA X), g ∈ Formalism.L2.DIV.UA X.toD7.sp.cm (Vc X.toD7 i).gram →
      A⁻¹ * castGL (rkEq X i).symm g * A ∈ Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV := by
    intro g hg
    refine (hAU _).2 ?_
    have e : A * (A⁻¹ * castGL (rkEq X i).symm g * A) * A⁻¹ = castGL (rkEq X i).symm g := by group
    rw [e, castGL_castGL_symm]
    exact hg
  have hxU : Formalism.UG.bc (swapAE X.toD7) ((x : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _) ∈
      Formalism.L2.DIV.UA X.toD7.sp.cm (Vc X.toD7 i).gram := by
    obtain ⟨g, hg⟩ := x.2
    rw [← hg]
    exact GlobalTheory.LevFinCong.finE_mem_UA _ g
  have hκP := mem_parLev_of_Q X I U L i t κ
  have hκU := Formalism.L2.DIV.parLev_UA hκP
  have hκS : Formalism.UG.bc (swapAE X.toD7) ((κ : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _) ∈
      Formalism.L2.DIV.St (1 : GL (Fin (Vc X.toD7 i).rank) (EA X)) := by
    have h0 := Formalism.L2.DIV.parLev_St hκP
    have hb : L.βV i = 1 := hL.beta.1 i
    exact hb ▸ h0
  set y := A⁻¹ * w x * A * k with hy
  set z := (A * k)⁻¹ * w κ * (A * k) with hz
  have hyU : y ∈ Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV := mul_mem (hconj _ hxU) hkU
  have hzU : z ∈ Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV := by
    have e : z = k⁻¹ * (A⁻¹ * w κ * A) * k := by rw [hz]; group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hkU) (hconj _ hκU)) hkU
  have hzS : z ∈ Formalism.L2.DIV.St (1 : GL (Fin X.B.R.nV) (EA X)) := by
    have hwS : w κ ∈ Formalism.L2.DIV.St (1 : GL (Fin X.B.R.nV) (EA X)) := castGL_mem_St_one _ _ hκS
    have hAk := mul_mem hASt hkSt
    exact mul_mem (mul_mem (inv_mem hAk) hwS) hAk
  have hzJ : z ∈ Formalism.L2.Col.J0 X.toD7.sp.cm X.B.R.nV (∅ : Finset (Pl X.toD7.host.E)) :=
    ⟨⟨hzU, hzS⟩, Subgroup.mem_iInf.2 fun P => Subgroup.mem_iInf.2 fun hP => absurd hP (Finset.notMem_empty _)⟩
  have hyz : A⁻¹ * w (x * κ) * A * k = y * z := by
    rw [hwmul, hy, hz]; group
  have hyzU : y * z ∈ Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV := mul_mem hyU hzU
  have hred : Formalism.L2.Col.redG X.toD7.sp.cm X.B.R.nV ∅ (sgL X I U t) ⟨z, hzJ⟩ = redZ X I U L i t A k κ := by
    funext v
    show _ = Formalism.L2.DIV.redFn (1 : GL (Fin X.B.R.nV) (EA X)) v.1 z
    unfold Formalism.L2.DIV.redFn
    rw [Formalism.L2.DIV.extendOne_of_mem _ hzS]
    rfl
  have hraw := GlobalTheory.Mem.Col2.TopCh.decoRaw_mul_levelIwahori_reduction X.toD7.sp.cm ∅ (sgL X I U t) y z hzJ
  rw [hred] at hraw
  apply Subtype.ext
  show (Formalism.L2.Col.decoOf ∅ (sgL X I U t) (A⁻¹ * w (x * κ) * A * k)).1 =
    (Formalism.L2.Col.decoOf ∅ (sgL X I U t) y).1.act 1 (redZ X I U L i t A k κ)⁻¹
  rw [hyz]
  unfold Formalism.L2.Col.decoOf
  rw [dite_eq_left (Formalism.L2.Col.decorated_lattice_exists X.toD7.sp.cm X.B.R.nV ∅ (sgL X I U t) _ hyzU),
    dite_eq_left (Formalism.L2.Col.decorated_lattice_exists X.toD7.sp.cm X.B.R.nV ∅ (sgL X I U t) _ hyU)]
  exact hraw

end GlobalTheory.Mem.R3.LiftBrg.ActQ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdFrameLevelCharacterAtTypePlaceEq
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.DIV

namespace GlobalTheory.MtChr

theorem sum_supEdge_castLE {R : Type} [AddCommMonoid R] {n r : ℕ} (hr : r ≤ n) (f : Fin n → Fin n → R) :
    (∑ i : Fin r, ∑ j : Fin r, if supEdge i j then f (Fin.castLE hr i) (Fin.castLE hr j) else 0) =
      ∑ a : Fin n, ∑ b : Fin n, if a.val + 1 = b.val ∧ b.val < r then f a b else 0 := by
  refine Fintype.sum_of_injective (Fin.castLE hr) (Fin.castLE_injective hr) _ _ ?_ ?_
  · intro a ha
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact ha ⟨⟨a.val, by omega⟩, Fin.ext rfl⟩
  · intro i
    refine Fintype.sum_of_injective (Fin.castLE hr) (Fin.castLE_injective hr) _ _ ?_ ?_
    · intro b hb
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact hb ⟨⟨b.val, h2⟩, Fin.ext rfl⟩
    · intro j
      by_cases hh : supEdge i j
      · have h' : j.val = i.val + 1 := hh
        rw [if_pos hh, if_pos (by simp only [Fin.val_castLE]; exact ⟨h'.symm, j.2⟩)]
      · have h' : ¬ j.val = i.val + 1 := hh
        rw [if_neg hh, if_neg (by simp only [Fin.val_castLE]; exact fun e => h' e.1.symm)]

theorem blkOf_eq_one_iff {n r t : ℕ} (a : Fin n) (ha : a.val < r + t) : blkOf r t a = 1 ↔ r ≤ a.val := by
  unfold blkOf
  by_cases h : a.val < r
  · simp only [h, if_true]; omega
  · simp only [h, if_false]
    rw [Nat.div_eq_of_lt (by omega)]
    omega

theorem edgeSum_supEdge_one {κ : Type} [CommRing κ] {r : ℕ} : edgeSum (κ := κ) (supEdge (r := r)) 1 = 0 := by
  unfold edgeSum
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  split_ifs with hh
  · rw [Units.val_one, Matrix.one_apply_ne]
    intro e; rw [e] at hh; unfold supEdge at hh; omega
  · rfl

theorem det_map_subtype {O k : Type} [CommRing O] [CommRing k] (φ : O →+* k) {n : ℕ} (M : Matrix (Fin n) (Fin n) O)
    (N : Matrix (Fin n) (Fin n) k) (hMN : ∀ a b, N a b = φ (M a b)) (p q : Fin n → Prop) [DecidablePred p] [DecidablePred q]
    (hpq : ∀ a, p a ↔ q a) :
    φ (Matrix.of fun a b : {y // q y} => M a.1 b.1).det = (N.submatrix (Subtype.val : {a // p a} → Fin n) Subtype.val).det := by
  rw [RingHom.map_det]
  rw [← Matrix.det_submatrix_equiv_self (Equiv.subtypeEquivRight hpq) (φ.mapMatrix _)]
  congr 1
  ext a b
  exact (hMN a.1 b.1).symm

end GlobalTheory.MtChr

set_option maxHeartbeats 2000000 in
theorem GlobalTheory.MtChr.levChar_std_uni : ∀ (D : D7) (hr : D.R.r ≤ D.R.nV) (Pg Q : Finset (Pl D.host.E)) (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (chi xi : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (φ : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* kP s.w), (∀ x, φ x = 0 ↔ Valued.v (x : s.v.adicCompletion (maximalRealSubfield D.host.E)) < 1) → (∀ κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV, ∀ a b, ∃ h : (s.loc D.R.nV κ).val a b ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E), (redFn (1 : GL (Fin D.R.nV) (EAf D)) s.w (km D D.R.nV κ)).val a b = φ ⟨_, h⟩) → s.w ∈ Pg → (∀ PP ∈ Pg, PP ≠ s.w → ¬ NG.OverPl PP s.v) → (∀ PP ∈ Q, ¬ NG.OverPl PP s.v) → ∀ (ψ₀ : AddChar (s.v.adicCompletion (maximalRealSubfield D.host.E)) ℂ) (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), (∀ x : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E), ψ₀ (x : s.v.adicCompletion (maximalRealSubfield D.host.E)) = ψ s.w (-φ x)) → (∀ (u : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ) (x : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)) (w : (kP s.w)ˣ), (x : s.v.adicCompletion (maximalRealSubfield D.host.E)) = u → φ x = w → ξ u = (chi s.w)⁻¹ w) → ∀ κ (h : κ ∈ stdJ (datV D D.R.nV hr Pg Q (P0 Pg D.R.r ψ) chi xi)), ReciprocityTheory.Aut.TrivOutside {s.v} κ → ∀ u : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ, (u : s.v.adicCompletion (maximalRealSubfield D.host.E)) = NG.detDD s D.R.r (s.loc D.R.nV κ) → ((stdX (datV D D.R.nV hr Pg Q (P0 Pg D.R.r ψ) chi xi) ⟨κ, h⟩ : ℂˣ) : ℂ) = ψ₀ (NG.supDiag s D.R.r (s.loc D.R.nV κ)) * ξ u := by
  intro D hr Pg Q ψ chi xi s φ hφ0 hred hsw hPg hQ ψ₀ ξ hψ₀ hξ κ h htriv u hu
  set Ld := GlobalTheory.MtIn.datV D D.R.nV hr Pg Q (P0 Pg D.R.r ψ) chi xi
  set x := km D D.R.nV κ
  have hL : x ∈ lev D.sp.cm 1 1 Ld := h
  have hpar : x ∈ parLev D.sp.cm 1 1 Ld := hL.1
  have hP0 : rTup 1 Ld x ∈ (P0 Pg D.R.r ψ).conj.H := hL.2
  obtain ⟨-, hStU, hout, -⟩ := _root_.GlobalTheory.MtRed.km_reduction D D.R.nV
  have hU : κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV := (hStU κ).1 (parLev_St hpar)
  have hg : ∀ PP ∈ Pg, redFn 1 PP x ∈ blockTri (blkOf D.R.r D.R.t) := fun PP hP => parLev_g hpar hP
  have triv : ∀ PP : Pl D.host.E, ¬ NG.OverPl PP s.v → redFn 1 PP x = 1 := by
    intro PP hn
    refine hout κ hU {s.v} (PP.under (𝓞 (maximalRealSubfield D.host.E))) PP htriv rfl ?_
    intro hv
    rw [Set.mem_singleton_iff] at hv
    exact hn (hv ▸ rfl)
  choose hint hredv using hred κ hU
  let ι := (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)).subtype
  let M' : Matrix (Fin D.R.nV) (Fin D.R.nV) (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)) :=
    fun a b => ⟨_, hint a b⟩

  let Sn : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) :=
    ∑ a : Fin D.R.nV, ∑ b : Fin D.R.nV, if a.val + 1 = b.val ∧ b.val < D.R.r then M' a b else 0
  have hSn : (Sn : s.v.adicCompletion (maximalRealSubfield D.host.E)) = NG.supDiag s D.R.r (s.loc D.R.nV κ) := by
    show ι Sn = _
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Sn, map_sum]
    unfold NG.supDiag
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs
    · rfl
    · exact map_zero ι
  have hφSn : φ Sn = edgeSum supEdge (upperLeftBlock hr (redFn 1 s.w x)) := by
    unfold edgeSum
    rw [upper_block_val_submatrix hr (blockTri_blkOf_le _ _ (hg s.w hsw))]
    simp only [Matrix.submatrix_apply]
    refine Eq.trans ?_ (GlobalTheory.MtChr.sum_supEdge_castLE hr (fun a b => (redFn (1 : GL (Fin D.R.nV) (EAf D)) s.w x).val a b)).symm
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Sn, map_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs
    · exact (hredv a b).symm
    · exact map_zero φ

  let Md : Matrix {y : Fin D.R.nV // D.R.r ≤ y.val} {y : Fin D.R.nV // D.R.r ≤ y.val}
      (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)) := fun a b => M' a.1 b.1
  have hdet : (Md.det : s.v.adicCompletion (maximalRealSubfield D.host.E)) = (u : s.v.adicCompletion (maximalRealSubfield D.host.E)) := by
    rw [hu]
    show ι Md.det = _
    rw [RingHom.map_det]
    unfold NG.detDD
    rfl
  have hφdet' : φ Md.det = (((redFn 1 s.w x).val).submatrix (Subtype.val : {a : Fin D.R.nV // blkOf D.R.r D.R.t a = 1} → Fin D.R.nV) Subtype.val).det :=
    GlobalTheory.MtChr.det_map_subtype φ M' _ hredv _ _ (fun a => GlobalTheory.MtChr.blkOf_eq_one_iff a (lt_of_lt_of_eq a.2 rfl))
  have hφdet : φ Md.det = ((dBlk (blkOf D.R.r D.R.t) 1 (redFn 1 s.w x) : (kP s.w)ˣ) : kP s.w) :=
    hφdet'.trans (diag_block_det_val 1 (hg s.w hsw)).symm
  have hξu := hξ u Md.det _ hdet hφdet

  have hA : ((ext1 (P0 Pg D.R.r ψ).conj.H (P0 Pg D.R.r ψ).conj.chi (rTup 1 Ld x) : ℂˣ) : ℂ) =
      (ψ s.w (edgeSum supEdge (upperLeftBlock hr (redFn 1 s.w x))))⁻¹ := by
    erw [extendOne_of_mem _ hP0]
    show (((P0 Pg D.R.r ψ).chi⁻¹ ⟨_, hP0⟩ : ℂˣ) : ℂ) = _
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
    congr 1
    show (((∏ PP : ↥Pg, (addCharHom (ψ PP.1) (supHom (kP PP.1) D.R.r)).comp (LevelP.prj _ PP)) ⟨_, hP0⟩ : ℂˣ) : ℂ) = _
    rw [MonoidHom.finsetProd_apply, Fintype.prod_eq_single ⟨s.w, hsw⟩]
    · rfl
    · intro PP hne
      apply Units.ext
      show ψ PP.1 (edgeSum supEdge (upperLeftBlock hr (redFn 1 PP.1 x))) = 1
      rw [triv PP.1 (hPg PP.1 PP.2 (fun e => hne (Subtype.ext e)))]
      unfold upperLeftBlock
      rw [blockDiagonalExtendByOnePrimeField_one, GlobalTheory.MtChr.edgeSum_supEdge_one, AddChar.map_zero_eq_one]
  have hB : (∏ PP ∈ Pg, ∏ c ∈ Finset.range 1, (chi PP)⁻¹ (dBlk (blkOf D.R.r D.R.t) (c + 1) (redFn 1 PP x))) =
      (chi s.w)⁻¹ (dBlk (blkOf D.R.r D.R.t) 1 (redFn 1 s.w x)) := by
    rw [Finset.prod_eq_single_of_mem s.w hsw]
    · rw [Finset.prod_range_one]
    · intro PP hP hne
      rw [Finset.prod_range_one, triv PP (hPg PP hP hne)]
      unfold dBlk
      rw [blockDiagonalExtendByOnePrimeField_one, map_one]
  have hC : (∏ PP ∈ Q, xi PP (dBlk (blk2 D.R.r) 1 (redFn 1 PP x))) = 1 := by
    refine Finset.prod_eq_one fun PP hP => ?_
    rw [triv PP (hQ PP hP)]
    unfold dBlk
    rw [blockDiagonalExtendByOnePrimeField_one, map_one]
  show ((ext1 (P0 Pg D.R.r ψ).conj.H (P0 Pg D.R.r ψ).conj.chi (rTup 1 Ld x) *
      (∏ PP ∈ Pg, ∏ c ∈ Finset.range 1, (chi PP)⁻¹ (dBlk (blkOf D.R.r D.R.t) (c + 1) (redFn 1 PP x))) *
      ∏ PP ∈ Q, xi PP (dBlk (blk2 D.R.r) 1 (redFn 1 PP x)) : ℂˣ) : ℂ) = _
  rw [hB, hC, mul_one, Units.val_mul, hA, hξu, ← hSn, hψ₀, AddChar.map_neg_eq_inv, hφSn]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymAllowed
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.GroupLoc

variable {D : D7}

def ModW (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (S : Set (VA X.B.I)) (y : VA X.B.I) : Prop :=
  y ∈ Submodule.span (Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) S ⊔ wLf X w

def CondAt (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (x : X.B.I.Gf) : Prop :=
  (∀ a : Fin D.R.rS, ModW X w (X.e0 '' {b | b.1 < a.1}) ((X.B.I.fmat x - 1) *ᵥ X.e0 a)) ∧
    ModW X w (Set.range X.e0) ((X.B.I.fmat x - 1) *ᵥ X.z0) ∧
    ∀ i : Fin D.R.k, ModW X w (Set.range X.e0 ∪ X.bw '' {j | j.1 < i.1}) ((X.B.I.fmat x - 1) *ᵥ X.bw i)

def symAllowed (ρ k : ℕ) {r : ℕ} (i j : Fin r) : Prop :=
  j.1 < i.1 ∧ ¬ (ρ ≤ j.1 ∧ j.1 < ρ + k ∧ i.1 = ρ + k)

def ColCond (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (x : X.B.I.Gf) : Prop :=
  ∀ i : Fin D.R.r, ModW X w (GlobalTheory.Mem.SymFrame.symVec X w '' {j | symAllowed D.R.rS D.R.k i j})
    ((X.B.I.fmat x - 1) *ᵥ GlobalTheory.Mem.SymFrame.symVec X w i)

end GlobalTheory.Mem.GroupLoc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupTiedOfMuIsW
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top.TupTieW

theorem tupTied_of_muIsW : ∀ (X : Stages) (f : Fr X.B.toPre) (T : TwDat X.B) (Wt : Set X.B.places.Pl) (xi : X.C.Tup → HChar X.B.host.E), V4.MuIsW X f T Wt xi → (∀ w, X.toD7.what₂.muAt w ≠ X.toD7.what₂.mu0 ↔ w ∈ Wt) ∧ Wt.Finite ∧ (∀ w ∈ Wt, X.B.places.conj w ∈ Wt) ∧ ∀ nch : NChoice X.toD7, (∀ w ∈ Wt, nch.Q w = T.Q w) → ∃ tp : TupTied X.toD7 (Fr.at X f) nch, tp.xi = xi ∧ tp.psi = T.psi := by
  intro X f T Wt xi h
  have key : ∀ w, X.toD7.what₂.muAt w ≠ X.toD7.what₂.mu0 ↔ w ∈ Wt := by
    intro w
    constructor
    · intro hw
      by_contra hn
      exact hw (h.off w hn)
    · intro hw he
      have he' : X.W.muAt w = X.C.mu0 := he
      rw [h.on w hw] at he'
      have h1 := h.tw w
      rw [he', h.mu0] at h1
      exact (TwFin.tw_fin X.B f T).2.1 w h1.symm
  have hfin : Wt.Finite :=
    Set.Finite.subset (TwFin.tw_fin X.B f T).2.2.2 fun w hw => h.sub w hw
  have hconj : ∀ w ∈ Wt, X.B.places.conj w ∈ Wt := by
    intro w hw
    refine (key _).1 ?_
    have hc : X.toD7.what₂.muAt (X.toD7.what₂.places.conj w) = X.toD7.what₂.muAt w :=
      X.toD7.what₂.muAt_conj w
    intro he
    exact (key w).2 hw (hc.symm.trans he)
  refine ⟨key, hfin, hconj, fun nch hQ => ?_⟩
  have hg : ∀ μ, TupTie.Good X.B.host.F (xi μ) :=
    fun μ => TupTie.good_set f T (h.range ▸ Set.mem_range_self μ)
  refine ⟨⟨xi, h.inj, fun μ => (hg μ).1, fun μ => (hg μ).2.1, fun μ => (hg μ).2.2, T.psi, h.mu0, h.star, h.star', h.tw,
    fun w hw => ?_, fun w hw => ?_⟩, rfl, rfl⟩
  · rw [hQ w ((key w).1 hw)]
    exact T.psi_is w
  · exact h.supp w fun hn => (key w).2 hn hw

end GlobalTheory.Mem.Top.TupTieW
end

