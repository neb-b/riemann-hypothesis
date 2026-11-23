module

public import Mathlib
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0069
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisIncl
public import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
public import Formalism.LocalToGlobal.Columns.GenericUnipotentCharacter
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousOfDense
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleCharacterSeries.FrobeniusSumFormula

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BcrisEqAcrisLocalizationPeriodT
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.BcrisT

variable {l : ℕ} [Fact l.Prime]

theorem mu_mem_kerP (e : Per.Fl l) (he : e.untilt = 1) :
    algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e - 1) ∈ Per.kerP l := by
  refine GlobalTheory.RingIface.alg_mem_kerP l ?_
  rw [map_sub, map_one, WittVector.fontaineTheta_teichmuller, he, sub_self]

theorem isLog_mem_fil (e : Per.Fl l) (he : e.untilt = 1) (y : Per.BdRp l) (hy : Per.IsLog l e y) :
    y ∈ Per.FilP l 1 := by
  have h := GlobalTheory.CrisIncl.factorial_mul_ev l e y he hy 1
  rw [Finset.sum_range_one] at h
  simp only [Nat.factorial_one, Nat.cast_one, one_mul, pow_zero, zero_add, Nat.div_one, pow_one] at h
  rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow, h, Ideal.Quotient.eq_zero_iff_mem, pow_one]
  exact mu_mem_kerP e he

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem isLog_pow (j : Per.Acris l →+* Per.BdRp l) (hj : IsCrisP j) (e : Per.Fl l) (he : e.untilt = 1)
    (x : Per.BdRp l) (hx : Per.IsLog l e x) (n : ℕ) :
    ∀ y : Per.BdRp l, Per.IsLog l (e ^ n) y → y = (n : Per.BdRp l) * x := by
  induction n with
  | zero =>
    intro y hy
    rw [pow_zero] at hy
    have h1 : (1 : Per.Fl l).untilt = 1 := map_one _
    have h := LogAdd.log_add l 1 1 y y y h1 h1 hy hy (by rwa [mul_one])
    rw [Nat.cast_zero, zero_mul]
    exact left_eq_add.1 h
  | succ n ih =>
    intro y hy
    have hn : (e ^ n).untilt = 1 := by rw [map_pow, he, one_pow]
    obtain ⟨t, u, ht, -, -⟩ := _root_.GlobalTheory.MemLoc.exists_isLogA l (e ^ n) hn
    have h1 := (_root_.GlobalTheory.MemLoc.LogFun.log_fun l (e ^ n) t hn ht).2.2.2 j hj
    have h := LogAdd.log_add l (e ^ n) e (j t) x y hn he h1 hx (by rwa [← pow_succ])
    rw [h, ih _ h1, Nat.cast_succ, add_mul, one_mul]

theorem phi_log (j : Per.Acris l →+* Per.BdRp l) (hj : IsCrisP j) (e : Per.Fl l) (he : e.untilt = 1)
    (t : Per.Acris l) (ht : IsLogA e t) : phiA l t = (l : Per.Acris l) ^ 1 * t := by
  have hl : (e ^ l).untilt = 1 := by rw [map_pow, he, one_pow]
  obtain ⟨-, -, h2, h3⟩ := _root_.GlobalTheory.MemLoc.LogFun.log_fun l e t he ht
  have h4 := (_root_.GlobalTheory.MemLoc.LogFun.log_fun l (e ^ l) _ hl h2).2.2.2 j hj
  apply _root_.GlobalTheory.MemLoc.crisP_injective l j hj
  rw [isLog_pow j hj e he _ (h3 j hj) l _ h4, pow_one, map_mul, map_natCast]

theorem l_dvd (C : Core l) : (l : Per.Acris l) ∣ C.t ^ (l - 1) := by
  have he : C.ε.untilt = 1 := (core_isEps l C).1
  obtain ⟨t, u, ht, -, htu⟩ := _root_.GlobalTheory.MemLoc.exists_isLogA l C.ε he
  have e1 : t = C.t := (_root_.GlobalTheory.MemLoc.LogFun.log_fun l C.ε C.t he C.t_log).1 t ht
  obtain ⟨w, hw, -⟩ := _root_.GlobalTheory.MemLoc.exists_mu_pow_div l C.ε he
  have hw0 : (l : Per.Acris0 l) * w = algebraMap (Per.Ainf l) (Per.Acris0 l) (mu C.ε) ^ (l - 1) := by
    apply Subtype.ext
    simpa using hw
  have hw1 := congrArg (algebraMap (Per.Acris0 l) (Per.Acris l)) hw0
  rw [map_mul, map_natCast, map_pow] at hw1
  have e2 : algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) (mu C.ε)) =
      algebraMap (Per.Ainf l) (Per.Acris l) (mu C.ε) := (GlobalTheory.RingIface.tower l _).symm
  rw [e2] at hw1
  rw [← e1, htu, mul_pow, ← hw1]
  exact (dvd_mul_right _ _).mul_right _

theorem mu_dvd_pt (C : Core l) [Nontrivial (Per.Bcris l)] (e : Per.Fl l) (he : e.untilt = 1) (hne : e ≠ 1) :
    ∃ r : ℕ, algebraMap (Per.Ainf l) (Per.Acris l) (Per.tm e - 1) ∣ C.t ^ r := by
  have hyu := GlobalTheory.CrisLoc.unit_of_root l e he hne
  obtain ⟨t, u, ht, hu, htu⟩ := _root_.GlobalTheory.MemLoc.exists_isLogA l e he
  have hlog := (_root_.GlobalTheory.MemLoc.LogFun.log_fun l e t he ht).2.2.2 C.j C.j_cris
  obtain ⟨z, k, hz⟩ := GlobalTheory.T.acris_frobenius_eigen_fil_eq_qlMul_tPow l C 1 t (phi_log C.j C.j_cris e he t ht) (isLog_mem_fil e he _ hlog)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [map_zero, map_zero, zero_mul, htu] at hz
    have h := congrArg (algebraMap (Per.Acris l) (Per.Bcris l)) hz
    rw [map_zero, map_mul, map_mul, map_pow, map_natCast] at h
    have hU : IsUnit (0 : Per.Bcris l) := by
      rw [← h]
      exact ((_root_.GlobalTheory.MemLoc.core_t_unit_fil l C).2.2.2.pow k).mul (hyu.mul (hu.map _))
    exact not_isUnit_zero hU
  have hs := congrArg ((algebraMap (Per.Ainf l) (Per.Acris l)).comp (Per.zA l)) (PadicInt.unitCoeff_spec hz0)
  rw [map_mul, map_pow, map_natCast] at hs
  have hU := (PadicInt.unitCoeff hz0).isUnit.map ((algebraMap (Per.Ainf l) (Per.Acris l)).comp (Per.zA l))
  have h1 : algebraMap (Per.Ainf l) (Per.Acris l) (mu e) ∣
      ((algebraMap (Per.Ainf l) (Per.Acris l)).comp (Per.zA l)) z * C.t ^ 1 := by
    rw [RingHom.comp_apply, ← hz, htu]
    exact (dvd_mul_right _ _).mul_left _
  rw [hs, mul_assoc, hU.dvd_mul_left] at h1
  refine ⟨(l - 1) * z.valuation + 1, h1.trans ?_⟩
  rw [pow_add, pow_mul]
  exact mul_dvd_mul_right (pow_dvd_pow_of_dvd (l_dvd C) _) _

theorem away_pt (C : Core l) [Nontrivial (Per.Bcris l)] (b : Per.Bcris l) :
    ∃ (r : ℕ) (x : Per.Acris l),
      b * algebraMap (Per.Acris l) (Per.Bcris l) C.t ^ r = algebraMap (Per.Acris l) (Per.Bcris l) x := by
  obtain ⟨e, he, hne⟩ := GlobalTheory.CrisLoc.exists_root_ne_one l
  obtain ⟨n, x, hx⟩ := GlobalTheory.CrisLoc.exists_mul_pow_eq l e he hne b
  obtain ⟨r, c, hc⟩ := mu_dvd_pt C e he hne
  refine ⟨r * n, x * c ^ n, ?_⟩
  rw [← map_pow, pow_mul, hc, mul_pow, map_mul, map_mul, map_pow, ← mul_assoc, hx]

end GlobalTheory.MemLoc.BcrisT

namespace GlobalTheory.MemLoc

theorem bcris_eq_acris_localization_periodT_alt (l : ℕ) [Fact l.Prime] (C : Core l) (b : Per.Bcris l) :
    ∃ (r : ℕ) (x : Per.Acris l),
      b * algebraMap (Per.Acris l) (Per.Bcris l) C.t ^ r = algebraMap (Per.Acris l) (Per.Bcris l) x := by
  rcases subsingleton_or_nontrivial (Per.Bcris l) with h | h
  · exact ⟨0, 0, Subsingleton.elim _ _⟩
  exact BcrisT.away_pt C b

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockBaseChangeAt
section
noncomputable section

namespace GlobalTheory.Mem.R3.LiftLatBC

open Module NumberField Formalism.L2.DIV Formalism.DivisionValues
open scoped Matrix

variable {K K' : Type} [Field K] [NumberField K] [StarRing K] [Field K'] [NumberField K'] [StarRing K']
  {G G' : Type} [Group G] [Fintype G] [Group G'] [Fintype G'] {Pl0 Pl0' : Type}

def bcF (φ : K →+* K') (B : BlockDat K G Pl0) (B' : BlockDat K' G' Pl0') (C : Matrix (Fin B'.S.dim) (Fin B.S.dim) K')
    (f : B.S.Forms) : B'.S.Forms :=
  B'.S.basis.equivFun.symm (C *ᵥ fun k => φ (B.S.basis.equivFun f k))

structure BlockBaseChangeAt (φ : K →+* K') (e : G ≃* G') (B : BlockDat K G Pl0) (B' : BlockDat K' G' Pl0')
    (ℓ : Lvl K G) (ℓ' : Lvl K' G') (Z : Submodule K B.S.Forms) (Z' : Submodule K' B'.S.Forms)
    (C : Matrix (Fin B'.S.dim) (Fin B.S.dim) K') : Prop where

  bij : Function.Bijective C.mulVec

  H : Cᴴ * B'.S.H * C = B.S.H.map φ

  act : ∀ g : G, B'.S.actMat B'.r (e g) * C = C * (B.S.actMat B.r g).map φ

  nab : B'.S.nabLat = Submodule.span (𝓞 K') ((fun x : Fin B.S.dim → K => C *ᵥ (fun k => φ (x k))) '' (B.S.nabLat : Set (Fin B.S.dim → K)))

  sub : B'.coord Z' = Submodule.span K' ((fun x : Fin B.S.dim → K => C *ᵥ (fun k => φ (x k))) '' (B.coord Z : Set (Fin B.S.dim → K)))

  X : ∀ χ' : G' → K', χ' ∈ ℓ'.X ↔ ∃ χ ∈ ℓ.X, χ' = fun g => φ (χ (e.symm g))

  P : ℓ'.P = ℓ.P.map e.toMonoidHom

  ψ : ∀ h : ℓ.P, ((ℓ'.ψ ⟨e h, P ▸ Subgroup.mem_map_of_mem e.toMonoidHom h.2⟩ : K'ˣ) : K') = φ (ℓ.ψ h : K)

section Cx

open Formalism.IndefR.Cx Formalism.L2.Indef

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
  {fc : DefSub A → DefFace Bs}

theorem tC_cpt (cr : Crd A fc) (b : Bool) (j : Bs.J) (t : Bs.Tup) (x : Fin ((lv (fc X.zs) b).dZ j t) → K) :
    X.tC cr b j t (cpt Bs.v0.embedding x) = X.θ' j t (X.jL j t (cr.toL X.zs b j t x)) := by
  have hx : x = ∑ k, x k • Pi.single k 1 := by
    funext i; simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hx]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, map_smulₛₗ, CxData.tC, lin, Fintype.linearCombination_apply, cpt]

end Cx

end GlobalTheory.Mem.R3.LiftLatBC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockTriangularBlockIndexOfIffColBlockUTTwoBlock
section
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem blockIndexOf_blockIndexTwo_eq_coarseBlocks_pointwise {n r t : ℕ} (hn : n = r + t) (a : Fin n) :
    Formalism.L2.DIV.blkOf r t a = Formalism.L2.Col.coarse r [t] a.val ∧
      Formalism.L2.DIV.blk2 r a = Formalism.L2.Col.coarse r [t] a.val := by
  have ha := a.isLt
  by_cases h : a.val < r
  · rw [Formalism.L2.Col.coarse_of_lt h]
    simp [Formalism.L2.DIV.blkOf, Formalism.L2.DIV.blk2, h]
  · have h' : r ≤ a.val := Nat.not_lt.mp h
    rw [Formalism.L2.Col.coarse_of_le h']
    have hlt : a.val - r < t := by omega
    have hd : (a.val - r) / t = 0 := Nat.div_eq_of_lt hlt
    simp [Formalism.L2.DIV.blkOf, Formalism.L2.DIV.blk2, h, hd, Formalism.L2.Col.blkIdx, hlt]

theorem blockTriangular_blockIndexOf_iff_colBlockUT_twoBlocks :
    ∀ {κ : Type} [CommRing κ] {n r t : ℕ}, n = r + t → ∀ g : GL (Fin n) κ,
      (g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) ↔ g ∈ Formalism.L2.Col.blockUT n κ r [t]) ∧
        (g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) ↔ g ∈ Formalism.L2.Col.blockUT n κ r [t]) := by
  intro κ _ n r t hn g
  rw [Formalism.L2.DIV.mem_blockTri, Formalism.L2.DIV.mem_blockTri, Formalism.L2.Col.mem_btG]
  refine ⟨?_, ?_⟩
  · simp only [(blockIndexOf_blockIndexTwo_eq_coarseBlocks_pointwise hn _).1]
  · simp only [(blockIndexOf_blockIndexTwo_eq_coarseBlocks_pointwise hn _).2]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassFunctionLabelOfLabelMapLabel
section
open CategoryTheory Polynomial

namespace GlobalTheory.SerCmp

open Formalism.IrreducibleCountingLemmas.TYPES

theorem hasLabel_of_hasLabelO : ∀ (g : ℕ) [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) {C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod g)} (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod g) C), (∀ (d : ℕ) (V : FDRep ℂ (GL (Fin d) (ZMod g))), 1 ≤ d → CategoryTheory.Simple V → Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) V → GlobalTheory.GLq.IsCuspOf L (O.lab d V) (fun x => V.character x)) → (∀ (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} (ZMod g))), Function.Surjective b → ∀ x : GL (Fin r) (ZMod g), LinearMap.trace ℂ (Formalism.IrreducibleCountingLemmas.TYPES.hcSpace (ZMod g) b lam) (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam x) = GlobalTheory.GLq.hcL (GlobalTheory.SerCmp.canonList b lam) r x) → (∀ (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} (ZMod g))) (τ : FDRep ℂ (GL (Fin r) (ZMod g))), CategoryTheory.Simple τ → (Formalism.IrreducibleCountingLemmas.TYPES.IsConstituent τ (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam) ↔ GlobalTheory.GLq.ip (fun x => τ.character x) (fun x => LinearMap.trace ℂ (Formalism.IrreducibleCountingLemmas.TYPES.hcSpace (ZMod g) b lam) (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam x)) ≠ 0)) → ∀ (r : ℕ) (τ : FDRep ℂ (GL (Fin r) (ZMod g))) (f : (ZMod g)[X]), CategoryTheory.Simple τ → Formalism.IrreducibleCountingLemmas.TYPES.HasLabelO O τ f → GlobalTheory.GLq.HasLabel L (fun x => τ.character x) f := by
  intro g _ L C O h1 h2 h3 r τ f hτ hL
  obtain ⟨s, b, lam, hb, hl, hcon, rfl⟩ := hL
  have hc : ∀ c, 1 ≤ Fintype.card {i // b i = c} := fun c => by
    obtain ⟨i, hi⟩ := hb c
    exact Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩
  let Q : List ((ZMod g)[X] × GlobalTheory.GLq.Pc g) := (List.finRange s).map fun c =>
    (labO O (lam c), ⟨Fintype.card {i // b i = c},
      fun x => (transp (Fintype.equivFin {i // b i = c}) (lam c)).character x⟩)
  have hQ : Q.map Prod.snd = canonList b lam := by
    simp only [Q, canonList, List.map_map]
    rfl
  refine ⟨Q, ?_, ?_, ?_, ?_⟩
  · intro p hp
    simp only [Q, List.mem_map] at hp
    obtain ⟨c, -, rfl⟩ := hp
    exact h1 _ _ (hc c) (Formalism.L2.PT.simple_transp _ (hl c).1) (Formalism.L2.PT.isCuspidal_transp _ (hl c).2)
  · rw [hQ]
    unfold GlobalTheory.GLq.degL canonList
    rw [List.map_map]
    have e : ((List.finRange s).map ((fun p : GlobalTheory.GLq.Pc g => p.1) ∘ fun c : Fin s =>
        (⟨Fintype.card {i // b i = c},
          fun x => (transp (Fintype.equivFin {i // b i = c}) (lam c)).character x⟩ : GlobalTheory.GLq.Pc g))).sum =
        ∑ c : Fin s, Fintype.card {i // b i = c} := by
      rw [Fin.sum_univ_def]
      rfl
    rw [e, ← Fintype.card_sigma, Fintype.card_congr (Equiv.sigmaFiberEquiv b), Fintype.card_fin]
  · simp only [Q, List.map_map]
    rw [Fin.prod_univ_def]
    rfl
  · rw [hQ]
    have ht : (fun x => LinearMap.trace ℂ (hcSpace (ZMod g) b lam) (hcRep (ZMod g) b lam x)) =
        GlobalTheory.GLq.hcL (canonList b lam) r := funext (h2 r s b lam hb)
    have := (h3 r s b lam τ hτ).1 hcon
    rw [ht] at this
    exact this

end GlobalTheory.SerCmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBlocksOfCuspidalCharacterList
section
open CategoryTheory Polynomial

noncomputable section

namespace GlobalTheory.SerCmp.ListBlocks

open Formalism.IrreducibleCountingLemmas.TYPES

theorem glEquiv_transp_cancel {g : ℕ} [Fact g.Prime] {F : Type} [Fintype F] [DecidableEq F] {n : ℕ}
    (E : F ≃ Fin n) (x : GL (Fin n) (ZMod g)) :
    (glEquiv (ZMod g) E.symm).symm ((glEquiv (ZMod g) E).symm x) = x := by
  ext i j
  rw [Formalism.L2.PT.coe_glEquiv_symm, Formalism.L2.PT.coe_glEquiv_symm]
  simp

theorem entry_eq {g : ℕ} [Fact g.Prime] {F : Type} [Fintype F] [DecidableEq F] {d : ℕ}
    (h : Fintype.card F = d) (V : FDRep ℂ (GL (Fin d) (ZMod g))) :
    (⟨Fintype.card F, fun x => (transp (Fintype.equivFin F)
      (transp ((finCongr h.symm).trans (Fintype.equivFin F).symm) V)).character x⟩ : GlobalTheory.GLq.Pc g) =
      ⟨d, fun x => V.character x⟩ := by
  generalize Fintype.equivFin F = E
  subst h
  refine Sigma.ext rfl (heq_of_eq (funext fun x => ?_))
  dsimp only
  rw [Formalism.L2.PT.character_transp, Formalism.L2.PT.character_transp]
  congr 1
  have : (finCongr (rfl : Fintype.card F = Fintype.card F)).trans E.symm = E.symm := by ext; simp
  rw [this, glEquiv_transp_cancel]

theorem exists_blocks (s : ℕ) (d : Fin s → ℕ) (r : ℕ) (hr : ∑ c, d c = r) :
    ∃ b : Fin r → Fin s, ∀ c, Fintype.card {i // b i = c} = d c := by
  subst hr
  refine ⟨fun i => (finSigmaFinEquiv.symm i).1, fun c => ?_⟩
  rw [Fintype.card_congr ((finSigmaFinEquiv.symm.subtypeEquiv (fun _ => Iff.rfl)).trans (Equiv.sigmaSubtype c))]
  simp

end GlobalTheory.SerCmp.ListBlocks

open Formalism.IrreducibleCountingLemmas.TYPES in
theorem GlobalTheory.SerCmp.canonList_of_cuspidal_list : ∀ (g : ℕ) [Fact g.Prime] (Q : List (GlobalTheory.GLq.Pc g)), (∀ p ∈ Q, 1 ≤ p.1 ∧ ∃ V : FDRep ℂ (GL (Fin p.1) (ZMod g)), CategoryTheory.Simple V ∧ Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) V ∧ ∀ x, V.character x = p.2 x) → ∃ (b : Fin (GlobalTheory.GLq.degL Q) → Fin Q.length) (lam : ∀ c : Fin Q.length, FDRep ℂ (GL {i // b i = c} (ZMod g))), Function.Surjective b ∧ (∀ c, CategoryTheory.Simple (lam c) ∧ Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) (lam c)) ∧ GlobalTheory.SerCmp.canonList b lam = Q := by
  intro g _ Q hQ
  have H : ∀ c : Fin Q.length, ∃ V : FDRep ℂ (GL (Fin (Q.get c).1) (ZMod g)), 1 ≤ (Q.get c).1 ∧
      CategoryTheory.Simple V ∧ IsCuspidal (ZMod g) V ∧ ∀ x, V.character x = (Q.get c).2 x := by
    intro c
    obtain ⟨h1, V, h2⟩ := hQ _ (List.get_mem Q c)
    exact ⟨V, h1, h2⟩
  choose V hd hVs hVc hVch using H
  have hsum : ∑ c : Fin Q.length, (Q.get c).1 = GlobalTheory.GLq.degL Q := by
    rw [GlobalTheory.GLq.degL]
    rw [← Fin.sum_univ_getElem]
    exact Fintype.sum_equiv (finCongr (List.length_map _).symm) _ _ (fun c => by simp)
  obtain ⟨b, hcard⟩ := GlobalTheory.SerCmp.ListBlocks.exists_blocks Q.length (fun c => (Q.get c).1) _ hsum
  refine ⟨b, fun c => transp ((finCongr (hcard c).symm).trans (Fintype.equivFin _).symm) (V c), ?_, ?_, ?_⟩
  · intro c
    have : 0 < Fintype.card {i // b i = c} := by rw [hcard c]; exact hd c
    obtain ⟨⟨i, hi⟩⟩ := Fintype.card_pos_iff.1 this
    exact ⟨i, hi⟩
  · intro c
    exact ⟨Formalism.L2.PT.simple_transp _ (hVs c), Formalism.L2.PT.isCuspidal_transp _ (hVc c)⟩
  · apply List.ext_get (GlobalTheory.SerCmp.canonList_length _ _)
    intro n h1 h2
    simp only [GlobalTheory.SerCmp.canonList, List.get_eq_getElem, List.getElem_map, List.getElem_finRange]
    rw [GlobalTheory.SerCmp.ListBlocks.entry_eq (hcard _) (V _)]
    have key : ∀ c, (⟨(Q.get c).1, fun x => (V c).character x⟩ : GlobalTheory.GLq.Pc g) = Q.get c := fun c =>
      Sigma.ext rfl (heq_of_eq (_root_.funext fun x => hVch c x))
    rw [key]
    simp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryRepOfActionOnTotalFamily
section
noncomputable section

namespace GlobalTheory.TotalFamilyRep

variable {S H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem norm_linearCombination_eq (E F : S → H) (h : ∀ p q, inner ℂ (F p) (F q) = inner ℂ (E p) (E q))
    (x : S →₀ ℂ) : ‖Finsupp.linearCombination ℂ F x‖ = ‖Finsupp.linearCombination ℂ E x‖ := by
  have : inner ℂ (Finsupp.linearCombination ℂ F x) (Finsupp.linearCombination ℂ F x) =
      inner ℂ (Finsupp.linearCombination ℂ E x) (Finsupp.linearCombination ℂ E x) := by
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum, inner_smul_left,
      inner_smul_right, h]
  rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ _ _ _ _ (Finsupp.linearCombination ℂ E x), this]

theorem exists_isometry [CompleteSpace H] (E F : S → H) (hE : Dense (Submodule.span ℂ (Set.range E) : Set H))
    (h : ∀ p q, inner ℂ (F p) (F q) = inner ℂ (E p) (E q)) :
    ∃ T : H →L[ℂ] H, (∀ x, ‖T x‖ = ‖x‖) ∧ ∀ p, T (E p) = F p := by
  have hd : DenseRange (Finsupp.linearCombination ℂ E) := by
    rw [← Finsupp.range_linearCombination] at hE
    exact hE
  have hT : ∀ x, (Finsupp.linearCombination ℂ F).extendOfNorm (Finsupp.linearCombination ℂ E)
      (Finsupp.linearCombination ℂ E x) = Finsupp.linearCombination ℂ F x :=
    LinearMap.extendOfNorm_eq hd ⟨1, fun x => by rw [one_mul, norm_linearCombination_eq E F h]⟩
  refine ⟨(Finsupp.linearCombination ℂ F).extendOfNorm (Finsupp.linearCombination ℂ E), fun x => ?_,
    fun p => ?_⟩
  · refine hd.induction_on (p := fun x => ‖(Finsupp.linearCombination ℂ F).extendOfNorm
      (Finsupp.linearCombination ℂ E) x‖ = ‖x‖) x (isClosed_eq (by fun_prop) (by fun_prop)) fun y => ?_
    rw [hT, norm_linearCombination_eq E F h]
  · simpa using hT (Finsupp.single p 1)

theorem exists_rep : ∀ (G S H : Type) [Group G] [TopologicalSpace G] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (act : G → S → S) (E : S → H), (∀ p, act 1 p = p) →
    (∀ g h p, act (g * h) p = act g (act h p)) → Dense (Submodule.span ℂ (Set.range E) : Set H) →
    (∀ g p q, inner ℂ (E (act g p)) (E (act g q)) = inner ℂ (E p) (E q)) →
    (∀ p q, Continuous fun g => inner ℂ (E q) (E (act g p))) →
    ∃ π : G →* (H →L[ℂ] H), (∀ g x, ‖π g x‖ = ‖x‖) ∧ (∀ x, Continuous fun g => π g x) ∧
      ∀ g p, π g (E p) = E (act g p) := by
  intro G S H _ _ _ _ _ act E h1 hmul hE hinv hcont
  choose T hT hTE using fun g => exists_isometry E (fun p => E (act g p)) hE (hinv g)
  have hp : ∀ p, Continuous fun g => T g (E p) := by
    intro p
    refine continuous_iff_continuousAt.2 fun g₀ => ?_
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    have key : ∀ g, ‖T g (E p) - T g₀ (E p)‖ =
        √(‖E p‖ ^ 2 - 2 * RCLike.re (inner ℂ (E (act g₀ p)) (E (act g p))) + ‖E p‖ ^ 2) := by
      intro g
      rw [norm_sub_rev, ← hTE, ← hTE, ← Real.sqrt_sq (norm_nonneg (T g₀ (E p) - T g (E p))),
        @norm_sub_sq ℂ, hT, hT]
    have hc : Continuous fun g => ‖T g (E p) - T g₀ (E p)‖ := by
      simp only [key]
      have := hcont p (act g₀ p)
      fun_prop
    simpa using hc.tendsto g₀
  refine ⟨{ toFun := T, map_one' := ?_, map_mul' := fun g h => ?_ }, hT, ?_, hTE⟩
  · refine ContinuousLinearMap.ext_on hE ?_
    rintro _ ⟨p, rfl⟩
    simp [hTE, h1]
  · refine ContinuousLinearMap.ext_on hE ?_
    rintro _ ⟨p, rfl⟩
    simp [hTE, hmul]
  · refine GlobalTheory.FockSeq.continuous_of_dense T hT hE fun x hx => ?_
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨p, rfl⟩ := hx; exact hp p
    | zero => simpa using continuous_const
    | add x y _ _ hx hy => simp only [map_add (f := _)]; exact hx.add hy
    | smul a x _ hx => simp only [map_smul]; exact hx.const_smul a

end GlobalTheory.TotalFamilyRep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsConstituentHarishChandraRepIffPairingNeZero
section
open CategoryTheory Polynomial

noncomputable section
namespace GlobalTheory.GLq.ConstIff

open Formalism.IrreducibleCountingLemmas.TYPES

theorem isConstituent_iff_ip_ne_zero {G : Type} [Group G] [Fintype G] (τ : FDRep ℂ G)
    {V : Type} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] (ρ : Representation ℂ G V) :
    IsConstituent τ ρ ↔ GlobalTheory.GLq.ip (fun x => τ.character x) (fun x => LinearMap.trace ℂ V (ρ x)) ≠ 0 := by
  classical
  let W := FDRep.of ρ
  let H := FDRep.of (Representation.linHom τ.ρ W.ρ)
  let _ : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have havg := FDRep.average_char_eq_finrank_invariants H
  have hH : ∀ g, H.character g = τ.character g⁻¹ * LinearMap.trace ℂ V (ρ g) := fun g =>
    FDRep.char_linHom τ W g
  have hsum : ∑ x, τ.character x * LinearMap.trace ℂ V (ρ x⁻¹) = ∑ g, H.character g := by
    refine Fintype.sum_equiv (Equiv.inv G) _ _ fun x => ?_
    rw [Equiv.inv_apply, hH, inv_inv]
  have hcard : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have key : GlobalTheory.GLq.ip (fun x => τ.character x) (fun x => LinearMap.trace ℂ V (ρ x)) =
      (Module.finrank ℂ (Representation.invariants H.ρ) : ℂ) := by
    rw [← havg, ← hsum, GlobalTheory.GLq.ip, Nat.card_eq_fintype_card]
  rw [key, Ne, Nat.cast_eq_zero, Submodule.finrank_eq_zero, ← Ne, Submodule.ne_bot_iff]
  constructor
  · rintro ⟨φ, hφ, hne⟩
    exact ⟨φ, (PI.SerBridgeGLW.mem_inv_linHom_iff τ.ρ W.ρ φ).mpr hφ, hne⟩
  · rintro ⟨φ, hφ, hne⟩
    exact ⟨φ, (PI.SerBridgeGLW.mem_inv_linHom_iff τ.ρ W.ρ φ).mp hφ, hne⟩

theorem constituent_hcRep_iff : ∀ (g : ℕ) [Fact g.Prime] (r s : ℕ) (b : Fin r → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} (ZMod g))) (τ : FDRep ℂ (GL (Fin r) (ZMod g))),
    CategoryTheory.Simple τ →
      (Formalism.IrreducibleCountingLemmas.TYPES.IsConstituent τ (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam) ↔
        GlobalTheory.GLq.ip (fun x => τ.character x)
          (fun x => LinearMap.trace ℂ (Formalism.IrreducibleCountingLemmas.TYPES.hcSpace (ZMod g) b lam)
            (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam x)) ≠ 0) := by
  intro g _ r s b lam τ _
  have : Module.Finite ℂ (PiTensorProduct ℂ (fun c => (lam c : Type))) :=
    Module.Finite.of_basis (Basis.piTensorProduct fun c => Module.Free.chooseBasis ℂ (lam c))
  exact isConstituent_iff_ip_ne_zero τ (Formalism.IrreducibleCountingLemmas.TYPES.hcRep (ZMod g) b lam)

end GlobalTheory.GLq.ConstIff
end
end

