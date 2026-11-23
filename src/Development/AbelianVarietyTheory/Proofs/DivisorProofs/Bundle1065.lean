module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0932
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0982
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalLowestKtypeKilledByCompactRoots
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0218
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0976
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0259
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0381
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0341
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0985
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1037
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalLowestKTypeKilledCompactRoots
section
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HolRead.KCpt

open GlobalTheory.HolDict GlobalTheory.HolDict.BorelK

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Mt n → (H →L[ℂ] H)}

theorem revNeg_lt {a b : Fin n} (ha : ε a = false) (hb : ε b = false) (h : b < a) : revNeg ε a < revNeg ε b := by
  have ma : a ∈ negS ε := by simp [negS, ha]
  have mb : b ∈ negS ε := by simp [negS, hb]
  have h1 : revNeg ε a = (revOn ε ⟨a, ma⟩ : Fin n) := Equiv.Perm.ofSubtype_apply_of_mem _ ma
  have h2 : revNeg ε b = (revOn ε ⟨b, mb⟩ : Fin n) := Equiv.Perm.ofSubtype_apply_of_mem _ mb
  rw [h1, h2]
  have h3 : (⟨b, mb⟩ : {x // x ∈ negS ε}) < ⟨a, ma⟩ := h
  have h4 := ((negS ε).orderIsoOfFin rfl).symm.strictMono h3
  exact ((negS ε).orderIsoOfFin rfl).strictMono (Fin.rev_lt_rev.2 h4)

theorem isWtOn_root (hσ : IsURepOn (UJset ε) σ) {μ : Fin n → ℝ} {v : H}
    (hs : SmoothVec (lieH (Formalism.REAL.Jm ε)) σ v) (hv : IsWtOn (Formalism.REAL.Kset ε) σ μ v) (a c : Fin n) :
    IsWtOn (Formalism.REAL.Kset ε) σ (μ + Formalism.REAL.root a c) (dRepC (Formalism.REAL.Jm ε) σ (Matrix.single a c 1) v) := by
  have hh : (Formalism.REAL.Jm ε).IsHermitian := Formalism.REAL.Jm_conjTranspose ε
  have z0 : ∀ x : H, dRepC (Formalism.REAL.Jm ε) σ 0 x = 0 := by
    intro x
    simp [dRepC, conjH, dRep]
  have l1 : ∀ (s : ℂ) Z, dRepC (Formalism.REAL.Jm ε) σ (s • Z) v = s • dRepC (Formalism.REAL.Jm ε) σ Z v := by
    intro s Z
    have := LieAct.dRepC_lin hh det_Jm hσ hs s Z 0
    rwa [add_zero, z0, add_zero] at this
  have l2 : ∀ (s : ℂ) Z, dRepC (Formalism.REAL.Jm ε) σ Z (s • v) = s • dRepC (Formalism.REAL.Jm ε) σ Z v := by
    intro s Z
    have := LieAct.dRepC_vec (π := σ) hh det_Jm hs hs (s - 1) Z
    rw [sub_smul, one_smul, sub_add_cancel, sub_smul, one_smul, sub_add_cancel] at this
    exact this
  intro θ hθ
  have hinv : (diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I))⁻¹ =
      diagonal fun a => Complex.exp (-((θ a : ℂ) * Complex.I)) := by
    apply Matrix.inv_eq_left_inv
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext b
    rw [← Complex.exp_add]; simp
  have e : (diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)) * Matrix.single a c (1 : ℂ) *
      (diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I))⁻¹ =
      Complex.exp ((θ a : ℂ) * Complex.I + -((θ c : ℂ) * Complex.I)) • Matrix.single a c (1 : ℂ) := by
    rw [hinv]
    ext i j
    simp only [mul_diagonal, diagonal_mul, Matrix.smul_apply, Matrix.single_apply]
    by_cases h' : a = i ∧ c = j
    · obtain ⟨rfl, rfl⟩ := h'
      simp [Complex.exp_add]
    · simp [h']
  rw [LieAct.rep_dRepC hh det_Jm hσ hs (kset_uj hθ), e, hv θ hθ, l2, l1, smul_smul, ← Complex.exp_add]
  congr 2
  simp [Formalism.REAL.root, Pi.single_apply, add_mul, Finset.sum_add_distrib, sub_eq_add_neg]

theorem killed {lam : Fin n → ℝ} (hσ : IsURepOn (UJset ε) σ) {v : H} (hv : v ∈ lowKSub ε lam σ)
    (hs : SmoothVec (lieH (Formalism.REAL.Jm ε)) σ v)
    (hw : IsWtOn (Formalism.REAL.Kset ε) σ (fun a => Formalism.QuantumDeterminants.lowK ε lam (revNeg ε a)) v) {a c : Fin n} (hac : ε a = ε c)
    (hlt : revNeg ε a < revNeg ε c) : dRepC (Formalism.REAL.Jm ε) σ (Matrix.single a c 1) v = 0 := by
  have hε : ∀ b, ε ((revNeg ε).symm b) = ε b := fun b => by
    rw [← eps_revNeg ε ((revNeg ε).symm b), Equiv.apply_symm_apply]
  have h1 := isWtOn_perm hσ (revNeg ε).symm hε (isWtOn_root hσ hs hw a c)
  have e : (fun b => ((fun a => Formalism.QuantumDeterminants.lowK ε lam (revNeg ε a)) + Formalism.REAL.root a c) ((revNeg ε).symm b)) =
      Formalism.QuantumDeterminants.lowK ε lam + Formalism.REAL.root (revNeg ε a) (revNeg ε c) := by
    funext b
    simp [Formalism.REAL.root, Pi.single_apply, Equiv.symm_apply_eq]
  rw [e] at h1
  have h2 := orth_of_not_cdom hσ h1 (not_cdom _ hlt)
  have hK := pM_mem (revNeg ε).symm hε
  have h3 : ∀ x ∈ lowKSub ε lam σ, ⟪dRepC (Formalism.REAL.Jm ε) σ (Matrix.single a c 1) v, x⟫_ℂ = 0 := by
    intro x hx
    rw [← inner_rep hσ hK]
    exact h2 _ (stable_sSup _ hK x hx)
  exact inner_self_eq_zero.1 (inner_dRepC stable_sSup h3 hv hac)

theorem extremal_killed_compact : ∀ (n : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool) (lam : Fin n → ℝ) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) π → ∀ v ∈ lowKSub ε lam π, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0} π v → IsWtOn (Formalism.REAL.Kset ε) π (fun a => Formalism.QuantumDeterminants.lowK ε lam (revNeg ε a)) v → ∀ a b : Fin n, ((ε a = true ∧ ε b = true ∧ a < b) ∨ (ε a = false ∧ ε b = false ∧ b < a)) → ∀ X ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0}, ∀ Y ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0}, X + Complex.I • Y = Matrix.single a b 1 → dRep π X v + Complex.I • dRep π Y v = 0 := by
  intro n H _ _ ε lam π hπ v hv hs hw a b hab X hX Y hY hE
  rw [← LieAct.dRepC_parts (G := Formalism.REAL.Jm ε) det_Jm hX hY, hE]
  rcases hab with ⟨ha, hb, h⟩ | ⟨ha, hb, h⟩
  · exact killed hπ hv hs hw (ha.trans hb.symm) (by rwa [revNeg_of_pos ε ha, revNeg_of_pos ε hb])
  · exact killed hπ hv hs hw (ha.trans hb.symm) (revNeg_lt ha hb h)

end GlobalTheory.HolRead.KCpt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicUnitaryPointEqOfSectionComponentsEq
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocInj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem eq_of_toSub_eq {G : Type} [Group G] {H : Subgroup G} {g h : G} (hg : g ∈ H) (hh : h ∈ H)
    (e : toSub H g = toSub H h) : g = h := by
  unfold toSub at e
  rw [dite_eq_left hg, dite_eq_left hh] at e
  exact congrArg Subtype.val e

theorem under_conjSrc (w : Pl E) :
    (conjSrc (GlobalTheory.SplitPts.conjE E) w).under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) :=
  (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) w _).2
    (Or.inr (GlobalTheory.SplitPts.conjPl_self_conjSrc w))

theorem conjSrc_eq_of_not_split {w : Pl E} (hw : ¬ IsSplitAt w) : conjSrc (GlobalTheory.SplitPts.conjE E) w = w := by
  by_contra h
  exact hw ⟨_, h, under_conjSrc w⟩

theorem ext_cj (w : Pl E) (a : Af E) : ∀ (v : Pl E) (_ : v = w) (f : v.adicCompletion E →+* w.adicCompletion E),
    Continuous f → (∀ k : E, f (algebraMap E _ k) = algebraMap E _ (IsCMField.complexConj E k)) →
      f (pLoc E v a) = cj w (pLoc E w a) := by
  rintro v rfl f hf h
  have hex : ∃ s : v.adicCompletion E →+* v.adicCompletion E, Continuous s ∧
      ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x) := ⟨f, hf, h⟩
  have hcj : cj v = hex.choose := by unfold cj; rw [dite_eq_left hex]
  rw [hcj]
  exact congrFun ((HeightOneSpectrum.denseRange_algebraMap (K := E) v).equalizer hf hex.choose_spec.1
    (funext fun k => (h k).trans (hex.choose_spec.2 k).symm)) _

theorem cLoc_mem_UL {w : Pl E} (hw : ¬ IsSplitAt w) (x : UA E n) : cLoc w x ∈ UL n w := by
  have hUL : UL n w = UJ (cj w) 1 := by unfold UL; rw [if_neg hw]
  rw [hUL]
  show cT (cj w) (cLoc w x).val * 1 * (cLoc w x).val = 1
  have hc := GlobalTheory.SplitPts.comp_eq x w
  have e : (cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) x).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) w) =
      (cLoc w x).val.map (cj w) := by
    refine Matrix.ext fun i j => ?_
    exact ext_cj w (pFin E (x.1.val i j)) _ (conjSrc_eq_of_not_split hw) _ (conjLoc_spec _ w).1
      (conjLoc_spec _ w).2.1
  rw [e] at hc
  rw [Matrix.mul_one]
  exact hc

theorem cLoc_conj_eq (w : Pl E) (x y : UA E n) (h : cLoc w x = cLoc w y) :
    cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) x = cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) y := by
  have hx := GlobalTheory.SplitPts.comp_eq x w
  have hy := GlobalTheory.SplitPts.comp_eq y w
  rw [h] at hx
  have e : ((cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) x).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) w))ᵀ =
      ((cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) y).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) w))ᵀ := by
    have h1 := mul_eq_one_comm.1 hx
    have h2 := mul_eq_one_comm.1 hy
    calc _ = ((cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) y).val.map (conjLoc (GlobalTheory.SplitPts.conjE E) w))ᵀ *
            ((cLoc w y).val * ((cLoc (conjSrc (GlobalTheory.SplitPts.conjE E) w) x).val.map
              (conjLoc (GlobalTheory.SplitPts.conjE E) w))ᵀ) := by rw [← Matrix.mul_assoc, hy, Matrix.one_mul]
      _ = _ := by rw [h1, Matrix.mul_one]
  refine Units.ext (Matrix.ext fun i j => (conjLoc (GlobalTheory.SplitPts.conjE E) w).injective ?_)
  have := congrFun (congrFun e j) i
  simpa using this

end GlobalTheory.LocInj

open GlobalTheory.LocInj in
theorem GlobalTheory.BCT.finU_eq_of_loc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ,
    ∀ S : Set (Pl E), IsSection S → ∀ x y : finU (E := E) (n := n),
      (∀ w ∈ S, toSub (UL n w) (cLoc w (x : UA E n)) = toSub (UL n w) (cLoc w (y : UA E n))) → x = y := by
  intro E _ _ _ _ n S hS x y hxy

  have hS' : ∀ w ∈ S, cLoc w (x : UA E n) = cLoc w (y : UA E n) := by
    intro w hw
    by_cases hsp : IsSplitAt w
    · have hUL : ∀ g, g ∈ UL n w := fun g => by unfold UL; rw [if_pos hsp]; trivial
      exact eq_of_toSub_eq (hUL _) (hUL _) (hxy w hw)
    · exact eq_of_toSub_eq (cLoc_mem_UL hsp _) (cLoc_mem_UL hsp _) (hxy w hw)

  have hall : ∀ u : Pl E, cLoc u (x : UA E n) = cLoc u (y : UA E n) := by
    intro u
    obtain ⟨s, ⟨hsS, hsu⟩, -⟩ := hS u
    by_cases hus : u = s
    · subst hus; exact hS' u hsS
    · have hsp : IsSplitAt s := ⟨u, hus, hsu.symm⟩
      obtain ⟨-, -, hover⟩ := GlobalTheory.SplitPts.over_split hsp
      rcases hover u hsu.symm with h | h
      · exact absurd h hus
      · subst h; exact cLoc_conj_eq s _ _ (hS' s hsS)
  have hxi : cInf (x : UA E n) = 1 := MonoidHom.mem_ker.1 x.2
  have hyi : cInf (y : UA E n) = 1 := MonoidHom.mem_ker.1 y.2
  refine Subtype.ext (Subtype.ext (ga_ext (hxi.trans hyi.symm) ?_))
  refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext (R := 𝓞 E) E fun u => ?_)
  exact congrArg (fun g : GL (Fin n) (u.adicCompletion E) => g.val i j) (hall u)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicUnitaryPointLocalComponentMemLocalUn
section
noncomputable section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.LocMem

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem conjSrc_eq_of_not_split (w : Pl E) (hw : ¬ IsSplitAt w) :
    conjSrc (IsCMField.complexConj E).toRingEquiv w = w := by
  set c : E ≃+* E := (IsCMField.complexConj E).toRingEquiv
  set u := conjSrc c w with hu
  have h : GlobalTheory.Mem.Chr.ConjPl c u w := conjPl_conjSrc c w
  by_contra hne
  apply hw
  refine ⟨u, hne, ?_⟩
  apply HeightOneSpectrum.ext
  ext y
  change algebraMap _ _ y ∈ u.asIdeal ↔ algebraMap _ _ y ∈ w.asIdeal
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E), ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E)]
  have hfix : c ((algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) y : 𝓞 E) : E) =
      ((algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) y : 𝓞 E) : E) := by
    change IsCMField.complexConj E _ = _
    rw [IsCMField.complexConj_eq_self_iff]
    exact ((y : maximalRealSubfield E)).2
  rw [← h, hfix]

theorem eq_cj_of_ext (w u : Pl E) (hu : u = w) (f : u.adicCompletion E →+* w.adicCompletion E) (hf : Continuous f)
    (hext : ∀ k : E, f (algebraMap E _ k) = algebraMap E _ (IsCMField.complexConj E k)) (b : Af E) :
    f (pLoc E u b) = cj w (pLoc E w b) := by
  subst hu
  have hex : ∃ s : u.adicCompletion E →+* u.adicCompletion E, Continuous s ∧
      ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x) := ⟨f, hf, hext⟩
  have hcj : cj u = hex.choose := by
    unfold cj
    rw [dite_eq_left hex]
  have hfs : (f : u.adicCompletion E → u.adicCompletion E) = hex.choose :=
    (HeightOneSpectrum.denseRange_algebraMap E u).equalizer hf hex.choose_spec.1
      (funext fun k => by simp only [Function.comp_apply, hext, hex.choose_spec.2])
  rw [hcj, ← hfs]

theorem cj_pLoc_pFin (w : Pl E) (hw : ¬ IsSplitAt w) (a : Ad E) :
    cj w (pLoc E w (pFin E a)) = pLoc E w (pFin E (conjAd E a)) := by
  change _ = pLoc E w (conjFin (IsCMField.complexConj E).toRingEquiv (pFin E a))
  rw [pLoc_conjFin]
  exact (eq_cj_of_ext w _ (conjSrc_eq_of_not_split w hw) _ (conjLoc_spec _ w).1
    (fun k => (conjLoc_spec _ w).2.1 k) (pFin E a)).symm

end GlobalTheory.BCT.LocMem


open GlobalTheory.BCT.LocMem in
theorem GlobalTheory.BCT.cLoc_mem_UL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ,
    ∀ (w : Pl E) (x : finU (E := E) (n := n)), cLoc w (x : UA E n) ∈ UL n w := by
  intro E _ _ _ _ n w x
  unfold UL
  split_ifs with hs
  · exact Subgroup.mem_top _
  have hx : cT (conjAd E) ((x : UA E n) : GA E n).val * 1 * ((x : UA E n) : GA E n).val = 1 := (x : UA E n).2
  set φ : Ad E →+* w.adicCompletion E := (pLoc E w).comp (pFin E)
  have hval : (cLoc w (x : UA E n)).val = φ.mapMatrix ((x : UA E n) : GA E n).val := rfl
  have hcT : cT (cj w) (φ.mapMatrix ((x : UA E n) : GA E n).val) =
      φ.mapMatrix (cT (conjAd E) ((x : UA E n) : GA E n).val) := by
    refine Matrix.ext fun i j => ?_
    exact cj_pLoc_pFin w hs _
  change cT (cj w) (cLoc w (x : UA E n)).val * 1 * (cLoc w (x : UA E n)).val = 1
  rw [hval, hcT, ← map_one φ.mapMatrix, ← map_mul, ← map_mul, hx]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFixedUnitClassesCentralizerRegular
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.LKCx.ClsReg.finite_fixed_classes_regular : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ), sh G β = β →
    ∀ (y₀ : G.Cˣ) (s : ℚ), (y₀ : G.C) * β * sh G (y₀ : G.C) = algebraMap ℚ G.C s * β →
    (minpoly G.F (y₀ : G.C)).Separable → (minpoly G.F (y₀ : G.C)).natDegree = G.n → ∀ S : Finset ℕ,
    ∃ A : Finset G.C, ∀ a : G.C, IsUnit a → Commute a y₀ → (β : G.C) * sh G a * ((β⁻¹ : G.Cˣ) : G.C) = a →
      (∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∉ S → ∃ (u : ℚ_[ℓ]ˣ) (z : (ℚ_[ℓ] ⊗[ℚ] G.C)ˣ), Commute (z : ℚ_[ℓ] ⊗[ℚ] G.C) (inC G ℚ_[ℓ] (y₀ : G.C)) ∧
      inC G ℚ_[ℓ] a = algebraMap ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] G.C) (u : ℚ_[ℓ]) * ((z : ℚ_[ℓ] ⊗[ℚ] G.C) * inC G ℚ_[ℓ] (β : G.C) *
        (starT G.star ℚ_[ℓ] (z : ℚ_[ℓ] ⊗[ℚ] G.C)).unop * inC G ℚ_[ℓ] ((β⁻¹ : G.Cˣ) : G.C))) →
      ∃ a₀ ∈ A, ∃ (r : ℚˣ) (e : G.Cˣ), Commute (e : G.C) y₀ ∧
        a = algebraMap ℚ G.C (r : ℚ) * ((e : G.C) * a₀ * ((β : G.C) * sh G (e : G.C) * ((β⁻¹ : G.Cˣ) : G.C))) := by
  intro p _ G β hβ y₀ s hy hsep hdeg S
  classical
  set Ec : Subalgebra ℚ G.C := Subalgebra.centralizer ℚ ({(y₀ : G.C)} : Set G.C) with hEc
  have memE : ∀ x : G.C, x ∈ Ec ↔ Commute x (y₀ : G.C) := by
    intro x
    rw [hEc, Subalgebra.mem_centralizer_iff]
    constructor
    · intro h; exact (h (y₀ : G.C) (Set.mem_singleton _)).symm
    · intro h g hg; rw [Set.mem_singleton_iff.1 hg]; exact h.eq.symm
  have hcomm : ∀ a b : Ec, a * b = b * a := fun a b => Subtype.ext
    (GlobalTheory.LKCx.ClsReg.commute_of_commute_of_separable G y₀ hsep hdeg a b ((memE a).1 a.2) ((memE b).1 b.2)).eq
  letI : CommRing Ec := { (inferInstance : Ring Ec) with mul_comm := hcomm }
  haveI : FiniteDimensional ℚ G.C := Module.Finite.trans G.F G.C
  haveI : FiniteDimensional ℚ Ec := inferInstance
  haveI : IsReduced Ec := ⟨fun x ⟨k, hk⟩ => Subtype.ext (GlobalTheory.T.eq_zero_of_nilpotent_commute_separable_minpoly p G y₀ hsep hdeg x ((memE x).1 x.2) k
    (by simpa using congrArg Subtype.val hk))⟩

  have sh_add : ∀ x y : G.C, sh G (x + y) = sh G x + sh G y := fun x y => by simp [sh]
  have sh_mul : ∀ x y : G.C, sh G (x * y) = sh G y * sh G x := fun x y => by simp [sh]
  have sh_one : sh G 1 = 1 := by simp [sh]
  have sh_zero : sh G 0 = 0 := by simp [sh]
  have sh_alg : ∀ q : ℚ, sh G (algebraMap ℚ G.C q) = algebraMap ℚ G.C q := fun q => by
    simp only [sh, RingHom.map_rat_algebraMap G.star q, MulOpposite.algebraMap_apply, MulOpposite.unop_op]
  have sh_sh : ∀ x, sh G (sh G x) = x := fun x => G.star_star x
  have sh_binv : sh G ((β⁻¹ : G.Cˣ) : G.C) = ((β⁻¹ : G.Cˣ) : G.C) := by
    have h1 : sh G ((β⁻¹ : G.Cˣ) : G.C) * (β : G.C) = 1 := by
      rw [← hβ, ← sh_mul, Units.mul_inv, sh_one]
    calc sh G ((β⁻¹ : G.Cˣ) : G.C) = sh G ((β⁻¹ : G.Cˣ) : G.C) * (β : G.C) * ((β⁻¹ : G.Cˣ) : G.C) := by
          rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [h1, one_mul]
  have hs0 : s ≠ 0 := by
    rintro rfl
    have h0 : sh G (y₀ : G.C) = 0 := by
      have := congrArg (fun t => ((β⁻¹ : G.Cˣ) : G.C) * (((y₀⁻¹ : G.Cˣ) : G.C) * t)) hy
      simpa [← mul_assoc] using this
    have : (y₀ : G.C) = 0 := by rw [← sh_sh (y₀ : G.C), h0, sh_zero]
    exact y₀.ne_zero this
  have tC_y : (β : G.C) * sh G (y₀ : G.C) * ((β⁻¹ : G.Cˣ) : G.C) = algebraMap ℚ G.C s * ((y₀⁻¹ : G.Cˣ) : G.C) := by
    have := congrArg (fun t => ((y₀⁻¹ : G.Cˣ) : G.C) * t * ((β⁻¹ : G.Cˣ) : G.C)) hy
    simp only [← mul_assoc, Units.inv_mul, one_mul] at this
    rw [this, mul_assoc, Units.mul_inv, mul_one, Algebra.commutes]
  have tC_mul : ∀ x y : G.C, (β : G.C) * sh G (x * y) * ((β⁻¹ : G.Cˣ) : G.C) =
      ((β : G.C) * sh G y * ((β⁻¹ : G.Cˣ) : G.C)) * ((β : G.C) * sh G x * ((β⁻¹ : G.Cˣ) : G.C)) := by
    intro x y
    rw [sh_mul]; simp only [mul_assoc, Units.inv_mul_cancel_left]
  have tC_mem : ∀ x : G.C, Commute x (y₀ : G.C) →
      Commute ((β : G.C) * sh G x * ((β⁻¹ : G.Cˣ) : G.C)) (y₀ : G.C) := by
    intro x hx
    have h1 : Commute ((β : G.C) * sh G x * ((β⁻¹ : G.Cˣ) : G.C)) (algebraMap ℚ G.C s * ((y₀⁻¹ : G.Cˣ) : G.C)) := by
      rw [← tC_y]
      show _ * _ = _ * _
      rw [← tC_mul, ← tC_mul, hx.eq]
    have h2 : Commute ((β : G.C) * sh G x * ((β⁻¹ : G.Cˣ) : G.C)) ((y₀⁻¹ : G.Cˣ) : G.C) := by
      have h3 := h1.smul_right (s⁻¹)
      rwa [Algebra.smul_def, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hs0, map_one, one_mul] at h3
    simpa using h2.units_inv_right

  let τf : Ec → Ec := fun x => ⟨(β : G.C) * sh G (x : G.C) * ((β⁻¹ : G.Cˣ) : G.C), (memE _).2 (tC_mem x ((memE x).1 x.2))⟩
  have τf_val : ∀ x : Ec, ((τf x : Ec) : G.C) = (β : G.C) * sh G (x : G.C) * ((β⁻¹ : G.Cˣ) : G.C) := fun x => rfl
  have τf_inv : ∀ x, τf (τf x) = x := by
    intro x; apply Subtype.ext
    rw [τf_val, τf_val, sh_mul, sh_mul, sh_sh, hβ, sh_binv]
    simp only [mul_assoc, Units.mul_inv_cancel_left]
    rw [Units.mul_inv, mul_one]
  let τa : Ec →ₐ[ℚ] Ec :=
    { toFun := τf
      map_one' := by apply Subtype.ext; rw [τf_val]; simp [sh_one]
      map_mul' := by
        intro x y; apply Subtype.ext
        rw [τf_val, Subalgebra.coe_mul, tC_mul, ← τf_val, ← τf_val, ← Subalgebra.coe_mul, hcomm]
      map_zero' := by apply Subtype.ext; rw [τf_val]; simp [sh_zero]
      map_add' := by
        intro x y; apply Subtype.ext
        rw [τf_val, Subalgebra.coe_add, sh_add, mul_add, add_mul]; rfl
      commutes' := by
        intro q; apply Subtype.ext
        rw [τf_val]
        change (β : G.C) * sh G (algebraMap ℚ G.C q) * ((β⁻¹ : G.Cˣ) : G.C) = algebraMap ℚ G.C q
        rw [sh_alg, ← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one] }
  have τa_apply : ∀ x, τa x = τf x := fun x => rfl
  let τe : Ec ≃ₐ[ℚ] Ec := AlgEquiv.ofAlgHom τa τa (AlgHom.ext fun x => τf_inv x) (AlgHom.ext fun x => τf_inv x)
  have τe_apply : ∀ x, τe x = τf x := fun x => rfl
  have τe_inv : ∀ x, τe (τe x) = x := fun x => τf_inv x

  obtain ⟨x₁, hx₁⟩ := DFunLike.ne_iff.mp (IsCMField.complexConj_ne_one G.F)
  set jF : G.F := x₁ - IsCMField.complexConj G.F x₁ with hjF
  have hjF0 : jF ≠ 0 := by
    rw [hjF, sub_ne_zero]; intro h; exact hx₁ (by rw [← h]; rfl)
  have hjFc : IsCMField.complexConj G.F jF = -jF := by
    rw [hjF, map_sub, IsCMField.complexConj_apply_apply]; ring
  have cen : ∀ z : G.F, algebraMap G.F G.C z ∈ Ec := fun z => (memE _).2 (Algebra.commutes z (y₀ : G.C))
  let jE : Ec := ⟨algebraMap G.F G.C jF, cen jF⟩
  have hjE : IsUnit jE := by
    have h : jE * ⟨algebraMap G.F G.C jF⁻¹, cen _⟩ = 1 := by
      apply Subtype.ext
      change algebraMap G.F G.C jF * algebraMap G.F G.C jF⁻¹ = 1
      rw [← map_mul, mul_inv_cancel₀ hjF0, map_one]
    exact ⟨⟨jE, _, h, by rw [hcomm]; exact h⟩, rfl⟩
  have hjτ : τe jE = -jE := by
    apply Subtype.ext
    rw [τe_apply, τf_val]
    change (β : G.C) * (G.star (algebraMap G.F G.C jF)).unop * ((β⁻¹ : G.Cˣ) : G.C) = -algebraMap G.F G.C jF
    rw [G.star_F, hjFc, ← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one, map_neg]
  obtain ⟨A', hA'⟩ := GlobalTheory.T.finite_classes_fixedUnits_mod_rat_norms Ec τe τe_inv jE hjE hjτ S
  refine ⟨A'.image Subtype.val, ?_⟩
  intro a ha hac hafix hloc

  obtain ⟨ua, rfl⟩ := ha
  have ha' : (ua : G.C) ∈ Ec := (memE _).2 hac
  set a' : Ec := ⟨ua, ha'⟩ with ha'def
  have hinvE : ((ua⁻¹ : G.Cˣ) : G.C) ∈ Ec := (memE _).2 hac.units_inv_left
  have ha'u : IsUnit a' := by
    have h : a' * ⟨_, hinvE⟩ = 1 := Subtype.ext ua.mul_inv
    exact ⟨⟨a', _, h, by rw [hcomm]; exact h⟩, rfl⟩
  have ha'fix : τe a' = a' := Subtype.ext hafix
  have hloc' : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∃ (c : ℚ) (b x y : Ec), c ≠ 0 ∧ IsUnit b ∧
      a' = x * (algebraMap ℚ Ec c * (b * τe b)) ∧
      algebraMap ℚ Ec c * (b * τe b) = y * a' ∧ ∃ d : ℕ, ¬ ℓ ∣ d ∧ IsIntegral ℤ ((d : Ec) * x) ∧
        IsIntegral ℤ ((d : Ec) * y) := by
    intro ℓ hℓ hℓS
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    obtain ⟨u, z, hzc, hz⟩ := hloc ℓ hℓS
    obtain ⟨hinj, hsurj⟩ := GlobalTheory.T.tensor_centralizer_injective_commutant_eq ℚ_[ℓ] G.C (y₀ : G.C)
    set ι := Algebra.TensorProduct.map (AlgHom.id ℚ_[ℓ] ℚ_[ℓ]) Ec.val with hι
    have hinCy : inC G ℚ_[ℓ] (y₀ : G.C) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (y₀ : G.C) := rfl
    obtain ⟨w, hw⟩ := hsurj z (hinCy ▸ hzc)
    obtain ⟨w2, hw2⟩ := hsurj ((z⁻¹ : (ℚ_[ℓ] ⊗[ℚ] G.C)ˣ) : ℚ_[ℓ] ⊗[ℚ] G.C) (hinCy ▸ hzc.units_inv_left)
    have hww : w * w2 = 1 := hinj (by rw [map_mul, hw, hw2, Units.mul_inv, map_one])
    let Z : (ℚ_[ℓ] ⊗[ℚ] Ec)ˣ := ⟨w, w2, hww, by rw [mul_comm]; exact hww⟩
    set τℓ := Algebra.TensorProduct.map (AlgHom.id ℚ_[ℓ] ℚ_[ℓ]) τe.toAlgHom with hτℓ
    have hkey : ∀ t : ℚ_[ℓ] ⊗[ℚ] Ec, ι (τℓ t) = inC G ℚ_[ℓ] (β : G.C) * (starT G.star ℚ_[ℓ] (ι t)).unop *
        inC G ℚ_[ℓ] ((β⁻¹ : G.Cˣ) : G.C) := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul r e =>
        rw [hτℓ, hι, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
          starT_tmul]
        simp only [inC, AlgHom.id_apply, Subalgebra.coe_val, RingHom.coe_coe,
          Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
        rfl
      | add t1 t2 h1 h2 => rw [map_add (f := _), map_add (f := _), h1, h2, map_add (f := _), map_add (f := _), MulOpposite.unop_add, mul_add, add_mul]
    have heq : (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] a' = algebraMap ℚ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] Ec) (u : ℚ_[ℓ]) *
        ((Z : ℚ_[ℓ] ⊗[ℚ] Ec) * τℓ (Z : ℚ_[ℓ] ⊗[ℚ] Ec)) := by
      apply hinj
      rw [map_mul, map_mul, AlgHom.commutes, hkey]
      have hZ : ι (Z : ℚ_[ℓ] ⊗[ℚ] Ec) = z := hw
      rw [hZ, hι, Algebra.TensorProduct.map_tmul]
      change inC G ℚ_[ℓ] (ua : G.C) = _
      rw [hz]
      simp only [mul_assoc]
    obtain ⟨c, b, x, y, hc, hb, h1, h2, d, hd, hx, hy⟩ := GlobalTheory.T.exists_global_norm_approx_of_local_padic_norm Ec τe.toAlgHom ℓ a' u Z ha'u heq
    exact ⟨c, b, x, y, hc, hb, h1, h2, d, hd, hx, hy⟩
  obtain ⟨a₀, ha₀, r, e, hre⟩ := hA' a' ha'u ha'fix hloc'
  refine ⟨(a₀ : G.C), Finset.mem_image_of_mem _ ha₀, r, Units.map (Ec.val : Ec →* G.C) e, (memE _).1 (e : Ec).2, ?_⟩
  rw [τe_apply] at hre
  have := congrArg Subtype.val hre
  simp only [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, τf_val] at this
  simpa using this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomotopyInvQuotIInfKerRetractionsStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hInv_quot_iInf_ker_retractions : ∀ (q : ℕ) [NeZero q] (D T E : Type) [CommRing D] [IsDomain D] [CommRing T] [IsDomain T] [Algebra D T] [Algebra.IsIntegral D T] [CommRing E] [Algebra D E] [Algebra.IsIntegral D E], IsUnit (q : D) → HInv q T → (∀ (E' : Type) [CommRing E'] [Algebra D E'] [Algebra.IsIntegral D E'] (s : D), s ≠ 0 → algebraMap D E' s = 0 → HInv q E') → ∀ (ι : T →ₐ[D] E) (X : Finset (E →ₐ[D] T)), (∀ χ ∈ X, χ.comp ι = AlgHom.id D T) → HInv q (E ⧸ ⨅ χ ∈ X, RingHom.ker χ) := by
  first | (exact @GlobalTheory.homotopyInv_quot_iInf_ker_retractions) | (exact GlobalTheory.homotopyInv_quot_iInf_ker_retractions) | (intros; apply GlobalTheory.homotopyInv_quot_iInf_ker_retractions  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthStalkNeTopOfNoGenerisationStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_stalk_ne_infty_of_no_generization : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (F : X.Modules) [GlobalTheory.QCoh.IsFiniteQC F] (w : X), (∀ y ∈ GlobalTheory.QCoh.support F, w ∈ closure ({y} : Set X) → y = w) → Module.length (X.presheaf.stalk w) (F.presheaf.stalk w :) ≠ ⊤ := by
  first | exact @GlobalTheory.QCoh.length_stalk_ne_top_of_no_generisation | exact GlobalTheory.QCoh.length_stalk_ne_top_of_no_generisation | (intros; apply GlobalTheory.QCoh.length_stalk_ne_top_of_no_generisation <;> assumption)
end

