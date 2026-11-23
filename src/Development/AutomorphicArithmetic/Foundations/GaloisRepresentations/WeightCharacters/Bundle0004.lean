module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.CAllFin
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1081
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1113
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.BlockBoundTheorem
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BlockCharacterApproximation.NeatOfPlace
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.ProjEx
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenFormEqFiniteSumAutRepEigenForms

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.LadicWeightAtEmbeddingOverPlace
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching

namespace UpperTheory.Gal.Wt

theorem ladic_weight_at_embedding_over_place : Kap0 := by
  intro E _ _ _ l _ ι a v' τ hτ
  obtain ⟨u, hu⟩ := GlobalTheory.LadicPlace.exists_place_of_embedding E l (ι.symm.toRingHom.comp τ)
  have hle : v'.asIdeal ≤ u.asIdeal := fun x hx => by
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E)]
    exact (hu _).2 (hτ x hx)
  have huv : v' = u := HeightOneSpectrum.ext (v'.isMaximal.eq_of_le u.isPrime.ne_top hle)
  subst huv
  obtain ⟨j, hj, hjE⟩ := GlobalTheory.exists_continuous_extension_adicCompletion E l (ι.symm.toRingHom.comp τ) v' hu
  have hl : ((l : ℕ) : 𝓞 E) ∈ v'.asIdeal := by
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E)]
    have h1 : ‖(ι.symm.toRingHom.comp τ) ((((l : ℕ) : 𝓞 E)) : E)‖ < 1 := by
      have h0 : (ι.symm.toRingHom.comp τ) ((((l : ℕ) : 𝓞 E)) : E) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
      rw [h0, PadicAlgCl.norm_extends (p := l) (l : ℚ_[l])]
      exact Padic.norm_p_lt_one
    simpa using (hu (((l : ℕ) : 𝓞 E) : E)).2 h1
  have hκ : ∀ (g : UA E a) (p q : Fin a), ((((Matrix.GeneralLinearGroup.map (ι.toRingHom.comp j)).comp (cLoc v')) g :
      GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) p q = ι (j (((cLoc v' g : GL (Fin a) (v'.adicCompletion E)) :
        Matrix (Fin a) (Fin a) (v'.adicCompletion E)) p q)) := fun _ _ _ => rfl
  refine ⟨(Matrix.GeneralLinearGroup.map (ι.toRingHom.comp j)).comp (cLoc v'), ?_, ?_, ?_, ?_, ?_⟩
  · rintro γ ⟨g₀, hg₀⟩
    ext p q
    change ι (j (pLoc E v' (pFin E ((γ.1 : Matrix (Fin a) (Fin a) (Ad E)) p q)))) =
      coord τ (pInf E ((γ.1 : Matrix (Fin a) (Fin a) (Ad E)) p q))
    have hg₁ : (γ.1 : GL (Fin a) (Ad E)) = ratGL E a g₀ := hg₀.symm
    rw [hg₁]
    change ι (j (pLoc E v' (pFin E (algebraMap E (Ad E) ((g₀ : Matrix (Fin a) (Fin a) E) p q))))) =
      coord τ (pInf E (algebraMap E (Ad E) ((g₀ : Matrix (Fin a) (Fin a) E) p q)))
    rw [coord_algebraMap]
    have h := congrArg (fun φ : E →+* Qbar l => φ ((g₀ : Matrix (Fin a) (Fin a) E) p q)) hjE
    simp only [RingHom.coe_comp, Function.comp_apply] at h
    change ι (j (algebraMap E (v'.adicCompletion E) _)) = _
    rw [h]
    simp
  · intro x hx
    have hx' : Matrix.GeneralLinearGroup.map (pFin E) x.1 = 1 := hx
    have h2 : cLoc v' x = Matrix.GeneralLinearGroup.map (pLoc E v') (Matrix.GeneralLinearGroup.map (pFin E) x.1) := by
      ext; rfl
    rw [MonoidHom.comp_apply, h2, hx', map_one, map_one]
  · intro g
    constructor
    · intro h
      have hinj : Function.Injective (ι.toRingHom.comp j) := RingHom.injective _
      refine Units.ext (Matrix.ext fun p q => hinj ?_)
      have h3 := congrArg (fun m : GL (Fin a) ℂ => (m : Matrix (Fin a) (Fin a) ℂ) p q) h
      simp only [hκ] at h3
      have h4 : (ι.toRingHom.comp j) (((1 : GL (Fin a) (v'.adicCompletion E)) : Matrix (Fin a) (Fin a) (v'.adicCompletion E)) p q) =
          ((1 : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) p q := by
        simp only [Units.val_one, Matrix.one_apply]
        split_ifs <;> simp
      exact h3.trans h4.symm
    · intro h
      rw [MonoidHom.comp_apply, h, map_one]
  · intro p q
    have h1 : (fun g : UA E a => ι.symm (((((Matrix.GeneralLinearGroup.map (ι.toRingHom.comp j)).comp (cLoc v')) g :
        GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) p q)) =
        fun g => j (((cLoc v' g : GL (Fin a) (v'.adicCompletion E)) : Matrix (Fin a) (Fin a) (v'.adicCompletion E)) p q) :=
      funext fun g => by rw [hκ, RingEquiv.symm_apply_apply]
    rw [h1]
    exact hj.comp ((Units.continuous_val.matrix_elem p q).comp (GlobalTheory.BCT.GlobLev.continuous_cLoc v'))
  · intro g hg p q
    obtain ⟨h1, h2⟩ := GlobalTheory.EulerTwRestr.mem_KGL_iff.1 hg
    constructor
    · rw [hκ, RingEquiv.symm_apply_apply]
      exact UpperTheory.Gal.Gen.Loc.norm_map_integer_le_one l v' j hl hj _ (h1 p q)
    · rw [MonoidHom.comp_apply, ← map_inv]
      change ‖ι.symm (ι (j ((((cLoc v' g)⁻¹ : GL (Fin a) (v'.adicCompletion E)) :
        Matrix (Fin a) (Fin a) (v'.adicCompletion E)) p q)))‖ ≤ 1
      rw [RingEquiv.symm_apply_apply]
      exact UpperTheory.Gal.Gen.Loc.norm_map_integer_le_one l v' j hl hj _ (h2 p q)

end UpperTheory.Gal.Wt

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.NearSub
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

private theorem entry_mul_le {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ}
    {A B : Matrix (Fin a) (Fin a) ℂ} {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hA : ∀ i j, ‖ι.symm (A i j)‖ ≤ r) (hB : ∀ i j, ‖ι.symm (B i j)‖ ≤ s) (i j : Fin a) :
    ‖ι.symm ((A * B) i j)‖ ≤ r * s := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.mul_apply, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hr hs) fun k _ => ?_
  rw [map_mul, norm_mul]
  exact mul_le_mul (hA i k) (hB k j) (norm_nonneg _) hr

theorem UpperTheory.Gal.Wt.nearSub_of :
    UpperTheory.Gal.Wt.NearSub := by
  intro l _ ι a Γ _ _ _ φ hc hI ε hε
  refine ⟨{ carrier := {g | NearOne ι ε (φ g)}
            mul_mem' := ?_
            one_mem' := ?_
            inv_mem' := ?_ }, ?_, fun g => Iff.rfl⟩
  · intro g h hg hh
    have hg' : NearOne ι ε (φ g) := hg
    have hh' : NearOne ι ε (φ h) := hh
    show NearOne ι ε (φ (g * h))
    intro i j
    have key : ((φ (g * h) : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) - 1
        = (((φ g : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) - 1) * ((φ h : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)
          + (((φ h : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) - 1) := by
      rw [map_mul, Units.val_mul]
      noncomm_ring
    have e := congrFun (congrFun key i) j
    rw [Matrix.sub_apply] at e
    rw [e, Matrix.add_apply, map_add (f := _)]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · have := entry_mul_le ι hε.le zero_le_one
        (A := ((φ g : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) - 1)
        (B := ((φ h : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ))
        (fun i j => by rw [Matrix.sub_apply]; exact hg' i j) (fun i j => (hI h i j).1) i j
      exact this.trans_eq (mul_one ε)
    · rw [Matrix.sub_apply]
      exact hh' i j
  · show NearOne ι ε (φ 1)
    intro i j
    rw [map_one, Units.val_one, sub_self, map_zero, norm_zero]
    exact hε.le
  · intro g hg
    have hg' : NearOne ι ε (φ g) := hg
    show NearOne ι ε (φ g⁻¹)
    intro i j
    have key : ((φ g⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) - 1
        = -((((φ g)⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ)
            * (((φ g : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) - 1)) := by
      rw [map_inv, mul_sub, Units.inv_mul, mul_one, neg_sub]
    have e := congrFun (congrFun key i) j
    rw [Matrix.sub_apply] at e
    rw [e, Matrix.neg_apply, map_neg, norm_neg]
    have := entry_mul_le ι zero_le_one hε.le
      (A := (((φ g)⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ))
      (B := ((φ g : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) - 1)
      (fun i j => (hI g i j).2) (fun i j => by rw [Matrix.sub_apply]; exact hg' i j) i j
    exact this.trans_eq (one_mul ε)
  · have hset : ({g | NearOne ι ε (φ g)} : Set Γ)
        = ⋂ i, ⋂ j, (fun g => ι.symm (((φ g : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j)) ⁻¹'
            Metric.closedBall (ι.symm ((1 : Matrix (Fin a) (Fin a) ℂ) i j)) ε := by
      ext g
      simp only [Set.mem_setOf_eq, NearOne, map_sub, Set.mem_iInter, Set.mem_preimage,
        Metric.mem_closedBall, dist_eq_norm]
    show IsOpen ({g | NearOne ι ε (φ g)} : Set Γ)
    rw [hset]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (hc i j).isOpen_preimage _ (IsUltrametricDist.isOpen_closedBall _ hε.ne')
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.NeatLev
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.neatLev_of :
    UpperTheory.Gal.Wt.NeatLev := by
  intro E _ _ _ l hl a ha w₀ hmem hs v' hv' hap K hK hint Kv hKv W f hf
  obtain ⟨N, hN, hNf⟩ := UpperTheory.Gal.Gen.smoothAt_holds E a w₀ hs W f
  obtain ⟨J, hJ, hJN, hJt, -⟩ := UpperTheory.Gal.Gen.tower_holds E w₀ a l hl hmem ha N hN
  obtain ⟨hLev, hmemC, hcJ, -, -, -⟩ :=
    UpperTheory.Gal.Gen.levFacts_holds E a w₀ hs K hK (J 0) (hJ.isOpen 0) (hJ.compact 0)
  have hKC : K ≤ UpperTheory.Gal.Gen.lev K w₀ (J 0) := le_sup_left
  refine ⟨UpperTheory.Gal.Gen.lev K w₀ (J 0), hLev, hKC, ?_, ?_, ?_⟩
  · intro g γ hγ c hc x hx h
    have hT : UpperTheory.Gal.CharacterCongruences.TorsFreeAt (UpperTheory.Gal.Gen.lev K w₀ (J 0)) w₀ :=
      fun k hk ho => hJt _ (hcJ k hk) ho
    exact UpperTheory.Gal.CharacterCongruences.neatOfPlace_holds E a _ ⟨hLev.fin, hLev.compact, hLev.isOpen⟩ w₀ hT
      g γ hγ c hc x hx h
  · have hKGL : GlobalTheory.LFun.KGL v' (n := a) ≤ (UpperTheory.Gal.Gen.lev K w₀ (J 0)).map (cLoc v') := by
      intro y hy
      obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E a v' hv'
      have hy' : cLoc v' (e.symm y : UA E a) = y := by rw [← he]; simp
      exact ⟨(e.symm y : UA E a), hKC (hint _ (e.symm y).2 (hy'.symm ▸ hy)), hy'⟩
    have hmax := UpperTheory.Gal.Gen.maxCpt_holds E v' a ((UpperTheory.Gal.Gen.lev K w₀ (J 0)).map (cLoc v'))
      (cLoc v' '' (UpperTheory.Gal.Gen.lev K w₀ (J 0) : Set (UA E a)))
      (hLev.compact.image (GlobalTheory.BCT.GlobLev.continuous_cLoc v'))
      (fun _ h => h) hKGL
    intro c hc
    exact hmax ⟨c, hc, rfl⟩
  · intro c hc v g
    obtain ⟨hcC, hcv⟩ := hc
    obtain ⟨k, hk, x, hx, hxJ, rfl⟩ := (hmemC _).1 hcC
    have hx1 : cLoc v' x = 1 :=
      MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx.2 v') hap)
    have hkv : k ∈ K ⊓ Kv.comap (cLoc v') := by
      refine ⟨hk, ?_⟩
      have h2 : cLoc v' (k * x) ∈ Kv := hcv
      rw [map_mul, hx1, mul_one] at h2
      exact h2
    rw [← mul_assoc, hNf x hx (hJN hxJ) v (g * k)]
    exact hf k hkv v g
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.PevExp
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

private theorem tor_entry_mem_expLe_one_expGe_zero (h : ExpBasic) (a k : ℕ) (A B : GL (Fin a) ℂ) (i j : Fin a) :
    (fun z : Circle => ((A * (tor a k z * B) : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j) ∈ ExpLe 1 ∧
    (fun z : Circle => ((A * (tor a k z * B) : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j) ∈ ExpGe 0 := by
  obtain ⟨_, _, hmono, hmon, hconst, _⟩ := h
  have heq : (fun z : Circle => ((A * (tor a k z * B) : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j) =
      ∑ l : Fin a, fun z : Circle => (A : Matrix (Fin a) (Fin a) ℂ) i l *
        ((if (l:ℕ) < k then (z:ℂ) else 1) * (B : Matrix (Fin a) (Fin a) ℂ) l j) := by
    funext z
    rw [Finset.sum_apply, Units.val_mul, Units.val_mul, Matrix.mul_apply]
    simp [tor_coe, Matrix.diagonal_mul]
  rw [heq]
  constructor
  · refine Submodule.sum_mem _ fun l _ => ?_
    by_cases hl : (l:ℕ) < k
    · convert (hmon ((A : Matrix (Fin a) (Fin a) ℂ) i l * (B : Matrix (Fin a) (Fin a) ℂ) l j) 1).1 using 1
      funext z
      simp only [hl, if_true, zpow_one]
      ring
    · convert (hmono 0 1 (by norm_num)).1
        (hconst ((A : Matrix (Fin a) (Fin a) ℂ) i l * (B : Matrix (Fin a) (Fin a) ℂ) l j)).1 using 1
      funext z
      simp [hl]
  · refine Submodule.sum_mem _ fun l _ => ?_
    by_cases hl : (l:ℕ) < k
    · convert (hmono 0 1 (by norm_num)).2
        (hmon ((A : Matrix (Fin a) (Fin a) ℂ) i l * (B : Matrix (Fin a) (Fin a) ℂ) l j) 1).2 using 1
      funext z
      simp only [hl, if_true, zpow_one]
      ring
    · convert (hconst ((A : Matrix (Fin a) (Fin a) ℂ) i l * (B : Matrix (Fin a) (Fin a) ℂ) l j)).2 using 1
      funext z
      simp [hl]

private theorem pow_mem_expLe_expGe_of_mem (h : ExpBasic) (f : Circle → ℂ) (hf : f ∈ ExpLe 1 ∧ f ∈ ExpGe 0) (n : ℕ) :
    (fun z => f z ^ n) ∈ ExpLe (n : ℤ) ∧ (fun z => f z ^ n) ∈ ExpGe 0 := by
  obtain ⟨hmulL, hmulG, _, _, hconst, _⟩ := h
  induction n with
  | zero =>
    simp only [pow_zero, Nat.cast_zero]
    exact hconst 1
  | succ n ih =>
    have e : (fun z => f z ^ (n + 1)) = fun z => (fun z => f z ^ n) z * f z := by
      funext z
      exact pow_succ _ _
    rw [e]
    constructor
    · have := hmulL _ _ _ _ ih.1 hf.1
      push_cast
      exact this
    · have := hmulG _ _ _ _ ih.2 hf.2
      simpa using this

private theorem prod_pow_mem_expLe_sum_expGe {ι : Type} [DecidableEq ι] (h : ExpBasic) (e : ι → Circle → ℂ)
    (he : ∀ i, e i ∈ ExpLe 1 ∧ e i ∈ ExpGe 0) (d : ι → ℕ) (S : Finset ι) :
    (fun z => ∏ i ∈ S, e i z ^ d i) ∈ ExpLe ((∑ i ∈ S, d i : ℕ) : ℤ) ∧
    (fun z => ∏ i ∈ S, e i z ^ d i) ∈ ExpGe 0 := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty, Nat.cast_zero]
    exact h.2.2.2.2.1 1
  | insert x S hx ih =>
    have hp := pow_mem_expLe_expGe_of_mem h (e x) (he x) (d x)
    have e1 : (fun z => ∏ i ∈ insert x S, e i z ^ d i) =
        fun z => (fun z => e x z ^ d x) z * (fun z => ∏ i ∈ S, e i z ^ d i) z := by
      funext z
      exact Finset.prod_insert hx
    rw [e1]
    constructor
    · have := h.1 _ _ _ _ hp.1 ih.1
      rw [Finset.sum_insert hx, Nat.cast_add]
      exact this
    · have := h.2.1 _ _ _ _ hp.2 ih.2
      simpa using this

theorem UpperTheory.Gal.Wt.pevExp_of :
    UpperTheory.Gal.Wt.ExpBasic → UpperTheory.Gal.Wt.PevExp := by
  intro h a k P A B
  classical
  let e : Fin a × Fin a → Circle → ℂ := fun p z =>
    ((A * (tor a k z * B) : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) p.1 p.2
  have he : ∀ p, e p ∈ ExpLe 1 ∧ e p ∈ ExpGe 0 := fun p => tor_entry_mem_expLe_one_expGe_zero h a k A B p.1 p.2
  have hsum : (fun z => pev P (A * (tor a k z * B))) =
      ∑ d ∈ P.support, fun z => AddMonoidAlgebra.coeff P d * ∏ i ∈ d.support, e i z ^ d i := by
    funext z
    rw [Finset.sum_apply]
    simp only [pev]
    rw [MvPolynomial.eval_eq]
  rw [hsum]
  constructor
  · refine Submodule.sum_mem _ fun d hd => ?_
    have hp := (prod_pow_mem_expLe_sum_expGe h e he d d.support).1
    have hle : ((∑ i ∈ d.support, d i : ℕ) : ℤ) ≤ (P.totalDegree : ℤ) := by
      exact_mod_cast MvPolynomial.le_totalDegree hd
    have hm := (h.2.2.1 _ _ hle).1 hp
    convert Submodule.smul_mem _ (AddMonoidAlgebra.coeff P d) hm using 1
  · refine Submodule.sum_mem _ fun d _ => ?_
    have hp := (prod_pow_mem_expLe_sum_expGe h e he d d.support).2
    convert Submodule.smul_mem _ (AddMonoidAlgebra.coeff P d) hp using 1
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.Pieces
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching

namespace UpperTheory.Gal.Wt

private theorem pev_map {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ}
    (P' : MvPolynomial (Fin a × Fin a) (Qbar l)) (h : GL (Fin a) ℂ) :
    ι.symm (pev (MvPolynomial.map ι.toRingHom P') h) =
      MvPolynomial.eval (fun p : Fin a × Fin a => ι.symm ((h : Matrix (Fin a) (Fin a) ℂ) p.1 p.2)) P' := by
  induction P' using MvPolynomial.induction_on with
  | C c => simp [pev]
  | add p q hp hq =>
    simp only [pev, map_add (f := _)] at hp hq ⊢
    rw [hp, hq]
  | mul_X p i hp =>
    simp only [pev, map_mul, MvPolynomial.map_X, MvPolynomial.eval_X] at hp ⊢
    rw [hp]

theorem pieces_of (hS : SepPoly) (hN : NearSub) : Pieces := by
  intro l _ ι a Γ _ _ _ _ φ hcont hint Γ' hΓ' hker ε hε
  obtain ⟨H, hHo, hH⟩ := hN l ι a Γ φ hcont hint ε hε
  set K : Subgroup Γ := H ⊓ Γ' with hK
  have hKo : IsOpen (K : Set Γ) := by
    rw [hK, Subgroup.coe_inf]
    exact hHo.inter hΓ'
  have hkerK : φ.ker ≤ K := by
    intro g hg
    refine Subgroup.mem_inf.mpr ⟨(hH g).2 ?_, hker hg⟩
    intro i j
    rw [MonoidHom.mem_ker.mp hg]
    simpa using hε.le
  haveI : Finite (Γ ⧸ K) := Subgroup.quotient_finite_of_isOpen K hKo
  letI : Fintype (Γ ⧸ K) := Fintype.ofFinite _
  let c : Γ ⧸ K → Γ := fun q => q.out
  let v : Γ → (Fin a × Fin a → Qbar l) := fun g p => ι.symm ((φ g : Matrix (Fin a) (Fin a) ℂ) p.1 p.2)
  have hv : Continuous v := continuous_pi fun p => hcont p.1 p.2
  have hKc : IsClosed (K : Set Γ) := Subgroup.isClosed_of_isOpen K hKo
  have hinj : ∀ g g', v g = v g' → g⁻¹ * g' ∈ K := by
    intro g g' hgg
    apply hkerK
    rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
    apply Units.ext
    apply Matrix.ext
    intro i j
    exact ι.symm.injective (congrFun hgg (i, j))
  have hsep : ∀ q : Γ ⧸ K, ∃ P' : MvPolynomial (Fin a × Fin a) (Qbar l),
      (∀ z ∈ v '' {g | (c q)⁻¹ * g ∈ K}, ‖MvPolynomial.eval z P' - 1‖ ≤ ε) ∧
      (∀ z ∈ v '' {g | (c q)⁻¹ * g ∉ K}, ‖MvPolynomial.eval z P'‖ ≤ ε) := by
    intro q
    have hc1 : IsCompact (v '' {g | (c q)⁻¹ * g ∈ K}) :=
      (hKc.preimage (continuous_const.mul continuous_id)).isCompact.image hv
    have hc2 : IsCompact (v '' {g | (c q)⁻¹ * g ∉ K}) :=
      (hKo.isClosed_compl.preimage (continuous_const.mul continuous_id)).isCompact.image hv
    have hd : Disjoint (v '' {g | (c q)⁻¹ * g ∈ K}) (v '' {g | (c q)⁻¹ * g ∉ K}) := by
      rw [Set.disjoint_left]
      rintro z ⟨g, hg, rfl⟩ ⟨g', hg', hgg⟩
      apply hg'
      have hm := K.mul_mem hg (hinj g g' hgg.symm)
      simpa [mul_assoc] using hm
    exact hS (Qbar l) (Fin a × Fin a) _ _ hc1 hc2 hd ε hε
  choose P' hP1 hP2 using hsep
  refine ⟨Γ ⧸ K, inferInstance, c, fun q => MvPolynomial.map ι.toRingHom (P' q), ?_⟩
  intro g
  have hmem : ∀ q : Γ ⧸ K, (c q)⁻¹ * g ∈ K ↔ q = (g : Γ ⧸ K) := by
    intro q
    rw [← QuotientGroup.eq]
    simp [c]
  have h0 : (c (g : Γ ⧸ K))⁻¹ * g ∈ K := (hmem _).2 rfl
  refine ⟨(g : Γ ⧸ K), (Subgroup.mem_inf.mp h0).2, (hH _).1 (Subgroup.mem_inf.mp h0).1, ?_, ?_⟩
  · beta_reduce
    rw [map_sub, map_one, pev_map]
    exact hP1 _ _ ⟨g, h0, rfl⟩
  · intro q hq
    beta_reduce
    rw [pev_map]
    exact hP2 q _ ⟨g, fun h => hq ((hmem q).1 h), rfl⟩

end UpperTheory.Gal.Wt

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.SumRep
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.sumRep_of :
    UpperTheory.Gal.Wt.SumRep := by
  intro E _ _ _ a S hfin hS
  classical
  obtain ⟨B₀, -, -, hd, hi⟩ := _root_.GlobalTheory.DefU.Petersson.exists_invariant_pos_form E a
  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective (autU E a).subtype (autU E a).ker_subtype
  have hpv : ∀ (φ : UA E a → ℂ) (h : IsAutFormU φ), p φ = ⟨φ, h⟩ := fun φ h =>
    LinearMap.congr_fun hp (⟨φ, h⟩ : autU E a)
  let B : (UA E a → ℂ) →ₗ⋆[ℂ] (UA E a → ℂ) →ₗ[ℂ] ℂ := (B₀.compl₂ p).comp p
  have hB : ∀ φ φ', B φ φ' = B₀ (p φ) (p φ') := fun _ _ => rfl
  have hsum : ∀ φ : UA E a → ℂ, IsAutFormU φ → φ ∈ sSup {U : Submodule ℂ (UA E a → ℂ) | IsAutRepU U} := by
    intro φ hφ
    have h := UpperTheory.mem_iSup_automorphicReps_of_invariant_form E a B (fun f hf h0 => by
        rw [hB, hpv f hf] at h0
        exact congrArg Subtype.val (hd _ h0))
      (fun x f g hf hg => by
        rw [hB, hB, hpv f hf, hpv g hg, hpv _ (RU_mem_autU x f hf), hpv _ (RU_mem_autU x g hg)]
        exact hi x ⟨f, hf⟩ ⟨g, hg⟩) φ hφ
    exact (iSup_le fun σ => le_sSup σ.2 : _ ≤ sSup {U : Submodule ℂ (UA E a → ℂ) | IsAutRepU U}) h
  let b := Module.finBasis ℂ S
  have hex : ∀ i, ∃ s : Finset (Submodule ℂ (UA E a → ℂ)), (↑s ⊆ {U : Submodule ℂ (UA E a → ℂ) | IsAutRepU U}) ∧
      (b i : UA E a → ℂ) ∈ ⨆ U ∈ s, U :=
    fun i => Submodule.mem_sSup_iff_exists_finset.1 (hsum _ (hS _ (b i).2))
  choose s hsA hsm using hex
  let s0 := Finset.univ.biUnion s
  have hs0A : ∀ U ∈ s0, IsAutRepU U := by
    intro U hU
    obtain ⟨i, -, hi'⟩ := Finset.mem_biUnion.1 hU
    exact hsA i hi'
  obtain ⟨t, hts, hti, htS⟩ := GlobalTheory.EigenDecomp.exists_indep s0 hs0A
  refine ⟨t, fun U hU => hs0A U (hts hU), hti, ?_⟩
  intro φ hφ
  rw [htS]
  have e : φ = ∑ i, (b.repr ⟨φ, hφ⟩ i) • (b i : UA E a → ℂ) := by
    have h := congrArg Subtype.val (b.sum_repr ⟨φ, hφ⟩)
    rw [Submodule.coe_sum] at h
    exact h.symm
  rw [e]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  refine (iSup₂_le fun U hU => le_sSup ?_ : (⨆ U ∈ s i, U) ≤ sSup (s0 : Set (Submodule ℂ (UA E a → ℂ)))) (hsm i)
  exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hU⟩)
end

