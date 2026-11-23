module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractOf
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0201
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1475
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0242

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PDgFacts
section
noncomputable section

open Formalism.MainNotions.N Polynomial
open Formalism.MainNotions.SumRepresentations.At (sumRep)

namespace UpperTheory.Gal.TP.Sub

section

variable {Γ k : Type} [Group Γ] [Field k]

private theorem dg_val {t : ℕ} (a : Fin t → Γ →* kˣ) (g : Γ) :
    ((dg a g : GL (Fin t) k) : Matrix (Fin t) (Fin t) k) = Matrix.diagonal fun i => (a i g : k) := rfl

private theorem ss_dg_one (b : Fin 1 → Γ →* kˣ) : IsSSRep (dg b) := by
  have key : ∀ (W : Submodule k (Fin 1 → k)), IsInv (dg b) W := by
    intro W g v hv
    have : ((dg b g : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k).mulVec v = ((b 0 g : kˣ) : k) • v := by
      ext i
      fin_cases i
      simp [dg_val, Matrix.mulVec_diagonal]
    rw [this]
    exact W.smul_mem _ hv
  intro W _
  obtain ⟨W', hW'⟩ := exists_isCompl W
  exact ⟨W', key W', hW'⟩

private theorem dg_succ {t : ℕ} (a : Fin (t + 1) → Γ →* kˣ) :
    dg a = sumRep (dg fun i : Fin t => a i.castSucc) (dg fun _ : Fin 1 => a (Fin.last t)) := by
  ext g : 1
  apply Units.ext
  rw [GlobalTheory.BCGal.sumRep_val, dg_val, dg_val, dg_val]
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.diagonal_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  · rfl
  · intro h
    have h' := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at h'
    omega
  · intro h
    have h' := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at h'
    omega
  · obtain rfl : i = 0 := Subsingleton.elim _ _
    obtain rfl : j = 0 := Subsingleton.elim _ _
    rfl

private theorem ss_dg {t : ℕ} (a : Fin t → Γ →* kˣ) : IsSSRep (dg a) := by
  induction t with
  | zero => exact GlobalTheory.BCGal.ss_zero _
  | succ t ih =>
    rw [dg_succ]
    exact GlobalTheory.BCGal.ss_sumRep _ _ (ih _) (ss_dg_one _)

end

theorem dgFacts_holds : DgFacts := by
  intro Γ k _ _ t a
  refine ⟨ss_dg a, fun g => ?_⟩
  show ((dg a g : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).charpoly = _
  rw [dg_val, Matrix.charpoly_diagonal]

end UpperTheory.Gal.TP.Sub

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PEigSum
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

private theorem dg_mulVec {Γ k : Type} [Group Γ] [Field k] {t : ℕ} (a : Fin t → Γ →* kˣ) (g : Γ)
    (u : Fin t → k) (i : Fin t) :
    ((dg a g : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec u i = (a i g : k) * u i := by
  simp [dg, Matrix.mulVec_diagonal]

theorem UpperTheory.Gal.TP.Sub.eigSum_holds :
    EigSum := by
  intro Γ k _ _ m t r a c
  refine ⟨?_, ?_⟩
  · rintro ⟨i, hi⟩
    let e : Fin t → k := Pi.single i 1
    let w : Fin (m + t) → k := fun x => (finSumFinEquiv.symm x).elim (fun _ => 0) e
    have hwl : w ∘ ⇑finSumFinEquiv ∘ Sum.inl = 0 := by
      funext y
      simp [w]
    have hwr : w ∘ ⇑finSumFinEquiv ∘ Sum.inr = e := by
      funext y
      simp [w]
    refine ⟨w, ?_, ?_⟩
    · intro h
      have := congrFun hwr i
      rw [h] at this
      simp [e] at this
    · intro g
      funext x
      obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective x
      rcases y with y | y
      · rw [GlobalTheory.EigTwist.sumRep_mulVec_inl, hwl, Matrix.mulVec_zero, Pi.smul_apply]
        have := congrFun hwl y
        simp only [Function.comp_apply] at this
        rw [this]
        simp
      · rw [GlobalTheory.EigTwist.sumRep_mulVec_inr, hwr, dg_mulVec]
        have := congrFun hwr y
        simp only [Function.comp_apply] at this
        rw [Pi.smul_apply, this, smul_eq_mul]
        by_cases hy : y = i
        · subst hy
          rw [hi]
        · simp [e, Pi.single_apply, hy]
  · intro hne hex
    obtain ⟨w, hw0, hw⟩ := hex
    rcases GlobalTheory.EigTwist.eigen_pair c r (dg a) w hw0 hw with h | ⟨v, hv0, hv⟩
    · exact h
    · exfalso
      obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact hv0 (funext hcon)
      apply hne j
      ext g
      have := congrFun (hv g) j
      rw [dg_mulVec, Pi.smul_apply, smul_eq_mul] at this
      exact mul_right_cancel₀ hj this
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PEigTransfer
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.eigTransfer_holds :
    EigTransfer := by
  intro Γ k _ _ _ _ N N' ρ ρ' hρ hρ' hcp c ⟨v, hv0, hv⟩
  have hN : N = N' := by
    have h := congrArg Polynomial.natDegree (hcp 1)
    simpa [cp, Matrix.charpoly_natDegree_eq_dim] using h
  subst hN
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix ρ ρ' hρ hρ' (fun g => hcp g)
  refine ⟨(P : Matrix (Fin N) (Fin N) k).mulVec v, ?_, ?_⟩
  · intro h
    apply hv0
    have := congrArg (((P⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).mulVec) h
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec,
      Matrix.mulVec_zero] at this
    exact this
  · intro g
    have hg : ρ g * P = P * ρ' g := by
      rw [hP g]
      group
    have hm : (ρ g : Matrix (Fin N) (Fin N) k) * P = P * ρ' g := by
      rw [← Units.val_mul, hg, Units.val_mul]
    rw [Matrix.mulVec_mulVec, hm, ← Matrix.mulVec_mulVec, hv g, Matrix.mulVec_smul]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PFrobSub
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

namespace UpperTheory.Gal.TP.Sub.PFrobSub

private theorem prod_scale {K : Type} [Field K] {c : K} (hc : c ≠ 0) (x : K) (S : Multiset K) :
    c ^ Multiset.card S * (S.map fun z => x / c - z).prod = (S.map fun z => x - z * c).prod := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih =>
    have e : c * (x / c - a) = x - a * c := by
      field_simp
    rw [Multiset.card_cons, Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons, ← ih, ← e]
    ring

private theorem charpoly_smul_eq {K : Type} [Field K] [Infinite K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) {c : K}
    (hc : c ≠ 0) (S : Multiset K) (h : M.charpoly = (S.map fun z => X - C z).prod) :
    (c • M).charpoly = (S.map fun z => X - C (z * c)).prod := by
  apply Polynomial.funext
  intro x
  have hn : Multiset.card S = n := by
    have := congrArg Polynomial.natDegree h
    rw [Matrix.charpoly_natDegree_eq_dim, Polynomial.natDegree_multiset_prod_X_sub_C_eq_card] at this
    simpa using this.symm
  have key : Matrix.scalar (Fin n) x - c • M = c • (Matrix.scalar (Fin n) (x / c) - M) := by
    rw [smul_sub]
    congr 1
    ext i j
    simp [Matrix.diagonal_apply]
    split_ifs <;> field_simp
  rw [Matrix.eval_charpoly, key, Matrix.det_smul, ← Matrix.eval_charpoly, h, Fintype.card_fin, ← hn,
    Polynomial.eval_multiset_prod, Polynomial.eval_multiset_prod, Multiset.map_map, Multiset.map_map]
  simp only [Function.comp_def, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  exact prod_scale hc x S

private theorem sumRep_left {Γ k : Type} [Group Γ] [Field k] {a b : ℕ} (r : Γ →* GL (Fin a) k) (s : Γ →* GL (Fin b) k)
    (g : Γ) (i j : Fin a) :
    (sumRep r s g : Matrix (Fin (a + b)) (Fin (a + b)) k) (Fin.castAdd b i) (Fin.castAdd b j) =
      (r g : Matrix (Fin a) (Fin a) k) i j := by
  simp [sumRep, Formalism.MainNotions.SumRepresentations.At.blkHom]
  rfl

private theorem characterAsRankOneRep_entry {Γ k : Type} [Group Γ] [Field k] (μ : Γ →* kˣ) (g : Γ) :
    (rk1 μ g : Matrix (Fin 1) (Fin 1) k) 0 0 = (μ g : k) := by
  unfold rk1
  simp

end UpperTheory.Gal.TP.Sub.PFrobSub

open UpperTheory.Gal.TP.Sub.PFrobSub in
theorem UpperTheory.Gal.TP.Sub.frobSub_holds :
    CpFacts → FrobSub := by
  intro h E Ω _ _ _ _ _ l _ ι a w S c μ hμ
  have hc : ∀ A, IsPlaceOver A w → ∀ σ : G E Ω, IsFrob A (normV w) σ →
      ι.toRingHom (μ σ⁻¹ : Qbar l) = c := by
    intro A hA σ hσ
    have h1 := (hμ A hA).2 σ hσ
    have h2 := (h (G E Ω) (Qbar l) 1 1).2.1 μ σ⁻¹
    unfold cp at h2
    rw [h2] at h1
    simpa using h1
  refine ⟨fun s hs => ?_, fun s hs => ?_⟩
  · intro A hA
    obtain ⟨hI, hF⟩ := hs A hA
    refine ⟨fun σ hσ => ?_, fun σ hσ => ?_⟩
    · have e := hI σ hσ
      ext i j
      have hij := sumRep_left s (rk1 μ) σ i j
      rw [e] at hij
      rw [← hij]
      simp [Matrix.one_apply]
    · have e := hF σ hσ
      have h3 := (h (G E Ω) (Qbar l) a 1).1 s (rk1 μ) σ⁻¹
      have h4 := (h (G E Ω) (Qbar l) 1 1).2.1 μ σ⁻¹
      unfold cp at h3 h4
      rw [h3, Polynomial.map_mul, h4] at e
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] at e
      rw [hc A hA σ hσ, Multiset.map_add (f := _), Multiset.prod_add, Multiset.map_singleton,
        Multiset.prod_singleton] at e
      exact mul_right_cancel₀ (Polynomial.X_sub_C_ne_zero c) e
  · intro A hA
    obtain ⟨hI, hF⟩ := hs A hA
    obtain ⟨hIμ, -⟩ := hμ A hA
    refine ⟨fun σ hσ => ?_, fun σ hσ => ?_⟩
    · have e1 := hI σ hσ
      have e2 : (μ σ : Qbar l) = 1 := by
        rw [← characterAsRankOneRep_entry μ σ, hIμ σ hσ]
        simp
      ext i j
      rw [UpperTheory.V.Af.tw_val, e1, e2]
      simp
    · have e := hF σ hσ
      have hc' := hc A hA σ hσ
      have hc0 : c ≠ 0 := by
        rw [← hc']
        simp
      rw [UpperTheory.V.Af.tw_val, ← Matrix.charpoly_map]
      rw [← Matrix.charpoly_map] at e
      have hm : ((μ σ⁻¹ : Qbar l) • (s σ⁻¹ : Matrix (Fin a) (Fin a) (Qbar l))).map ι.toRingHom =
          c • (s σ⁻¹ : Matrix (Fin a) (Fin a) (Qbar l)).map ι.toRingHom := by
        rw [← hc']
        ext i j
        simp
      rw [hm, Multiset.map_map]
      exact charpoly_smul_eq _ hc0 S e
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PPeelAll
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

private theorem univ_map_snoc {α : Type*} {t : ℕ} (f : Fin (t + 1) → α) :
    Finset.univ.val.map f =
      Finset.univ.val.map (fun i : Fin t => f i.castSucc) + {f (Fin.last t)} := by
  rw [Fin.univ_castSuccEmb]
  simp [Finset.map_val, Multiset.map_map, add_comm, Function.comp_def]

theorem UpperTheory.Gal.TP.Sub.peelAll_holds :
    PeelOne → ContLeft → ClConj → ClSub → PeelAll := by
  intro hP hC hJ hS E Ω _ _ _ _ _ l _ ι n m' t' r' a' hr' t
  induction t with
  | zero =>
    intro r a hc hss _ _ _
    refine ⟨r, hc, hss, ?_⟩
    intro w S c J m _ h
    simpa using h
  | succ t ih =>
    intro r a hc hss ha hne hid
    obtain ⟨s₁, hs₁, hiso, hid₁⟩ :=
      hP (G E Ω) (Qbar l) (n + t) m' t t' r r' a a' hss hr' hne hid
    have hC' := hC (G E Ω) (Qbar l) (n + t) 1
    have hC1 := hC (G E Ω) (Qbar l) (n + t + 1) 1
    have hcl : Continuous (sumRep s₁ (rk1 (a (Fin.last t)))) := hC1.2.1 _ _ hiso hc
    have hcs₁ : Continuous s₁ := hC'.1 _ _ hcl
    obtain ⟨s, hsc, hss', hcl'⟩ := ih s₁ (fun i => a i.castSucc) hcs₁ hs₁
      (fun i => ha _) (fun i j => hne _ _) hid₁
    refine ⟨s, hsc, hss', ?_⟩
    intro w S c J m hcl0 h
    have h2 := hJ E Ω l ι _ r _ hc hiso w _ _ h
    refine hcl' w S (fun i => c i.castSucc) J (fun i => m i.castSucc) (fun i => hcl0 _) ?_
    refine hS E Ω l ι _ s₁ (a (Fin.last t)) hcs₁ (ha _) w _ (c (Fin.last t)) _
      (m (Fin.last t)) (hcl0 _) ?_
    have e1 : S + Finset.univ.val.map c =
        S + Finset.univ.val.map (fun i : Fin t => c i.castSucc) + {c (Fin.last t)} := by
      rw [univ_map_snoc c, add_assoc]
    have e2 : (fun τ => J τ + Finset.univ.val.map fun i => m i τ) =
        fun τ => J τ + Finset.univ.val.map (fun i : Fin t => m i.castSucc τ) +
          {m (Fin.last t) τ} := by
      funext τ
      rw [univ_map_snoc (fun i => m i τ), add_assoc]
    rw [e1, e2] at h2
    exact h2
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PPeelOne
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.peelOne_holds :
    DgFacts → CpFacts → EigTransfer → EigSum → SplitLine → SSLeft → PeelOne := by
  intro hDg hCp hTr hEig hSplit hSS Γ k _ _ _ _ m m' t t' r r' a a' hr hr' hne hcp
  set c := a (Fin.last t) with hc
  have hR1 : IsSSRep (sumRep r (dg a')) := GlobalTheory.BCGal.ss_sumRep _ _ hr (hDg Γ k t' a').1
  have hR2 : IsSSRep (sumRep r' (dg a)) := GlobalTheory.BCGal.ss_sumRep _ _ hr' (hDg Γ k (t + 1) a).1
  have hcpR : ∀ g, cp (sumRep r (dg a')) g = cp (sumRep r' (dg a)) g := by
    intro g
    rw [(hCp Γ k (m + 1) t').1, (hCp Γ k m' (t + 1)).1, (hDg Γ k t' a').2, (hDg Γ k (t + 1) a).2]
    exact hcp g
  have hv2 := (hEig Γ k m' (t + 1) r' a c).1 ⟨Fin.last t, rfl⟩
  have hv1 := hTr Γ k _ _ (sumRep r (dg a')) (sumRep r' (dg a)) hR1 hR2 hcpR c hv2
  have hv := (hEig Γ k (m + 1) t' r a' c).2 (fun j h => hne (Fin.last t) j h.symm) hv1
  obtain ⟨s, hs⟩ := hSplit Γ k m r hr c hv
  have hsum : IsSSRep (sumRep s (rk1 c)) := (hSS Γ k (m + 1) 0).2.1 r _ hs hr
  refine ⟨s, (hSS Γ k m 1).1 s (rk1 c) hsum, hs, ?_⟩
  intro g
  have h1 : cp r g = cp s g * (X - C ((c g : kˣ) : k)) := by
    rw [← (hCp Γ k (m + 1) 0).2.2 r _ hs g, (hCp Γ k m 1).1, (hCp Γ k m 1).2.1]
  have h2 : lin a g = lin (fun i => a i.castSucc) g * (X - C ((c g : kˣ) : k)) := by
    simp only [lin]
    rw [Fin.prod_univ_castSucc]
  have hX : (X - C ((c g : kˣ) : k) : k[X]) ≠ 0 := Polynomial.X_sub_C_ne_zero _
  have key := hcp g
  rw [h1, h2] at key
  apply mul_right_cancel₀ hX
  calc cp s g * lin a' g * (X - C ((c g : kˣ) : k))
      = cp s g * (X - C ((c g : kˣ) : k)) * lin a' g := by ring
    _ = cp r' g * (lin (fun i => a i.castSucc) g * (X - C ((c g : kˣ) : k))) := key
    _ = cp r' g * lin (fun i => a i.castSucc) g * (X - C ((c g : kˣ) : k)) := by ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PSatAE
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub
open GlobalTheory.PRep Formalism.UG GlobalTheory.BCT

theorem UpperTheory.Gal.TP.Sub.satAE_holds :
    SatAE := by
  intro E _ _ _ a U hU
  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU.ne_bot
  let L : Subgroup (finU (E := E) (n := a)) :=
    { carrier := {k | RU E a k φ = φ}
      one_mem' := by simp
      mul_mem' := by
        intro x y hx hy
        simp only [Set.mem_setOf_eq] at *
        rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hy, hx]
      inv_mem' := by
        intro x hx
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hLo : IsOpen (L : Set (finU (E := E) (n := a))) := (hU.aut φ hφ).level
  filter_upwards [GlobalTheory.T.eventually_localIntegralPoints_mem_openSubgroup_definiteUnitary E a L hLo] with w hw hs
  obtain ⟨hJo, hJc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a
  obtain ⟨σ, hσ, v, hv0, hv⟩ := GlobalTheory.T.exists_localComponent_eigenvector_splitPlace E a U hU w hs (GlobalTheory.LFun.KGL w (n := a)) hJo hJc 1 φ hφ hφ0
    (fun x hx hxK => by
      have h : RU E a x φ = φ := hw x hx hxK hx.1
      simpa using h)
  have hsph : GlobalTheory.LGrp.IsSpherical σ.ρ (GlobalTheory.LFun.KGL w (n := a)) :=
    (Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.LGrp.mem_fixed.2 fun k hk => by simpa using hv ⟨k, hk⟩, hv0⟩
  obtain ⟨B, hB⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible σ.smooth σ.irred hsph
  exact ⟨B, σ, hσ, hB⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PSatPol
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

private theorem satPol_val (q a : ℕ) (b : ℂˣ) (m : ℤ) :
    ((((q : ℝ) ^ (((a : ℝ) - 1) / 2) : ℝ) : ℂ) * (b : ℂ)) ^ (-m) =
      ((q : ℂ) ^ ((((1 : ℝ) - a) / 2 : ℝ) : ℂ)) ^ m * ((b : ℂ)⁻¹) ^ m := by
  have hx : ((((q : ℝ) ^ (((a : ℝ) - 1) / 2) : ℝ) : ℂ))⁻¹ = (q : ℂ) ^ ((((1 : ℝ) - a) / 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg q), Complex.ofReal_natCast, ← Complex.cpow_neg]
    congr 1
    push_cast
    ring
  rw [zpow_neg, ← inv_zpow, mul_inv, ← hx, mul_zpow]

theorem UpperTheory.Gal.TP.Sub.satPol_holds :
    SatPol := by
  intro E Ω _ _ _ _ _ A w h a B g
  rw [GlobalTheory.SatChar.charPol_satWD]
  unfold unrPol algSat
  simp only [bind, pure, Multiset.bind_singleton, Multiset.map_map, Function.comp_def]
  congr 1
  refine Multiset.map_congr rfl fun b _ => ?_
  rw [satPol_val]
end

