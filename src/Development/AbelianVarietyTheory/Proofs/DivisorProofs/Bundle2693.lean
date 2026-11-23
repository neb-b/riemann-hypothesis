module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0980
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2650
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTerms
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1188
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2653
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0627
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionTowerRecognition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2542
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2151
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2584
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2247
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1147
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2652
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2607
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1163
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1011
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2660
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1239
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramedTorsionPointTorusExtensionEqOfLiesOver
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

open GlobalTheory.Poinc.Tors

noncomputable section

namespace GlobalTheory.Poinc.Sep.LiesUniq

theorem frame_unique {R : Type} [CommRing R] [IsDomain R] [CharZero R] {I : Ideal R} (hA : AdmBase R I)
    {D : DegData R I} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (hG : IsSemiAbelian G) (U : Unif I D A G) {w₀ : W0 U.toUnifPre} (hw₀ : w₀.IsGen) {F : Type} [Field F]
    [Algebra (FractionRing R) F] {g : GtPtF D.toPre F} {w w' : Frm D.toPre F 1 g.b} {x : TFK (R := R) F ⟶ A.A}
    {fr : FrAt x} (hw : w.IsGen) (hw' : w'.IsGen) (hfr : fr.IsGen) (h : LiesOver U.toUnifPre w₀ g w x fr)
    (h' : LiesOver U.toUnifPre w₀ g w' x fr) :
    ∀ z J, Good D.toPre.P.L z J → val w (𝟙 _) z J = val w' (𝟙 _) z J := by
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  have hbij := (expBijF_and_expandsF_lin hL R _ hA D A G hG U).1 F
  obtain ⟨lam, -, hlam⟩ := CoefBasic.exists_frame_ratio hw hw'
  have hk : ∀ k : ℕ, 4 ≤ k → lam ^ k = 1 := fun k hk => by
    obtain ⟨W, hW, hWv⟩ := TorsionValue.exists_frm_pow w hw k
    obtain ⟨W', hW', hWv'⟩ := TorsionValue.exists_frm_pow w' hw' k
    obtain ⟨s, e, he, hs⟩ := NonVan.exists_sec_ne_zero hL R A F k hk x fr hfr
    obtain ⟨s', hs', -⟩ := (hbij k (by omega) w₀ hw₀).1 s
    have S₁ := h k (by omega) W hWv hW s s' e hs' hs
    have S₂ := h' k (by omega) W' hWv' hW' s s' e hs' hs
    have sc := TorsionValue.coef_scale (w' := W') hW (c := lam ^ k) (fun z J hJ => by
      rw [hWv z J hJ, hWv' z J hJ, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hlam z J hJ, mul_pow,
        CoefBasic.cst_eq, CoefBasic.cst_eq, map_pow]) s'
    have S₃ := (GlobalTheory.AdicSum.sumF_calculus R I hA F _ _ _ e e).2.1 S₁ S₁ (lam ^ k - 1)
    have e₁ : (fun i => (lam ^ k - 1) * coef s' g W i + coef s' g W i) = coef s' g W' := funext fun i => by
      rw [sc]; ring
    rw [e₁] at S₃
    have e₂ := (GlobalTheory.AdicSum.sumF_calculus R I hA F _ _ (coef s' g W') _ _).1 S₃ S₂
    exact sub_eq_zero.1 ((mul_eq_zero.1 (add_eq_right.1 e₂)).resolve_right he)
  have h1 : lam = 1 := by
    have := hk 5 (by norm_num)
    rwa [pow_succ, hk 4 le_rfl, _root_.one_mul] at this
  intro z J hJ
  have := hlam z J hJ
  rw [h1, CoefBasic.cst_eq, map_one, _root_.one_mul] at this
  exact Units.ext this.symm

theorem eq_of_liesOver : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G) (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ N : ℕ, 1 ≤ N → ∀ (g g' : GtPtF D.toPre (FractionRing V)) (w : Frm D.toPre (FractionRing V) 1 g.b) (w' : Frm D.toPre (FractionRing V) 1 g'.b) (x : TFK (R := V) (FractionRing V) ⟶ A.A) (fr : FrAt x), (∃ o, GtPtF.IsNsmul N g o ∧ o.IsZero) → (∃ o, GtPtF.IsNsmul N g' o ∧ o.IsZero) → w.IsGen → w'.IsGen → fr.IsGen → LiesOver U.toUnifPre w₀ g w x fr → LiesOver U.toUnifPre w₀ g' w' x fr → g = g' ∧ ∀ z J, Good D.toPre.P.L z J → val w (𝟙 _) z J = val w' (𝟙 _) z J := by
  intro V _ _ _ hCN D A G _ _ hG U w₀ hw₀ N hN g g' w w' x fr hg hg' hw hw' hfr h h'
  haveI : CharZero V := hCN.2.2.2
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws
  have hA : AdmBase V (maximalIdeal V) := ⟨hCN.1, inferInstance, hCN.2.1, hCN.2.2.1⟩
  have hB := D.tau_bimult
  obtain ⟨p, hy, rfl, hp⟩ := GlobalTheory.T.exists_torus_pair_of_torsion_point_over V hCN D A G hG U w₀ hw₀ N hN g w x fr hg hw hfr h
  obtain ⟨p', hy', rfl, hp'⟩ := GlobalTheory.T.exists_torus_pair_of_torsion_point_over V hCN D A G hG U w₀ hw₀ N hN g' w' x fr hg' hw' hfr h'
  have hf : (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp
      (algebraMap (FractionRing V) (FractionRing V)) = algebraMap _ _ := RingHom.comp_id _
  have hq := (GlobalTheory.TorsionExt.qkToAkU_iff_of_algebra hL.1.globalFns hL.1.kerPow U hN
    ((GlobalTheory.TorusExt.qkExt_iff hB _ hf p _).2 rfl) x).1 hp
  have hq' := (GlobalTheory.TorsionExt.qkToAkU_iff_of_algebra hL.1.globalFns hL.1.kerPow U hN
    ((GlobalTheory.TorusExt.qkExt_iff hB _ hf p' _).2 rfl) x).1 hp'
  have he := GlobalTheory.TorsionMapInj.qkToAk_injective hL.1 hL.2.1 V _ hA D A G hG U _ N hN _ _ _ hq hq'
  obtain ⟨z, hz, hz'⟩ := (GlobalTheory.TorusExt.equiv_iff hB _ _).1 he
  have e : p.g = p'.g := by
    letI := GlobalTheory.TorusExt.gtGroup D.toPre (AlgebraicClosure (FractionRing V))
    have hz₁ : p'.y = p.y + N • z := hz
    rw [hy, hy', zero_add, ← natCast_zsmul] at hz₁
    obtain rfl : z = 0 := (smul_eq_zero.1 hz₁.symm).resolve_left (by exact_mod_cast (by omega : N ≠ 0))
    rw [map_zero, add_zero] at hz'
    exact GlobalTheory.Balanced.gtExt_injective _ hf D.toPre hz'.symm
  obtain ⟨y, g, hg₁⟩ := p
  obtain ⟨y', g', hg₁'⟩ := p'
  dsimp only at e
  subst e
  exact ⟨rfl, frame_unique hA hG U hw₀ hw hw' hfr h h'⟩

end GlobalTheory.Poinc.Sep.LiesUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFlagBundlePushForwardFormula
section
noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory.FlagPushProof

theorem flagPushForward : GlobalTheory.Published.FlagPushForward := by
  intro F _ _ X Y ι _ m E E' φ f gr hf hg Q R hR
  have hswap := _root_.GlobalTheory.FlagPush.interPoly_swap_adjacent F X Y ι m E E' φ f hf gr hg
  refine _root_.GlobalTheory.FlagPush.linForm_eq_of_antisymm_eq ι m (Y.interPoly gr) hswap Q (chernRoots m R * fibrePoint m) ?_
  classical
  have rename_chernRoots (ι : Type) [Fintype ι] (m : ι → ℕ) (w : ∀ τ, Equiv.Perm (Fin (m τ)))
      (R : MvPolynomial (ι × ℕ) ℝ) :
      rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) (chernRoots m R) = chernRoots m R := by
    have h : (rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m))).comp (chernRoots m) = chernRoots m := by
      apply MvPolynomial.algHom_ext
      intro x
      simp only [AlgHom.comp_apply, chernRoots, aeval_X, rename_rename]
      have e : ((fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) ∘ Sigma.mk x.1) = Sigma.mk x.1 ∘ (w x.1) := by
        funext i; rfl
      rw [e, ← rename_rename, rename_esymm]
    exact AlgHom.congr_fun h R

  have antisymm_chernRoots_mul (ι : Type) [Fintype ι] (m : ι → ℕ) (R : MvPolynomial (ι × ℕ) ℝ)
      (Q : MvPolynomial (Root m) ℝ) : antisymm (chernRoots m R * Q) = chernRoots m R * antisymm Q := by
    unfold GlobalTheory.GoodMetric.antisymm
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [map_mul, rename_chernRoots, mul_smul_comm]

  have prod_Ioi_rev {R : Type} [CommRing R] {N : ℕ} (v : Fin N → R) :
      (∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (v (Fin.rev i) - v (Fin.rev j))) = ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (v j - v i) := by
    have h : ∀ f : Fin N → Fin N → R, (∏ i : Fin N, ∏ j ∈ Finset.Ioi i, f i j) =
        ∏ i : Fin N, ∏ j : Fin N, if i < j then f i j else 1 := by
      intro f
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← Finset.prod_filter]
      congr 1
      ext j; simp
    rw [h, h, ← Fintype.prod_prod_type' (f := fun i j => if i < j then v (Fin.rev i) - v (Fin.rev j) else 1),
      ← Fintype.prod_prod_type' (f := fun i j => if i < j then v j - v i else 1)]
    refine Fintype.prod_equiv ((Equiv.prodComm _ _).trans (Fin.revPerm.prodCongr Fin.revPerm)) _ _ fun p => ?_
    simp [Fin.rev_lt_rev]

  have sum_sign_prod_neg_pow {R : Type} [CommRing R] {N : ℕ} (v : Fin N → R) :
      (∑ σ : Equiv.Perm (Fin N), (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : R) * ∏ i : Fin N, (-v (σ i)) ^ (N - 1 - (i : ℕ))) =
        ∏ j : Fin N, ∏ i ∈ Finset.Iio j, (v j - v i) := by
    let M : Matrix (Fin N) (Fin N) R := Matrix.of fun j i => (-v j) ^ (N - 1 - (i : ℕ))
    have h1 : M.det = ∑ σ : Equiv.Perm (Fin N), (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : R) * ∏ i : Fin N, (-v (σ i)) ^ (N - 1 - (i : ℕ)) := by
      rw [Matrix.det_apply']
      rfl
    have h2 : M.submatrix Fin.revPerm Fin.revPerm = Matrix.vandermonde (fun j => -v (Fin.rev j)) := by
      ext j i
      simp only [M, Matrix.submatrix_apply, Matrix.of_apply, Matrix.vandermonde_apply, Fin.revPerm_apply, Fin.val_rev]
      congr 1
      omega
    rw [← h1, ← Matrix.det_submatrix_equiv_self Fin.revPerm, h2, Matrix.det_vandermonde,
      GlobalTheory.GoodMetric.RootDiscrPerm.prod_Iio_eq_det, Matrix.det_vandermonde]
    simp only [neg_sub_neg]
    rw [prod_Ioi_rev]

  have antisymm_fibrePoint (ι : Type) [Fintype ι] (m : ι → ℕ) : antisymm (fibrePoint m) = rootDiscr m := by
    have hw : ∀ w : ∀ τ, Equiv.Perm (Fin (m τ)),
        ((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) • rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) (fibrePoint m) =
          ∏ τ, ((((Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) : MvPolynomial (Root m) ℝ) *
            ∏ i : Fin (m τ), (-(MvPolynomial.X (⟨τ, w τ i⟩ : Root m) : MvPolynomial (Root m) ℝ)) ^ (m τ - 1 - (i : ℕ))) := by
      intro w
      unfold fibrePoint
      rw [map_prod, Fintype.prod_sigma, zsmul_eq_mul, Units.coe_prod, Int.cast_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun τ _ => ?_
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      simp [map_pow, map_neg, rename_X]
    unfold GlobalTheory.GoodMetric.antisymm
    rw [Finset.sum_congr rfl fun w _ => hw w]
    rw [← Fintype.prod_sum (fun τ (σ : Equiv.Perm (Fin (m τ))) => ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : MvPolynomial (Root m) ℝ) *
            ∏ i : Fin (m τ), (-(MvPolynomial.X (⟨τ, σ i⟩ : Root m) : MvPolynomial (Root m) ℝ)) ^ (m τ - 1 - (i : ℕ))))]
    unfold rootDiscr
    refine Finset.prod_congr rfl fun τ _ => ?_
    exact sum_sign_prod_neg_pow (fun i : Fin (m τ) => (MvPolynomial.X (⟨τ, i⟩ : Root m) : MvPolynomial (Root m) ℝ))
  rw [hR, antisymm_chernRoots_mul ι m R, antisymm_fibrePoint ι m]

end GlobalTheory.FlagPushProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisEquivariantTorsionValuesUltrametric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.Recog

open GlobalTheory GlobalTheory.Ex GlobalTheory.TorusExt GlobalTheory.LabTrans GlobalTheory.SeriesCompare GlobalTheory.ArcPull

theorem recognition_core : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (lab : Labels D.toPre A), ∀ n : ℕ, n.Prime → Odd n → IsUnit (n : R) → OneTrait D.toPre A lab → GalEqN n lab → (∀ (j : ℕ) (v : QkPt D.toPre (Kb R) ((n ^ j) ^ 2) → Kb R), (∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [Algebra (FractionRing R) C], GlobalTheory.Ex.CExt R (maximalIdeal R) C → ∀ (em : Kb R →ₐ[FractionRing R] C) (N : GlobalTheory.Ex.NumD C) (nu : GlobalTheory.Ex.NumOf D.toPre C N) (p₁ : QkPt D.toPre (Kb R) ((n ^ j) ^ 2) → QkPt D.toPre C ((n ^ j) ^ 2)) (q : QkPt D.toPre (Kb R) ((n ^ j) ^ 2) → N.QT ((n ^ j) ^ 2)), (∀ i, QkExt em.toRingHom i (p₁ i)) → (∀ i, nu.QPt (p₁ i) (q i)) → ∃ s : Cˣ, ∀ i, em (v i) = s * N.tx (n ^ j) (q i)) → IsThetaPt A (n ^ j) (lab ((n ^ j) ^ 2)) (fun p => GlobalTheory.Ex.fnOf (v p))) → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R →+* W), Function.Injective φ → IsLocalHom φ → ∀ (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G'] (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W))) (U' : Unif (maximalIdeal W) D' A' G') (a : A'.A.left ⟶ A.A.left), IsSemiAbelian G' → IsFib φ A A' a → ∃ hD : IsPullDeg φ D.toPre D'.toPre, ∃ (C : Type) (_ : Field C) (_ : IsAlgClosed C) (_ : Algebra (FractionRing W) C) (_ : Algebra (FractionRing R) C) (em : Kb R →ₐ[FractionRing R] C), (∀ r, algebraMap (FractionRing R) C (algebraMap R _ r) = algebraMap (FractionRing W) C (algebraMap W _ (φ r))) ∧ ∀ j : ℕ, ∀ (p : QkPt D.toPre (Kb R) (n ^ j)) (p₁ : QkPt D.toPre C (n ^ j)) (p' : QkPt D'.toPre C (n ^ j)) (x' : TFK (R := W) C ⟶ A'.A), QkExt em.toRingHom p p₁ → p'.y = hD.xe.symm p₁.y → IsPullGtF φ hD C p₁.g p'.g → x'.left ≫ a = spMap em.toRingHom ≫ (lab (n ^ j) p).left → QkToAkU U'.toUnifPre C (n ^ j) p' x' := by
  intro R _ _ _ hR D A lab n hn ho hu hT hgal htheta W _ _ _ hW φ iφ lφ G' _ _ D' A' U' a hG' hfib
  have hV := GlobalTheory.lawsAndExpansions
  have hL : Laws := hV.1.1
  have hL₂ : Laws2 := hV.1.2.1
  have hGF := hL.globalFns
  have := hR.2
  have := hR.1.1
  have := hW.1
  have := hW.2.2
  have hB := D.tau_bimult
  have bW : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩

  obtain ⟨W₀, _, _, _, φ₀, G₀, _, _, D₀, A₀, U₀, h₀, a₀, _, em₀, hW₀, i₀, l₀, hG₀, fib₀, c₀, H₀⟩ := hT
  have := hW₀.1
  have := hW₀.2.2
  have b₀ : AdmBase W₀ (maximalIdeal W₀) := ⟨inferInstance, inferInstance, inferInstance, hW₀.2.1⟩
  obtain ⟨g₀, hg₀, hg₀'⟩ := exists_goodLab b₀ hG₀ U₀ (Kb W₀)
  have Glab : GoodLab D.toPre A (Kb R) lab := by
    refine (goodLab_move h₀ c₀ em₀ D₀.tau_bimult fib₀ lab g₀ fun k hk p => ?_).2 hg₀
    obtain ⟨ga₀, hga₀, gp₀, -⟩ := fib₀
    obtain ⟨x, hx⟩ := exists_lift_pt gp₀.1 em₀.toRingHom
      (em₀.comp_algebraMap.trans (IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => (c₀ r).trans
        (congrArg (algebraMap (FractionRing W₀) (Kb W₀)) (hga₀ r).symm)))) (lab k p)
    obtain ⟨p₁, t₁, t₂, t₃⟩ := (lies_iff h₀ c₀ em₀ D₀.tau_bimult p _).2 rfl
    rw [← (hg₀' k hk _ x).1 (H₀ k hk p p₁ _ x t₁ t₂ t₃ hx)]
    exact hx

  haveI := lφ
  obtain ⟨DW, ⟨hWp⟩⟩ := GlobalTheory.MumPull.exists_pull R W φ iφ lφ D
  have hBW := DW.tau_bimult
  obtain ⟨C, _, _, _, _, _, gam, hgam, hC⟩ := _root_.GlobalTheory.Ex.exists_complete_isAlgClosed_cExt W (Kb W)
  have : CharZero C := (RingHom.charZero_iff (algebraMap (FractionRing W) C).injective).1 inferInstance
  letI : Algebra (FractionRing R) C := ((algebraMap (FractionRing W) C).comp (fracMap iφ)).toAlgebra
  have cC : Compat φ C := fun r => congrArg (algebraMap (FractionRing W) C) (fracMap_algebraMap iφ r)
  obtain ⟨em⟩ := nonempty_lift (FractionRing R) C

  obtain ⟨ε, hε, -, -, -⟩ := exists_ptHom hfib cC em
  let fW : ∀ k, QkPt DW.toPre C k → (TFK (R := W) C ⟶ A'.A) := fun k q =>
    if hk : 1 ≤ k then ε (lab k ((Equiv.ofBijective _ (tr_bij hWp cC em hBW hk)).symm q)) else 1
  have hfW : ∀ k (hk : 1 ≤ k) p, fW k (tr hWp cC em hBW p) = ε (lab k p) := fun k hk p => by
    simp only [fW, dif_pos hk, Equiv.ofBijective_symm_apply_apply]
  have GW : GoodLab DW.toPre A' C fW := (goodLab_move hWp cC em hBW hfib lab fW fun k hk p => by
    rw [hfW k hk p]; exact (hε _ _).1 rfl).1 Glab
  obtain ⟨f', G'', hf'⟩ := exists_goodLab bW hG' U' C

  have hO : CExt W ⊥ C := ⟨hC.1, fun r hr => hC.2 r (bot_le (a := maximalIdeal W) hr)⟩
  have huW : IsUnit (n : W) := by simpa using hu.map φ
  have h1 : ‖(n : C)‖ = 1 := (isUnit_iff_norm hC n).1 huW
  have hnC : (n : C) ≠ 0 := fun h => by rw [h, norm_zero] at h1; exact zero_ne_one h1
  obtain ⟨N₁, ν₁, -⟩ := _root_.GlobalTheory.ValuesExist.exists_integral_values hL W DW.toPre DW.psi_even hBW C ⊤ fun _ => trivial
  obtain ⟨N, ν, q₀, -, hIν, hq₀, -⟩ := exists_integral hW DW hC ν₁
  have hT := GlobalTheory.ValuesTorsion.tors_of_integral hL hL₂ (_root_.GlobalTheory.ThetaInValues.brUth_of_laws hL) W DW.toPre DW.psi_even hBW C hO N ν hIν n hn
    ho h1
  have hd : ∀ g : N.Gt, ∃ g', g' ^ n = g := fun g => by
    obtain ⟨g', hg'⟩ := (GlobalTheory.Ex.QStr.qStructure C N n _ hnC hT 1).2.1 g
    exact ⟨g', by rw [← hg', pow_one]⟩
  have h0 : ∃ q : N.QT ((n ^ 1) ^ 2), N.tx (n ^ 1) q ≠ 0 := by
    obtain ⟨h, -, -, hh⟩ := (_root_.GlobalTheory.tx_coset_criterion C N q₀ hq₀ n _ hn ho h1 hT 1 le_rfl).2.2 1
    exact ⟨_, hh⟩
  obtain ⟨N', ν', -⟩ := _root_.GlobalTheory.ValuesExist.exists_integral_values hL W D'.toPre D'.psi_even D'.tau_bimult C ⊤ fun _ => trivial

  have galW : ∀ k, (∃ j, k = n ^ j) → ∀ (σ : C ≃ₐ[FractionRing W] C) (p pσ : QkPt DW.toPre C k),
      QkExt (σ : C →+* C) p pσ → (fW k pσ).left = spMap (σ : C →+* C) ≫ (fW k p).left := by
    rintro k ⟨j, rfl⟩ σ p pσ hp
    have hk : 1 ≤ n ^ j := Nat.one_le_pow _ _ hn.pos
    obtain ⟨p₀, rfl⟩ := (tr_bij hWp cC em hBW hk).2 p
    let σR : C →ₐ[FractionRing R] C := ⟨(σ : C →+* C), fun t => σ.commutes (fracMap iφ t)⟩
    obtain ⟨ρ, hρ⟩ : ∃ ρ : Kb R →ₐ[FractionRing R] Kb R, em.toRingHom.comp ρ.toRingHom = (σR.comp em).toRingHom := by
      letI : Algebra (Kb R) C := em.toRingHom.toAlgebra
      haveI : IsScalarTower (FractionRing R) (Kb R) C := IsScalarTower.of_algebraMap_eq fun x => (em.commutes x).symm
      exact ⟨(σR.comp em).restrictNormal (Kb R), RingHom.ext fun x => (σR.comp em).restrictNormal_commutes (Kb R) x⟩
    obtain ⟨p₀ρ, hρp⟩ := exists_ext hB ρ p₀
    obtain ⟨p₁, t₁, t₂, t₃⟩ := (lies_iff hWp cC em hBW p₀ _).2 rfl
    obtain ⟨r, hr⟩ := exists_ext hB σR p₁
    have u₁ := qkExt_trans t₁ hr
    obtain ⟨r', hr'⟩ := exists_ext hB em p₀ρ
    have u₂ := qkExt_trans hρp hr'
    rw [hρ] at u₂
    obtain rfl := ext_unique hB (σR.comp em) u₁ u₂
    have e₁ : pσ = tr hWp cC em hBW p₀ρ := (lies_iff hWp cC em hBW p₀ρ pσ).1 ⟨r, hr', by
      rw [hp.1, t₂, hr.1], isPullGtF_ext hWp cC (σ : C →+* C) σ.toAlgHom.comp_algebraMap t₃ hr hp⟩
    rw [e₁, hfW _ hk, hfW _ hk]
    obtain ⟨ga, -, gpa, -⟩ := hfib
    apply gpa.1.hom_ext
    · rw [(hε _ _).1 rfl, Category.assoc, (hε _ _).1 rfl, hgal ρ j p₀ p₀ρ hρp, ← Category.assoc,
        ← Category.assoc, ← Geo.Tor.spMap_comp, ← Geo.Tor.spMap_comp, hρ]
      rfl
    · rw [Category.assoc, Over.w (ε (lab _ p₀ρ)), Over.w (ε (lab _ p₀))]
      exact ((Geo.Tor.spMap_comp _ _).symm.trans (congrArg spMap σ.toAlgHom.comp_algebraMap)).symm
  have gal' : ∀ k, 1 ≤ k → ∀ (σ : C ≃ₐ[FractionRing W] C) (p pσ : QkPt D'.toPre C k),
      QkExt (σ : C →+* C) p pσ → (f' k pσ).left = spMap (σ : C →+* C) ≫ (f' k p).left := by
    intro k hk σ p pσ hp
    obtain ⟨-, hx, hiff⟩ := GlobalTheory.UT.Cl.galois_holds W _ bW D' A' G' hG' U' C C σ.toAlgHom k hk p
    obtain ⟨x', hx'⟩ := hx (f' k p)
    rw [← (hf' k hk pσ x').1 ((hiff pσ (f' k p) x' hp hx').1 ((hf' k hk p _).2 rfl))]
    exact hx'
  have gal : ∀ (σ : C ≃ₐ[FractionRing W] C) (p pσ : QkPt DW.toPre C ((n ^ 1) ^ 2))
      (p' pσ' : QkPt D'.toPre C ((n ^ 1) ^ 2)), QkExt (σ : C →+* C) p pσ → QkExt (σ : C →+* C) p' pσ' →
      fW _ p = f' _ p' → fW _ pσ = f' _ pσ' := fun σ p pσ p' pσ' h₁ h₂ h₃ =>
    Over.OverMorphism.ext (by
      rw [galW _ ⟨2, by ring⟩ σ p pσ h₁, h₃, gal' _ (Nat.one_le_pow _ _ (Nat.one_le_pow _ _ hn.pos)) σ p' pσ' h₂])

  have BG' := GlobalTheory.Ex.GtValues.points_correspond W D'.toPre D'.psi_even D'.tau_bimult C N' ν'
  have hc : ∀ j, ∃ c : Cˣ, ∀ p p' q q', ν.QPt p q → ν'.QPt p' q' → fW ((n ^ j) ^ 2) p = f' _ p' →
      N'.tx (n ^ j) q' = c * N.tx (n ^ j) q := by
    intro j
    have hm : Odd (n ^ j) := ho.pow
    have hk : 1 ≤ (n ^ j) ^ 2 := Nat.one_le_pow _ _ (Nat.one_le_pow _ _ hn.pos)
    have hum : IsUnit ((n ^ j : ℕ) : R) := by rw [Nat.cast_pow]; exact hu.pow j
    obtain ⟨v, hv⟩ := _root_.GlobalTheory.Mum.ThetaSer.theta_series_algebraic R hR D (n ^ j) hm hum _ id
    have Θ := htheta j v hv
    have hCR : CExt R (maximalIdeal R) C :=
      ⟨fun r => (cC r).symm ▸ hC.1 _, fun r hr => (cC r).symm ▸ hC.2 _ (map_nonunit φ r hr)⟩
    obtain ⟨N₀, ν₀, -⟩ := _root_.GlobalTheory.ValuesExist.exists_integral_values hL R D.toPre D.psi_even hB C ⊤ fun _ => trivial
    obtain ⟨J, hJX, hJ⟩ := GlobalTheory.Mum.OneTraitTheta.exists_values_iso hL hWp cC ν₀ ν
    choose q₀ hq₀ using fun i : QkPt D.toPre (Kb R) ((n ^ j) ^ 2) =>
      exists_val D.psi_even hB ν₀ (qkExt hB em.toRingHom em.comp_algebraMap i)
    obtain ⟨s, hs⟩ := hv C hCR em N₀ ν₀ (fun i => qkExt hB em.toRingHom em.comp_algebraMap i) q₀
      (fun i => (qkExt_iff hB _ em.comp_algebraMap _ _).2 rfl) hq₀
    choose pp hpp using fun i => G''.onto _ hk (fW _ (tr hWp cC em hBW i)) (GW.pow _ hk _)
    choose qq hqq using fun i => exists_val D'.psi_even D'.tau_bimult ν' (pp i)
    have Q := _root_.GlobalTheory.Ex.ThetaSeries.theta_const_eq_series hV _root_.GlobalTheory.Ex.GtValues.points_correspond (_root_.GlobalTheory.Ex.brFam hL hL₂) W _ hW rfl D' A' G' hG' U' C hC N' ν' (n ^ j) hm _ pp qq
      (fun i => fW _ (tr hWp cC em hBW i)) (fun i => (hf' _ hk _ _).2 (hpp i).symm) hqq
    obtain ⟨c₃, hc₃⟩ := theta_prop hfib cC em hm (x := lab _) (x' := fun i => fW _ (tr hWp cC em hBW i))
      (fun i => by rw [hfW _ hk]; exact (hε _ _).1 rfl) (fun i => GW.pow _ hk _) Θ Q
    refine ⟨c₃ * s * J.lam, fun p p' q q' hp hp' hpp' => ?_⟩
    obtain ⟨i, rfl⟩ := (tr_bij hWp cC em hBW hk).2 p
    obtain ⟨p₁, t₁, t₂, t₃⟩ := (lies_iff hWp cC em hBW i _).2 rfl
    obtain rfl := (qkExt_iff hB _ em.comp_algebraMap _ _).1 t₁
    have e₁ : N'.tx (n ^ j) (qq i) = N'.tx (n ^ j) q' :=
      GlobalTheory.ModelData.Scalar.tx_congr N' hm (((BG'.2.2.2.2 _).2.2 _ _ _ _ (hqq i) hp').1
        ((G''.eqv _ hk _ _).1 ((hpp i).trans hpp')))
    have e₂ := (GlobalTheory.RelabelCoords.series_iso J hm (p := q) (p' := q₀ i) (ν₀.eX.injective (by
      rw [hJX, hp.1, t₂, AddEquiv.apply_symm_apply]; exact (hq₀ i).1)) (hJ _ _ _ _ (hq₀ i).2 hp.2 t₃)).1
    rw [← e₁, hc₃ i, hs i, e₂, Units.val_mul, Units.val_mul, _root_.mul_assoc, _root_.mul_assoc,
      Units.mul_inv_cancel_left]

  obtain ⟨e, he⟩ := rec_trait hW hC ν ν' GW G'' hn ho huW hd gal hc h0
  obtain ⟨hD, T⟩ := GlobalTheory.LabTrans.exists_comp iφ Function.injective_id hWp e
  refine ⟨hD, C, inferInstance, inferInstance, inferInstance, inferInstance, em, cC, fun j p p₁ p'' x' h₁ h₂ h₃ h₄ => ?_⟩
  have hk : 1 ≤ n ^ j := Nat.one_le_pow _ _ hn.pos
  refine (hf' _ hk p'' x').2 ?_
  obtain rfl := (qkExt_iff hB _ em.comp_algebraMap _ _).1 h₁
  rw [(hε _ _).2 h₄, ← hfW _ hk p]
  obtain ⟨p₁', t₁, t₂, t₃⟩ := (lies_iff hWp cC em hBW p _).2 rfl
  obtain rfl := (qkExt_iff hB _ em.comp_algebraMap _ _).1 t₁
  have cI : Compat (RingHom.id W) C := fun _ => rfl
  have g₁ := T.isPullGtF cC t₃ (isPullGtF_pullGt e hGF cI (tr hWp cC em hBW p).g)
  have g₂ := pullGt_unique hD cC g₁ h₃
  refine he j _ _ ?_ ?_
  · apply hD.xe.injective
    rw [h₂, AddEquiv.apply_symm_apply, ← T.xe_eq, AddEquiv.apply_symm_apply, t₂, AddEquiv.apply_symm_apply]
  · rw [← g₂]
    exact isPullGtF_pullGt e hGF cI _

end GlobalTheory.Mum.Recog
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricDegreePosOfAmpleSemiPositive
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem exists_pair_mem_H_of_rep {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (P : Pair p)
    {a b : ℤ} {M : HermLB p} (h : P.Rep a b M) : ∃ Q : Pair p, Q.L = M ∧ ∀ f ∈ P.H a b, f ∈ Q.H 1 0 := by
  obtain ⟨ρ, hρ, hu, -⟩ := h
  refine ⟨⟨M, P.A, ρ, P.r', hρ, P.hr'⟩, rfl, fun f hf x c j hc hj => ?_⟩
  have hx : x ∈ (⨆ i, P.L.B.U i) := by rw [P.L.isLB.cover]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hx
  have h1 := (hu x c i j hc hi hj).regAt.mul (hf x i j hi hj)
  have hi0 : (P.r i : X.functionField) ^ a ≠ 0 := zpow_ne_zero _ (P.r i).ne_zero
  have hj0 : (P.r' j : X.functionField) ^ b ≠ 0 := zpow_ne_zero _ (P.r' j).ne_zero
  convert h1 using 1
  simp only [Pair.loc, zpow_one, zpow_zero]
  field_simp

theorem gdeg_pos_of_ample : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ L : HermLB p, IsAmpleLB L.B → L.SemiPos D → 0 < gdeg L D := by
  intro hA hS k _ X _ p D hX L hL hs
  obtain ⟨P, rfl, hPA⟩ := exists_pair L L
  obtain ⟨x, hx⟩ := (_root_.GlobalTheory.ArithTrdeg.isTranscendenceBasis_functionField k X p D hX).1
  obtain ⟨c, g, hc, hg, -, hm⟩ := _root_.GlobalTheory.HSNef.Den.exists_clear_denominators k X p D hX P (hPA ▸ hL) 0 (Finset (Fin D)) fun S => ∏ i ∈ S, x i
  have hr := Pair.rep_pow k X p P 0 1 P.A c (Pair.rep_base k X p P).2.1
  rw [mul_zero, mul_one, hPA] at hr
  obtain ⟨Q, hQ, hH⟩ := exists_pair_mem_H_of_rep P hr
  have hQa : IsAmpleLB Q.L.B := by
    rw [hQ]
    exact (isAmpleLB_pow_iff hL.isLB hc).2 hL
  have hQs : Q.L.SemiPos D := by rw [hQ]; exact hs.pow c
  haveI : CharZero X.functionField :=
    have := hX.charZero
    ((fnOf (X := X) ⊤ trivial).charZero_iff (fnOf_injective _ _)).1 this
  have hli : LinearIndependent ℤ (fun _ : Unit => g) := linearIndependent_unique_iff.2 hg
  have h := _root_.GlobalTheory.HSNef.factorial_mul_card_le_gdeg_of_boxFam hA hS k X p D hX Q hQa hQs Unit (fun _ => g) x hli hx.1 fun c' => hH _ (hm c'.2)
  rw [hQ, _root_.GlobalTheory.GdegPow.gdeg_pow hA k X p D hX] at h
  have h0 : (0 : ℝ) < (c : ℝ) ^ D := by positivity
  have h1 : (0 : ℝ) < (D.factorial : ℝ) * Fintype.card Unit := by
    simp [Nat.factorial_pos]
  exact (mul_pos_iff_of_pos_left h0).1 (h1.trans_le h)

end GlobalTheory.HSNef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceIntegralUnitaryPointsFixVacuumStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_integralUnitaryPoints_fix_vacuum : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L)
      (JS : GL (Fin a') L) (JT : GL (Fin (a + a')) L) (ψL : AddChar L ℂ)
      (κ : Matrix (Fin (a + a')) (Fin a') L →+ Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
      (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) →* UA σ G.V'.J)
      (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J),
      GlobalTheory.InertBridge.Chart σ B G v ϖ σL q δ JS JT ψL κ ιS ιT →
    ∀ ω : (Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) × Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →*
        Module.End ℂ (SB (Fin a' × Fin (a + a') → Fv F v))),
      (∀ g h (m : SB (Fin a' × Fin (a + a') → Fv F v)) (φ₁ : (Fin a' × Fin (a + a') → Fv F v) → ℂ),
        φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v) →
        (Acts (evFin F v) (om' (ιS g, ιT h)) (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) φ₁ ↔
          ((ω (g, h) m : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ) = φ₁)) →
    ∀ s : SB (Fin a' × Fin (a + a') → Fv F v), (s : (Fin a' × Fin (a + a') → Fv F v) → ℂ) = G.M'.vac v →
    ∀ (g : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L)) (h : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L)),
      (g : GL (Fin a') L) ∈ Formalism.UG.GLint (Fin a') (Formalism.UG.intL L) →
      (h : GL (Fin (a + a')) L) ∈ Formalism.UG.GLint (Fin (a + a')) (Formalism.UG.intL L) → ω (g, h) s = s := by
  first | exact @GlobalTheory.InertBridge.fix_vac | exact GlobalTheory.InertBridge.fix_vac | (intros; apply GlobalTheory.InertBridge.fix_vac <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberMultilinearSymmStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_number_multilinear_symm : ∀ (K : Type) [Field K] (A : AbVar K) (J : Type) [Fintype J], Fintype.card J = A.dim → (∃ M : MultilinearMap (RingHom.id ℤ) (fun _ : J => Pic A.X.left) ℤ, ∀ c, M c = inter A c) ∧ ∀ (J' : Type) [Fintype J'] (e : J' ≃ J) (c : J → Pic A.X.left), inter A (c ∘ e) = inter A c := by
  intro K _ A J _ hJ
  classical
  have hMultilinear : ∃ M : MultilinearMap (RingHom.id ℤ) (fun _ : J => Pic A.X.left) ℤ,
      ∀ c, M c = inter A c := by
    refine ⟨MultilinearMap.mk' (fun c => inter A c) (inter_update_add A hJ) ?_, fun c => rfl⟩
    intro c i n a
    exact map_zsmul (interAdd A hJ c i) n a
  exact ⟨hMultilinear, fun J' _ e c => inter_comp_equiv A e c⟩
end

