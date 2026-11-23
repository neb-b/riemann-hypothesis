module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1971
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1997
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2000
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1877
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2042
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfTrivAxes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2037
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1999

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivationDetEqUnitMulProdNormalCrossings
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

namespace GlobalTheory

theorem derivation_prod_eq_zero_of_forall {F R : Type} [CommRing F] [CommRing R] [Algebra F R]
    (D : Derivation F R R) {ι : Type} (s : Finset ι) (f : ι → R) (h : ∀ i ∈ s, D (f i) = 0) :
    D (∏ i ∈ s, f i) = 0 :=
  Finset.prod_induction f (fun y => D y = 0)
    (fun a b ha hb => by rw [Derivation.leibniz, ha, hb, smul_zero, smul_zero, add_zero])
    (Derivation.map_one_eq_zero D) h

theorem logDet_local_eq_unit_mul_prod :
    ∀ (F A R : Type) [Field F] [CommRing A] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsRegularLocalRing R] [IsNoetherianRing A] [Algebra F A] [Algebra A R] [Algebra F R] [IsScalarTower F A R] [Algebra.FiniteType F A] (P : Ideal A) [P.IsPrime] [IsLocalization.AtPrime R P] (n m : ℕ) (x : Fin n → A) (e : Fin m ↪ Fin n) (J : Finset (Fin m)), ReciprocityTheory.AnForm.R.FinalTheorems.Rsp R m (fun j => algebraMap A R (x (e j))) → (∃ bs : Module.Basis (Fin n) R Ω[R⁄F], ∀ i, bs i = KaehlerDifferential.D F R (algebraMap A R (x i))) → ∀ (I : Ideal A), I.map (algebraMap A R) = Ideal.span {algebraMap A R (∏ j ∈ J, x (e j))} → ∀ (b : Fin n → Derivation ℤ A A), (∀ j c, b j (algebraMap F A c) = 0) → (∀ j, ∀ f ∈ I, b j f ∈ I) → (∀ D : Derivation ℤ A A, (∀ c, D (algebraMap F A c) = 0) → (∀ f ∈ I, D f ∈ I) → ∃ c : Fin n → A, D = ∑ j, c j • b j) → ∃ u : Rˣ, algebraMap A R (GlobalTheory.LogPole.logDet b x) = u * algebraMap A R (∏ j ∈ J, x (e j)) := by
  intro F A R _ _ _ _ _ _ _ _ _ _ _ _ P _ _ n m x e J hrsp hbs I hI b _hbF hbI hspan
  obtain ⟨bs, hbs⟩ := hbs
  set φ := algebraMap A R with hφ
  set r : Fin m → R := fun j => φ (x (e j)) with hr
  set g : R := ∏ j ∈ J, r j with hg
  have hφg : φ (∏ j ∈ J, x (e j)) = g := by rw [map_prod]
  have hIg : I.map φ = Ideal.span {g} := by rw [hI, hφg]

  let dd : Fin n → Derivation F R R := fun i => (bs.coord i).compDer (KaehlerDifferential.D F R)
  have hδ : ∀ i l, dd i (φ (x l)) = if l = i then 1 else 0 := by
    intro i l
    show bs.coord i (KaehlerDifferential.D F R (φ (x l))) = _
    rw [← hbs l, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  let hm : Fin n → R := fun l => if l ∈ J.map e then φ (x l) else 1
  let E : Fin n → Derivation F R R := fun i => hm i • dd i
  have hEapp : ∀ i y, E i y = hm i * dd i y := fun i y => rfl

  have hEg : ∀ i, E i g ∈ Ideal.span {g} := by
    intro i
    rw [hEapp]
    by_cases hi : i ∈ J.map e
    · obtain ⟨j0, hj0, rfl⟩ := Finset.mem_map.mp hi
      have hsplit : g = r j0 * ∏ j ∈ J.erase j0, r j := (Finset.mul_prod_erase J r hj0).symm
      have hrest : dd (e j0) (∏ j ∈ J.erase j0, r j) = 0 := by
        refine derivation_prod_eq_zero_of_forall _ _ _ fun j hj => ?_
        have hne : e j ≠ e j0 := fun h => (Finset.ne_of_mem_erase hj) (e.injective h)
        show dd (e j0) (φ (x (e j))) = 0
        rw [hδ, if_neg hne]
      have hone : dd (e j0) (r j0) = 1 := by
        show dd (e j0) (φ (x (e j0))) = 1
        rw [hδ, if_pos rfl]
      have hmv : hm (e j0) = r j0 := if_pos hi
      have : hm (e j0) * dd (e j0) g = g := by
        conv_lhs => rw [hsplit]
        rw [Derivation.leibniz, hrest, hone, hmv, smul_zero, zero_add, smul_eq_mul, mul_one, ← hsplit]
      rw [this]
      exact Ideal.mem_span_singleton_self g
    · have : dd i g = 0 := by
        refine derivation_prod_eq_zero_of_forall _ _ _ fun j hj => ?_
        have hne : e j ≠ i := fun h => hi (Finset.mem_map.mpr ⟨j, hj, h⟩)
        show dd i (φ (x (e j))) = 0
        rw [hδ, if_neg hne]
      rw [this, mul_zero]
      exact Ideal.zero_mem _
  have hE : ∀ i, ∀ f ∈ I.map φ, E i f ∈ I.map φ := by
    intro i f hf
    rw [hIg] at hf ⊢
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hf
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hEg i))
      (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self g))
  choose N hN using fun i => _root_.GlobalTheory.logDerivation_atPrime_span F A R P I n b hspan (E i) (hE i)

  choose D' hD' using fun k =>
    _root_.GlobalTheory.derivation_extend_localization_atPrime ℤ A R P ((Algebra.linearMap A R).compDer (b k))
  have hD'a : ∀ k a, D' k (φ a) = φ (b k a) := fun k a => hD' k a
  have hD'I : ∀ k, ∀ f ∈ I.map φ, D' k f ∈ I.map φ := by
    intro k f hf
    induction hf using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      rw [hD'a]
      exact Ideal.mem_map_of_mem _ (hbI k a ha)
    | zero => rw [map_zero]; exact Ideal.zero_mem _
    | add y z _ _ hy hz => rw [map_add (f := _)]; exact Ideal.add_mem _ hy hz
    | smul c y hy hy' =>
      rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hy') (Ideal.mul_mem_right _ _ hy)
  have hdiv : ∀ l k, ∃ c, φ (b k (x l)) = hm l * c := by
    intro l k
    by_cases hl : l ∈ J.map e
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hl
      have hgk : D' k g ∈ Ideal.span {g} := by
        rw [← hIg]; exact hD'I k g (by rw [hIg]; exact Ideal.mem_span_singleton_self g)
      have := _root_.GlobalTheory.dvd_derivation_of_mem_span_prod_params R m r hrsp J (D' k) hgk j hj
      obtain ⟨c, hc⟩ := this
      refine ⟨c, ?_⟩
      have hmv : hm (e j) = r j := if_pos hl
      rw [hmv, ← hc]
      exact (hD'a k (x (e j))).symm
    · refine ⟨φ (b k (x l)), ?_⟩
      have hmv : hm l = 1 := if_neg hl
      rw [hmv, one_mul]
  choose M hM using hdiv

  let Bm : Matrix (Fin n) (Fin n) R := Matrix.of fun l k => φ (b k (x l))
  have hBdet : φ (logDet b x) = Bm.det := by
    rw [logDet, RingHom.map_det]
    congr 1
  have h1 : Bm = Matrix.diagonal hm * Matrix.of M := by
    ext l k
    simp [Bm, Matrix.diagonal_mul, hM]
  have h2 : Matrix.diagonal hm = Bm * (Matrix.of N).transpose := by
    ext l i
    rw [Matrix.mul_apply]
    have hsum : ∑ k, Bm l k * (Matrix.of N).transpose k i = ∑ k, N i k * φ (b k (x l)) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [Bm, mul_comm]
    rw [hsum, ← hN i (x l), hEapp, hδ, Matrix.diagonal_apply]
    by_cases hli : l = i
    · subst hli; simp
    · simp [hli]
  have hdetD : (Matrix.diagonal hm).det = g := by
    rw [Matrix.det_diagonal]
    have : ∏ l, hm l = ∏ l ∈ J.map e, φ (x l) := by
      rw [← Finset.prod_filter]
      congr 1
      ext l; simp
    rw [this, Finset.prod_map]
  haveI : IsDomain R := ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing
  have hprime : ∀ j, Prime (r j) := ReciprocityTheory.AnForm.R.prime_of_regular_params r hrsp.1 hrsp.2
  have hg0 : g ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => (hprime j).ne_zero
  have hMN : (Matrix.of M).det * (Matrix.of N).transpose.det = 1 := by
    have h3 : Matrix.diagonal hm = Matrix.diagonal hm * (Matrix.of M * (Matrix.of N).transpose) := by
      conv_lhs => rw [h2, h1]
      rw [Matrix.mul_assoc]
    have h4 := congrArg Matrix.det h3
    rw [Matrix.det_mul, Matrix.det_mul, hdetD] at h4
    exact (mul_left_cancel₀ hg0 (h4.symm.trans (mul_one g).symm))
  refine ⟨Units.mkOfMulEqOne _ _ hMN, ?_⟩
  rw [Units.val_mkOfMulEqOne, hφg, hBdet, h1, Matrix.det_mul, hdetD, mul_comm]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogKappaLengthBounds
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CovTop.CovSz

theorem ceil_mul_le_pow {y PP Dd k m : ℝ} (hy : 2 ≤ y) (hP0 : 0 ≤ PP) (hP : PP ≤ y) (hD0 : 0 ≤ Dd) (hD : Dd ≤ y ^ 2)
    (hk0 : 0 ≤ k) (hk : k ≤ y) (hm : 1 ≤ m) : (⌈PP ^ 2 * Dd ^ 2 * k / m⌉₊ : ℝ) * PP ≤ y ^ 9 := by
  have h0 : 0 ≤ PP ^ 2 * Dd ^ 2 * k := by positivity
  have h1 : PP ^ 2 * Dd ^ 2 * k ≤ y ^ 7 := by
    calc PP ^ 2 * Dd ^ 2 * k ≤ y ^ 2 * (y ^ 2) ^ 2 * y := by gcongr
      _ = y ^ 7 := by ring
  have h2 : PP ^ 2 * Dd ^ 2 * k / m ≤ y ^ 7 := (div_le_self h0 hm).trans h1
  have h3 : (⌈PP ^ 2 * Dd ^ 2 * k / m⌉₊ : ℝ) < PP ^ 2 * Dd ^ 2 * k / m + 1 :=
    Nat.ceil_lt_add_one (div_nonneg h0 (by linarith))
  have h4 : 1 ≤ y ^ 7 := one_le_pow₀ (by linarith)
  have h5 : (⌈PP ^ 2 * Dd ^ 2 * k / m⌉₊ : ℝ) ≤ y ^ 8 := by
    have : y ^ 8 = y ^ 7 * y := by ring
    nlinarith
  calc (⌈PP ^ 2 * Dd ^ 2 * k / m⌉₊ : ℝ) * PP ≤ y ^ 8 * y := by gcongr
    _ = y ^ 9 := by ring

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem kap_le {PP : ℝ} (hW : WtNum p i PP) : CovTop.kap p i ≤ (D.R.f : ℝ) * D.R.r * (4 * L.sc.b) := by
  have hc : (Fintype.card (Psi p.T.Q.H) : ℝ) = D.R.f := by
    rw [← hW.card, Nat.card_eq_fintype_card]
  have hr : (((dat p i).p + (dat p i).q : ℕ) : ℝ) = D.R.r := by rw [hW.sig.2.2]
  unfold CovTop.kap sizeK
  calc _ ≤ ∑ _τ : Psi p.T.Q.H, ∑ _k : Fin ((dat p i).p + (dat p i).q), 4 * L.sc.b :=
        Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun k _ => hW.up τ k
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [hc, hr]; ring

theorem kapT_at {PP A : ℝ} (hH : HostNum D L PP A 18) (hW : WtNum p i PP) :
    Real.log (CovTop.kap p i) ≤ 2 * L.sc.L ∧ (lenT p i PP : ℝ) * PP ≤ Real.sqrt L.sc.b := by
  obtain ⟨-, hL, -, -⟩ := hH.big
  obtain ⟨-, hPy, hfy⟩ := hH.poly
  have hroom := hH.room
  have hlow := hH.ppLow
  set y := L.sc.x ^ A with hy
  have hroom' : y ^ 18 ≤ L.sc.b := by
    have : y ^ (18 : ℝ) = y ^ (18 : ℕ) := by exact_mod_cast Real.rpow_natCast y 18
    rwa [this] at hroom
  have hm2 := D.R.two_le_m
  have hkm := D.R.m_add_three_le_k
  have hkr : D.R.k ≤ D.R.r := by unfold Ranks.r; omega
  have hr1 : 1 ≤ D.R.r := by omega
  have hn1 : 1 ≤ D.R.nV := by unfold Ranks.nV; omega
  have hf8 : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hH.f8
  have hr1' : (1 : ℝ) ≤ D.R.r := by exact_mod_cast hr1
  have hn1' : (1 : ℝ) ≤ D.R.nV := by exact_mod_cast hn1
  have hkr' : (D.R.k : ℝ) ≤ D.R.r := by exact_mod_cast hkr
  have hm' : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hfr : (8 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := by nlinarith
  have h10 : (D.R.f : ℝ) * D.R.r * 10 ≤ y := by
    refine le_trans ?_ hfy
    calc (D.R.f : ℝ) * D.R.r * 10 = (D.R.f : ℝ) * D.R.r * 1 * 10 := by ring
      _ ≤ _ := by gcongr
  have hy2 : 2 ≤ y := by linarith
  have hb0 : 0 < L.sc.b := Real.exp_pos _
  have hyb : y ≤ L.sc.b := (le_self_pow₀ (by linarith) (by norm_num)).trans hroom'
  have hP0 : 0 ≤ PP := le_trans (Even.pow_nonneg (by decide) _) hlow
  refine ⟨?_, ?_⟩
  · have hk := kap_le p i hW
    have hk0 : 0 ≤ CovTop.kap p i :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hk2 : CovTop.kap p i ≤ Real.exp (2 * L.sc.L) := by
      have e : Real.exp (2 * L.sc.L) = L.sc.b * L.sc.b := by
        unfold Scale.b; rw [← Real.exp_add]; ring_nf
      rw [e]
      nlinarith
    rcases hk0.eq_or_lt with h | h
    · rw [← h, Real.log_zero]; linarith
    · exact (Real.log_le_iff_le_exp h).2 hk2
  · have hch : (D.R.r.choose 2 : ℝ) ≤ (D.R.r : ℝ) ^ 2 := by exact_mod_cast Nat.choose_le_pow D.R.r 2
    have hD : (CompHt.dimFlag (dat p i) : ℝ) ≤ y ^ 2 := by
      rw [hW.dim]; push_cast
      calc (D.R.f : ℝ) * (D.R.r.choose 2 : ℝ) ≤ (D.R.f : ℝ) ^ 2 * (D.R.r : ℝ) ^ 2 := by
            gcongr; nlinarith
        _ = ((D.R.f : ℝ) * D.R.r) ^ 2 := by ring
        _ ≤ y ^ 2 := by gcongr; linarith
    have hky : (D.R.k : ℝ) ≤ y := by nlinarith
    have h9 := ceil_mul_le_pow hy2 hP0 hPy (Nat.cast_nonneg _) hD (Nat.cast_nonneg _) hky hm'
    refine h9.trans (Real.le_sqrt_of_sq_le ?_)
    calc (y ^ 9) ^ 2 = y ^ 18 := by ring
      _ ≤ _ := hroom'

end Point

end GlobalTheory.CovTop.CovSz

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKernelDiagonalRestrictionOfSymmetricTrivial
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.DualCon
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.AbDual

theorem memKL_diag_of_triv_ev_of_symm : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G], IsAbelianScheme G → ∀ P : LB (G ⊗ G).left, P.IsLB → (∃ t : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∀ (T : Over (Sp R)) (a : T ⟶ G), (∃ t : (P.pull (lift (snd G T ≫ a) (fst G T)).left).Gen, t.IsGen) → GlobalTheory.MemKL G (P.pull (lift (𝟙 G) (𝟙 G)).left) a := by
  intro R _ _ G _ hA P hP h0l h0r hsym T a ha
  have hs : (swap P).IsLB := pull_isLB hP _
  have hadd := (isAdditive_iff hP).1 (CubeNoeth.isAdditive_of_triv_axes hA hA hP h0l h0r)
  have hadd' := (isAdditive_iff hs).1 (CubeNoeth.isAdditive_swap_of_triv_axes hA hA hP h0l h0r)
  have hadd2 : ∀ (Y : Over (Sp R)) (u v w : Y ⟶ G), evc hP u (v * w) = evc hP u v + evc hP u w := by
    intro Y u v w
    rw [← evc_swap hP hs, ← evc_swap hP hs, ← evc_swap hP hs]
    exact hadd' Y v w u
  have hc : cls P hP = cls (swap P) hs := (cls_eq_iff hP hs).2 hsym
  have hsymm : ∀ (Y : Over (Sp R)) (u v : Y ⟶ G), evc hP u v = evc hP v u := by
    intro Y u v
    rw [← evc_swap hP hs u v]
    simp only [evc, hc]
  have hL : (P.pull (lift (𝟙 G) (𝟙 G)).left).IsLB := pull_isLB hP _
  have hcL : ∀ (Y : Over (Sp R)) (u : Y ⟶ G), CechPic.pull u.left (cls _ hL) = evc hP u u := by
    intro Y u
    rw [cls_ev hP, pull_evc, Category.comp_id]
  have hx0 : evc hP (fst T G ≫ a) (snd T G) = 0 := by
    have e := congrArg (CechPic.pull (lift (snd T G) (fst T G)).left) ((triv_ev_iff hP _ _).1 ha)
    rwa [pull_evc, map_zero, lift_snd_assoc, lift_fst] at e
  have hD : (Out.translDiff G _ a).IsLB := LB.isLB_linComb hL _ _
  intro p
  obtain ⟨V, hV, hc'⟩ := exists_pull_eq_zero (evc hP a a) p
  refine ⟨V, hV, (cls_eq_zero_iff (pull_isLB hD _)).1 ?_⟩
  have e₁ := pull_translDiff hL a hD (fst T G) (snd T G)
  rw [lift_fst_snd, Over.id_left, pull_id, hcL, hcL] at e₁
  have e₂ : cls _ hD = CechPic.pull (fst T G).left (evc hP a a) := by
    rw [e₁, pull_evc, hadd, hadd2, hadd2, hsymm _ (snd T G) (fst T G ≫ a), hx0]
    abel
  rw [cls_pull hD, e₂, ← pull_comp]
  exact pull_eq_zero_of_mem V (((fst T G).left ⁻¹ᵁ V).ι ≫ (fst T G).left) (fun z ↦ z.2) hc'

end GlobalTheory.AbDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKernelLiftOneOfAxisTrivialBundle
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.DualCon
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.AbDual

theorem memKL_lift_one_of_triv_ev : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G], IsAbelianScheme G → ∀ P : LB (G ⊗ G).left, P.IsLB → (∃ t : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∀ (T : Over (Sp R)) (a : T ⟶ G), (∃ t : (P.pull (lift (snd G T ≫ a) (fst G T)).left).Gen, t.IsGen) → GlobalTheory.MemKL (G ⊗ G) P (lift a (1 : T ⟶ G)) := by
  intro R _ _ G _ hG P hP h0l h0r _ T a ha
  have hadd : IsAdditive P := CubeNoeth.isAdditive_of_triv_axes hG hG hP h0l h0r
  have hD : (Out.translDiff (G ⊗ G) P (lift a (1 : T ⟶ G))).IsLB := LB.isLB_linComb hP _ _
  have hz : cls _ hD = 0 := by
    have e₁ := pull_translDiff hP (lift a (1 : T ⟶ G)) hD (fst T (G ⊗ G)) (snd T (G ⊗ G))
    rw [lift_fst_snd, Over.id_left, pull_id] at e₁
    have em : (fst T (G ⊗ G) ≫ lift a (1 : T ⟶ G)) * snd T (G ⊗ G) =
        lift ((fst T (G ⊗ G) ≫ a) * (snd T (G ⊗ G) ≫ fst G G)) (snd T (G ⊗ G) ≫ snd G G) := by
      ext <;> simp [MonObj.mul_comp]
    have eu : snd T (G ⊗ G) = lift (snd T (G ⊗ G) ≫ fst G G) (snd T (G ⊗ G) ≫ snd G G) := by
      ext <;> simp
    have k₁ : CechPic.pull ((fst T (G ⊗ G) ≫ lift a (1 : T ⟶ G)) * snd T (G ⊗ G)).left (cls P hP) =
        evc hP ((fst T (G ⊗ G) ≫ a) * (snd T (G ⊗ G) ≫ fst G G)) (snd T (G ⊗ G) ≫ snd G G) := by
      rw [em]; rfl
    have k₂ : CechPic.pull (snd T (G ⊗ G)).left (cls P hP) =
        evc hP (snd T (G ⊗ G) ≫ fst G G) (snd T (G ⊗ G) ≫ snd G G) := by
      rw [evc, ← eu]
    have k₃ : evc hP (fst T (G ⊗ G) ≫ a) (snd T (G ⊗ G) ≫ snd G G) = 0 := by
      have e := congrArg (CechPic.pull (lift (snd T (G ⊗ G) ≫ snd G G) (fst T (G ⊗ G))).left)
        ((triv_ev_iff hP _ _).1 ha)
      rwa [pull_evc, map_zero, lift_snd_assoc, lift_fst] at e
    rw [e₁, k₁, k₂, (isAdditive_iff hP).1 hadd, add_sub_cancel_right, k₃]
  intro p
  refine ⟨⊤, trivial, (cls_eq_zero_iff (pull_isLB hD _)).1 ?_⟩
  rw [cls_pull hD, hz, map_zero]

end GlobalTheory.AbDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKernelOfLineBundleOfDualPairLeftTrivial
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbDual

theorem memKL_of_triv_ev_left : ∀ (K : Type) [Field K] [IsAlgClosed K] (A B : Over (Sp K)) [GrpObj A] [GrpObj B]
    (P : LB (A ⊗ B).left) (L : LB A.left), IsAbelianScheme A → IsAbelianScheme B → IsDual A B P → L.IsLB →
    ∀ (T : Over (Sp K)) (x : T ⟶ A), Triv (ev P (fst T B ≫ x) (snd T B)) → GlobalTheory.MemKL A L x := by
  intro K _ _ A B _ _ P L hA _ hD hL T x hx
  haveI := hA.comm
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  have e : ∀ (Y : Over (Sp K)) (a b : Y ⟶ A), evc hP a b = lam (cls L hL) a b := fun Y a b ↦ by
    rw [evc, show cls _ hP = lam (cls L hL) (fst A A) (snd A A) from cls_cube_two hL _ _ hP, pull_lam, lift_fst,
      lift_snd]
  have hadd := GlobalTheory.CubeNoeth.isAdditive_of_triv_axes hA hA hP
    (by rw [triv_ev_iff hP, e, lam_one_left]) (by rw [triv_ev_iff hP, e, lam_one_right])
  obtain ⟨φ, hφ, -⟩ := hD.univ A (abelian₂ A L) hP hadd
  have hc : cls _ hP = evc hD.isLB (fst A A) (snd A A ≫ φ) :=
    (cls_eq_iff hP (pull_isLB hD.isLB _)).2 hφ
  have hx0 : lam (cls L hL) (fst T A ≫ x) (snd T A) = 0 := by
    have e₁ := congrArg (CechPic.pull (lift (fst T A) (snd T A ≫ φ)).left) ((triv_ev_iff hD.isLB _ _).1 hx)
    rw [pull_evc, map_zero, lift_fst_assoc, lift_snd] at e₁
    rw [← e, evc, hc, pull_evc, lift_fst, lift_snd_assoc]
    exact e₁
  have hD' : (Out.translDiff A L x).IsLB := LB.isLB_linComb hL _ _
  intro p
  obtain ⟨V, hV, hc'⟩ := exists_pull_eq_zero
    (CechPic.pull x.left (cls L hL) - CechPic.pull (1 : T ⟶ A).left (cls L hL)) p
  refine ⟨V, hV, (cls_eq_zero_iff (pull_isLB hD' _)).1 ?_⟩
  have e₁ := pull_translDiff hL x hD' (fst T A) (snd T A)
  rw [lift_fst_snd, Over.id_left, pull_id] at e₁
  have e₂ : cls _ hD' = CechPic.pull (fst T A).left
      (CechPic.pull x.left (cls L hL) - CechPic.pull (1 : T ⟶ A).left (cls L hL)) := by
    rw [e₁, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, MonObj.comp_one,
      ← sub_eq_zero, ← hx0, lam]
    abel
  rw [cls_pull hD', e₂, ← pull_comp]
  exact pull_eq_zero_of_mem V (((fst T A).left ⁻¹ᵁ V).ι ≫ (fst T A).left) (fun z ↦ z.2) hc'

end GlobalTheory.AbDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonvanishingLocusExtendFromBigOpen
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem extend_isLocus_of_big_open : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] [X.IsSeparated], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → ∀ V W : X.Opens, IsAffineOpen V → V ≤ W → (∀ z : X, ringKrullDim ((X).presheaf.stalk z) ≤ 1 → z ∈ W) → ∀ c : Pic X, IsLocus (GlobalTheory.CechPic.pull W.ι c) (W.ι ⁻¹ᵁ V) → IsLocus c V := by
  intro X _ _ hX V W hV hVW hW c hloc
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  obtain ⟨r, hr⟩ := IsLocus.exists_sec (pull_isLB hL W.ι) hloc
  obtain ⟨t, ht, -⟩ := ((GlobalTheory.extension_over_codim_two X hX).1 W hW).2.1 L r
  have e : GlobalTheory.secPull t W.ι = r := (GlobalTheory.lbSec_ext fun i => rfl).trans ht
  have h1 : W.ι ⁻¹ᵁ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus t = W.ι ⁻¹ᵁ V := by
    rw [← GlobalTheory.nonzeroLocus_secPull, e, hr]
  have key : ∀ x (hx : x ∈ W), x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus t ↔ x ∈ V := fun x hx => by
    have := congrArg (fun U : W.toScheme.Opens => (⟨x, hx⟩ : W.toScheme) ∈ U) h1
    exact Iff.of_eq this
  refine ⟨L, hL, t, rfl, ?_⟩
  exact GlobalTheory.T.eq_of_isAffineOpen_of_ringKrullDim_le_one' X hX V (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus t) hV (fun x hx => (key x (hVW hx)).2 hx)
    (fun z hz hz1 => (key z (hW z hz1)).1 hz)

end GlobalTheory
end

