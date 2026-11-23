module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2862
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ReductionSurjectiveOfIsNilpotent
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.InvariantVectorFieldsBasisVerticalDerivations
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2872
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0292

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFinitePointCongrOneOfInvConjCongr
section
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors
open GlobalTheory.CosetOrth

noncomputable section

namespace GlobalTheory.CosetOrth.Cong

theorem count_coe_ne_zero_iff {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {J : Ideal (𝓞 E)}
    (hJ : J ≠ ⊥) : FractionalIdeal.count E w (J : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 ↔ J ≤ w.asIdeal := by
  rw [FractionalIdeal.count_coe E w hJ, Nat.cast_ne_zero, Associates.count_ne_zero_iff_dvd hJ w.irreducible,
    Ideal.dvd_iff_le]

theorem val_le_one_of_mul_eq_one {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) {n : ℕ}
    (G H : Matrix (Fin n) (Fin n) K) (hHG : H * G = 1) (hH : ∀ i j, v ((1 - H) i j) < 1) (i j : Fin n) : v (G i j) ≤ 1 := by
  obtain ⟨p, -, hp⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n)) (fun k => v (G k j)) ⟨i, Finset.mem_univ _⟩
  refine (hp i (Finset.mem_univ _)).trans ?_
  by_contra hlt
  rw [not_le] at hlt
  have h0 : v (G p j) ≠ 0 := (zero_lt_one.trans hlt).ne'
  have e : G = 1 + (1 - H) * G := by rw [sub_mul, hHG, one_mul]; abel
  have e2 : G p j = (1 : Matrix (Fin n) (Fin n) K) p j + ∑ k, (1 - H) p k * G k j := by
    conv_lhs => rw [e]
    rw [Matrix.add_apply, Matrix.mul_apply]
  have h1 : v ((1 : Matrix (Fin n) (Fin n) K) p j) < v (G p j) := by
    refine lt_of_le_of_lt ?_ hlt
    rw [Matrix.one_apply]; split_ifs <;> simp
  have h2 : v (∑ k, (1 - H) p k * G k j) < v (G p j) := by
    refine v.map_sum_lt h0 fun k _ => ?_
    rw [map_mul]
    calc v ((1 - H) p k) * v (G k j) ≤ v ((1 - H) p k) * v (G p j) := by
          gcongr; exact hp k (Finset.mem_univ _)
      _ < 1 * v (G p j) := mul_lt_mul_of_pos_right (hH p k) (zero_lt_one.trans hlt)
      _ = _ := one_mul _
  have := v.map_add_lt h1 h2
  rw [← e2] at this
  exact lt_irrefl _ this

variable {D : D7}

def evAt (w : HeightOneSpectrum (𝓞 D.host.E)) : FA D →+* w.adicCompletion D.host.E where
  toFun x := x w
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem inv_apply {n : ℕ} (y : Formalism.MainNotions.StandardLatticesGL3.GA D n) (i j : Fin n) :
    (((y⁻¹ : Formalism.MainNotions.StandardLatticesGL3.GA D n) : GL (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin n) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j =
      Formalism.MainNotions.StandardLatticesGL3.sgA D (((y : GL (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin n) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) j i) := by
  have hh : Formalism.UG.cT (Formalism.MainNotions.StandardLatticesGL3.sgA D) (y.1 : Matrix (Fin n) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) * y.1 = 1 := by
    have h2 := y.2
    change Formalism.UG.cT _ (y.1 : Matrix (Fin n) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) * _ * _ = _ at h2
    rw [Matrix.map_one _ (map_zero _) (map_one _), mul_one] at h2
    exact h2
  rw [Subgroup.coe_inv, Units.inv_eq_of_mul_eq_one_left hh]
  rfl

theorem finMat_inv_mul {n : ℕ} (y : Formalism.MainNotions.StandardLatticesGL3.GA D n) : finMat y⁻¹ * finMat y = 1 := by
  unfold finMat
  have := (Matrix.map_mul (f := GlobalTheory.BotFormula.toFinE D)
    (L := (((y⁻¹ : Formalism.MainNotions.StandardLatticesGL3.GA D n) : GL (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin n) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)))
    (M := ((y : GL (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin n) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)))).symm
  rw [this, Subgroup.coe_inv, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]

theorem val_one_le {n : ℕ} (i j : Fin n) (w : HeightOneSpectrum (𝓞 D.host.E)) :
    Valued.v ((1 : Matrix (Fin n) (Fin n) (FA D)) i j w) ≤ 1 := by
  change Valued.v (evAt w ((1 : Matrix (Fin n) (Fin n) (FA D)) i j)) ≤ 1
  rw [Matrix.one_apply]; split_ifs <;> simp

theorem val_sub_le {x y : FA D} {w : HeightOneSpectrum (𝓞 D.host.E)} (hx : Valued.v (x w) ≤ 1) (hy : Valued.v (y w) ≤ 1) :
    Valued.v ((x - y) w) ≤ 1 := by
  change Valued.v (evAt w (x - y)) ≤ 1
  rw [map_sub]
  exact (Valued.v.map_sub _ _).trans (max_le hx hy)

theorem integral_of_cong {n : ℕ} (y : Formalism.MainNotions.StandardLatticesGL3.GA D n) (w : HeightOneSpectrum (𝓞 D.host.E))
    (h : ∀ i j, Valued.v ((1 - finMat y⁻¹) i j w) < 1) (i j : Fin n) :
    Valued.v (finMat y i j w) ≤ 1 ∧ Valued.v (finMat y⁻¹ i j w) ≤ 1 := by
  constructor
  · refine val_le_one_of_mul_eq_one Valued.v ((finMat y).map (evAt w)) ((finMat y⁻¹).map (evAt w)) ?_ (fun a b => ?_) i j
    · rw [← Matrix.map_mul, finMat_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    · have : (1 - (finMat y⁻¹).map (evAt w)) a b = evAt w ((1 - finMat y⁻¹) a b) := by
        rw [Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]
        split_ifs <;> simp
      rw [this]; exact h a b
  · have : finMat y⁻¹ i j = (1 : Matrix (Fin n) (Fin n) (FA D)) i j - (1 - finMat y⁻¹) i j := by
      rw [Matrix.sub_apply, sub_sub_cancel]
    rw [this]
    exact val_sub_le (val_one_le i j w) (h i j).le

theorem inHat_of_inv_cong : ∀ {D : D7}, (∀ w : HeightOneSpectrum (𝓞 D.host.E), ∃ w' : HeightOneSpectrum (𝓞 D.host.E), w'.asIdeal = D.host.conj • w.asIdeal ∧
    (∀ x : Formalism.MainNotions.StandardLatticesGL3.AE D, Valued.v (GlobalTheory.BotFormula.toFinE D (Formalism.MainNotions.StandardLatticesGL3.sgA D x) w') = Valued.v (GlobalTheory.BotFormula.toFinE D x w)) ∧
    (∀ 𝔞 : Ideal (𝓞 D.host.E), 𝔞 ≠ ⊥ → FractionalIdeal.count D.host.E w' ((D.host.conj • 𝔞 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) =
      FractionalIdeal.count D.host.E w (𝔞 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) ∧
    ∀ w'' : HeightOneSpectrum (𝓞 D.host.E), w''.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) ↔ w'' = w ∨ w'' = w') →
  ∀ (𝔪 : Ideal (𝓞 D.host.E)) (Sf : Finset (FinPl D)), GoodMod D 𝔪 Sf → ∀ {n : ℕ} (y : Formalism.MainNotions.StandardLatticesGL3.GA D n),
  (∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∉ Sf → ∀ i j,
    Valued.v (finMat y i j w) ≤ 1 ∧ Valued.v (finMat y⁻¹ i j w) ≤ 1) →
  (∀ w : HeightOneSpectrum (𝓞 D.host.E), D.host.conj • 𝔪 ≤ w.asIdeal → ∀ i j,
    Valued.v ((1 - finMat y⁻¹) i j w) ≤ WithZero.exp (-(FractionalIdeal.count D.host.E w
      ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)))) →
  ∀ i j, InHat 1 (finMat y i j) ∧ InHat 1 (finMat y⁻¹ i j) ∧
    InHat (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ((finMat y - 1) i j) := by
  intro D hc 𝔪 Sf hG n y hoff hcong
  obtain ⟨h0, hsup, -, hS⟩ := hG
  have h0' : D.host.conj • 𝔪 ≠ ⊥ := fun h => h0 (by
    have := congrArg (fun I => D.host.conj⁻¹ • I) h
    simpa using this)
  have hb : ∀ w : HeightOneSpectrum (𝓞 D.host.E), D.host.conj • 𝔪 ≤ w.asIdeal → ∀ i j,
      Valued.v (finMat y i j w) ≤ 1 ∧ Valued.v (finMat y⁻¹ i j w) ≤ 1 := by
    intro w hw
    refine integral_of_cong y w fun i j => (hcong w hw i j).trans_lt ?_
    have h1 := (count_coe_ne_zero_iff w h0').2 hw
    have h2 := FractionalIdeal.count_coe_nonneg D.host.E w (D.host.conj • 𝔪)
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have key : ∀ w : HeightOneSpectrum (𝓞 D.host.E), ∀ i j, Valued.v (finMat y i j w) ≤ 1 ∧ Valued.v (finMat y⁻¹ i j w) ≤ 1 ∧
      Valued.v ((finMat y - 1) i j w) ≤ WithZero.exp (-(FractionalIdeal.count D.host.E w
        (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E))) := by
    intro w i j
    by_cases hw : 𝔪 ≤ w.asIdeal
    · obtain ⟨w', e', hv, hcnt, -⟩ := hc w
      have hw' : D.host.conj • 𝔪 ≤ w'.asIdeal := by
        rw [e']; exact Ideal.pointwise_smul_le_pointwise_smul_iff.2 hw
      have t : ∀ (z : Formalism.MainNotions.StandardLatticesGL3.GA D n) (a b : Fin n), Valued.v (finMat z a b w) = Valued.v (finMat z⁻¹ b a w') := by
        intro z a b
        unfold finMat
        rw [Matrix.map_apply, Matrix.map_apply, inv_apply, hv]
      refine ⟨(t y i j).trans_le (hb w' hw' j i).2, (t y⁻¹ i j).trans_le (by rw [inv_inv]; exact (hb w' hw' j i).1), ?_⟩
      rw [← hcnt 𝔪 h0]
      refine le_of_eq_of_le ?_ (hcong w' hw' j i)
      have e1 : (finMat y - 1) i j = GlobalTheory.BotFormula.toFinE D
          ((((y : GL (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin n) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) - 1) i j) := by
        unfold finMat
        rw [Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]
        split_ifs <;> simp
      have e2 : (1 - finMat y⁻¹) j i = -GlobalTheory.BotFormula.toFinE D (Formalism.MainNotions.StandardLatticesGL3.sgA D
          ((((y : GL (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin n) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) - 1) i j)) := by
        unfold finMat
        rw [Matrix.sub_apply, Matrix.sub_apply, map_sub, map_sub, Matrix.map_apply, inv_apply, neg_sub, Matrix.one_apply,
          Matrix.one_apply]
        by_cases hij : i = j
        · subst hij; simp
        · rw [if_neg hij, if_neg (Ne.symm hij)]; simp
      rw [e1, e2, ← hv]
      exact (Valuation.map_neg _ _).symm
    · have hint : Valued.v (finMat y i j w) ≤ 1 ∧ Valued.v (finMat y⁻¹ i j w) ≤ 1 := by
        by_cases hu : w.under (𝓞 D.host.F) ∈ Sf
        · obtain ⟨w₀, hw₀, e₀⟩ := (hS _).1 hu
          obtain ⟨w', e', -, -, hun⟩ := hc w₀
          rcases (hun w).1 e₀.symm with rfl | rfl
          · exact absurd hw₀ hw
          · exact hb _ (by rw [e']; exact Ideal.pointwise_smul_le_pointwise_smul_iff.2 hw₀) i j
        · exact hoff w hu i j
      refine ⟨hint.1, hint.2, ?_⟩
      have hz : FractionalIdeal.count D.host.E w (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) = 0 := by
        by_contra h; exact hw ((count_coe_ne_zero_iff w h0).1 h)
      rw [hz, neg_zero, WithZero.exp_zero, Matrix.sub_apply]
      exact val_sub_le hint.1 (val_one_le i j w)
  exact fun i j => ⟨(inHat_one_iff _).2 fun w => (key w i j).1, (inHat_one_iff _).2 fun w => (key w i j).2.1,
    fun w => (key w i j).2.2⟩

end GlobalTheory.CosetOrth.Cong
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValueAtInvariantFieldTranslateSqZero
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TangentOrigin

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VertCoeffRing

theorem spMap_fstHom_surjective (B : Type) [CommRing B] :
    Function.Surjective (spMap (TrivSqZeroExt.fstHom B B B).toRingHom) := by
  intro p
  haveI := p.isPrime
  refine ⟨(⟨p.asIdeal.comap (algebraMap B (DualNumber B)), Ideal.IsPrime.comap _⟩ : PrimeSpectrum B), ?_⟩
  refine PrimeSpectrum.ext (Ideal.ext fun x => ?_)
  change (algebraMap B (DualNumber B)) x.fst ∈ p.asIdeal ↔ x ∈ p.asIdeal
  have hx : x = algebraMap B (DualNumber B) x.fst + TrivSqZeroExt.inr x.snd := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have hn : (TrivSqZeroExt.inr x.snd : DualNumber B) ∈ p.asIdeal := by
    apply p.isPrime.mem_of_pow_mem 2
    rw [pow_two, TrivSqZeroExt.inr_mul_inr]
    exact zero_mem _
  constructor
  · intro h
    rw [hx]
    exact add_mem h hn
  · intro h
    have h2 := sub_mem h hn
    rwa [show x - TrivSqZeroExt.inr x.snd = algebraMap B (DualNumber B) x.fst by
      rw [sub_eq_iff_eq_add]; exact hx] at h2

theorem evalPt_tvE_mul : ∀ {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {u : TanM (𝟙 (Sp R)) G} {dd : Fld G.left}, IsInv G u dd → ∀ {B : Type} [CommRing B] [Algebra R B]
    (e : B) (he : e * e = 0) (z : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) B ⟶ G) (O : G.left.Opens) (h : ⊤ ≤ z.left ⁻¹ᵁ O),
    ∃ h' : ⊤ ≤ ((ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.epsTo R e he) ≫ GlobalTheory.VertCoeffRing.tvE u) * z).left ⁻¹ᵁ O, ∀ f,
      GlobalTheory.TangentOrigin.evalPt _ O h' f = GlobalTheory.TangentOrigin.evalPt z.left O h f + e * GlobalTheory.TangentOrigin.evalPt z.left O h (dd O f) := by
  intro R _ G _ _ u dd hinv B _ _ e he z O h
  set φ : R →+* B := algebraMap R B with hφ
  have hz : z.left ≫ G.hom = spMap φ := Over.w z
  have eφ : (dualMap φ).comp (algebraMap R (DualNumber R)) = (algebraMap B (DualNumber B)).comp φ := by
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have hv : (tv u).left ≫ G.hom = spMap (algebraMap R (DualNumber R)) :=
    (Over.w (tv u)).trans (Category.comp_id _)
  have h2 : (spMap (dualMap φ) ≫ (tv u).left) ≫ G.hom = (tEpsG (z.left ≫ G.hom)).hom := by
    show _ = spMap (algebraMap B (DualNumber B)) ≫ z.left ≫ G.hom
    refine (Category.assoc _ _ _).trans ((congrArg (spMap (dualMap φ) ≫ ·) hv).trans ?_)
    rw [hz, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, eφ]
  let g' : tEpsG (z.left ≫ G.hom) ⟶ G :=
    Over.homMk (spMap (algebraMap B (DualNumber B)) ≫ z.left) (Category.assoc _ _ _)
  let v' : tEpsG (z.left ≫ G.hom) ⟶ G := Over.homMk (spMap (dualMap φ) ≫ (tv u).left) h2
  have htr : IsTr G φ z.left u (g' * v').left := ⟨g', v', rfl, rfl, rfl⟩

  have hk : ∀ (t : B) (ht : t * t = 0), ∃ kt : Chart.sp (R₀ := R) B ⟶ tEpsG (z.left ≫ G.hom),
      kt.left = spMap (GlobalTheory.SqZero.dualTo (AlgHom.id R B) t ht).toRingHom ∧ kt ≫ g' = z ∧
        kt ≫ v' = Chart.spMap (GlobalTheory.SqZero.epsTo R t ht) ≫ tvE u := by
    intro t ht
    have hτa : (GlobalTheory.SqZero.dualTo (AlgHom.id R B) t ht).toRingHom.comp (algebraMap B (DualNumber B)) =
        RingHom.id B := by
      ext b
      simp [GlobalTheory.SqZero.dualTo_apply, TrivSqZeroExt.algebraMap_eq_inl]
    have hsp : spMap (GlobalTheory.SqZero.dualTo (AlgHom.id R B) t ht).toRingHom ≫ spMap (algebraMap B (DualNumber B)) =
        𝟙 _ := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hτa, CommRingCat.ofHom_id, Spec.map_id]
    refine ⟨Over.homMk (spMap (GlobalTheory.SqZero.dualTo (AlgHom.id R B) t ht).toRingHom) ?_, rfl, ?_, ?_⟩
    · show spMap _ ≫ spMap (algebraMap B (DualNumber B)) ≫ z.left ≫ G.hom = _
      rw [← Category.assoc, hsp, Category.id_comp]
      exact hz
    · apply Over.OverMorphism.ext
      show spMap _ ≫ spMap (algebraMap B (DualNumber B)) ≫ z.left = z.left
      rw [← Category.assoc, hsp, Category.id_comp]
    · apply Over.OverMorphism.ext
      show spMap _ ≫ spMap (dualMap φ) ≫ (tv u).left = (Chart.spMap (GlobalTheory.SqZero.epsTo R t ht)).left ≫ (tv u).left
      rw [Chart.spMap_left, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 3
      refine RingHom.ext fun a => ?_
      simp [GlobalTheory.SqZero.dualTo_apply, GlobalTheory.SqZero.epsTo, dualMap, hφ, TrivSqZeroExt.algebraMap_eq_inl, Algebra.smul_def]
  obtain ⟨k, hkl, hkg, hkv⟩ := hk e he
  obtain ⟨k0, hk0l, hk0g, hk0v⟩ := hk 0 (mul_zero 0)

  have hone : Chart.spMap (GlobalTheory.SqZero.epsTo R (0 : B) (mul_zero 0)) ≫ tvE u = 1 := by
    let K : Chart.sp (R₀ := R) B ⟶ overAt (𝟙 (Sp R)) (DualNumber R) :=
      Over.homMk (spMap (GlobalTheory.SqZero.epsTo R (0 : B) (mul_zero 0)).toRingHom) (by
        show _ ≫ spMap (algebraMap R (DualNumber R)) ≫ 𝟙 _ = spMap φ
        rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        congr 2
        refine RingHom.ext fun a => ?_
        simp [GlobalTheory.SqZero.epsTo, GlobalTheory.SqZero.dualTo_apply, TrivSqZeroExt.algebraMap_eq_inl, hφ])
    have e1 : Chart.spMap (GlobalTheory.SqZero.epsTo R (0 : B) (mul_zero 0)) ≫ tvE u =
        K ≫ smT (𝟙 (Sp R)) 0 (tv u) := by
      apply Over.OverMorphism.ext
      show (Chart.spMap _).left ≫ (tv u).left = spMap _ ≫ (smT (𝟙 (Sp R)) 0 (tv u)).left
      rw [smT_left, Chart.spMap_left, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 3
      refine RingHom.ext fun a => ?_
      simp [GlobalTheory.SqZero.epsTo, GlobalTheory.SqZero.dualTo_apply, epsMul]
    rw [e1, ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_mem, MonObj.comp_one]
  have hp : (Chart.spMap (GlobalTheory.SqZero.epsTo R e he) ≫ tvE u) * z = k ≫ (g' * v') := by
    rw [MonObj.comp_mul, hkg, hkv, mul_comm]
  have hp0 : k0 ≫ (g' * v') = z := by
    rw [MonObj.comp_mul, hk0g, hk0v, hone, _root_.mul_one]
  have hfst : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ (g' * v').left = z.left := by
    have := congrArg (fun q => q.left) hp0
    simp only [Over.comp_left, hk0l] at this
    have hfh : (GlobalTheory.SqZero.dualTo (AlgHom.id R B) (0 : B) (mul_zero 0)).toRingHom =
        (TrivSqZeroExt.fstHom B B B).toRingHom := RingHom.ext fun a => by
      simp [GlobalTheory.SqZero.dualTo_apply]
    rw [← hfh]
    exact this
  have hw : ⊤ ≤ (g' * v').left ⁻¹ᵁ O := by
    intro p _
    obtain ⟨q, rfl⟩ := spMap_fstHom_surjective B p
    rw [← hfst] at h
    exact h (Set.mem_univ q)
  have hpl : ((Chart.spMap (GlobalTheory.SqZero.epsTo R e he) ≫ tvE u) * z).left =
      spMap (GlobalTheory.SqZero.dualTo (AlgHom.id R B) e he).toRingHom ≫ (g' * v').left := by
    rw [hp, Over.comp_left, hkl]
  have h' : ⊤ ≤ ((Chart.spMap (GlobalTheory.SqZero.epsTo R e he) ≫ tvE u) * z).left ⁻¹ᵁ O := by
    rw [hpl]
    intro q _
    exact hw (Set.mem_univ _)
  refine ⟨h', fun f => ?_⟩
  have hval : valR (g' * v').left O f = evalPt (g' * v').left O hw f := by
    unfold valR; rw [dite_eq_left hw]; rfl
  have hvalz : valR z.left O (dd O f) = evalPt z.left O h (dd O f) := by
    unfold valR; rw [dite_eq_left h]; rfl
  have hsnd := hinv.2 B φ z.left (g' * v').left O f hz h htr
  rw [hval, hvalz] at hsnd
  have key : ∀ (y : Sp B ⟶ G.left) (hy : ⊤ ≤ y ⁻¹ᵁ O),
      spMap (GlobalTheory.SqZero.dualTo (AlgHom.id R B) e he).toRingHom ≫ (g' * v').left = y →
      evalPt y O hy f = (evalPt (g' * v').left O hw f).fst + (evalPt (g' * v').left O hw f).snd * e := by
    rintro y hy rfl
    rw [evalPt_spMap_comp _ _ O hw hy f]
    exact GlobalTheory.SqZero.dualTo_apply _ _ _ _
  have key0 : ∀ (y : Sp B ⟶ G.left) (hy : ⊤ ≤ y ⁻¹ᵁ O),
      spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ (g' * v').left = y →
      evalPt y O hy f = (evalPt (g' * v').left O hw f).fst := by
    rintro y hy rfl
    exact evalPt_spMap_comp _ _ O hw hy f
  rw [key _ h' hpl.symm, key0 _ h hfst, hsnd]
  ring

end GlobalTheory.VertCoeffRing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuedFiniteUnitaryLeOneOffOpenSubset
section
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors
open GlobalTheory.CosetOrth

noncomputable section

open scoped TensorProduct Matrix

namespace GlobalTheory.CosetOrth

section Local

open GlobalTheory.AdelicU GlobalTheory.LFun

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem valued_toCompl_le_one {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} (h : w.under (𝓞 F) = v)
    {y : Fv F v ⊗[F] E} (hy : y ∈ intLoc F E v) : Valued.v (toCompl h y) ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 <|
    intLoc_induction (p := fun y => toCompl h y ∈ w.adicCompletionIntegers E)
      (fun _ ha x => mul_mem (complMap_mem h ha) (GlobalTheory.AdeleBaseChange.algebraMap_int_mem x w))
      (by rw [map_zero]; exact zero_mem _) (fun _ _ h h' => by rw [map_add]; exact add_mem h h')
      (fun _ h => by rw [map_neg]; exact neg_mem h) hy

theorem map_evalV_map_sndA (v : HeightOneSpectrum (𝓞 F)) (z : AF F ⊗[F] E) :
    Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E)
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z) =
      Algebra.TensorProduct.map (evFin F v) (AlgHom.id F E) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a e => rfl
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

end Local

variable {D : D7}

theorem valued_finMat_finStd_le_one (V : HSp D) (hG : V.gram = 1) (k : GA D V)
    (w : HeightOneSpectrum (𝓞 D.host.E))
    (hk : GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram (w.under (𝓞 D.host.F)) k ∈
      GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram (stdLat V) (w.under (𝓞 D.host.F))) (i j : Fin V.rank) :
    Valued.v (finMat (GlobalTheory.BotClassDict.finStd V hG k) i j w) ≤ 1 := by
  have hL : stdLat V = GlobalTheory.AdelicU.stdLattice D.host.E V.rank := by
    ext x
    exact ⟨fun h i _ => Submodule.mem_one.1 (h i trivial), fun h i _ => Submodule.mem_one.2 (h i trivial)⟩
  rw [hL] at hk
  have h1 := (GlobalTheory.AdelicU.mem_stabLoc_stdLattice_iff.1 hk).1 i j
  have e : finMat (GlobalTheory.BotClassDict.finStd V hG k) i j =
      GlobalTheory.LFun.finAdEquiv D.host.F D.host.E ((finHom V k).1 i j) := by
    rw [← GlobalTheory.BotClassDict.toAfE_finStd V hG, GlobalTheory.BotClassDict.finAdEquiv_toAfE]
    rfl
  rw [e, GlobalTheory.LFun.finAdEquiv_apply rfl]
  refine valued_toCompl_le_one rfl ?_
  have e2 := map_evalV_map_sndA (w.under (𝓞 D.host.F)) ((matHom V k).1 i j)
  exact e2 ▸ h1

end GlobalTheory.CosetOrth

theorem GlobalTheory.CosetOrth.valued_finMat_le_one_of_mem_openOff : ∀ {D : D7} (V : HSp D) (g : GA D V) (y : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank) (Sf : Finset (FinPl D)), V.gram = 1 →
  GlobalTheory.BotFormula.IsFinPt V g y → g ∈ openOff V (stdLat V) Sf →
  ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∉ Sf → ∀ i j,
    Valued.v (finMat y i j w) ≤ 1 ∧ Valued.v (finMat y⁻¹ i j w) ≤ 1 := by
  intro D V g y Sf hG hy hg w hw i j
  have hfy := GlobalTheory.BotClassDict.finStd_of_isFinPt V hG hy
  subst hfy
  have h := hg _ hw
  refine ⟨GlobalTheory.CosetOrth.valued_finMat_finStd_le_one V hG g w h i j, ?_⟩
  rw [← map_inv]
  refine GlobalTheory.CosetOrth.valued_finMat_finStd_le_one V hG g⁻¹ w ?_ i j
  have h' := inv_mem h
  rwa [← map_inv] at h'
end
end

