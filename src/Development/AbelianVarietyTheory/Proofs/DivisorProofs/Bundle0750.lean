module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0731
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0013
public import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRepUniversal
section
set_option autoImplicit false
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.EndLoc.HomGlue

theorem lbIso_pullPull {P X Y : Scheme.{0}} {M : LB P} (hM : M.IsLB) (b : X ⟶ P) (c : Y ⟶ X) :
    LBIso ((M.pull b).pull c) (M.pull (c ≫ b)) :=
  LBIso.chartPull (chartPullLinComb M b (fun _ : PUnit => c) (fun _ => c ≫ b) (fun _ => 1) (𝟙 _)
      fun _ => (Category.id_comp _).symm) (chartPullId _) (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hM _))

theorem lbIso_pullAlong {X Y : Scheme.{0}} {P Q : LB X} (H : LBIso P Q) (h : Y ⟶ X) :
    LBIso (P.pull h) (Q.pull h) :=
  LBIso.chartPull (chartPullPull P h h rfl) (chartPullPull Q h h rfl) H

theorem Pt.f_eq {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}
    {Z : Scheme.{0}} {x x' : Pt A B L M Z} (h : x = x') (e : x.t = x'.t) :
    pullback.lift (pullback.fst A.hom x'.t) (pullback.snd A.hom x'.t) (by rw [pullback.condition, e]) ≫ x.f = x'.f := by
  subst h
  rw [pullback.lift_fst_snd, Category.id_comp]

section
variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}
  {V : Scheme.{0}} {j : V ⟶ S} {A' B' : Over V} [GrpObj A'] [GrpObj B'] {φA : A'.left ⟶ A.left}
  {φB : B'.left ⟶ B.left}

theorem univ_iso (hL : L.IsLB) (hM : M.IsLB) (R : HomFixRep A' B' (L.pull φA) (M.pull φB)) :
    LBIso (L.pull (R.φA ≫ φA)) ((M.pull (R.φB ≫ φB)).pull R.Φ.left) :=
  LBIso.trans (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _) (pull_isLB (pull_isLB hM _) _)
    (lbIso_pullPull hL φA R.φA).symm
    (LBIso.trans (pull_isLB (pull_isLB hL _) _) (pull_isLB (pull_isLB (pull_isLB hM _) _) _)
      (pull_isLB (pull_isLB hM _) _) R.iso (lbIso_pullAlong (lbIso_pullPull hM φB R.φB) R.Φ.left))

def univPt (hL : L.IsLB) (hM : M.IsLB) (R : HomFixRep A' B' (L.pull φA) (M.pull φB))
    (hA : IsGrpPullback A' A j φA) (hB : IsGrpPullback B' B j φB) : Pt A B L M R.H :=
  Pt.ofData (R.π ≫ j) R.AH R.BH (R.φA ≫ φA) (R.φB ≫ φB) R.Φ (R.pbA.comp hA) (R.pbB.comp hB) R.hom
    (univ_iso hL hM R)

theorem univPt_key (hL : L.IsLB) (hM : M.IsLB) (R : HomFixRep A' B' (L.pull φA) (M.pull φB))
    (hA : IsGrpPullback A' A j φA) (hB : IsGrpPullback B' B j φB) {Z P : Scheme.{0}} (c : Z ⟶ R.H) (t : Z ⟶ V)
    (e : P ⟶ pullback A.hom (t ≫ j)) (ψ : P ⟶ R.AH.left)
    (h1 : ψ ≫ R.φA ≫ φA = e ≫ pullback.fst _ _) (h2 : ψ ≫ R.AH.hom = e ≫ pullback.snd _ _ ≫ c)
    (w : pullback.fst A.hom (t ≫ j) ≫ A.hom = pullback.snd A.hom (t ≫ j) ≫ c ≫ R.π ≫ j) :
    e ≫ pullback.lift (pullback.fst _ _) (pullback.snd _ _) w ≫ pmap A (R.π ≫ j) c ≫ (univPt hL hM R hA hB).f =
      ψ ≫ R.Φ.left ≫ R.φB ≫ φB := by
  have hk : e ≫ pullback.lift (pullback.fst _ _) (pullback.snd _ _) w ≫ pmap A (R.π ≫ j) c =
      ψ ≫ (R.pbA.comp hA).1.isoPullback.hom := by
    apply pullback.hom_ext
    · simp only [pmap, Category.assoc, pullback.lift_fst, IsPullback.isoPullback_hom_fst]
      exact h1.symm
    · simp only [pmap, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, IsPullback.isoPullback_hom_snd]
      exact h2.symm
  have e0 : (univPt hL hM R hA hB).f = (R.pbA.comp hA).1.isoPullback.inv ≫ R.Φ.left ≫ R.φB ≫ φB := rfl
  have := congrArg (· ≫ ((R.pbA.comp hA).1.isoPullback.inv ≫ R.Φ.left ≫ R.φB ≫ φB)) hk
  simp only [Category.assoc, Iso.hom_inv_id_assoc] at this
  rw [e0]
  exact this

end
end GlobalTheory.EndLoc.HomGlue

namespace GlobalTheory.EndLoc.HomGlue

theorem localRep_universal : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left)
    (hL : L.IsLB) (hM : M.IsLB) (V : Scheme.{0}) (j : V ⟶ S) [IsOpenImmersion j] (A' B' : Over V) [GrpObj A']
    [GrpObj B'] (φA : A'.left ⟶ A.left) (φB : B'.left ⟶ B.left) (R : HomFixRep A' B' (L.pull φA) (M.pull φB)),
    IsGrpPullback A' A j φA → IsGrpPullback B' B j φB → ∃ y : HomGlue.Pt A B L M R.H, y.t = R.π ≫ j ∧
      ∀ (Z : Scheme.{0}) (x : HomGlue.Pt A B L M Z) (b : Z ⟶ V), x.t = b ≫ j → ∃! c : Z ⟶ R.H, y.map hL hM c = x := by
  intro S A B _ _ L M hL hM V j _ A' B' _ _ φA φB R hA hB
  refine ⟨univPt hL hM R hA hB, rfl, ?_⟩
  rintro Z ⟨t, f, w⟩ b hx
  dsimp only at hx
  subst hx
  have w₀ := w
  obtain ⟨A'', B'', _, _, φ'', ψ'', Φ'', hA'', hB'', hΦ'', hI'', e, e1, e2, e3⟩ := w₀
  let φ'A : A''.left ⟶ A'.left := hA.1.lift φ'' (A''.hom ≫ b) (by rw [hA''.1.w, Category.assoc])
  have fA : φ'A ≫ φA = φ'' := hA.1.lift_fst _ _ _
  have sA : φ'A ≫ A'.hom = A''.hom ≫ b := hA.1.lift_snd _ _ _
  have pA : IsGrpPullback A'' A' b φ'A := hA.cancel (hA''.congr rfl fA.symm) sA
  let φ'B : B''.left ⟶ B'.left := hB.1.lift ψ'' (B''.hom ≫ b) (by rw [hB''.1.w, Category.assoc])
  have fB : φ'B ≫ φB = ψ'' := hB.1.lift_fst _ _ _
  have sB : φ'B ≫ B'.hom = B''.hom ≫ b := hB.1.lift_snd _ _ _
  have pB : IsGrpPullback B'' B' b φ'B := hB.cancel (hB''.congr rfl fB.symm) sB
  have iso' : LBIso ((L.pull φA).pull φ'A) (((M.pull φB).pull φ'B).pull Φ''.left) := by
    have h1 := lbIso_pullPull hL φA φ'A
    rw [fA] at h1
    have h2 := (lbIso_pullAlong (lbIso_pullPull hM φB φ'B) Φ''.left).symm
    rw [fB] at h2
    exact LBIso.trans (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) (pull_isLB (pull_isLB (pull_isLB hM _) _) _) h1
      (LBIso.trans (pull_isLB hL _) (pull_isLB (pull_isLB hM _) _) (pull_isLB (pull_isLB (pull_isLB hM _) _) _) hI'' h2)
  obtain ⟨h, ⟨hh, ψA, ψB, qA, qB, gA, gB, qΦ⟩, huniq⟩ := R.rep Z b A'' B'' φ'A φ'B Φ'' pA pB hΦ'' iso'
  have he : e = hA''.1.isoPullback.hom := by
    apply pullback.hom_ext
    · rw [e1, IsPullback.isoPullback_hom_fst]
    · rw [e2, IsPullback.isoPullback_hom_snd]
  have hΦw : Φ''.left ≫ B''.hom = A''.hom := Over.w Φ''
  refine ⟨h, ?_, ?_⟩
  · refine Pt.ext' (show h ≫ R.π ≫ j = b ≫ j by rw [← Category.assoc, hh]) ?_
    have : IsIso e := by rw [he]; infer_instance
    rw [← cancel_epi e, e3]
    refine (univPt_key hL hM R hA hB h b e ψA (by rw [← Category.assoc, gA, fA, e1])
      (by rw [qA.1.w, ← Category.assoc, e2]) _).trans ?_
    rw [← Category.assoc ψA, ← qΦ, Category.assoc, ← Category.assoc ψB, gB, fB]
  · intro c hc
    have ht : c ≫ R.π ≫ j = b ≫ j := congrArg Pt.t hc
    have hcb : c ≫ R.π = b := (cancel_mono j).1 (by rw [Category.assoc]; exact ht)
    have hf := Pt.f_eq hc ht
    let ψA' : A''.left ⟶ R.AH.left := R.pbA.1.lift φ'A (A''.hom ≫ c) (by rw [sA, ← hcb, Category.assoc])
    have kA : ψA' ≫ R.φA = φ'A := R.pbA.1.lift_fst _ _ _
    have kA2 : ψA' ≫ R.AH.hom = A''.hom ≫ c := R.pbA.1.lift_snd _ _ _
    let ψB' : B''.left ⟶ R.BH.left := R.pbB.1.lift φ'B (B''.hom ≫ c) (by rw [sB, ← hcb, Category.assoc])
    have kB : ψB' ≫ R.φB = φ'B := R.pbB.1.lift_fst _ _ _
    have kB2 : ψB' ≫ R.BH.hom = B''.hom ≫ c := R.pbB.1.lift_snd _ _ _
    have key := univPt_key hL hM R hA hB c b e ψA' (by rw [← Category.assoc, kA, fA, e1])
      (by rw [kA2, ← Category.assoc, e2]) (by rw [pullback.condition, ← ht])
    have hΦA : R.Φ.left ≫ R.BH.hom = R.AH.hom := Over.w R.Φ
    apply huniq
    refine ⟨hcb, ψA', ψB', R.pbA.cancel (pA.congr hcb.symm kA.symm) kA2,
      R.pbB.cancel (pB.congr hcb.symm kB.symm) kB2, kA, kB, ?_⟩
    apply R.pbB.1.hom_ext
    · rw [Category.assoc, kB]
      apply hB.1.hom_ext
      · rw [Category.assoc, fB, ← e3, Category.assoc, Category.assoc, ← key]
        exact congrArg (e ≫ ·) hf.symm
      · rw [Category.assoc, sB, ← Category.assoc, hΦw, Category.assoc, Category.assoc, R.pbB.1.w,
          ← Category.assoc R.Φ.left, hΦA, ← Category.assoc, kA2, Category.assoc, hcb]
    · rw [Category.assoc, kB2, ← Category.assoc, hΦw, Category.assoc, hΦA, kA2]

end GlobalTheory.EndLoc.HomGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModFFiniteIdeleUpToExtension
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.UpIdeleMod

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (finiteCompletionMap finiteCompletionMap_coe finiteCompletionMap_mapsTo)

variable {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]


omit [NumberField K] in
theorem valued_algebraMap {R : Type} [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K]
    (v : HeightOneSpectrum R) (k : K) :
    Valued.v (algebraMap K (v.adicCompletion K) k) = v.valuation K k :=
  HeightOneSpectrum.adicCompletion.valued_coe K v k

theorem valued_finiteCompletionMap (w : HeightOneSpectrum (𝓞 E)) (x : (w.under (𝓞 K)).adicCompletion K) :
    Valued.v (finiteCompletionMap K E w x) =
      Valued.v x ^ ((w.under (𝓞 K)).asIdeal.ramificationIdx' w.asIdeal) := by
  have he : (w.under (𝓞 K)).asIdeal.ramificationIdx' w.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal (w.under (𝓞 K)).ne_bot
  rcases eq_or_ne x 0 with rfl | hx
  · rw [map_zero, map_zero, map_zero, zero_pow he]
  have hx0 : Valued.v x ≠ 0 := by simpa using hx
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer K (w.under (𝓞 K))
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  set m := WithZero.log (Valued.v x)
  set k : K := π ^ (-m)
  have hvk : (w.under (𝓞 K)).valuation K k = Valued.v x := by
    rw [map_zpow₀, hπ, ← WithZero.exp_zsmul]
    simp only [smul_eq_mul, neg_mul_neg, mul_one]
    exact WithZero.exp_log hx0
  set c : (w.under (𝓞 K)).adicCompletion K := algebraMap K _ k
  have hc : Valued.v c = Valued.v x := (valued_algebraMap (w.under (𝓞 K)) k).trans hvk
  have hc0 : c ≠ 0 := fun h => hx0 (by rw [← hc, h, map_zero])
  set u := x * c⁻¹
  have hu0 : u ≠ 0 := mul_ne_zero hx (inv_ne_zero hc0)
  have hu : Valued.v u = 1 := by
    rw [map_mul, map_inv₀, hc, mul_inv_cancel₀ hx0]
  have hu1 : u ∈ (w.under (𝓞 K)).adicCompletionIntegers K := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hu]
  have hu2 : u⁻¹ ∈ (w.under (𝓞 K)).adicCompletionIntegers K := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hu, inv_one]
  have a1 := finiteCompletionMap_mapsTo K E w hu1
  have a2 := finiteCompletionMap_mapsTo K E w hu2
  simp only [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers] at a1 a2
  have hfu : Valued.v (finiteCompletionMap K E w u) = 1 := by
    have hprod : finiteCompletionMap K E w u * finiteCompletionMap K E w u⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hu0, map_one]
    have h3 := congrArg Valued.v hprod
    rw [map_mul, map_one] at h3
    exact eq_one_of_one_le_mul_left a1 a2 h3.ge
  have hxu : x = u * c := by
    simp only [u, mul_assoc, inv_mul_cancel₀ hc0, mul_one]
  conv_lhs => rw [hxu, map_mul, map_mul, hfu, one_mul, finiteCompletionMap_coe, valued_algebraMap,
    ← HeightOneSpectrum.valuation_liesOver E (w.under (𝓞 K)) w k, hvk]
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ (w.under (𝓞 K)).ne_bot]

theorem factor_upIdele (t : (Af K)ˣ) (w : HeightOneSpectrum (𝓞 E)) :
    ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ WithZero.log (Valued.v ((upIdele K E t : Af E) w)) =
      (((Ideal.absNorm (w.under (𝓞 K)).asIdeal : ℕ) : ℝ) ^
          WithZero.log (Valued.v ((t : Af K) (w.under (𝓞 K))))) ^
        (w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K)) := by
  haveI := w.isMaximal
  haveI := (w.under (𝓞 K)).isMaximal
  have h1 : ((upIdele K E t : Af E) w) = finiteCompletionMap K E w ((t : Af K) (w.under (𝓞 K))) := rfl
  rw [h1, valued_finiteCompletionMap, WithZero.log_pow,
    Ideal.ramificationIdx'_eq_ramificationIdx _ _ (w.under (𝓞 K)).ne_bot,
    Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver w.asIdeal (w.under (𝓞 K)).asIdeal (w.under (𝓞 K)).isPrime
      (w.under (𝓞 K)).ne_bot,
    Ideal.inertiaDeg'_eq_inertiaDeg]
  push_cast
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul]
  congr 1
  rw [nsmul_eq_mul]
  push_cast
  ring


open Classical in
theorem sum_fiber (v : HeightOneSpectrum (𝓞 K)) (s : Finset (HeightOneSpectrum (𝓞 E)))
    (hs : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 K) = v → w ∈ s) :
    ∑ w ∈ s with w.under (𝓞 K) = v, w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K) =
      Module.finrank K E := by
  rw [IsFractionRing.finrank_eq (𝓞 K) K (𝓞 E) E, ← Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 E)]
  refine Finset.sum_bij'
    (fun w hw => (⟨w.asIdeal, w.isPrime, by
      rw [← (Finset.mem_filter.mp hw).2]
      exact GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.liesOver_under K E w⟩ : v.asIdeal.primesOver (𝓞 E)))
    (fun q _ => (⟨q.1, q.2.1, by
      haveI := q.2.2
      exact Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot q.1⟩ : HeightOneSpectrum (𝓞 E)))
    (fun _ _ => Finset.mem_univ _) (fun q _ => ?_) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  have hq : (⟨q.1, q.2.1, by
      haveI := q.2.2
      exact Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot q.1⟩ : HeightOneSpectrum (𝓞 E)).under (𝓞 K) = v :=
    HeightOneSpectrum.ext q.2.2.over.symm
  exact Finset.mem_filter.mpr ⟨hs _ hq, hq⟩

theorem modF_upIdele (t : (Af K)ˣ) : modF (upIdele K E t) = modF t ^ Module.finrank K E := by
  classical
  set a : HeightOneSpectrum (𝓞 K) → ℝ := fun v =>
    ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ WithZero.log (Valued.v ((t : Af K) v)) with ha
  have hfin : {v : HeightOneSpectrum (𝓞 K) | ¬ Valued.v ((t : Af K) v) = 1}.Finite :=
    Filter.eventually_cofinite.mp (FiniteAdeleRing.isUnit_iff.mp t.isUnit).2
  have hT : ((fun w : HeightOneSpectrum (𝓞 E) => w.under (𝓞 K)) ⁻¹'
      {v : HeightOneSpectrum (𝓞 K) | ¬ Valued.v ((t : Af K) v) = 1}).Finite := by
    have h2 := Filter.mem_cofinite.mp (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under K E hfin.compl_mem_cofinite)
    rwa [Set.preimage_compl, compl_compl] at h2
  set S := hfin.toFinset
  set T := hT.toFinset
  have haS : ∀ v, v ∉ S → a v = 1 := fun v hv => by
    have h3 : Valued.v ((t : Af K) v) = 1 := by
      by_contra h
      exact hv (hfin.mem_toFinset.mpr h)
    simp only [ha, h3, WithZero.log_one, zpow_zero]
  have h1 : modF t = ∏ v ∈ S, a v := by
    refine finprod_eq_prod_of_mulSupport_subset a fun v hv => ?_
    by_contra h
    exact hv (haS v h)
  have h2 : modF (upIdele K E t) = ∏ w ∈ T, a (w.under (𝓞 K)) ^
      (w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K)) := by
    unfold modF
    rw [finprod_congr (factor_upIdele t)]
    refine finprod_eq_prod_of_mulSupport_subset _ fun w hw => ?_
    by_contra h
    apply hw
    have h4 : w.under (𝓞 K) ∉ S := fun h5 => h (hT.mem_toFinset.mpr (hfin.mem_toFinset.mp h5))
    show a (w.under (𝓞 K)) ^ _ = 1
    rw [haS _ h4, one_pow]
  rw [h2, h1, ← Finset.prod_fiberwise_of_maps_to (s := T) (t := S) (g := fun w => w.under (𝓞 K))
    (fun w hw => hfin.mem_toFinset.mpr (hT.mem_toFinset.mp hw)), ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun v hv => ?_
  rw [Finset.prod_congr rfl (g := fun w => a v ^ (w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K)))
      (fun w hw => by rw [(Finset.mem_filter.mp hw).2]),
    Finset.prod_pow_eq_pow_sum, sum_fiber v T fun w hw => hT.mem_toFinset.mpr (by
      show w.under (𝓞 K) ∈ {v : HeightOneSpectrum (𝓞 K) | ¬ Valued.v ((t : Af K) v) = 1}
      rw [hw]; exact hfin.mem_toFinset.mp hv)]

end GlobalTheory.UpIdeleMod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicityLinearCharacterEqCharacterSum
section
open Formalism.L2.DIV NumberField Module

noncomputable section

namespace GlobalTheory.multiplicity_linearCharacter_eq_characterSum

theorem nOf_eq_charSum : ∀ (K : Type) [Field K] [CharZero K] (G : Type) [Group G] [Fintype G] (W : Type) [AddCommGroup W] [Module K W] [FiniteDimensional K W] (τ : Representation K G W) (H : Subgroup G) [Fintype H] (ψ : H →* Kˣ), (Formalism.IndefR.IndefiniteEpsilonOperator.nOf τ ⟨H, ψ⟩ : K) = (Nat.card H : K)⁻¹ * ∑ h : H, Formalism.IndefR.TransferLatticeStatement.charOf τ (h : G) * (((ψ h)⁻¹ : Kˣ) : K) := by
  intro K _ _ G _ _ W _ _ _ τ H _ ψ
  classical
  have hc : (Nat.card H : K) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := H)).ne'
  set T : Module.End K W := ∑ h : H, (((ψ h)⁻¹ : Kˣ) : K) • τ (h : G) with hT
  have hep : Formalism.IndefR.IndefiniteEpsilonOperator.epOp τ ⟨H, ψ⟩ = (Nat.card H : K)⁻¹ • T := by
    unfold Formalism.IndefR.IndefiniteEpsilonOperator.epOp
    congr 1
    rw [hT]
    simp only [map_inv]
    congr!
  have h1 : ∀ a : H, ((((ψ a)⁻¹ : Kˣ) : K) • τ (a : G)) * T = T := by
    intro a
    rw [hT, Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft a) _ _ fun h => ?_
    simp [smul_smul, mul_comm]
  have h2 : T * T = (Nat.card H : K) • T := by
    conv_lhs => rw [hT, Finset.sum_mul, ← hT]
    rw [Finset.sum_congr rfl fun a _ => h1 a]
    simp [Nat.card_eq_fintype_card, Nat.cast_smul_eq_nsmul]
  have hid : IsIdempotentElem (Formalism.IndefR.IndefiniteEpsilonOperator.epOp τ ⟨H, ψ⟩) := by
    rw [IsIdempotentElem, hep, smul_mul_smul_comm, h2, smul_smul, mul_assoc, inv_mul_cancel₀ hc, mul_one]
  have htr := (LinearMap.IsIdempotentElem.isProj_range _ hid).trace
  unfold Formalism.IndefR.IndefiniteEpsilonOperator.nOf Formalism.IndefR.IndefiniteEpsilonOperator.epSp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← htr, hep, map_smul, map_sum, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]
  rfl

end GlobalTheory.multiplicity_linearCharacter_eq_characterSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyStandardLatticesEqBaseVector
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.NatAtStd

theorem isSD_pi (E : Type) [Field E] [NumberField E] [StarRing E] (N : ℕ) :
    IsSDLat E N (Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)) := by
  have hr : ∀ x : E, x ∈ (algebraMap (𝓞 E) E).range ↔ IsIntegral ℤ x := fun x =>
    ⟨by rintro ⟨a, rfl⟩; exact a.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩
  have hm : ∀ x : Fin N → E, x ∈ (Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)) ↔
      ∀ k, IsIntegral ℤ (x k) := fun x => by
    simp only [Submodule.mem_pi, Set.mem_univ, forall_true_left, Submodule.mem_one]
    exact forall_congr' fun k => hr (x k)
  have hs : ∀ k : Fin N, (Pi.single k 1 : Fin N → E) ∈
      (Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)) := fun k => by
    rw [hm]
    intro j
    rw [Pi.single_apply]
    split_ifs
    · exact isIntegral_one
    · exact isIntegral_zero
  refine ⟨Submodule.fg_pi fun _ => ?_, ?_, fun y => ⟨fun hy x hx => ?_, fun h => ?_⟩⟩
  · rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
  · rw [eq_top_iff, ← (Pi.basisFun E (Fin N)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨k, rfl⟩
    simpa using hs k
  · rw [hr]
    rw [hm] at hx hy
    exact IsIntegral.sum _ fun i _ => ((hx i).map (starRingEnd E).toIntAlgHom).mul (hy i)
  · rw [hm]
    intro k
    have := h _ (hs k)
    rw [hr] at this
    simpa [stdH, Pi.single_apply, apply_ite] using this

theorem detId_std (D : D7) (N : ℕ) : TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N) = 1 := by
  classical
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨A, hA, rfl⟩
    have h : ∀ i j, ∃ b : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E b = A i j := fun i j => by
      have h1 : (Pi.single j 1 : Fin N → D.host.E) ∈ StandardLatticesGL3.stdL D N := fun k _ => by
        by_cases e : k = j
        · subst e
          rw [Pi.single_eq_same]
          exact Submodule.one_le.1 le_rfl
        · rw [Pi.single_eq_of_ne e]
          exact Submodule.zero_mem _
      have h2 := Submodule.mem_one.1 (hA _ h1 i trivial)
      simpa using h2
    choose b hb using h
    have e : A = (algebraMap (𝓞 D.host.E) D.host.E).mapMatrix (Matrix.of b) :=
      Matrix.ext fun i j => (hb i j).symm
    rw [e, ← RingHom.map_det]
    exact Submodule.mem_one.2 ⟨_, rfl⟩
  · exact Submodule.one_le.2 (Submodule.subset_span ⟨1, fun v hv => by simpa using hv, Matrix.det_one.symm⟩)

theorem chi_one (D : D7) (χ : TaylorLogMetric.IdE D → ℂ) (h : TaylorLogMetric.IsChi D χ) : χ 1 = 1 := by
  letI := D.host.cmStar
  have h1 := h.2 1
  rw [Submodule.one_eq_span]
  simpa using h1

theorem chiFac_std (D : D7) (χ : TaylorLogMetric.IdE D → ℂ) (h : TaylorLogMetric.IsChi D χ) (a b : ℕ) :
    Base.chiFac χ a b (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) = 1 := by
  simp [Base.chiFac, detId_std, chi_one D χ h]

variable (D : D7) (T : TaylorLogMetric.Tor D) {N N' : ℕ}

theorem Iop_self (A : AddSubgroup (TaylorLogMetric.VC D N N')) :
    ∃ x ∈ A, ∀ G : TaylorLogMetric.VC D N N' → ℂ, TaylorLogMetric.Iop D T A A G = fun z => TaylorLogMetric.al D T x * TaylorLogMetric.U D T x G z := by
  have htop : A.addSubgroupOf A = ⊤ := AddSubgroup.addSubgroupOf_self A
  haveI hsub : Subsingleton (A ⧸ A.addSubgroupOf A) := by
    rw [htop]; exact QuotientAddGroup.subsingleton_quotient_top
  let q0 : A ⧸ A.addSubgroupOf A := QuotientAddGroup.mk 0
  refine ⟨((Quotient.out q0 : A) : TaylorLogMetric.VC D N N'), Subtype.property _, fun G => ?_⟩
  funext z
  have hi : (A.addSubgroupOf A).index = 1 := by rw [htop]; exact AddSubgroup.index_top
  unfold TaylorLogMetric.Iop
  rw [finsum_eq_single _ q0 (fun q hq => absurd (Subsingleton.elim q q0) hq), hi]
  simp

theorem Hf_neg_right (z x : TaylorLogMetric.VC D N N') : TaylorLogMetric.Hf D T z (-x) = -TaylorLogMetric.Hf D T z x := by
  simp [TaylorLogMetric.Hf, neg_div]

theorem Hf_neg_left (z x : TaylorLogMetric.VC D N N') : TaylorLogMetric.Hf D T (-z) x = -TaylorLogMetric.Hf D T z x := by
  simp [TaylorLogMetric.Hf, neg_div]

theorem Hf_add_left (z w x : TaylorLogMetric.VC D N N') : TaylorLogMetric.Hf D T (z + w) x = TaylorLogMetric.Hf D T z x + TaylorLogMetric.Hf D T w x := by
  simp [TaylorLogMetric.Hf, add_mul, Finset.sum_add_distrib, add_div]

theorem al_neg_mul (x : TaylorLogMetric.VC D N N') : TaylorLogMetric.al D T (-x) * TaylorLogMetric.al D T x = 1 := by
  unfold TaylorLogMetric.al
  rw [Hf_neg_left, Hf_neg_right, neg_neg, ← mul_zpow]
  simp

theorem inv_op (x : TaylorLogMetric.VC D N N') (G : TaylorLogMetric.VC D N N' → ℂ) (z : TaylorLogMetric.VC D N N') :
    TaylorLogMetric.al D T (-x) * TaylorLogMetric.U D T (-x) (fun w => TaylorLogMetric.al D T x * TaylorLogMetric.U D T x G w) z = G z := by
  have h := al_neg_mul D T x
  unfold TaylorLogMetric.U
  simp only [Hf_add_left, Hf_neg_left, Hf_neg_right, neg_add_cancel_right]
  have he : Complex.exp (-(Real.pi : ℂ) * (TaylorLogMetric.Hf D T z x + -TaylorLogMetric.Hf D T x x) - (Real.pi : ℂ) * TaylorLogMetric.Hf D T x x / 2) *
      Complex.exp (-(Real.pi : ℂ) * -TaylorLogMetric.Hf D T z x - (Real.pi : ℂ) * - -TaylorLogMetric.Hf D T x x / 2) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    ring
  linear_combination (G z) * he * (TaylorLogMetric.al D T (-x) * TaylorLogMetric.al D T x) + G z * h

theorem eNat_std : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (dl : ℂ) (B : Base D cc dl) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ → B.VecP χ → ∀ a b : ℕ, Even a → Even b → TaylorLogMetric.admitted D a b (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) ∧ B.eNat χ a b (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) = B.thZero a b := by
  intro D cc dl B χ hχ hV a b ha hb
  have hA : TaylorLogMetric.admitted D a b (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) := by
    letI := D.host.cmStar
    exact ⟨ha, hb, isSD_pi _ a, isSD_pi _ b⟩
  refine ⟨hA, ?_⟩
  obtain ⟨x, hx, hI⟩ := Iop_self D B.tor (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b))
  have hTh : B.eNat χ a b (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) ∈ TaylorLogMetric.Th D B.tor (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) :=
    (hV a b _ _ hA).1
  have hfix := hTh.2 (-x) (neg_mem hx)
  have he : B.eNat χ a b (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) = fun z => TaylorLogMetric.al D B.tor x * TaylorLogMetric.U D B.tor x
      (fun w => TaylorLogMetric.al D B.tor x * TaylorLogMetric.U D B.tor x (B.thZero a b) w) z := by
    funext z
    unfold Base.eNat Base.thMoved Base.thHalf
    rw [chiFac_std D χ hχ, one_mul, hI, hI]
  have h1 : B.eNat χ a b (StandardLatticesGL3.stdL D a) (StandardLatticesGL3.stdL D b) =
      fun w => TaylorLogMetric.al D B.tor x * TaylorLogMetric.U D B.tor x (B.thZero a b) w := by
    funext z
    rw [← hfix z]
    conv_lhs => rw [he]
    exact inv_op D B.tor x _ z
  funext z
  rw [← hfix z]
  conv_lhs => rw [h1]
  exact inv_op D B.tor x _ z

end GlobalTheory.NatAtStd
end
end

