module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCocycle
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0131
public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIntDomainDim
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatDefs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormExistsOfCocycle
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
noncomputable section
namespace GlobalTheory.CompanionTheory.GrForm

variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

theorem lift_sub_mem {W : X.Opens} {P : ObjectProperty (Thick (LL q))} (hP : ∀ T, P T → InU W T) (f : Γ(X, W))
    (v : ∀ T : Thick (LL q), T.B) (hv : ∀ (T : Thick (LL q)) (h : InU W T), Ideal.Quotient.mk T.J (v T) = ev T h f)
    {T T' : P.FullSubcategory} (φ : T ⟶ T') :
    (show (sP P).A.obj T' from v T'.obj) - ((sP P).A.map φ).hom (show (sP P).A.obj T from v T.obj) ∈ (sP P).J.S T' := by
  have h := hP _ T.property
  have h' := hP _ T'.property
  change v T'.obj - φ.hom.φ (v T.obj) ∈ T'.obj.J
  rw [← Ideal.Quotient.eq, hv _ h', ev_nat φ.hom h h' f, ← hv _ h]
  rfl

theorem exists_of_cocycle : StCocycle → StExists := by
  intro hC O _ X q W d t u hu P hP r x
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil P
  have hu' : ∀ i {T T' : P.FullSubcategory} (φ : T ⟶ T'),
      (show (sP P).A.obj T' from u i T'.obj) - ((sP P).A.map φ).hom (show (sP P).A.obj T from u i T.obj) ∈ (sP P).J.S T' :=
    fun i _ _ φ => lift_sub_mem hP (t i) (u i) (hu i) φ
  have hy : ∀ (I : Idx r d) {T T' : P.FullSubcategory} (φ : T ⟶ T'),
      (show (sP P).A.obj T' from lft W T'.obj (x I)) -
        ((sP P).A.map φ).hom (show (sP P).A.obj T from lft W T.obj (x I)) ∈ (sP P).J.S T' :=
    fun I _ _ φ => lift_sub_mem hP (x I) (fun T => lft W T (x I)) (fun T h => lft_spec T h (x I)) φ
  choose f hf hz using fun I : Idx r d =>
    hC hF (fun i (T : P.FullSubcategory) => (show (sP P).A.obj T from u i T.obj)) hu'
      (fun T : P.FullSubcategory => (show (sP P).A.obj T from lft W T.obj (x I))) (hy I) I.1
  have hd : CH.d (sq (sFil P r) (sFil P ((r : ℤ) + 1))) r (∑ I, f I) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_eq_zero fun I _ => hf I
  refine ⟨(CH.cx (sq (sFil P r) (sFil P ((r : ℤ) + 1)))).cls (∑ I, f I) hd, ∑ I, f I, hd, rfl, ?_⟩
  intro s
  have e : (show sqM (sFil P r) (sFil P ((r : ℤ) + 1)) _ from (∑ I, f I) s) =
      ∑ I, (show sqM (sFil P r) (sFil P ((r : ℤ) + 1)) _ from f I s) := Finset.sum_apply _ _ _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, AddSubmonoidClass.coe_finsetSum, map_sum]
  exact Finset.sum_congr rfl fun I _ => hz I s

end GlobalTheory.CompanionTheory.GrForm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormLocalOfFrame
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
noncomputable section
namespace GlobalTheory.CompanionTheory.GrForm

theorem rep_congr {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R} {a b : IdF A} {j : ℕ}
    {z z' : ∀ s : ComposableArrows C j, A.obj (s.obj (Fin.last j))} {c : CH.H (sq a b) j}
    (h : ∀ s, z s - z' s ∈ b.S _) (hr : Rep a b z c) : Rep a b z' c := by
  obtain ⟨f, hf, hc, hz⟩ := hr
  exact ⟨f, hf, hc, fun s => (hz s).trans (Ideal.Quotient.eq.2 (h s))⟩

section Frame
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {d : ℕ} (E : Frame (Φ := Φ) d)
  (σ : ∀ T : C, E.D ⟶ T) {t : Fin d → Φ.A.obj E.D} (ht : E.Coords t) {u : Fin d → ∀ T : C, Φ.A.obj T}
  (hu : ∀ i T, (Φ.A.map (σ T)).hom (t i) = u i T)

include ht hu

theorem a_eq (i : Fin d) {T T' : C} (φ : T ⟶ T') : E.a σ i φ = u i T' - (Φ.A.map φ).hom (u i T) := by
  have e : (Φ.A.map (σ T ≫ φ)).hom (t i) = (Φ.A.map φ).hom ((Φ.A.map (σ T)).hom (t i)) := by
    rw [Functor.map_comp]; rfl
  rw [Frame.a, ht, hu, e, hu]

theorem form_eq {j : ℕ} (I : Fin j → Fin d) (x : Φ.A.obj E.D) (s : ComposableArrows C j) :
    E.form σ I x s = wz u I s * (Φ.A.map (σ _)).hom x := by
  unfold Frame.form wz
  refine congrArg (· * _) (Finset.prod_congr rfl fun k _ => ?_)
  rw [a_eq E σ ht hu]

theorem form_sub_mem {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) {r : ℕ} (I : Fin r → Fin d) (x : Φ.A.obj E.D)
    (s : ComposableArrows C r) (l : Φ.A.obj (s.obj (Fin.last r)))
    (hl : (Φ.A.map (σ _)).hom x - l ∈ Φ.J.S _) :
    E.form σ I x s - wz u I s * l ∈ (Fil ((r : ℤ) + 1)).S _ := by
  have hm : ∀ i {T T' : C} (φ : T ⟶ T'), u i T' - (Φ.A.map φ).hom (u i T) ∈ Φ.J.S T' := fun i T T' φ => by
    rw [← a_eq E σ ht hu]
    exact E.mem _ _ _
  have h1 := wz_mem hF u hm I s
  have h2 : (Φ.A.map (σ _)).hom x - l ∈ (Fil ((1 : ℕ) : ℤ)).S _ := by
    simpa [hF.one] using hl
  have h3 := hF.mul r 1 _ h1 h2
  rw [form_eq E σ ht hu, ← mul_sub]
  simpa using h3

end Frame

theorem stLoc : StFrame → KH.LocGr → KH.PolyTf → StLoc := by
  intro hFr hLoc hPoly O _ l s hb X q W d c u hu r hr
  obtain ⟨E, σ, θ, hGr, hbot, hco, hσ, hpt⟩ := hFr l s hb q c u hu
  obtain ⟨Q, hQ⟩ := hPoly (dividedPowersBot O) q (Ideal.Quotient.mk ⊥) l s {W}
  have hF : IsFil (sP (SS q l s W)) (sFil (SS q l s W)) := GlobalTheory.CompanionTheory.DPFil.isFil_sFil (SS q l s W)
  obtain ⟨-, hL⟩ := hLoc Q hF E σ hGr (r : ℤ) (fun r' h => (hQ r' (by omega)).1) r
  obtain ⟨h2, h3⟩ := hL 0 (by simp)
  have hin : ∀ T : (SS q l s W).FullSubcategory, InU W T.obj := fun T => by
    obtain ⟨-, V, hV, h⟩ := T.property
    rwa [Set.mem_singleton_iff.1 hV] at h
  have key : ∀ (y : Idx r d → Γ(X, W)) (z : ComposableArrows (SS q l s W).FullSubcategory r),
      (∑ I : Idx r d, E.form σ I.1 (θ (y I)) z) - (∑ I : Idx r d,
        wz (Φ := sP (SS q l s W)) (fun i T => u i T.obj) I.1 z *
          (show (sP (SS q l s W)).A.obj (z.obj (Fin.last r)) from lft W (z.obj (Fin.last r)).obj (y I))) ∈
        (sFil (SS q l s W) ((r : ℤ) + 1)).S _ := by
    intro y z
    rw [← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun I _ => ?_
    refine form_sub_mem E σ hco (u := fun i T => u i T.obj) (fun i T => hσ i T) hF I.1 _ z _ ?_
    have h := hpt _ (hin (z.obj (Fin.last r))) (y I)
    rw [← lft_spec _ (hin (z.obj (Fin.last r))) (y I)] at h
    exact Ideal.Quotient.eq.1 h
  refine ⟨fun cl => ?_, fun x hx => ?_⟩
  · obtain ⟨x, -, hx⟩ := h2 cl
    refine ⟨fun I => θ.symm (x I), ?_⟩
    refine rep_congr (fun z => ?_) hx
    have := key (fun I => θ.symm (x I)) z
    simpa using this
  · have h4 := h3 (fun I => θ (x I)) (fun I => by
      rw [hF.top _ (by simp)]
      trivial) (rep_congr (fun z => by
        have := Ideal.neg_mem_iff _ |>.2 (key x z)
        simpa using this) hx)
    funext I
    have h5 := h4 I
    have e : (sFil (SS q l s W) (((0 : ℕ) : ℤ) + 1)).S E.D = ⊥ := by
      simpa using hbot 1 one_ne_zero
    rw [e] at h5
    exact θ.injective ((Ideal.mem_bot.1 h5).trans (map_zero θ).symm)

end GlobalTheory.CompanionTheory.GrForm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormRestrict
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
noncomputable section
namespace GlobalTheory.CompanionTheory.GrForm

variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

theorem lift_cocycle_mem {W : X.Opens} {d : ℕ} {t : Fin d → Γ(X, W)} {u : Fin d → ∀ T : Thick (LL q), T.B}
    (hu : IsLift W t u) {Q : ObjectProperty (Thick (LL q))} (hQ : ∀ T, Q T → InU W T) (i : Fin d)
    {T T' : Q.FullSubcategory} (φ : T ⟶ T') :
    (show (sP Q).A.obj T' from u i T'.obj) - ((sP Q).A.map φ).hom (show (sP Q).A.obj T from u i T.obj) ∈ (sP Q).J.S T' := by
  have h := hQ _ T.property
  have h' := hQ _ T'.property
  change u i T'.obj - φ.hom.φ (u i T.obj) ∈ T'.obj.J
  refine Ideal.Quotient.eq.1 ?_
  rw [hu i T'.obj h', ev_nat φ.hom h h' (t i), ← hu i T.obj h]
  rfl

theorem lft_res_sub_mem {W W' : X.Opens} (hW : W' ≤ W) (T : Thick (LL q)) (h : InU W T) (h' : InU W' T) (f : Γ(X, W)) :
    lft W T f - lft W' T (rs hW f) ∈ T.J := by
  refine Ideal.Quotient.eq.1 ?_
  rw [lft_spec T h f, lft_spec T h' (rs hW f), ev_res hW T h h' f]

theorem stRes : StRes := by
  intro O _ X q W W' hW d t u hu P P' hPP hP hP' r x c hc
  obtain ⟨f, hf, rfl, hz⟩ := hc
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil P'
  have hP'W : ∀ T, P' T → InU W T := fun T h => hP T (hPP T h)
  refine ⟨(resU (GF q r) hPP).pullC r f, ?_, rfl, ?_⟩
  · have := (resU (GF q r) hPP).d_pullC r f
    refine this.trans ?_
    have hf' : CH.d (P.ι ⋙ GF q r) r f = 0 := hf
    rw [hf', map_zero]
  · intro s
    refine (hz (s ⋙ ObjectProperty.ιOfLE hPP)).trans ?_
    refine Ideal.Quotient.eq.2 ?_
    have hdiff : ∀ I : Idx r d,
        wz (Φ := sP P') (fun i T => u i T.obj) I.1 s *
          ((show (sP P').A.obj (s.obj (Fin.last r)) from lft W (s.obj (Fin.last r)).obj (x I)) -
            (show (sP P').A.obj (s.obj (Fin.last r)) from lft W' (s.obj (Fin.last r)).obj (rs hW (x I)))) ∈
          (sFil P' ((r : ℤ) + 1)).S (s.obj (Fin.last r)) := by
      intro I
      have hw := wz_mem hF (fun i T => u i T.obj)
        (fun i {T T'} φ => lift_cocycle_mem hu hP'W i φ) I.1 s
      have hδ : (show (sP P').A.obj (s.obj (Fin.last r)) from lft W (s.obj (Fin.last r)).obj (x I)) -
          (show (sP P').A.obj (s.obj (Fin.last r)) from lft W' (s.obj (Fin.last r)).obj (rs hW (x I))) ∈
          (sFil P' ((1 : ℕ) : ℤ)).S (s.obj (Fin.last r)) := by
        have e : (sFil P' ((1 : ℕ) : ℤ)).S (s.obj (Fin.last r)) = (sP P').J.S (s.obj (Fin.last r)) := hF.one _
        rw [e]
        exact lft_res_sub_mem hW _ (hP'W _ (s.obj (Fin.last r)).property) (hP' _ (s.obj (Fin.last r)).property) (x I)
      have := hF.mul r 1 _ hw hδ
      simpa using this
    have hsum := Ideal.sum_mem _ (t := Finset.univ) (fun I _ => hdiff I)
    simp only [mul_sub, Finset.sum_sub_distrib] at hsum
    exact hsum

end GlobalTheory.CompanionTheory.GrForm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormSmul
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.GrFormSmul
open GlobalTheory.CompanionTheory.GrForm

theorem rep_smul {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R} (a b : IdF A) {j : ℕ}
    {z z' : ∀ s : ComposableArrows C j, A.obj (s.obj (Fin.last j))} {c : CH.H (sq a b) j} (r : R)
    (h : Rep a b z c) (hz : ∀ s, z' s - r • z s ∈ b.S _) : Rep a b z' (r • c) := by
  obtain ⟨f, hf, rfl, hfz⟩ := h
  refine ⟨r • f, by rw [map_smul, hf, smul_zero], rfl, fun s => ?_⟩
  rw [Ideal.Quotient.eq.mpr (hz s), ← Ideal.Quotient.mkₐ_eq_mk R, map_smul, Ideal.Quotient.mkₐ_eq_mk, ← hfz s]
  rfl

variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

theorem lft_str_sub {W : X.Opens} (T : Thick (LL q)) (h : InU W T) (a : O) (f : Γ(X, W)) :
    lft W T (strV q W a * f) - T.i a * lft W T f ∈ T.J := by
  rw [← Ideal.Quotient.eq, lft_spec T h, map_mul, map_mul, lft_spec T h, ev_str T h]

theorem lift_nat {W : X.Opens} {d : ℕ} {t : Fin d → Γ(X, W)} {u : Fin d → ∀ T : Thick (LL q), T.B}
    (hu : IsLift W t u) (i : Fin d) {T T' : Thick (LL q)} (φ : T ⟶ T') (h : InU W T) (h' : InU W T') :
    u i T' - φ.φ (u i T) ∈ T'.J := by
  rw [← Ideal.Quotient.eq, hu i T' h', ev_nat φ h h', ← hu i T h, Ideal.quotientMap_mk]

private theorem mul_mem_sFil_succ_of_mem_sFil_of_mem_J {P : ObjectProperty (Thick (LL q))} {r : ℕ} (T : P.FullSubcategory)
    {y z : T.obj.B} (hy : y ∈ (sFil P (r : ℤ)).S T) (hz : z ∈ T.obj.J) :
    y * z ∈ (sFil P ((r : ℤ) + 1)).S T := by
  have h1 : z ∈ pdP T.obj.δ 1 := by
    have := GlobalTheory.CompanionTheory.DPFil.dpow_mem_pdP T.obj.δ 1 hz
    rwa [T.obj.δ.dpow_one hz] at this
  exact GlobalTheory.CompanionTheory.DPFil.dividedPowerFiltration_mul_le T.obj.δ r 1 (Ideal.mul_mem_mul (show y ∈ pdP T.obj.δ r from hy) h1)

theorem stSmul : StSmul := by
  intro O _ X q W d t u hu P hP r x c a hc
  unfold Rp at hc ⊢
  refine rep_smul _ _ a hc (fun s => ?_)
  have hw : ∀ I : Fin r → Fin d, wz (Φ := sP P) (fun i T => u i T.obj) I s ∈ (sFil P (r : ℤ)).S (s.obj (Fin.last r)) :=
    fun I => wz_mem (GlobalTheory.CompanionTheory.DPFil.isFil_sFil P) _
      (fun i T T' φ => lift_nat hu i (P.ι.map φ) (hP _ T.property) (hP _ T'.property)) I s
  simp only [Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ (fun I _ => ?_)
  rw [← mul_smul_comm, ← mul_sub]
  exact mul_mem_sFil_succ_of_mem_sFil_of_mem_J _ (hw _) (lft_str_sub _ (hP _ (s.obj (Fin.last r)).property) a (x I))

end GlobalTheory.CompanionTheory.GrFormSmul
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormVanishOfFrame
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section
namespace GlobalTheory.CompanionTheory.GrForm

theorem isLift_lft {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} (W : X.Opens) {d : ℕ}
    (t : Fin d → Γ(X, W)) : IsLift (q := q) W t (fun i T => lft W T (t i)) :=
  fun i T h => lft_spec T h (t i)

theorem rep_zero {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R} (a b : IdF A) {j : ℕ}
    (c : CH.H (sq a b) j) (h : Rep a b (fun s => 0) c) : c = 0 := by
  obtain ⟨f, hf, rfl, hz⟩ := h
  have e : f = 0 := by
    funext s
    apply Subtype.ext
    rw [show (show sqM a b _ from f s).1 = _ from hz s]
    simp
  subst e
  rfl

theorem van : StFrame → CrystallineSemistableComparison.Pb.KH.LocGr → CrystallineSemistableComparison.Pb.KH.PolyTf → StVan := by
  intro hFr hL hP O _ l s hb X q W d c r j hrs hjr
  obtain ⟨E, σ, θ, hGr, hbot, -, -, -⟩ := hFr l s hb q c _ (isLift_lft W c.t)
  obtain ⟨Q, hQ⟩ := hP (dividedPowersBot O) q (Ideal.Quotient.mk ⊥) l s {W}
  have hCr : ∀ r' ≤ (r : ℤ) + 1, Q.Crit (sFil (SS q l s W)) r' := fun r' h => (hQ r' (by omega)).1
  have key := hL Q (GlobalTheory.CompanionTheory.DPFil.isFil_sFil (SS q l s W)) E σ hGr (r : ℤ) hCr j
  rcases lt_or_gt_of_ne hjr with hlt | hlt
  · obtain ⟨h1, -⟩ := key.2 (r - j) (by omega)
    have all : ∀ cl : CH.H (gr (sFil (SS q l s W)) (r : ℤ)) j, cl = 0 := by
      intro cl
      obtain ⟨x, hx, hR⟩ := h1 cl
      have x0 : ∀ I, x I = 0 := fun I => by
        have h := hx I
        rw [hbot (r - j) (by omega)] at h
        exact h
      have e : (fun s => ∑ I : Idx j d, E.form σ I.1 (x I) s) = fun s => 0 := by
        funext s
        refine Finset.sum_eq_zero fun I _ => ?_
        simp [x0, Frame.form]
      rw [e] at hR
      exact rep_zero _ _ cl hR
    exact ⟨fun a b => (all a).trans (all b).symm⟩
  · exact key.1 (by exact_mod_cast hlt)

end GlobalTheory.CompanionTheory.GrForm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KrullDimQuotientEqTrdegSucc
section
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.CompanionTheory.DimChart

theorem isIso_residueFieldMap {X Y : Scheme.{0}} (j : X ⟶ Y) [IsOpenImmersion j] (x : X) :
    IsIso (j.residueFieldMap x) := by
  refine (ConcreteCategory.isIso_iff_bijective _).mpr ⟨(j.residueFieldMap x).hom.injective, ?_⟩
  intro a
  obtain ⟨b, rfl⟩ := X.residue_surjective x a
  obtain ⟨c, rfl⟩ := j.stalkMap_surjective x b
  refine ⟨Y.residue _ c, ?_⟩
  rw [← CommRingCat.comp_apply, Scheme.residue_residueFieldMap]
  rfl

noncomputable def residueFieldEquiv {Y : Scheme.{0}} {B : Type} [CommRing B] (j : Spec (.of B) ⟶ Y)
    [IsOpenImmersion j] (q : PrimeSpectrum B) :
    Y.residueField (j q) ≃+* q.asIdeal.ResidueField :=
  haveI := isIso_residueFieldMap j q
  (asIso (j.residueFieldMap q) ≪≫ Scheme.Spec.residueFieldIso (.of B) q).commRingCatIsoToRingEquiv

theorem trdeg_int_eq_of_isFractionRing (A : Type) [CommRing A] [IsDomain A] [Algebra ℤ A] (L : Type)
    [Field L] [Algebra ℤ L] [Algebra A L] [IsFractionRing A L]
    (hA : Function.Injective (algebraMap ℤ A)) :
    Algebra.trdeg ℤ A = Algebra.trdeg ℤ L := by
  obtain rfl : ‹Algebra ℤ A› = Ring.toIntAlgebra A := Subsingleton.elim _ _
  obtain rfl : ‹Algebra ℤ L› = Ring.toIntAlgebra L := Subsingleton.elim _ _
  have : FaithfulSMul A L :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (IsFractionRing.injective A L)
  have : FaithfulSMul ℤ A := (faithfulSMul_iff_algebraMap_injective _ _).2 hA
  have : Algebra.IsAlgebraic A L := IsLocalization.isAlgebraic L (nonZeroDivisors A)
  rw [← trdeg_add_eq ℤ A (A := L), trdeg_eq_zero (R := A) (A := L), add_zero]

theorem trdeg_int_eq_of_ringEquiv {L L' : Type} [CommRing L] [CommRing L'] [Algebra ℤ L]
    [Algebra ℤ L'] (e : L ≃+* L') : Algebra.trdeg ℤ L = Algebra.trdeg ℤ L' := by
  obtain rfl : ‹Algebra ℤ L› = Ring.toIntAlgebra L := Subsingleton.elim _ _
  obtain rfl : ‹Algebra ℤ L'› = Ring.toIntAlgebra L' := Subsingleton.elim _ _
  exact e.toIntAlgEquiv.trdeg_eq

theorem ringKrullDim_quotient_eq (Y : Scheme.{0}) (B : Type) [CommRing B] [Algebra ℤ B]
    [Algebra.FiniteType ℤ B] (j : Spec (.of B) ⟶ Y) [IsOpenImmersion j] (q : PrimeSpectrum B)
    (h0 : CharZero (Y.residueField (j q))) :
    ringKrullDim (B ⧸ q.asIdeal) =
      (((Algebra.trdeg ℤ (Y.residueField (j q))).toENat + 1 : ℕ∞) : WithBot ℕ∞) := by
  have e := residueFieldEquiv j q
  have : CharZero q.asIdeal.ResidueField := charZero_of_injective_ringHom (f := e.toRingHom) e.injective
  have hinj : Function.Injective (algebraMap ℤ (B ⧸ q.asIdeal)) := by
    have hK : Function.Injective
        ((algebraMap (B ⧸ q.asIdeal) q.asIdeal.ResidueField).comp (algebraMap ℤ (B ⧸ q.asIdeal))) := by
      rw [show (algebraMap (B ⧸ q.asIdeal) q.asIdeal.ResidueField).comp
        (algebraMap ℤ (B ⧸ q.asIdeal)) = Int.castRingHom _ from Subsingleton.elim _ _]
      exact Int.cast_injective
    rw [RingHom.coe_comp] at hK
    exact Function.Injective.of_comp hK
  have : Algebra.FiniteType ℤ (B ⧸ q.asIdeal) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℤ q.asIdeal) (Ideal.Quotient.mkₐ_surjective _ _)
  rw [GroundTheory.Heights₂.Heights.IntDomainDim.proof (B ⧸ q.asIdeal) hinj,
    trdeg_int_eq_of_isFractionRing (B ⧸ q.asIdeal) q.asIdeal.ResidueField hinj,
    trdeg_int_eq_of_ringEquiv e.symm]

end GlobalTheory.CompanionTheory.DimChart
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeIdealQuotientChain
section
open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LatVal

variable {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ)

theorem f_mem_IB : f ξ ∈ Lat.IB f ξ := Ideal.subset_span (Set.mem_singleton _)

theorem η_mem_IB : Lat.η f ξ l M ∈ Lat.IB f ξ := by
  unfold Lat.η
  rw [Algebra.smul_def]
  exact Ideal.mul_mem_left _ _ (f_mem_IB f ξ)

theorem dpE_succ_mem_IB (i : ℕ) : Lat.dpE f ξ l M (i + 1) ∈ Lat.IB f ξ := by
  unfold Lat.dpE
  rw [Algebra.smul_def]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ (η_mem_IB f ξ l M) _ (Nat.succ_pos i))

theorem dpE_zero_eq : Lat.dpE f ξ l M 0 = 1 := by simp [Lat.dpE]

theorem exists_rep_B (x : B) (hx : x ∈ Lat.sub f ξ l M) : ∃ a : W, x - f a ∈ Lat.IB f ξ := by
  unfold Lat.sub at hx
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨w, rfl⟩ | ⟨i, rfl⟩
    · exact ⟨w, by simp⟩
    · cases i with
      | zero => exact ⟨1, by simp [dpE_zero_eq]⟩
      | succ i => exact ⟨0, by simpa using dpE_succ_mem_IB f ξ l M i⟩
  | zero => exact ⟨0, by simp⟩
  | one => exact ⟨1, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, ?_⟩
    have h := Ideal.add_mem _ ha hb
    have e : x + y - f (a + b) = x - f a + (y - f b) := by rw [map_add (f := _)]; ring
    rw [e]; exact h
  | neg x _ hx =>
    obtain ⟨a, ha⟩ := hx
    refine ⟨-a, ?_⟩
    have h := Ideal.neg_mem_iff _ |>.2 ha
    have e : -x - f (-a) = -(x - f a) := by rw [map_neg]; ring
    rw [e]; exact h
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a * b, ?_⟩
    have h := Ideal.add_mem _ (Ideal.mul_mem_right y _ ha) (Ideal.mul_mem_left _ (f a) hb)
    have e : x * y - f (a * b) = (x - f a) * y + f a * (y - f b) := by rw [map_mul]; ring
    rw [e]; exact h

theorem exists_rep (x : Lat.A f ξ l M) : ∃ a : W, Lat.ι f ξ l M x - f a ∈ Lat.IB f ξ :=
  exists_rep_B f ξ l M _ x.2

theorem mem_of_dvd {a b : W} {x y : Lat.A f ξ l M}
    (hx : Lat.ι f ξ l M x - f a ∈ Lat.IB f ξ) (hy : Lat.ι f ξ l M y - f b ∈ Lat.IB f ξ)
    (h : Ideal.Quotient.mk (Ideal.span {ξ}) a ∣ Ideal.Quotient.mk (Ideal.span {ξ}) b) :
    y ∈ Ideal.span {x} ⊔ Lat.I f ξ l M := by
  obtain ⟨c', hc⟩ := h
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c'
  rw [← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton] at hc
  obtain ⟨d, hd⟩ := hc
  have hI : y - Lat.ofW f ξ l M c * x ∈ Lat.I f ξ l M := by
    show Lat.ι f ξ l M (y - Lat.ofW f ξ l M c * x) ∈ Lat.IB f ξ
    have h1 : f (b - a * c) ∈ Lat.IB f ξ := by
      rw [hd, map_mul]; exact Ideal.mul_mem_right _ _ (f_mem_IB f ξ)
    have h2 := Ideal.add_mem _ (Ideal.sub_mem _ hy (Ideal.mul_mem_left _ (f c) hx)) h1
    have e : Lat.ι f ξ l M (y - Lat.ofW f ξ l M c * x)
        = Lat.ι f ξ l M y - f b - f c * (Lat.ι f ξ l M x - f a) + f (b - a * c) := by
      rw [map_sub, map_mul, Lat.ι_ofW, map_sub, map_mul]; ring
    rw [e]; exact h2
  have hs : Lat.ofW f ξ l M c * x ∈ Ideal.span {x} :=
    Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _))
  have e : y = Lat.ofW f ξ l M c * x + (y - Lat.ofW f ξ l M c * x) := by ring
  rw [e]
  exact Submodule.add_mem_sup hs hI

theorem val : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ) (m : ℕ),
    Lat.Hyp f ξ l m → ∀ x y : Lat.A f ξ l M,
      x ∈ Ideal.span {y} ⊔ Lat.I f ξ l M ∨ y ∈ Ideal.span {x} ⊔ Lat.I f ξ l M := by
  intro W B _ _ _ f ξ l M m h x y
  obtain ⟨a, ha⟩ := exists_rep f ξ l M x
  obtain ⟨b, hb⟩ := exists_rep f ξ l M y
  rcases h.val (Ideal.Quotient.mk _ a) (Ideal.Quotient.mk _ b) with hd | hd
  · exact Or.inr (mem_of_dvd f ξ l M ha hb hd)
  · exact Or.inl (mem_of_dvd f ξ l M hb ha hd)

end GlobalTheory.CompanionTheory.LatVal
end

