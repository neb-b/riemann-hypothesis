module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeLocalBasisDescription
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0029

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeLocalizationModelLieAlgebra
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.LieLoc

theorem coord_eq_sum {R₀ R K : Type} [CommRing R₀] [CommRing R] [CommRing K] {f : R₀ →+* R} {g : R →+* K}
    {A₀ : Over (Sp R₀)} {G : Over (Sp R)} {A : Over (Sp K)} [GrpObj A₀] [GrpObj G] [GrpObj A] [IsCommMonObj A]
    {φ : G.left ⟶ A₀.left} {ψ : A.left ⟶ G.left} (hφ : IsGrpPullback G A₀ (spMap f) φ)
    (hψ : IsGrpPullback A G (spMap g) ψ) {n m : ℕ} {v : Fin n → (epsR K ⟶ A)} (hv : IsLieBasis v)
    {e : Fin m → (epsR R ⟶ G)} (he : IsLieBasis e) {M : Fin m → Fin n → K}
    (hM : ∀ i, ∃ w, IsVecOver g ψ (e i) w ∧ IsLieComb (M i) v w)
    {u : epsR R₀ ⟶ A₀} (hu : IsTangent u) {w : epsR K ⟶ A} (hw : IsVecOver (g.comp f) (ψ ≫ φ) u w)
    {c : Fin n → K} (hc : IsLieComb c v w) : ∃ a : Fin m → R, c = ∑ i, g (a i) • M i := by
  choose e₀ h₁ h₂ using hM
  obtain ⟨u', hu', -⟩ := existsUnique_isVecOver hφ.1 u
  obtain ⟨a, ha, -⟩ := he.2 u' (hu'.isTangent hφ hu)
  have h₃ := (lieComb_baseChange R K g G A ψ hψ m e u' a e₀ w h₁ ha).1
    (EllComp.isVecOver_cancel hφ.1 hψ.1 hu' hw)
  obtain ⟨-, ht, hcomp, -⟩ := LieComb.lieComb_algebra K A n v hv.1
  exact ⟨a, (hv.2 w (ht _ _ hc)).unique hc (hcomp m M e₀ _ w h₂ h₃)⟩

theorem exists_denom {O R R' K : Type} [CommRing O] [CommRing R] [CommRing R'] [CommRing K] [Algebra O R]
    [Algebra R R'] [Algebra O K] (N : Submonoid O) [IsLocalization N R] (r : O)
    [IsLocalization.Away (algebraMap O R r) R'] (g : R' →+* K)
    (hg : ∀ x, g (algebraMap R R' (algebraMap O R x)) = algebraMap O K x) {m : ℕ} (b : Fin m → R') :
    ∃ s ∈ N, ∃ (k : ℕ) (a : Fin m → O), ∀ i, (r ^ k * s) • g (b i) = algebraMap O K (a i) := by
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsLocalization.exist_integer_multiples_of_finite
    (Submonoid.powers (algebraMap O R r)) b
  choose x hx using hk
  obtain ⟨⟨s, hs⟩, h⟩ := IsLocalization.exist_integer_multiples_of_finite N x
  choose a ha using h
  refine ⟨s, hs, k, a, fun i => ?_⟩
  rw [← hg, ha, Algebra.smul_def, Algebra.smul_def, map_mul (algebraMap R R'), hx, ← hg, Algebra.smul_def, ← map_mul]
  simp only [map_mul, map_pow]
  ring

theorem lieLat_localization : ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (R : Type) [CommRing R] [Algebra (𝓞 K) R] [Algebra R K] [IsScalarTower (𝓞 K) R K] (N : Submonoid (𝓞 K)) [IsLocalization N R] (G : Over (Sp R)) [GrpObj G] (φ : G.left ⟶ P.A.left) (ψ : F.P₀.A.left ⟶ G.left) (e : Fin F.P₀.g → (epsR R ⟶ G)) (e₀ : Fin F.P₀.g → (epsR K ⟶ F.P₀.A)) (M : Matrix (Fin F.P₀.g) (Fin F.P₀.g) K), IsGrpPullback G P.A (spMap (algebraMap (𝓞 K) R)) φ → IsGrpPullback F.P₀.A G (spMap (algebraMap R K)) ψ → ψ ≫ φ = F.φ → IsLieBasis e → (∀ i, IsVecOver (algebraMap R K) ψ (e i) (e₀ i) ∧ IsLieComb (M i) F.v (e₀ i)) →
  (∀ i, ∃ s ∈ N, s • M i ∈ F.lieLat) ∧ ∀ c ∈ F.lieLat, ∃ a : Fin F.P₀.g → R, c = ∑ i, algebraMap R K (a i) • M i := by
  intro K _ _ P F R _ _ _ _ N _ G _ φ ψ e e₀ M hφ hψ hF he hM
  refine ⟨fun i => ?_, fun c hc => ?_⟩
  · obtain ⟨n, r, M', -, hr, hL, hb⟩ := _root_.GlobalTheory.CM.LieGlue.exists_cover_lieLat K P F
    have key : ∀ j, ∃ s ∈ N, ∃ (k : ℕ) (a : Fin F.P₀.g → 𝓞 K), (r j ^ k * s) • M i = ∑ l, a l • M' j l := by
      intro j
      let R' := Localization.Away (algebraMap (𝓞 K) R (r j))
      have hu : IsUnit (algebraMap R K (algebraMap (𝓞 K) R (r j))) := by
        rw [← IsScalarTower.algebraMap_apply]
        exact IsUnit.mk0 _ (by simpa using (hr j).1)
      let g : R' →+* K := IsLocalization.Away.lift (algebraMap (𝓞 K) R (r j)) hu
      have hg : g.comp (algebraMap R R') = algebraMap R K := IsLocalization.Away.lift_comp _ hu
      have hg' : ∀ x, g (algebraMap R R' (algebraMap (𝓞 K) R x)) = algebraMap (𝓞 K) K x := fun x => by
        rw [IsScalarTower.algebraMap_apply (𝓞 K) R K, ← hg]; rfl
      let _ : Algebra R' K := g.toAlgebra
      have : IsScalarTower (𝓞 K) R' K := IsScalarTower.of_algebraMap_eq fun x => by
        rw [IsScalarTower.algebraMap_apply (𝓞 K) R R']; exact (hg' x).symm
      have h' := isGrpPullback_pullback G (spMap (algebraMap R R'))
      have n' : IsGrpPullback F.P₀.A G (spMap g ≫ spMap (algebraMap R R')) ψ :=
        hψ.congr (by rw [spMap_comp_spMap, hg]) rfl
      have w : ψ ≫ G.hom = (F.P₀.A.hom ≫ spMap g) ≫ spMap (algebraMap R R') :=
        n'.1.w.trans (Category.assoc _ _ _).symm
      have e₁ := h'.1.lift_fst _ _ w
      have hψ' := h'.cancel (n'.congr rfl e₁.symm) (h'.1.lift_snd _ _ w)
      obtain ⟨e', he', hM'⟩ := hb j R' _ _ _
        (by rw [IsScalarTower.algebraMap_apply (𝓞 K) R R']; exact IsLocalization.Away.algebraMap_isUnit _)
        ((h'.comp hφ).congr (by rw [spMap_comp_spMap, ← IsScalarTower.algebraMap_eq]) rfl) hψ'
        (by rw [← Category.assoc, e₁, hF])
      obtain ⟨b, hb⟩ := coord_eq_sum h' hψ' F.basis he' hM' (he.1 i) (by rw [e₁, hg]; exact (hM i).1) (hM i).2
      obtain ⟨s, hs, k, a, ha⟩ := exists_denom N (r j) g hg' b
      refine ⟨s, hs, k, a, ?_⟩
      rw [hb, Finset.smul_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [← smul_assoc, ha, algebraMap_smul]
    classical
    choose s hs k a h using key
    refine ⟨∏ j, s j, prod_mem fun j _ => hs j, (hL _).2 fun j => ⟨k j, (∏ l ∈ Finset.univ.erase j, s l) • a j, ?_⟩⟩
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j), smul_smul, ← _root_.mul_assoc, _root_.mul_comm, ← smul_smul, h,
      Finset.smul_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [smul_smul]; rfl
  · induction hc using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨u, hu, w, hw, hc⟩ := hc
      exact coord_eq_sum hφ hψ F.basis he (fun i => ⟨_, hM i⟩) hu
        (by rw [hF, ← IsScalarTower.algebraMap_eq]; exact hw) hc
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, by simp [add_smul, Finset.sum_add_distrib]⟩
    | smul t x _ hx =>
      obtain ⟨a, rfl⟩ := hx
      refine ⟨algebraMap (𝓞 K) R t • a, ?_⟩
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun l _ => by
        rw [Pi.smul_apply, smul_eq_mul, map_mul, ← IsScalarTower.algebraMap_apply, mul_smul, algebraMap_smul K t]

end GlobalTheory.CM.LieLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RelAmpleLineBundleOfPositiveHermitianCmForm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM

open GlobalTheory.Serre GlobalTheory.CechPic GlobalTheory.HermTensorLB

theorem isFinite_left_of_comp_eq_id {S : Scheme.{0}} {A B : Over S} [IsSeparated B.hom] (i : A ⟶ B) (r : B ⟶ A)
    (h : i ≫ r = 𝟙 A) : IsFinite i.left := by
  have : IsSeparated (r.left ≫ A.hom) := by rw [Over.w r]; infer_instance
  have : IsSeparated r.left := IsSeparated.of_comp r.left A.hom
  have : IsClosedImmersion (i.left ≫ r.left) := by
    rw [← Over.comp_left, h, Over.id_left]; infer_instance
  have : IsClosedImmersion i.left := IsClosedImmersion.of_comp i.left r.left
  infer_instance

theorem relAmple_of_kForm_pos : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsNoetherianRing R] (ω : R) (C : Ell H R ω) (D : Datum H) (ε : ℤˣ) (h : D.La → D.La → OK H) (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (b : OAct (OK H) A) (t : Serre.IsTensor A b C.P.A C.act D.La) (N : LB A.left), IsKForm D ε h → (∀ x : D.La, x ≠ 0 → 0 < (ε : ℤ) * D.EF (H.w0 • x) x) → N.IsLB → (∃ t : LB.Gen (Theta A N), t.IsGen) → LBIso N (cubeLB A ![𝟙 A, b.act (wK H)] N) → (∀ m m', LamEq N (t.tmul m) (t.tmul m') C.P.L (C.act.act (h m m')) (𝟙 C.P.A)) → Out.RelAmple A N := by
  intro laws E _ _ _ H R _ _ ω C D ε h A _ _ b t N hK hpos hN hT hiso hlam
  obtain ⟨n, k, l, r, hn, hrl, hl⟩ := _root_.GlobalTheory.CM.HermSq.kForm_sum_sq E H D ε h hK hpos
  obtain ⟨-, -, ⟨br, hbr, -, hbb⟩, -, -, hproj⟩ := OK_isDedekindDomain_and_projective E H
  obtain ⟨hfinM, hprojM, -⟩ := hproj D.La D.fin D.proj
  have hl' : ∀ x y, (n : OK H) * h x y = ∑ i, l x i * br (l y i) := fun x y => Subtype.ext (by
    have := hl x y
    simp only [← hbr] at this
    simpa using this)
  have hL := C.P.isLB
  obtain ⟨rig, hrig⟩ := C.P.rigid
  obtain ⟨cub⟩ := (laws.cube _ C.P ⟨C.P.L, rig, hL, hrig⟩ rfl).1
  have hΘ : ∃ t : LB.Gen (Theta C.P.A C.P.L), t.IsGen := ⟨cub.t, cub.isGen⟩
  let q := Out.powIsPowGrp C.P.A k
  let ψ := t.mapLeft (IsTensor.pow q C.act) l
  let p : Fin k → (A ⟶ C.P.A) := fun i => ψ ≫ q.pr i
  have pl : ∀ i, IsLinearHom b C.act (p i) := fun i =>
    (t.isLinearHom_mapLeft _ _).comp (isLinearHom_pr q C.act i)
  have pm : ∀ i, IsMonHom (p i) := fun i => (pl i).1
  have hp : ∀ m i, t.tmul m ≫ p i = C.act.act (l m i) := fun m i => by simp [p, ψ]
  have am := C.act.hom
  have adj : ∀ {T : Over (Sp R)} (x y : T ⟶ C.P.A) (c : OK H),
      lam (cls C.P.L hL) (x ≫ C.act.act c) y = lam (cls C.P.L hL) x (y ≫ C.act.act (br c)) := by
    intro T x y c
    have h₀ := (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).2 (C.adj c (br c) (hbr c))
    have h' := congrArg (pull (lift x y).left)
      ((cls_cube_two hL _ _ _).symm.trans (h₀.trans (cls_cube_two hL _ _ _)))
    simpa only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc, Category.comp_id] using h'
  have base : ∀ {T : Over (Sp R)} (x y : T ⟶ C.P.A) (m m' : D.La),
      lam (cls N hN) (x ≫ t.tmul m) (y ≫ t.tmul m') = lam (cls C.P.L hL) (x ≫ C.act.act (h m m')) y := by
    intro T x y m m'
    have h₀ := (cls_eq_iff (LB.isLB_linComb hN _ _) (LB.isLB_linComb hL _ _)).2 (hlam m m')
    have h' := congrArg (pull (lift x y).left)
      ((cls_cube_two hN _ _ _).symm.trans (h₀.trans (cls_cube_two hL _ _ _)))
    simpa only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc, Category.comp_id] using h'
  have key : ∀ {T : Over (Sp R)} (x y : T ⟶ A),
      n • lam (cls N hN) x y = ∑ i, lam (cls C.P.L hL) (x ≫ p i) (y ≫ p i) := by
    intro T x y
    induction x using t.induction_on with
    | one => simp only [MonObj.one_comp, lam_one_left, smul_zero, Finset.sum_const_zero]
    | mul x x' hx hx' =>
      simp only [MonObj.mul_comp, lam_mul_left hN hT, lam_mul_left hL hΘ, smul_add, hx, hx', Finset.sum_add_distrib]
    | tmul m x =>
      induction y using t.induction_on with
      | one => simp only [MonObj.one_comp, lam_one_right, smul_zero, Finset.sum_const_zero]
      | mul y y' hy hy' =>
        simp only [MonObj.mul_comp, lam_mul_right hN hT, lam_mul_right hL hΘ, smul_add, hy, hy',
          Finset.sum_add_distrib]
      | tmul m' y =>
        let φ : OK H →+ Pic T.left := AddMonoidHom.mk' (fun c => lam (cls C.P.L hL) (x ≫ C.act.act c) y) fun c d => by
          simp only [C.act.add, MonObj.comp_mul, lam_mul_left hL hΘ]
        have hφ : ∀ c d, lam (cls C.P.L hL) (x ≫ C.act.act c) (y ≫ C.act.act d) = φ (c * br d) := by
          intro c d
          have := adj (x ≫ C.act.act c) y (br d)
          rw [hbb, Category.assoc, ← C.act.mul] at this
          exact this.symm
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [Category.assoc, hp, hφ, ← map_sum, ← hl', base, ← nsmul_eq_mul, map_nsmul]
        rfl
  have prim : ∀ x : A ⟶ C.P.A, lam (cls C.P.L hL) x (x ≫ C.act.act (wK H)) = pull x.left (cls C.P.L hL) := by
    intro x
    have h₀ := ((cls_eq_iff hL (LB.isLB_linComb hL _ _)).2 C.prim).trans (cls_cube_two hL _ _ _)
    have h' := congrArg (pull x.left) h₀
    simpa only [pull_lam, Category.comp_id] using h'.symm
  have hB : (Out.boxLB C.P.L q.pr).IsLB := LB.isLB_linComb hL _ _
  have hψB := pull_isLB hB ψ.left
  have final : LBIso ((Out.boxLB C.P.L q.pr).pull ψ.left) (lbPow N n) := by
    refine (cls_eq_iff hψB (LB.isLB_linComb hN _ _)).1 ?_
    have h₀ := ((cls_eq_iff hN (LB.isLB_linComb hN _ _)).2 hiso).trans (cls_cube_two hN _ _ _)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [cls_lbPow hN, cls_pull hB, cls_linComb hL, h₀, key, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Category.id_comp, (pl i).comm, prim, one_smul, ← pull_comp]
    rfl
  have hA : IsAbelianScheme A := t.isAbelianScheme C.P.isAb
  have hG : IsAbelianScheme (Out.powObj C.P.A k) := (IsTensor.pow q C.act).isAbelianScheme C.P.isAb
  have := hG.proper
  have hfin : IsFinite ψ.left := isFinite_left_of_comp_eq_id ψ ((IsTensor.pow q C.act).mapLeft t r)
    (by rw [← IsTensor.mapLeft_comp, hrl, IsTensor.mapLeft_id])
  have hid : IsFinite (𝟙 A : A ⟶ A).left := by rw [Over.id_left]; infer_instance
  have a₁ := (relAmple_finite_pow_iso _ A _ ψ _ 1 one_pos hA hG hB hfin).1 (relAmple_powObj_boxLB R C.P k)
  have a₂ := (relAmple_finite_pow_iso _ A A (𝟙 A) _ 1 one_pos hA hA hψB hid).2.2.2 _
    (LB.isLB_linComb hN _ _) final a₁
  exact (relAmple_finite_pow_iso _ A A (𝟙 A) N n hn hA hA hN hid).2.1.1 a₂

end GlobalTheory.CM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.VecLineNormSqEqForm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.CM.LieMetric

theorem vecLine_norm_sq_eq_form : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (A : Out.PolAV (Sp (𝓞 K))) (x : KeyIn K) (φ : x.P.A.left ⟶ A.A.left) (hf : IsPolFibre (algebraMap (𝓞 K) K) A x.P φ) (h : HermFam K (Fin x.P.g → K)), (GenFib.mk x.P φ hf x.v x.basis : GenFib A).IsHerm h → ∀ (i : Fin x.P.g) (ℓ : MLine K), IsVecLine A x φ i ℓ → ∀ s : K →+* ℂ, ℓ.n s ^ 2 = (h.form s (Pi.single i 1) (Pi.single i 1)).re := by
  intro hU hL K _ _ A x φ hf h H i ℓ hℓ s
  obtain ⟨xs, u, Hm, χ, W, hg, hpb, hA, hW, e⟩ := hℓ.2.2 s
  obtain ⟨ψ, hg', hψ, hv⟩ := GlobalTheory.KeyFibre.exists_isPolFibre_of_keyPB K ℂ s x xs hpb
  have hc : IsLieComb (Pi.single i 1) x.v (x.v i) :=
    (LieComb.isLieComb_iff_tanExp _ _).2 (LieComb.tanExp_single x.basis.1 i).symm
  have hv' : IsVecOver s ψ (x.v i) (xs.v (i.cast hg.symm)) := hv (i.cast hg.symm)
  have := form_eq_pi_mul_hermForm hU hL K A (GenFib.mk x.P φ hf x.v x.basis) h H s xs.P ψ u Hm χ hψ hA
    _ _ _ _ _ _ W W hc hc hv' hv' hW hW
  rw [e]
  refine Eq.trans ?_ (congrArg Complex.re this).symm
  rw [Complex.re_ofReal_mul]
  rfl

end GlobalTheory.CM.LieMetric
end

